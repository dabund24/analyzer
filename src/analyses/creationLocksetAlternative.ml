(** alternative creation lockset analysis
    @see https://github.com/goblint/analyzer/pull/1865
*)

open Analyses
module TID = ThreadIdDomain.Thread
module TIDs = ConcDomain.MustThreadSet
module LID = LockDomain.MustLock
module LIDs = LockDomain.MustLockset

(** [creationLocksetAlternative]
    collects parent threads, which could protect the ego thread and its descendants,
    since the creation must happen with a lock held.
*)
module CreationLocksetAlternative = struct
  include IdentityUnitContextsSpec
  module D = Lattice.Unit

  module V = struct
    include TID
    include StdV
  end

  module G = Queries.CLS

  let name () = "creationLocksetAlternative"
  let startstate _ = D.bot ()
  let exitstate _ = D.bot ()

  let threadspawn man ~multiple lval f args fman =
    let ask = ask_of_man man in
    let tid_lifted = ask.f Queries.CurrentThreadId in
    let child_ask = ask_of_man fman in
    let child_tid_lifted = child_ask.f Queries.CurrentThreadId in
    match tid_lifted, child_tid_lifted with
    | `Lifted tid, `Lifted child_tid when TID.must_be_ancestor tid child_tid ->
      let lockset = ask.f Queries.MustLockset in
      let to_contribute = G.singleton tid lockset in
      man.sideg child_tid to_contribute
    | _ -> ()

  let query man (type a) (x : a Queries.t) : a Queries.result =
    match x with
    | Queries.CreationLocksetAlternative tid -> (man.global tid : G.t)
    | _ -> Queries.Result.top x
end

(** [taintedCreationLocksetAlternative]
    collects parent threads, which cannot protect the ego thread and its descendants,
    since an unlock could happen before joining
*)
module TaintedCreationLocksetAlternative = struct
  include IdentityUnitContextsSpec
  module D = Lattice.Unit

  module V = struct
    include TID
    include StdV
  end

  module LockToThreads = MapDomain.MapBot (LID) (TIDs)
  module G = MapDomain.MapBot (TID) (LockToThreads)

  let name () = "taintedCreationLocksetAlternative"
  let startstate _ = D.bot ()
  let exitstate _ = D.bot ()

  let get_unique_created_children tid (ask : Queries.ask) =
    let created_threads = ask.f Queries.CreatedThreads in
    TIDs.filter (TID.must_be_ancestor tid) created_threads

  (** handle unlock of mutex [lock] *)
  let unlock man tid created_tids lock =
    let ask = ask_of_man man in
    let joinedThreads = ask.f Queries.MustJoinedThreads in
    let contribute_lock child_tid =
      let to_contribute = G.singleton tid (LockToThreads.singleton lock joinedThreads) in
      man.sideg child_tid to_contribute
    in
    TIDs.iter contribute_lock created_tids

  (** handle unlock of an unknown mutex. Assumes that any mutex could have been unlocked *)
  let unknown_unlock man tid created_tids =
    let ask = ask_of_man man in
    let evaporate_locksets child_tid =
      let allCreationLocksets = ask.f @@ Queries.CreationLocksetAlternative child_tid in
      let creationLockset = CreationLocksetAlternative.G.find tid allCreationLocksets in
      let to_contribute_value =
        LIDs.fold
          (fun lock acc ->
             LockToThreads.join acc (LockToThreads.singleton lock (TIDs.empty ())))
          creationLockset
          (LockToThreads.empty ())
      in
      let to_contribute = G.singleton tid to_contribute_value in
      man.sideg child_tid to_contribute
    in
    TIDs.iter evaporate_locksets created_tids

  let event man e _ =
    match e with
    | Events.Unlock addr ->
      let ask = ask_of_man man in
      let tid_lifted = ask.f Queries.CurrentThreadId in
      (match tid_lifted with
       | `Lifted tid ->
         let created_tids = get_unique_created_children tid ask in
         let lock_opt = LockDomain.MustLock.of_addr addr in
         (match lock_opt with
          | Some lock -> unlock man tid created_tids lock
          | None -> unknown_unlock man tid created_tids)
       | _ -> ())
    | _ -> ()

  module A = struct
    (** ego tid * must-lockset * creation-lockset *)
    include Printable.Prod3 (TID) (LIDs) (Queries.CLS)

    let name () = "creationLockset"

    (** checks if [cl1] has a member ([tp1] |-> [ls1]) and [cl2] has a member ([tp2] |-> [ls2])
        such that [ls1] and [ls2] are not disjoint and [tp1] != [tp2]
        @param cl1 creation-lockset of first thread [t1]
        @param cl2 creation-lockset of second thread [t2]
        @returns whether [t1] and [t2] must be running mutually exclusive
    *)
    let both_protected_inter_threaded cl1 cl2 =
      let cl2_has_same_lock_other_tid tp1 ls1 =
        Queries.CLS.exists
          (fun tp2 ls2 -> not (LIDs.disjoint ls1 ls2 || TID.equal tp1 tp2))
          cl2
      in
      Queries.CLS.exists cl2_has_same_lock_other_tid cl1

    (** checks if [cl1] has a mapping ([tp1] |-> [ls1])
        such that [ls1] and [ls2] are not disjoint and [tp1] != [t2]
        @param cl1 creation-lockset of thread [t1] at first program point
        @param t2 thread id at second program point
        @param ls2 lockset at second program point
        @returns whether [t1] must be running mutually exclusive with second program point
    *)
    let one_protected_inter_threaded_other_intra_threaded cl1 t2 ls2 =
      Queries.CLS.exists
        (fun tp1 ls1 -> not (LIDs.disjoint ls1 ls2 || TID.equal tp1 t2))
        cl1

    let may_race (t1, ls1, cl1) (t2, ls2, cl2) =
      not
        (both_protected_inter_threaded cl1 cl2
         || one_protected_inter_threaded_other_intra_threaded cl1 t2 ls2
         || one_protected_inter_threaded_other_intra_threaded cl2 t1 ls1)

    let should_print (_t, _ls, cl) = not @@ Queries.CLS.is_empty cl
  end

  let access man _ =
    let ask = Analyses.ask_of_man man in
    let tid_lifted = ask.f Queries.CurrentThreadId in
    match tid_lifted with
    | `Lifted td ->
      let must_ancestors = TID.must_ancestors td in

      let compute_cl_transitive () =
        let cl_td = ask.f @@ Queries.CreationLocksetAlternative td in
        List.fold_left
          (fun acc t1 ->
             Queries.CLS.join acc (ask.f @@ Queries.CreationLocksetAlternative t1))
          cl_td
          must_ancestors
      in

      let compute_tcl_transitive () =
        let tcl_td = man.global td in
        List.fold_left (fun acc t1 -> G.join acc (man.global t1)) tcl_td must_ancestors
      in

      let compute_tcl_lockset tcl_transitive t0 =
        let tcl_transitive_t0 = G.find t0 tcl_transitive in
        LockToThreads.fold
          (fun l j acc -> if TIDs.mem td j then acc else LIDs.add l acc)
          tcl_transitive_t0
          (LIDs.empty ())
      in

      let compute_il cl_transitive tcl_transitive =
        Queries.CLS.fold
          (fun t0 l_cl acc ->
             let l_tcl = compute_tcl_lockset tcl_transitive t0 in
             let l_il = LIDs.diff l_cl l_tcl in
             Queries.CLS.add t0 l_il acc)
          cl_transitive
          (Queries.CLS.empty ())
      in

      let lockset = ask.f Queries.MustLockset in
      let cl_transitive = compute_cl_transitive () in
      let tcl_transitive = compute_tcl_transitive () in
      let il = compute_il cl_transitive tcl_transitive in
      td, lockset, il
    | _ -> ThreadIdDomain.UnknownThread, LIDs.empty (), Queries.CLS.empty ()
end

let _ =
  MCP.register_analysis
    ~dep:[ "threadid"; "mutex"; "threadJoins" ]
    (module CreationLocksetAlternative : MCPSpec)

let _ =
  MCP.register_analysis
    ~dep:[ "threadid"; "mutex"; "threadJoins"; "creationLocksetAlternative" ]
    (module TaintedCreationLocksetAlternative : MCPSpec)
