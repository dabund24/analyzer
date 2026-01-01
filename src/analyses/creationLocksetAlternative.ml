(** alternative creation lockset analysis
    @see https://github.com/goblint/analyzer/pull/1865
*)

open Analyses
module TID = ThreadIdDomain.Thread
module TIDs = ConcDomain.MustThreadSet
module Lock = LockDomain.MustLock
module Lockset = LockDomain.MustLockset

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

  module G = Lockset

  let name () = "creationLocksetAlternative"
  let startstate _ = D.bot ()
  let exitstate _ = D.bot ()

  let threadspawn man ~multiple lval f args fman =
    let ask = ask_of_man man in
    let tid_lifted = ask.f Queries.CurrentThreadId in
    let child_ask = ask_of_man fman in
    let child_tid_lifted = child_ask.f Queries.CurrentThreadId in
    match tid_lifted, child_tid_lifted with
    (* use [must_ancestors] instead of [must_be_ancestor], since the former is also used in [access] of the tainted analysis! *)
    | `Lifted tid, `Lifted child_tid when List.mem tid (TID.must_ancestors child_tid) ->
      let lockset = ask.f Queries.MustLockset in
      man.sideg child_tid lockset
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

  module G = MapDomain.MapBot (Lock) (TIDs)

  (** inter-threaded locksets; used in [access] and [A] *)
  module IL = MapDomain.MapBot (TID) (Lockset)

  let name () = "taintedCreationLocksetAlternative"
  let startstate _ = D.bot ()
  let exitstate _ = D.bot ()

  let get_unique_created_children tid (ask : Queries.ask) =
    let created_threads = ask.f Queries.CreatedThreads in
    TIDs.filter (TID.must_be_ancestor tid) created_threads

  (** handle unlock of mutex [lock] *)
  let unlock man tid created_tids joined_tids lock =
    let contribute_lock child_tid =
      let to_contribute = G.singleton lock joined_tids in
      man.sideg child_tid to_contribute
    in
    TIDs.iter contribute_lock created_tids

  (** handle unlock of an unknown mutex. Assumes that any mutex could have been unlocked *)
  let unknown_unlock man tid created_tids joined_tids =    let ask = ask_of_man man in
    let contribute_all_locks child_tid =
      let creation_lockset = ask.f @@ Queries.CreationLocksetAlternative child_tid in
      let to_contribute =
        Lockset.fold
          (fun lock acc -> G.join acc (G.singleton lock joined_tids))
          creation_lockset
          (G.empty ())
      in
      man.sideg child_tid to_contribute
    in
    TIDs.iter contribute_all_locks created_tids

  let event man e _ =
    match e with
    | Events.Unlock addr ->
      let ask = ask_of_man man in
      let tid_lifted = ask.f Queries.CurrentThreadId in
      (match tid_lifted with
       | `Lifted tid ->
         let created_tids = get_unique_created_children tid ask in
         let joined_tids = ask.f Queries.MustJoinedThreads in
         let lock_opt = LockDomain.MustLock.of_addr addr in
         (match lock_opt with
          | Some lock -> unlock man tid created_tids joined_tids lock
          | None -> unknown_unlock man tid created_tids joined_tids)
       | _ -> ())
    | _ -> ()

  module A = struct
    (** ego tid * must-lockset * creation-lockset *)
    include Printable.Prod3 (TID) (Lockset) (IL)

    let name () = "creationLockset"

    (** checks if [il1] has a member ([tp1] |-> [ls1]) and [il2] has a member ([tp2] |-> [ls2])
        such that [ls1] and [ls2] are not disjoint and [tp1] != [tp2]
        @param il1 creation-lockset of first thread [t1]
        @param il2 creation-lockset of second thread [t2]
        @returns whether [t1] and [t2] must be running mutually exclusive
    *)
    let both_protected_inter_threaded il1 il2 =
      let cl2_has_same_lock_other_tid tp1 ls1 =
        IL.exists (fun tp2 ls2 -> not (Lockset.disjoint ls1 ls2 || TID.equal tp1 tp2)) il2
      in
      IL.exists cl2_has_same_lock_other_tid il1

    (** checks if [il1] has a mapping ([tp1] |-> [ls1])
        such that [ls1] and [ls2] are not disjoint and [tp1] != [t2]
        @param il1 creation-lockset of thread [t1] at first program point
        @param t2 thread id at second program point
        @param ls2 lockset at second program point
        @returns whether [t1] must be running mutually exclusive with second program point
    *)
    let one_protected_inter_threaded_other_intra_threaded il1 t2 ls2 =
      IL.exists (fun tp1 ls1 -> not (Lockset.disjoint ls1 ls2 || TID.equal tp1 t2)) il1

    let may_race (t1, ls1, il1) (t2, ls2, il2) =
      not
        (both_protected_inter_threaded il1 il2
         || one_protected_inter_threaded_other_intra_threaded il1 t2 ls2
         || one_protected_inter_threaded_other_intra_threaded il2 t1 ls1)

    let should_print (_t, _ls, cl) = not @@ IL.is_empty cl
  end

  let access man _ =
    let module TclTransitive = MapDomain.MapBot (TID) (G) in
    let ask = Analyses.ask_of_man man in
    let tid_lifted = ask.f Queries.CurrentThreadId in
    match tid_lifted with
    | `Lifted td ->
      let parent = TID.parent td in
      let must_ancestors = TID.must_ancestors td in

      let compute_cl_transitive () =
        let initial_value = (* protections from parent only *)
          match parent with
          | Some td_parent -> 
            let cl_td = ask.f @@ Queries.CreationLocksetAlternative td in
            IL.singleton td_parent cl_td
          | None -> IL.empty ()
        in
        List.fold_left
          (fun acc t1 ->
             match TID.parent t1 with
             | Some t1_parent ->
               let cl_t1 = ask.f @@ Queries.CreationLocksetAlternative t1 in
               IL.join acc (IL.singleton t1_parent cl_t1)
             | None -> acc (* we don't know anything about non-transitive protections to t1 *)
          )
          initial_value
          must_ancestors
      in

      let compute_tcl_transitive () =
        let initial_value = (* tainted protections from parent only *)
          match parent with
          | Some td_parent -> 
            let tcl_td = man.global td in
            TclTransitive.singleton td_parent tcl_td
          | None -> TclTransitive.empty ()
        in
        List.fold_left
          (fun acc t1 ->
             match TID.parent t1 with
             | Some t1_parent ->
               let tcl_t1 = man.global t1 in
               TclTransitive.join acc (TclTransitive.singleton t1_parent tcl_t1)
             | None -> acc (* we don't know anything about non-transitive tainted protections to t1 *)
          )
          initial_value
          must_ancestors
      in

      let compute_tcl_lockset tcl_transitive t0 =
        let tcl_transitive_t0 = TclTransitive.find t0 tcl_transitive in
        G.fold
          (fun l j acc -> if TIDs.mem td j then acc else Lockset.add l acc)
          tcl_transitive_t0
          (Lockset.empty ())
      in
      let compute_il cl_transitive tcl_transitive =
        IL.fold
          (fun t0 l_cl acc ->
             let l_tcl = compute_tcl_lockset tcl_transitive t0 in
             let l_il = Lockset.diff l_cl l_tcl in
             IL.add t0 l_il acc)
          cl_transitive
          (IL.empty ())
      in

      let lockset = ask.f Queries.MustLockset in
      let cl_transitive = compute_cl_transitive () in
      let tcl_transitive = compute_tcl_transitive () in
      let il = compute_il cl_transitive tcl_transitive in
      td, lockset, il
    | _ -> ThreadIdDomain.UnknownThread, Lockset.empty (), IL.empty ()
end

let _ =
  MCP.register_analysis
    ~dep:[ "threadid"; "mutex"; "threadJoins" ]
    (module CreationLocksetAlternative : MCPSpec)

let _ =
  MCP.register_analysis
    ~dep:[ "threadid"; "mutex"; "threadJoins"; "creationLocksetAlternative" ]
    (module TaintedCreationLocksetAlternative : MCPSpec)
