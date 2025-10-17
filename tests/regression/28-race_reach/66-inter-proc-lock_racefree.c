//PARAM: --set lib.activated[+] sv-comp
#include <pthread.h>
#include "racemacros.h"

int global = 0;
pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

void *t1child_fun(void* arg) { // t1child is protected by mutex locked in t1
    access(global);
    return NULL;
}

void *tmainchild_fun(void *arg) { // tmainchild is protected by mutex locked in main thread
    assert_racefree(global); // NO RACE
    return NULL;
}

void *t1_fun(void *arg) {
  pthread_mutex_lock(&mutex);
  create_threads(t1child);
  join_threads(t1child);
  pthread_mutex_unlock(&mutex);
  return NULL;
}

int main(void) {
  create_threads(t1);
  pthread_mutex_lock(&mutex);
  create_threads(tmainchild);
  join_threads(tmainchild);
  pthread_mutex_unlock(&mutex);
  return 0;
}
