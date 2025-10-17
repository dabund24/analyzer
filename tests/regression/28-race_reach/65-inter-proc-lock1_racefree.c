//PARAM: --set lib.activated[+] sv-comp
#include <pthread.h>
#include "racemacros.h"

int global = 0;
pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

void *t1_fun(void *arg) {
  pthread_mutex_lock(&mutex);
  assert_racefree(global); // no race
  pthread_mutex_unlock(&mutex);
  return NULL;
}

void *t2_fun(void *arg) { // t2 is protected by mutex locked in main thread
    access(global);
}

int main(void) {
  create_threads(t1);
  pthread_mutex_lock(&mutex);
  create_threads(t2);
  join_threads(t2);
  pthread_mutex_unlock(&mutex);
  return 0;
}
