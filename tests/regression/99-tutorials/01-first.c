// PARAM: --set "ana.activated[+]" signs
#include <goblint.h>

int main() {
  int x;
  int y = -1;
  int unknown;

  if (unknown) {
    x = -5;
  } else {
    x = -7;
  }

  // The above code branches on an uninitialized variable.
  // The value of x could be either -5 or -7.

  __goblint_check(x < 0); // works
  __goblint_check(0 < x); // unknown, but why? 
  __goblint_check(0 < y); // works with y
  __goblint_check(x > 0); // unknown, but why?
  __goblint_check(0 > x); // works

  return 0;
}
