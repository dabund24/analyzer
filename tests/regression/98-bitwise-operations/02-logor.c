// PARAM: --enable ana.int.interval
#include <goblint.h>

int main() {
  unsigned int u_res;
  unsigned int unsigned_x;
  unsigned int unsigned_y;

  if (unsigned_x < 14 ) {
    unsigned_x = 14;
  }

  if (unsigned_y < 35 || unsigned_y > 60) {
    unsigned_y = 60;
  }

  u_res = unsigned_x | unsigned_y;
  __goblint_check(u_res >= 35);
  __goblint_check(u_res <= __UINT32_MAX__);
  
  int res;
  int both_pos_x;
  int both_pos_y;

  if (both_pos_x < 0 ||both_pos_x > 64) {
    both_pos_x = 0;
  }

  if (both_pos_y < 10 || both_pos_y > 30) {
    both_pos_y = 30;
  }

  res = both_pos_x | both_pos_y;
  __goblint_check(res >= 10);
  __goblint_check(res <= 127);

  int both_neg_x;
  int both_neg_y;

  if (both_neg_x < -64 || both_neg_x > -1) {
    both_neg_x = -64;
  }

  if (both_neg_y < -30 || both_neg_y > -1) {
    both_neg_y = -30;
  }

  res = both_neg_x | both_neg_y;
  __goblint_check(res <= 0);
  __goblint_check(res >= -30);

  int pos_neg_x;
  int pos_neg_y;

  if (pos_neg_x < -64 || pos_neg_x > -1) {
    pos_neg_x = -64;
  }

  if (pos_neg_y > 63 || pos_neg_y < 0) {
    pos_neg_y = 63;
  }

  res = pos_neg_x | pos_neg_y;
  __goblint_check(res <= 0);
  __goblint_check(res >= -64);

  int pos_neg_x2;
  int pos_neg_y2;

  if (pos_neg_x2 < -65 || pos_neg_x2 > -1) {
    pos_neg_x2 = -65;
  }

  if (pos_neg_y2 > 30 || pos_neg_y2 < 0) {
    pos_neg_y2 = 30;
  }

  res = pos_neg_x2 | pos_neg_y2;
  __goblint_check(res <= 0);
  __goblint_check(res >= -128); 

  int pos_neg_x3;
  int pos_neg_y3;

  if (pos_neg_x3 < -30 || pos_neg_x3 > -1) {
    pos_neg_x3 = -30;
  }

  if (pos_neg_y3 > 64 || pos_neg_y3 < 0) {
    pos_neg_y3 = 64;
  }

  res = pos_neg_x3 | pos_neg_y3;
  __goblint_check(res <= 0);
  __goblint_check(res >= -64);

  int pos_neg_x4;
  int pos_neg_y4;

  if (pos_neg_x4 < -30 || pos_neg_x4 > -1) {
    pos_neg_x4 = -30;
  }

  if (pos_neg_y4 > 65 || pos_neg_y4 < 0) {
    pos_neg_y4 = 65;
  }

  res = pos_neg_x4 | pos_neg_y4;
  __goblint_check(res <= 0);
  __goblint_check(res >= -128);

  int otherwise_x;
  int otherwise_y;

  if (otherwise_x < -63 || otherwise_x > 20) {
    otherwise_x = 0;
  }

  if (otherwise_y < -10 || otherwise_y > 63) {
    otherwise_y = 0;
  }
  res = otherwise_x | otherwise_y;
  __goblint_check(res >= -64);
  __goblint_check(res <= 63);

  int x_otherwise2;
  int y_otherwise2;

  if (x_otherwise2 < -64 || x_otherwise2 > 30) {
    x_otherwise2 = 0;
  }

  if (y_otherwise2 < -20 || y_otherwise2 > 64) {
    y_otherwise2 = 0;
  }

  res = x_otherwise2 | y_otherwise2;
  __goblint_check(res >= -128);
  __goblint_check(res <= 127);

  int x_otherwise3;
  int y_otherwise3;

  if (x_otherwise3 < -1 || x_otherwise3 > 1) {
    x_otherwise3 = 0;
  }

  if (y_otherwise3 < -1 || y_otherwise3 > 1) {
    y_otherwise3 = 0;
  }

  res = x_otherwise3 | y_otherwise3;
  __goblint_check(res >= -2);
  __goblint_check(res <= 1);


  long long ll_res;
  long long ll_large_x;
  long long ll_large_y;

  if (ll_large_x < -__LONG_LONG_MAX__ + 100 || ll_large_x > __LONG_LONG_MAX__ - 100) {
    ll_large_x = 0;
  }

  if (ll_large_y < -100 || ll_large_y > 100) {
    ll_large_y = 0;
  }

  ll_res = ll_large_x | ll_large_y;
  __goblint_check(ll_res >= -__LONG_LONG_MAX__ - 1);
  __goblint_check(ll_res <= __LONG_LONG_MAX__);

  long long ll_max_x;
  long long ll_max_y;

  if (ll_max_y < -100 || ll_max_y > 100) {
    ll_max_y = 0;
  }

  ll_res = ll_max_x | ll_max_y;
  __goblint_check(ll_res >= -__LONG_LONG_MAX__ - 1);
  __goblint_check(ll_res <= __LONG_LONG_MAX__);

  return 0;
}