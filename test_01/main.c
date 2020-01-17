#include <stdio.h>
#include <limits.h>

/*@
  requires valid: \valid(p);
  requires valid: \valid(q);
  assigns *p;
  assigns *q;
  ensures exchange: *p == \old(*q);
  ensures exchange: *q == \old(*p);
*/
void swap_bad(int* p, int* q){
  *q = *p;
  *p = *q;
}

/*@
  requires valid: \valid(p);
  requires valid: \valid(q);
  assigns *p;
  assigns *q;
  ensures exchange: *p == \old(*q);
  ensures exchange: *q == \old(*p);
*/
void swap_good(int* p, int* q){
  int tmp = *q;
  *q = *p;
  *p = tmp;
}

/*@
  requires INT_MIN < val;
  ensures positive_value: function_result: \result >= 0;
  ensures (val == 0 ==> \result == 0) &&
          (val > 0 ==> \result == val) &&
          (val < 0 ==> \result == -val);
*/
int abs_good(int val) {
  if(val < 0) return -val;
  return val;
}

/*@
  requires INT_MIN < val;
  ensures positive_value: function_result: \result >= 0;
  ensures (val == 0 ==> \result == 0) &&
          (val > 0 ==> \result == val) &&
          (val < 0 ==> \result == -val);
*/
int abs_bad(int val) {
//  if(val == 0) {
    return 0;
//  } else {
//    if(val < 0) {
//      return val;
//    } else {
//      return -val;
//    }
//  }
}

/*@
  ensures \result == 1;
 */
int tc_01() {
  //Initialize data
  int a = -42; int b = 37;

  //Call swap_good and assert
  //@ assert ((a == -42) && (b == 37));
  swap_good(&a, &b);
  //@ assert ((a == 37) && (b == -42));

  //Assert the test case
  return ((a == 37) && (b == -42));
}

/*@
  ensures \result == 1;
 */
int tc_02() {
  //Initialize data
  int a = -42; int b = 37;

  //Call swap_bad and assert
  //@ assert ((a == -42) && (b == 37));
  swap_bad(&a, &b);
  //@ assert ((a == 37) && (b == -42));

  //Assert the test case
  return ((a == 37) && (b == -42));
}

/*@
  ensures \result == 1;
 */
int tc_03() {
  //Initialize data
  int a = -42; int b = 37;

  //Call abs_good and assert
  b = abs_good(a);
  //@ assert ((a == -42) && (b == 42));

  //Assert the test case
  return ((a == -42) && (b == 42));
}

/*@
  ensures \result == 1;
 */
int tc_04() {
  //Initialize data
  int a = -42; int b = 37;

  //Call abs_bad and assert
  b = abs_bad(a);
  //@ assert ((a == -42) && (b == 42));

  //Assert the test case
  return ((a == -42) && (b == 42));
}

int main(){
  //Define the test case result
  int res = 0;

  res = tc_01();
  //@ assert (res == 1);
  printf("Test case 01 %s\n",((res == 1)? "pass" : "fail"));

  res = tc_02();
  //@ assert (res == 1);
  printf("Test case 02 %s\n",((res == 1)? "pass" : "fail"));

  res = tc_03();
  //@ assert (res == 1);
  printf("Test case 03 %s\n",((res == 1)? "pass" : "fail"));

  res = tc_04();
  //@ assert (res == 1);
  printf("Test case 04 %s\n",((res == 1)? "pass" : "fail"));

  return 0;
}
