#include <limits.h>
#include <stddef.h>
/*@
    requires a < INT_MAX - 10;
    ensures \result == \old(a)+10;
*/
int add_ten(int a){
    /*@
        loop invariant 0 <= i <= 10;
        loop invariant a == \at(a, Pre)+i;
        loop assigns i, a;
        loop variant 10-i;
    */
    for (int i = 0; i < 10; i++) {
        a++;
    }

    return a;
}


/*@
    requires valid_pointers:
        \valid(array_res + (0..length-1)) &&
        \valid_read(array_1 + (0..length-1)) &&
        \valid_read(array_2 + (0..length-1));

    requires mem_separation:
        \separated(array_res + (0..length-1), array_1 + (0..length-1)) &&
        \separated(array_res + (0..length-1), array_2 + (0..length-1));

    requires valid_range:
        \forall integer i; 0 <= i < length ==> 0 <= array_1[i] < 3000 && 0 <= array_2[i] < 3000;

    requires valid_length: 0 <= length < INT_MAX;

    assigns array_res[0..length-1];

    ensures \forall integer i; 0 <= i < length ==> array_res[i] == array_1[i] + array_2[i];
*/
void add_two_arrays(int* array_res, const int* array_1, const int* array_2, int length) {
    /*@
        loop invariant 0 <= i <= length;
        loop invariant \forall integer k; 0 <= k < i ==> array_res[k] == array_1[k] + array_2[k];
        loop assigns array_res[0..length-1];
        loop assigns i;
        loop variant length - i;
    */
    for (int i = 0; i < length; i++) {
        array_res[i] = array_1[i] + array_2[i];
    }
}