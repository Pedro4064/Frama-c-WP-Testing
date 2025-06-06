#include "test.h"

/*@
    logic integer sum_to_index(int* values, integer index) =
        (index < 0)? 0: 
                      values[index] + sum_to_index(values, index - 1);
        
    logic integer sum(int* values, integer length) = 
        sum_to_index(values, length-1);
*/

/*@
    requires valid_array: \valid(values+(0..length-1));
    requires valid_length: 0<=length<50;
    requires valid_range: \forall integer i; 0<= i < length ==> 0<=values[i]<=3000;

    assigns \nothing;

    ensures \result == sum(values, length);
 */
int sum(int *values, unsigned int length) {
    int result = 0;
    
    /*@
        loop invariant 0 <= i <= length;
        loop invariant result == (i == 0 ? 0 : sum_to_index(values, i - 1));
        loop invariant result <= i * 3000;
        loop assigns result, i;
        loop variant length - i;
    */
    for (int i = 0; i < length; i++) {
        result += values[i];
    }

    return result;
}