#include <limits.h>

/*@
    requires INT_MIN < val;

    ensures positive_value:
        function_result:
            \result >= 0;
    ensures (val>=0 ==> \result == val) && 
            (val<0 ==> \result == -val);
 */
int abs(int val){
    return (val > 0)? val:-val;
}

/*@
    requires (INT_MIN/2 < a < INT_MAX/2) && (INT_MIN/2 < b < INT_MAX/2);
    ensures \result == a+b;
*/
int add(int a, int b){
    return a+b;
}

/*@
    requires (INT_MIN/2 < a < INT_MAX/2) && (INT_MIN/2 < b < INT_MAX/2);
    ensures((a-b) > 0 ==> \result == a-b) &&
           ((a-b) <= 0 ==> \result == b-a);
*/
int distance(int a, int b){
    return (a>b)? a-b:b-a;
}

/*@
    requires pointer_validity: \valid(q) && \valid(r) && \separated(q, r);
    requires numerical_validity: y != 0;
    ensures (*q) * y + (*r) == x;
    ensures (*r) < y;
    assigns *q, *r;
*/
void div_rem(unsigned x, unsigned y, unsigned* q, unsigned* r){
    *q = x / y;
    *r = x % y;
}

/*@
    requires \valid(a) && \valid_read(b) && \separated(a, b);

    ensures (*b==1) ==> (*a == 0);
    ensures (*b==0) ==> (*a == \old(*a));
    ensures *b == \old(*b);
    assigns *a;
*/
void reset_1st_if_2nd_is_true(int* a, int const* b){ 
    if(*b) *a=0;
}

/*@
    requires pointer_validity: \valid_read(a) && \valid_read(b);
    requires numerical_validity: INT_MIN<=*a+*b<=INT_MAX;
    assigns \nothing;
    ensures \result == *a + *b;
*/
int p_add(int* a, int* b){
    return *a + *b;
}

enum Kind {VOWEL, CONSONANT};
/*@
    requires ('a' <= c <= 'z');
    assigns \nothing;

    behavior vowel:
        assumes c \in {'a', 'e', 'i', 'o', 'u'};
        ensures \result == VOWEL;
    behavior consonant:
        assumes !(c \in {'a', 'e', 'i', 'o', 'u'});
        ensures \result == CONSONANT;
*/
enum Kind kind_of_letter(char c){
    if (c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'){
        return VOWEL;
    }
    else{
        return CONSONANT;
    }
}

/*@
    requires \valid_read(a) && \valid_read(b);
    assigns \nothing;

    behavior a_greater:
        assumes *a > *b;
        ensures \result == *a;
    behavior b_greater_eq:
        assumes *b >= *a;
        ensures \result == *b;
    complete behaviors;
    disjoint behaviors;
*/
int max_ptr(int* a, int* b){
    return (*a > *b)? *a:*b;
}