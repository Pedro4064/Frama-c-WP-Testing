#include <test.h>

/*@
    requires \valid(a) && \valid(b); 
    assigns *a, *b; 
    ensures *a == \old(*b); 
    ensures *b == \old(*a); 
*/
void swap(int* a, int* b) {
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

int main() {
    int a = 42;
    int b = 37;
    swap(&a, &b);
    //@ assert a == 37 && b == 42;

    int potato[5] = {1, 2, 3, 4,5};
    int res = sum(potato, 5);
    return 0;
}