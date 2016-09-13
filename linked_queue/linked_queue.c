#include <stdbool.h>
#include <stdint.h>

struct node {
    uint8_t element;
    struct node* next;
};

struct node *front = 0;
struct node *back = 0;

bool dequeue(uint8_t *x) {
    if (front == 0) {
        return false;
    } else {
        *x = front->element;
        front = front->next;
        if (front == 0) {
            back = 0;
        }
        return true;
    }
}

void enqueue(struct node *x) {
    if (back == 0) {
        front = x;
    } else {
        back->next = x;
    }
    x->next = 0;
    back = x;
}
