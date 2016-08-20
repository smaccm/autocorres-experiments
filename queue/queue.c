#include <stdint.h>
#include <stdbool.h>

uint8_t contents[10];
uint32_t front = 0;
uint32_t length = 0;

bool is_full(void) {
    return length == 10;
}

bool is_empty(void) {
    return length == 0;
}

bool dequeue(uint8_t *x) {
    if (is_empty()) {
        return false;
    } else {
        *x = contents[front];
        front = (front + 1) % 10;
        length--;
        return true;
    }
}

bool enqueue(const uint8_t x) {
    if (is_full()) {
        return false;
    } else {
        contents[(front + length) % 10] = x;
        length++;
        return true;
    }
}
