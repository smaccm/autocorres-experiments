#include <stdint.h>

uint32_t max(uint32_t *A, uint32_t len) {
  uint32_t result = 0;
  for (uint32_t i = 0; i < len; i++) {
    if (A[i] > result) {
      result = A[i];
    }
  }
  return result;
}