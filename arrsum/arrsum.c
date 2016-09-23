#include "stdint.h"
uint32_t arrsum(uint32_t * a, uint32_t len) {
  uint32_t j = 0;
  uint32_t s = 0;
  while (j < len) {
    s = s + a[j];
    j = j + 1;
  }
  return s;
}