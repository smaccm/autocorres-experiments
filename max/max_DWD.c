#include <stdint.h>

uint32_t max(uint32_t * arr, uint32_t len) {
  uint32_t m, i;
  for(m = 0, i = 0; i < len; i++) {
    if(arr[i] > m) {
      m = arr[i];
    }
  }
  return m;
}
