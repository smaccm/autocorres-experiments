

unsigned int max(unsigned int * arr, unsigned int len) {
  unsigned int m = 0;
  unsigned int i = 0;
  while (i < len) {
    if(arr[i] > m) {
      m = arr[i];
    }
    i++;
  }
  return m;
}
