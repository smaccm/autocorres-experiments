unsigned int sum(const unsigned int x) {
  unsigned int r = 0;
  while (x > 0) {
    r += x;
    x--;
  }
  return r;
}

