/* #include <stdio.h> */
unsigned int sum(const unsigned int x) {

  unsigned int s = 0;
  unsigned int i = 0;
  while (x >= i) {
    s += i;
    i += 1;
  }
  return s;
}


/* int main() {

  unsigned int c = 0;
  for(c=0;c<50000;c++) {
    if(sum(c) != (c*(c+1))/2) {
      printf("%u\n",sum(c));
      printf("%u\n",c*(c+1)/2);
      return 0;
    }
  }
  return 0;
} */

