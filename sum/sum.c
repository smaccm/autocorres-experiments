/* #include <stdio.h> */

struct integer_result {
  unsigned char overflow;
  unsigned int result;
};

struct integer_result sum(const unsigned int x) {

  struct integer_result r = {0,0};
  unsigned int i = 0;
  while (x >= i) {
    if( r.result+i < i || i+1 < i ) {
      r.overflow = 1;
      //break; - I do not know how to reason through this yet.
    } 
    r.result += i;
    i += 1;
  }
  return r;
}


