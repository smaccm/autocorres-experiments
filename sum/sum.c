struct integer_result {
  unsigned char overflow;
  unsigned int result;
};

/* This function will calculate the sum for 0 to x slowly. The sum value will
   be stored in the result field of the integer_result structure. If the 
   overflow field in the integer_result structure is set then the result field
   contains some spurious value due to integer over flow. */
struct integer_result sum(const unsigned int x) {

  struct integer_result r = {0,0};
  while (x > 0) {
    /* Technically, "<" could be used here instead of "<=". However, this
       increase the difficulty of the proof because when considering a loop 
       invariant we need a logical mechanism to deal with what happens when
       "x = 0". This case however is absurd since we would never be in the loop
       to begin with if "x = 0". */
    /* For improved efficiency, we might add a break in the body of this if 
       condition. Again, that complicates the proof. */
    if( r.result+x <= r.result ) {
      r.overflow = 1;
    } 
    r.result += x;
    x--;
  }
  return r;
}


