theory graph imports
  "../../tools/autocorres/AutoCorres"
 Word
 WordBitwise
begin

new_C_include_dir "/home/dacosta/development/rockwellcollins/verification/musllibc/include"

install_C_file "./graph.c"
autocorres [ heap_abs_syntax, ts_rules = nondet ] "./graph.c"
context graph begin

end
