#define COUNT 10
byte n = 0;

proctype P() {
  byte x = 0;
  byte i = 0;
  for (i : 1 .. COUNT) {
    x = n;
    x = x + 1;
    n = x;
  }
}

init {
  run P(); run P();
  /* wait until all processes are finished */
  _nr_pr == 1;
  assert(2 <= n && n <= 20);
  printf("The final value is: %d\n", n);
}

ltl p1 { [] ((n == 10) -> [] (n >= 10)) }
ltl p2 { [] ((n == 10 && !enabled(1)) -> [] (n >= 10)) }
ltl p3 { !<>(n == 10 && P[1]:i == 6 && P[2]:i == 6) }
