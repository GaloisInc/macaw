static int f2(int i) {
  return i + 1;
}

static int f1(void) {
  int i = 3;
  return f2(i);
}

void _start(void) {
  f1();
}
