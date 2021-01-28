int g = -11;
int h = -12;
void f(int* g, int* h);

void _start() {
  if (g != h) {
    f(&g, &h);
  }
}

void f(int* g, int* h){
  if (g != h){
    *g = 2;
    *h = 1;
  }
}
