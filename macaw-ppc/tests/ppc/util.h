#define EXIT() \
  asm("li 0,1\n"              \
      "sc")
