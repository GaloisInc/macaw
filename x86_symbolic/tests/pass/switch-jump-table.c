// Regression test for "Index not in lookup table" during symbolic execution.

static int acc;
static void __attribute__((noinline)) tick(void) { acc++; }

typedef enum { A = 0, B, C, D, E, F, DONE } Mode;

typedef struct { Mode mode; } State;

__attribute__((noinline))
void run(State *s) {
    for (int i = 0; i < 128; i++) {
        tick();
        switch (s->mode) {
            case A: s->mode = B; break;
            case B: s->mode = C; break;
            case C: s->mode = D; break;
            case D: s->mode = E; break;
            case E: s->mode = F; break;
            case F: tick(); s->mode = DONE; break;
            case DONE:
            default: return;
        }
    }
}

int __attribute__((noinline)) test_jump_table(void) {
    State s = { .mode = A };
    run(&s);
    return s.mode == DONE;
}

void _start() { test_jump_table(); }
