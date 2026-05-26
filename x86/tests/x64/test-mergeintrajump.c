// Regression test for mergeIntraJump not joining jump bounds.
// When a block is re-discovered via multiple predecessors, the jump bounds
// at the merge point should be the join of all incoming bounds, not just
// the last predecessor processed.

int probe(void);
int sink(int);

int test_mergeintrajump(void) {
    int x = probe();
    int v;

    if (x == 0x1234) { v = 100; goto merge; }
    if (x == 0x5678) { v = 200; goto merge; }
    if (x == 0x9abc) { v = 300; goto merge; }
    return -1;

merge:
    return sink(x + v);
}
