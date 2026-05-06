// Test case for jump tables bounded by a bitmask (and) rather than a
// compare+branch (cmp/ja).

int ext_a(int);
int ext_b(int);
int ext_c(int);
int ext_d(int);
int ext_e(int);
int ext_f(int);
int ext_g(int);
int ext_h(int);

int switch_mask_bounded(int bits) {
    int btype = (bits >> 1) & 0x7;
    switch (btype) {
    case 0: return ext_a(bits);
    case 1: return ext_b(bits);
    case 2: return ext_c(bits);
    case 3: return ext_d(bits);
    case 4: return ext_e(bits);
    case 5: return ext_f(bits);
    case 6: return ext_g(bits);
    case 7: return ext_h(bits);
    default: __builtin_unreachable();
    }
}
