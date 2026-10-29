#include "kernel/sixteen3.h"
#include <iostream>
#include <stdexcept>
using lean::sixteen3;
static sixteen3 value(unsigned m) { return sixteen3(m & 1, m & 2, m & 4, m & 8); }
static unsigned mask(sixteen3 v) { return v.hasN | (v.hasT << 1) | (v.hasF << 2) | (v.hasB << 3); }
int main() {
    using order = bool (sixteen3::*)(sixteen3 const &) const;
    using operation = sixteen3 (sixteen3::*)(sixteen3 const &) const;
    order le[] = {&sixteen3::le_i, &sixteen3::le_t, &sixteen3::le_f};
    operation joins[] = {&sixteen3::join_i, &sixteen3::join_t, &sixteen3::join_f};
    operation meets[] = {&sixteen3::meet_i, &sixteen3::meet_t, &sixteen3::meet_f};
    unsigned reverse[] = {0, 5, 3};
    for (unsigned k = 0; k < 3; ++k) for (unsigned m = 0; m < 16; ++m)
        for (unsigned n = 0; n < 16; ++n) {
            auto x = value(m), y = value(n);
            auto a = m ^ reverse[k], b = n ^ reverse[k];
            if ((x.*le[k])(y) != ((a & b) == a) ||
                mask((x.*joins[k])(y)) != ((a | b) ^ reverse[k]) ||
                mask((x.*meets[k])(y)) != ((a & b) ^ reverse[k]))
                throw std::runtime_error("native lattice oracle mismatch");
            for (unsigned p = 0; p < 16; ++p) {
                auto z = value(p);
                if ((x.*le[k])(y) && (y.*le[k])(z) && !(x.*le[k])(z))
                    throw std::runtime_error("native transitivity");
                if ((x.*le[k])(z) && (y.*le[k])(z) && !((x.*joins[k])(y).*le[k])(z))
                    throw std::runtime_error("native least upper bound");
                if ((z.*le[k])(x) && (z.*le[k])(y) && !(z.*le[k])((x.*meets[k])(y)))
                    throw std::runtime_error("native greatest lower bound");
            }
        }
    for (unsigned seed = 0; seed < 16; ++seed) {
        std::array<sixteen3, 16> table;
        for (unsigned x = 0; x < 16; ++x) table[x] = value(x | seed);
        sixteen3 result;
        if (!lean::sixteen3_fixed_point(table, result) || result != value(seed))
            throw std::runtime_error("native union fixed point");
        for (unsigned x = 0; x < 16; ++x) table[x] = value(x & seed);
        if (!lean::sixteen3_fixed_point(table, result) || result != value(0))
            throw std::runtime_error("native intersection fixed point");
    }
    std::array<sixteen3, 16> table;
    sixteen3 result;
    for (unsigned x = 0; x < 16; ++x) table[x] = value(((x << 1) | 1) & 15);
    if (!lean::sixteen3_fixed_point(table, result) || result != value(15))
        throw std::runtime_error("native full-height fixed point");
    for (unsigned x = 0; x < 16; ++x) table[x] = value(x ^ 15);
    if (lean::sixteen3_fixed_point(table, result))
        throw std::runtime_error("native nonmonotone map accepted");
    for (unsigned x = 0; x < 16; ++x) table[x] = value(x);
    table[15] = value(0);
    if (lean::sixteen3_fixed_point(table, result))
        throw std::runtime_error("native off-path nonmonotone map accepted");
    std::cout << "native SIXTEEN_3 lattice controls passed\n";
}
