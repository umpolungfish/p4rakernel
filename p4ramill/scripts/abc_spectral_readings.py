#!/usr/bin/env python3
"""Finite ABC discrepancy enclosures using rational log-series remainders.

No floating-point values enter the enclosure calculation. This implements
an analytic interval algorithm; it does not emit Lean proof terms.
"""
import argparse
import json
from fractions import Fraction
from math import gcd

SCALE = 10**30


def log_series_bounds(x, terms):
    """For 1 <= x <= 2: integrate the geometric series for 2/(1-z*z)."""
    z = (x - 1) / (x + 1)
    power = z
    total = Fraction(0)
    for j in range(terms):
        total += 2 * power / (2 * j + 1)
        power *= z * z
    remainder = 2 * power / ((2 * terms + 1) * (1 - z * z))
    return total, total + remainder


def log_integer_bounds(n, terms, log_two):
    k = n.bit_length() - 1
    lo, hi = log_series_bounds(Fraction(n, 2**k), terms)
    lo += k * log_two[0]
    hi += k * log_two[1]
    return (lo.numerator * SCALE // lo.denominator,
            -((-hi.numerator * SCALE) // hi.denominator))


def tables(limit, terms):
    two = log_series_bounds(Fraction(2), terms)
    logs = [(0, 0)] + [log_integer_bounds(n, terms, two) for n in range(1, limit + 1)]
    radicals = [1] * (limit + 1)
    support_lo = [0] * (limit + 1)
    support_hi = [0] * (limit + 1)
    for p in range(2, limit + 1):
        if radicals[p] != 1:
            continue
        for n in range(p, limit + 1, p):
            radicals[n] *= p
            support_lo[n] += logs[p][0]
            support_hi[n] += logs[p][1]
    return logs, radicals, support_lo, support_hi


def outward_decimal(n, denominator, upper=False, digits=18):
    scaled = n * 10**digits
    q = -((-scaled) // denominator) if upper else scaled // denominator
    sign = '-' if q < 0 else ''
    whole, fraction = divmod(abs(q), 10**digits)
    return f'{sign}{whole}.{fraction:0{digits}d}'


def readings(cutoffs, epsilons, terms):
    logs, radicals, slo, shi = tables(max(cutoffs), terms)
    best_lo = [None] * len(epsilons)
    best_hi = [None] * len(epsilons)
    lower_witness = [None] * len(epsilons)
    upper_candidate = [None] * len(epsilons)
    count = 0
    rows = []
    for c in range(2, max(cutoffs) + 1):
        for a in range(1, c):
            b = c - a
            if gcd(a, b) != 1:
                continue
            count += 1
            # Coprimality implies pairwise disjoint prime supports of a,b,c.
            radical_lo = slo[a] + slo[b] + slo[c]
            radical_hi = shi[a] + shi[b] + shi[c]
            for j, epsilon in enumerate(epsilons):
                num, den = epsilon.numerator, epsilon.denominator
                lo = den * logs[c][0] - (den + num) * radical_hi
                hi = den * logs[c][1] - (den + num) * radical_lo
                witness = [a, b, c]
                if best_lo[j] is None or lo > best_lo[j]:
                    best_lo[j], lower_witness[j] = lo, witness
                if best_hi[j] is None or hi > best_hi[j]:
                    best_hi[j], upper_candidate[j] = hi, witness
        if c in cutoffs:
            for j, epsilon in enumerate(epsilons):
                den = epsilon.denominator * SCALE
                rows.append({
                    'c_max': c, 'lean_window_index': c - 2,
                    'ordered_triples': count, 'epsilon': str(epsilon),
                    'lower': outward_decimal(best_lo[j], den),
                    'upper': outward_decimal(best_hi[j], den, upper=True),
                    'lower_exact': str(Fraction(best_lo[j], den)),
                    'upper_exact': str(Fraction(best_hi[j], den)),
                    'lower_witness': lower_witness[j],
                    'upper_candidate': upper_candidate[j],
                })
    return rows


def self_test():
    """Independent high-precision spot checks, not Lean certification."""
    from decimal import Decimal, localcontext
    with localcontext() as ctx:
        ctx.prec = 90
        logs, radical, _, _ = tables(200, 40)
        for n in range(1, 201):
            exact = Decimal(n).ln()
            assert Decimal(logs[n][0]) / SCALE <= exact <= Decimal(logs[n][1]) / SCALE
            trial = 1
            m = n
            for p in range(2, n + 1):
                if m % p == 0:
                    trial *= p
                    while m % p == 0:
                        m //= p
            assert radical[n] == trial
        rows = readings([2, 9, 30], [Fraction(1, 10), Fraction(1)], 40)
        for row in rows:
            eps = Fraction(row['epsilon'])
            e = Decimal(eps.numerator) / eps.denominator
            values = [Decimal(c).ln() - (1 + e) * Decimal(radical[a] * radical[c-a] * radical[c]).ln()
                      for c in range(2, row['c_max'] + 1)
                      for a in range(1, c) if gcd(a, c-a) == 1]
            assert len(values) == row['ordered_triples']
            assert Decimal(row['lower']) <= max(values) <= Decimal(row['upper'])
    return {'self_test': 'passed', 'integer_logs_checked': 200, 'finite_windows_checked': 6}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cutoffs', nargs='+', type=int, default=[100, 300, 1000])
    parser.add_argument('--epsilon', nargs='+', type=Fraction, default=[Fraction(1, 100), Fraction(1, 10), Fraction(1)])
    parser.add_argument('--terms', type=int, default=40)
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    if args.self_test:
        print(json.dumps(self_test(), indent=2))
        return
    if min(args.cutoffs) < 2 or min(args.epsilon) <= 0 or args.terms < 1:
        parser.error('cutoffs must be >= 2; epsilon and terms must be positive')
    print(json.dumps({'method': 'rational logarithm enclosures; not Lean proof terms',
                      'terms': args.terms, 'fixed_point_scale': str(SCALE),
                      'readings': readings(sorted(set(args.cutoffs)), args.epsilon, args.terms)}, indent=2))


if __name__ == '__main__':
    main()
