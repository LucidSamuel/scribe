#!/usr/bin/env python3
"""Audit the stated r3 recursive-node ledger, without running participant code.

Inputs transcribed from submission 424fd2e1-a56b-4a4a-8864-224c95fae4a6,
proof.md sections 4.4 and E.3. This checks arithmetic conditional on that schedule,
not that the schedule implements the attack or accounts for all its work.
"""
import json
from decimal import Decimal, ROUND_CEILING, localcontext

# (log2(budget + 1), multiplicity). The recursion stops at budget 63.
OUTER_CALLS = ((16, 13), (15, 2), (14, 2), (13, 2), (12, 1),
               (11, 1), (10, 2), (9, 2), (8, 1), (7, 2))


def recursive_correction(j):
    if j == 6:
        return 0
    return 2 * recursive_correction(j - 1) + 14 * 2 ** (j - 1)


def rounded_log2(numerator, denominator=1):
    # More precision than the published five decimal places, avoiding binary
    # float rounding. This is a numerical projection, not a Lean theorem.
    with localcontext() as context:
        context.prec = 80
        value = (Decimal(numerator) / Decimal(denominator)).ln() / Decimal(2).ln()
        return value.quantize(Decimal('0.00001'), rounding=ROUND_CEILING)


def audit():
    rows = []
    for j, count in OUTER_CALLS:
        per_call = recursive_correction(j)
        if per_call != 7 * 2 ** j * (j - 6):
            raise ArithmeticError('recursive and closed-form correction disagree')
        rows.append(dict(j=j, outer_calls=count, extra_ops_per_call=per_call,
                         extra_ops=count * per_call))
    delta = sum(row['extra_ops'] for row in rows)
    added_code_bytes = ((8 * 22 + 3) - (8 * 20 + 3)) * 4
    total = 50_567_592_471 + delta
    memory = 126_200_572 + added_code_bytes
    time_log = rounded_log2(total, 279)
    memory_log = rounded_log2(memory)
    return {
        'scope': 'Arithmetic conditional on the stated schedule; not attack validation.',
        'source_submission': '424fd2e1-a56b-4a4a-8864-224c95fae4a6',
        'source_package_sha256': 'f3151c47514693f0739c59a0284d4eaa12c93b4083f60e44e01d687cb2193021',
        'recurrence': 'delta(6)=0; delta(j)=2*delta(j-1)+14*2^(j-1)',
        'outer_calls': rows,
        'extra_operations': delta,
        'corrected_row_D': 10_416_313_186 + delta,
        'corrected_total_operations': total,
        'memory_bytes': memory,
        'added_code_bytes': added_code_bytes,
        'time_log2': str(time_log),
        'memory_log2_bytes': str(memory_log),
        'score': str(time_log + max(Decimal(0), memory_log - 20)),
        'unresolved': [
            'Classical-tail terminal-zero specification and control-flow accounting',
            'Full-scale H-ONE and H-NORMAL evidence',
            'Complete implementation-derived cost and memory verification',
        ],
    }


if __name__ == '__main__':
    print(json.dumps(audit(), indent=2))
