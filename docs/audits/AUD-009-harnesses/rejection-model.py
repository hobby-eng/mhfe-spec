"""Independent finite check of the deniability rejection/failure coupling."""

from fractions import Fraction
from itertools import product
import json


def main():
    """Include zero allowed mass rather than condition failures out of the game."""
    distributions = [
        [Fraction(1), Fraction(0), Fraction(0)],
        [Fraction(1, 2), Fraction(1, 2), Fraction(0)],
        [Fraction(1, 2), Fraction(1, 3), Fraction(1, 6)],
    ]
    cases = 0
    for weights in distributions:
        for mask in product([False, True], repeat=len(weights)):
            mass = sum(w for w, allowed in zip(weights, mask) if allowed)
            expected = {i: w / mass for i, w in enumerate(weights)
                        if mask[i] and w} if mass else {None: Fraction(1)}
            coupled = {}
            mismatch = Fraction(0)
            for i, weight in enumerate(weights):
                if mask[i]:
                    outcomes = {i: Fraction(1)}
                else:
                    outcomes = expected
                for j, probability in outcomes.items():
                    joint = weight * probability
                    coupled[j] = coupled.get(j, Fraction(0)) + joint
                    if j != i:
                        mismatch += joint
            coupled = {i: w for i, w in coupled.items() if w}
            assert coupled == expected
            assert sum(coupled.values()) == 1
            assert mismatch <= 1 - mass
            variation = sum(abs(coupled.get(i, 0) -
                                (weights[i] if i is not None else 0))
                            for i in set(coupled) | set(range(3))) / 2
            assert variation <= mismatch
            cases += 1
        # These events bound the differing-password redraw even for a point mass.
        assert sum(w * w for w in weights) <= max(weights)
    print(json.dumps({"passed": cases, "includesSingletonAndZeroAllowedMass": True,
                      "limitation": "Finite coupling examples, not a theorem verifier."}))


if __name__ == "__main__":
    main()
