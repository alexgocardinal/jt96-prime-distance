# JT96: Prime-distance graph colorings

Lean 4 formalization of results concerning Jensen–Toft Problem 9.6.

## Verified results

- A three-colorability slope criterion for positive integer distance sets containing 2 and 3.
- Four-colorability and failure of three-colorability for the example {2, 3, 61, 131, 191, 257}.
- Three-colorability of every proper subset of that example.
- Four-colorability and failure of three-colorability for the six-distance prime pattern.
- Minimality, six distinct distances, and absence of twin-prime pairs for prime patterns satisfying the stated cone conditions.

## Infinitude: verification boundary

The theorem JT96.infinite_minimal_six_prime_obstructions explicitly assumes JT96.PrimePatternInput.

This hypothesis asserts the existence of arbitrarily large prime patterns in the required cone. It is passed as a theorem hypothesis and is not proved in this repository.

The elementary deduction of infinitude from that hypothesis is formalized. The external prime-pattern existence result is not formalized here.

## Build and audit

The project pins Lean and mathlib to version 4.19.0.

With Git and elan installed, run these commands in order:

    git clone https://github.com/alexgocardinal/jt96-prime-distance.git
    cd jt96-prime-distance
    lake exe cache get
    lake build JT96
    lake env lean Audit.lean

Audit.lean displays the principal theorem statements and their axiom dependencies. The audited results use only propext, Classical.choice, and Quot.sound. The infinitude statement retains its explicit prime-pattern hypothesis.

## Main files

- JT96/ColoringCriterion.lean: slope criterion and concrete four-color certificate.
- JT96/ProperSubsets.lean: concrete-example minimality.
- JT96/SixPrimePattern.lean: general prime-pattern certificate.
- JT96/FamilyCertificate.lean: cone-family certificate and definition of the external prime-pattern input.
- JT96/Infinitude.lean: conditional infinitude theorem.
- Audit.lean: theorem and axiom inspection.
