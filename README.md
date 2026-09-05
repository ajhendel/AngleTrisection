# Algebraic obstructions related to trisection and cube doubling

A small Lean 4 / Mathlib development of degree-based algebraic obstruction
lemmas motivated by the classical ruler-and-compass impossibility problems.
This is not a new mathematical result or a complete geometric formalization.

## Exact scope

[AngleTrisection/Basic.lean](AngleTrisection/Basic.lean) proves:

- `IsConstructible.minpoly_natDegree_dvd_two_pow`: under the local predicate,
  the minimal-polynomial degree divides a power of two.
- `not_constructible_cubeRoot_two`: a real root of `x³ = 2` fails that predicate.
- `not_constructible_trisection`: a real root of `x³ - 3x - 1 = 0` fails it.

The historical name `IsConstructible` denotes exactly this local predicate:

```lean
∃ (K : IntermediateField ℚ ℝ), α ∈ K ∧
  ∃ n : ℕ, Module.finrank ℚ K = 2 ^ n
```

The results exclude roots of `x³ - 2` and `x³ - 3x - 1` from every such
power-of-two-degree intermediate field. The code does not formalize geometric
construction steps, a tower of quadratic extensions, or the trigonometric bridge
to a 60-degree angle. It does not establish equivalence between this predicate
and geometric constructibility. Earlier comments calling it a full algebraic
characterization overstated the scope; the definition and proofs are unchanged.

## Checking and reuse

Lean and Mathlib are specified as v4.29.1 in `lean-toolchain` and `lakefile.toml`.
Install Lean through elan and obtain the specified Mathlib dependencies and
compiled cache. With dependencies available, check the file from this root:

```sh
nice -n 19 lake env lean -j2 AngleTrisection/Basic.lean
```

This uses two Lean worker threads. The September 2026 scope cleanup changed
comments and documentation only, checked that Lean code outside comments was
unchanged, and did not rerun a build. It adds no new build-success or independent
proof-audit claim.

An older expanded version remains in
[platonic-solids/Freek/Theorem8.lean](https://github.com/ajhendel/platonic-solids/blob/main/Freek/Theorem8.lean).
This repository is the standalone entry point; the copies are not automatically
synchronized. Reuse is permitted under [Apache-2.0](LICENSE). Author: Andrew Hendel.
