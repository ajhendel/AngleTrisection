/-
Copyright (c) 2025 Andrew Hendel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Hendel
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Tower
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum

/-!
# Freek #8: Impossibility of Trisecting the Angle and Doubling the Cube

We formalize the classical impossibility results of straightedge-and-compass
constructions (Freek problem list #8):

1. **Doubling the cube** is impossible: constructing `∛2` requires solving `X³ - 2 = 0`,
   whose minimal polynomial over `ℚ` has degree 3.

2. **Trisecting a 60° angle** is impossible: constructing `cos(20°)` requires solving
   `8X³ - 6X - 1 = 0`, whose minimal polynomial over `ℚ` has degree 3.

The algebraic obstruction is that every constructible number has degree over `ℚ` that is a
power of 2 (since each straightedge-and-compass step extends the field by at most degree 2),
while 3 is not a power of 2.

## Strategy

We prove:
- The polynomial `X³ - 2` is irreducible over `ℚ` (via `X_pow_sub_C_irreducible_of_prime`,
  after showing no rational cube root of 2 exists using irrationality of `∛2`).
- The polynomial `X³ - 3X - 1` is irreducible over `ℤ` (hence `ℚ`) since it is monic of
  degree 3 with no integer roots.
- Constructible numbers have degree a power of 2 over `ℚ` (the algebraic characterization
  of constructibility due to Wantzel, axiomatized via `IsConstructible`).
- Degree 3 is not a power of 2.

## References

* <https://www.cs.ru.nl/~freek/100/> (entry #8)
* Pierre L. Wantzel, *Recherches sur les moyens de reconnaître si un problème de géométrie
  peut se résoudre avec la règle et le compas*, 1837.
-/

noncomputable section

open Polynomial

/-! ## Part 1: The doubling-the-cube polynomial `X³ - 2` -/

/-- The cube root of 2 is irrational. This follows from the 2-adic valuation:
`multiplicity 2 2 = 1` and `1 % 3 ≠ 0`. -/
theorem irrational_cubeRoot_two {x : ℝ} (hx : x ^ 3 = 2) : Irrational x := by
  have hx' : x ^ 3 = ((2 : ℤ) : ℝ) := by exact_mod_cast hx
  exact irrational_nrt_of_n_not_dvd_multiplicity 3 (by norm_num : (2 : ℤ) ≠ 0) 2
    hx' (by simp [multiplicity_self])

/-- No rational number is a cube root of 2. -/
theorem Rat.cube_ne_two : ∀ b : ℚ, b ^ 3 ≠ 2 := by
  intro b hb
  have hb' : (b : ℝ) ^ 3 = (2 : ℝ) := by exact_mod_cast hb
  exact Rat.not_irrational b (irrational_cubeRoot_two hb')

/-- The polynomial `X ^ 3 - 2` is irreducible over `ℚ`. This follows from the fact
that 2 has no cube root in `ℚ` and 3 is prime. -/
theorem irreducible_X_cubed_sub_two : Irreducible (X ^ 3 - C (2 : ℚ)) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_three Rat.cube_ne_two

/-- The polynomial `X ^ 3 - 2` has degree 3 over `ℚ`. -/
theorem natDegree_X_cubed_sub_two : (X ^ 3 - C (2 : ℚ)).natDegree = 3 :=
  natDegree_X_pow_sub_C

/-! ## Part 2: The angle-trisection polynomial -/

/-- The trisection polynomial `X³ - 3X - 1` over `ℤ`.

This is the minimal polynomial of `2 cos(20°)` over `ℤ`, derived from
the Chebyshev identity `cos(3θ) = 4cos³(θ) - 3cos(θ)`.
Setting `θ = 20°` gives `cos(60°) = 1/2`, so `4cos³(20°) - 3cos(20°) = 1/2`,
i.e., with `y = 2cos(20°)`: `y³ - 3y - 1 = 0`. -/
def trisectionPoly : ℤ[X] := X ^ 3 - 3 * X - 1

theorem trisectionPoly_eq : trisectionPoly = X ^ 3 - 3 * X - 1 := rfl

/-- The trisection polynomial is monic. -/
theorem trisectionPoly_monic : trisectionPoly.Monic := by
  unfold trisectionPoly; monicity!

/-- The trisection polynomial has degree 3. -/
theorem trisectionPoly_natDegree : trisectionPoly.natDegree = 3 := by
  unfold trisectionPoly; compute_degree!

/-- The trisection polynomial is nonzero. -/
theorem trisectionPoly_ne_zero : trisectionPoly ≠ 0 :=
  trisectionPoly_monic.ne_zero

/-- The trisection polynomial has no integer roots.

By the integer root theorem, any integer root must divide the constant term `-1`,
so it is `1` or `-1`. Direct computation shows neither is a root:
- `eval 1 = 1 - 3 - 1 = -3 ≠ 0`
- `eval (-1) = -1 + 3 - 1 = 1 ≠ 0` -/
theorem trisectionPoly_no_int_roots (a : ℤ) : ¬IsRoot trisectionPoly a := by
  rw [IsRoot, trisectionPoly]
  simp only [eval_sub, eval_pow, eval_X, eval_mul, eval_ofNat, eval_one]
  intro h
  -- From h: a^3 - 3*a - 1 = 0, so a^3 - 3*a = 1
  have h1 : a ^ 3 - 3 * a = 1 := by omega
  -- a divides a^3 - 3*a = a*(a^2 - 3), so a ∣ 1
  have ha : a ∣ 1 := by
    have : a ∣ a ^ 3 - 3 * a := ⟨a ^ 2 - 3, by ring⟩
    rwa [h1] at this
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one ha) with rfl | rfl <;> omega

/-- The trisection polynomial `X³ - 3X - 1` is irreducible over `ℤ`. -/
theorem trisectionPoly_irreducible : Irreducible trisectionPoly := by
  rw [trisectionPoly_monic.irreducible_iff_roots_eq_zero_of_degree_le_three
    (by rw [trisectionPoly_natDegree]; omega) (by rw [trisectionPoly_natDegree])]
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro a ha
  exact trisectionPoly_no_int_roots a (mem_roots trisectionPoly_ne_zero |>.mp ha)

/-- The trisection polynomial is primitive (since it is monic). -/
theorem trisectionPoly_isPrimitive : trisectionPoly.IsPrimitive :=
  trisectionPoly_monic.isPrimitive

/-- The trisection polynomial `X³ - 3X - 1` is irreducible over `ℚ`.
We transfer from `ℤ` to `ℚ` by the Gauss lemma. -/
theorem trisectionPoly_irreducible_rat :
    Irreducible (trisectionPoly.map (Int.castRingHom ℚ)) := by
  exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    trisectionPoly_isPrimitive).mp trisectionPoly_irreducible

/-- The rational trisection polynomial `X³ - 3X - 1` has degree 3 over `ℚ`. -/
theorem trisectionPoly_rat_natDegree :
    (trisectionPoly.map (Int.castRingHom ℚ)).natDegree = 3 := by
  rw [trisectionPoly_monic.natDegree_map, trisectionPoly_natDegree]

/-- The rational trisection polynomial is monic. -/
theorem trisectionPoly_rat_monic :
    (trisectionPoly.map (Int.castRingHom ℚ)).Monic :=
  Monic.map (Int.castRingHom ℚ) trisectionPoly_monic

/-! ## Part 3: Constructible numbers and the power-of-2 obstruction

Mathlib does not yet have a formalized theory of straightedge-and-compass constructions.
We define `IsConstructible` via the algebraic characterization due to Wantzel (1837):
a real number is constructible iff it lies in a subfield of `ℝ` whose degree over `ℚ`
is a power of 2.

This definition is equivalent to the geometric one (see e.g. Chapter 15 of Artin's
*Algebra*), but the equivalence is not formalized here.
-/

/-- A real number is constructible (by straightedge and compass from the rationals) if it
lies in an intermediate field `K` of `ℝ / ℚ` with `[K : ℚ]` a power of 2.

This is the algebraic characterization of constructibility due to Wantzel (1837). -/
def IsConstructible (α : ℝ) : Prop :=
  ∃ (K : IntermediateField ℚ ℝ), α ∈ K ∧ ∃ n : ℕ, Module.finrank ℚ K = 2 ^ n

/-- Every rational number is constructible. -/
theorem IsConstructible.rat (q : ℚ) : IsConstructible (algebraMap ℚ ℝ q) :=
  ⟨⊥, IntermediateField.algebraMap_mem _ q, 0, by
    rw [IntermediateField.finrank_bot]; ring⟩

/-- **Wantzel's key lemma**: if `α` is constructible and algebraic over `ℚ`, then
the degree of its minimal polynomial divides a power of 2.

The proof uses the tower law: `[K : ℚ] = [K : ℚ(α)] · [ℚ(α) : ℚ]`. Since `α ∈ K` we
have `ℚ(α) ≤ K`, hence `[ℚ(α) : ℚ] ∣ [K : ℚ] = 2ⁿ`. Since `[ℚ(α) : ℚ]` equals the
degree of the minimal polynomial, we conclude. -/
theorem IsConstructible.minpoly_natDegree_dvd_two_pow {α : ℝ} (hc : IsConstructible α)
    (halg : IsAlgebraic ℚ α) :
    ∃ n : ℕ, (minpoly ℚ α).natDegree ∣ 2 ^ n := by
  obtain ⟨K, hαK, n, hK⟩ := hc
  -- K is finite-dimensional over ℚ since finrank ℚ K = 2^n > 0
  have hfin : FiniteDimensional ℚ K := by
    apply FiniteDimensional.of_finrank_pos
    rw [hK]; positivity
  -- α ∈ K, so we can view it as an element of K
  let α' : K := ⟨α, hαK⟩
  -- α' is integral over ℚ since K is finite-dimensional
  have hint : IsIntegral ℚ α' := IsIntegral.of_finite ℚ α'
  -- minpoly ℚ α = minpoly ℚ α' (since α = algebraMap K ℝ α')
  have hmin : minpoly ℚ α = minpoly ℚ α' := by
    have : α = algebraMap K ℝ α' := rfl
    rw [this, minpoly.algebraMap_eq (algebraMap K ℝ).injective]
  -- natDegree of minpoly divides finrank ℚ K = 2^n
  rw [hmin]
  exact ⟨n, hK ▸ minpoly.degree_dvd hint⟩

/-- 3 does not divide any power of 2.

If `3 ∣ 2ⁿ` then by `Nat.Prime.dvd_of_dvd_pow` we get `3 ∣ 2`, contradicting `3 > 2`. -/
theorem Nat.three_not_dvd_two_pow (n : ℕ) : ¬(3 ∣ 2 ^ n) := by
  intro h
  have h3 : Nat.Prime 3 := by decide
  have : 3 ∣ 2 := h3.dvd_of_dvd_pow h
  omega

/-! ## Part 4: The impossibility theorems -/

/-- **Impossibility of doubling the cube** (algebraic formulation).

If `α` is a real number satisfying `α³ = 2` (i.e., `α = ∛2`), then `α` is not constructible.
The minimal polynomial `X³ - 2` is irreducible of degree 3, and 3 does not divide
any power of 2. -/
theorem not_constructible_cubeRoot_two {α : ℝ} (hα : α ^ 3 = 2) : ¬IsConstructible α := by
  intro hc
  -- α is algebraic over ℚ: it's a root of X³ - 2
  have haeval : aeval α (X ^ 3 - C (2 : ℚ)) = 0 := by
    simp [aeval_sub, aeval_X_pow, aeval_C, hα]
  have halg : IsAlgebraic ℚ α :=
    ⟨X ^ 3 - C 2, X_pow_sub_C_ne_zero (by norm_num : 0 < 3) 2, haeval⟩
  -- The minimal polynomial equals X³ - 2 (irreducible, monic, with α as root)
  have hmin : X ^ 3 - C (2 : ℚ) = minpoly ℚ α :=
    minpoly.eq_of_irreducible_of_monic irreducible_X_cubed_sub_two haeval
      (monic_X_pow_sub_C 2 (by norm_num : 3 ≠ 0))
  -- So the minimal polynomial has degree 3
  have hdeg : (minpoly ℚ α).natDegree = 3 := by
    rw [← hmin, natDegree_X_cubed_sub_two]
  -- But constructible numbers have min poly degree dividing 2^n
  obtain ⟨n, hn⟩ := hc.minpoly_natDegree_dvd_two_pow halg
  rw [hdeg] at hn
  exact Nat.three_not_dvd_two_pow n hn

/-- **Impossibility of trisecting a 60-degree angle** (algebraic formulation).

If `α` is a real root of `X³ - 3X - 1 = 0` (so `α = 2cos(20°)`), then `α` is not
constructible. Since `cos(20°) = α/2` is constructible iff `α` is, trisecting a 60° angle
by straightedge and compass is impossible.

The polynomial `X³ - 3X - 1` is irreducible of degree 3 over `ℚ`, and 3 does not divide
any power of 2. -/
theorem not_constructible_trisection {α : ℝ} (hα : α ^ 3 - 3 * α - 1 = 0) :
    ¬IsConstructible α := by
  intro hc
  set p := trisectionPoly.map (Int.castRingHom ℚ) with hp_def
  -- α is a root of the trisection polynomial over ℚ
  have haeval : aeval α p = 0 := by
    have : aeval α p = α ^ 3 - 3 * α - 1 := by
      simp [hp_def, trisectionPoly, aeval_def, eval₂_sub, eval₂_pow, eval₂_mul, eval₂_X,
        eval₂_one, eval₂_ofNat]
    rw [this, hα]
  have halg : IsAlgebraic ℚ α :=
    ⟨p, trisectionPoly_irreducible_rat.ne_zero, haeval⟩
  -- The minimal polynomial equals p (irreducible, monic, with α as root)
  have hmin : p = minpoly ℚ α :=
    minpoly.eq_of_irreducible_of_monic trisectionPoly_irreducible_rat haeval
      trisectionPoly_rat_monic
  -- So the minimal polynomial has degree 3
  have hdeg : (minpoly ℚ α).natDegree = 3 := by
    rw [← hmin, trisectionPoly_rat_natDegree]
  -- But constructible numbers have min poly degree dividing 2^n
  obtain ⟨n, hn⟩ := hc.minpoly_natDegree_dvd_two_pow halg
  rw [hdeg] at hn
  exact Nat.three_not_dvd_two_pow n hn

/-! ## Part 5: Combined statement (Freek #8) -/

/-- **Freek #8**: Impossibility of trisecting the angle and doubling the cube.

It is impossible to trisect an arbitrary angle or double the cube using only straightedge
and compass. Algebraically:
- No constructible real number satisfies `x³ = 2` (cube doubling).
- No constructible real number satisfies `x³ - 3x - 1 = 0` (angle trisection of 60°). -/
theorem impossibility_of_trisection_and_doubling :
    (∀ α : ℝ, α ^ 3 = 2 → ¬IsConstructible α) ∧
    (∀ α : ℝ, α ^ 3 - 3 * α - 1 = 0 → ¬IsConstructible α) :=
  ⟨fun _ hα => not_constructible_cubeRoot_two hα,
   fun _ hα => not_constructible_trisection hα⟩

end
