/-
Copyright (c) 2026 Andrew Hendel. All rights reserved.
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

The classical impossibility results: no straightedge-and-compass construction can trisect
a 60° angle or double the cube. The proof is algebraic (Wantzel 1837): constructible numbers
have minimal polynomial degree dividing `2^n`, while the relevant polynomials have degree 3.

* <https://www.cs.ru.nl/~freek/100/> (entry #8)
-/

noncomputable section

open Polynomial

/-- A real number is constructible if it lies in an intermediate field `K` of `ℝ/ℚ`
with `[K : ℚ]` a power of 2 (Wantzel's algebraic characterization). -/
def IsConstructible (α : ℝ) : Prop :=
  ∃ (K : IntermediateField ℚ ℝ), α ∈ K ∧ ∃ n : ℕ, Module.finrank ℚ K = 2 ^ n

/-- If `α` is constructible and algebraic, its minimal polynomial degree divides `2^n`. -/
theorem IsConstructible.minpoly_natDegree_dvd_two_pow {α : ℝ} (hc : IsConstructible α)
    (_halg : IsAlgebraic ℚ α) : ∃ n : ℕ, (minpoly ℚ α).natDegree ∣ 2 ^ n := by
  obtain ⟨K, hαK, n, hK⟩ := hc
  have : FiniteDimensional ℚ K := by
    apply FiniteDimensional.of_finrank_pos; rw [hK]; positivity
  let α' : K := ⟨α, hαK⟩
  have hmin : minpoly ℚ α = minpoly ℚ α' := by
    have : α = algebraMap K ℝ α' := rfl
    rw [this, minpoly.algebraMap_eq (algebraMap K ℝ).injective]
  rw [hmin]
  exact ⟨n, hK ▸ minpoly.degree_dvd (IsIntegral.of_finite ℚ α')⟩

private theorem three_not_dvd_two_pow (n : ℕ) : ¬(3 ∣ 2 ^ n) := by
  intro h; have : 3 ∣ 2 := (by decide : Nat.Prime 3).dvd_of_dvd_pow h; omega

/-! ## Doubling the cube -/

private theorem Rat.cube_ne_two : ∀ b : ℚ, b ^ 3 ≠ 2 := by
  intro b hb
  exact Rat.not_irrational b (irrational_nrt_of_n_not_dvd_multiplicity 3
    (by norm_num : (2 : ℤ) ≠ 0) 2 (by exact_mod_cast hb) (by simp [multiplicity_self]))

/-- No constructible real satisfies `α³ = 2`. -/
theorem not_constructible_cubeRoot_two {α : ℝ} (hα : α ^ 3 = 2) : ¬IsConstructible α := by
  intro hc
  have haeval : aeval α (X ^ 3 - C (2 : ℚ)) = 0 := by
    simp [aeval_sub, aeval_X_pow, aeval_C, hα]
  have halg : IsAlgebraic ℚ α := ⟨_, X_pow_sub_C_ne_zero (by norm_num : 0 < 3) 2, haeval⟩
  have hmin := minpoly.eq_of_irreducible_of_monic
    (X_pow_sub_C_irreducible_of_prime Nat.prime_three Rat.cube_ne_two) haeval
    (monic_X_pow_sub_C 2 (by norm_num : 3 ≠ 0))
  obtain ⟨n, hn⟩ := hc.minpoly_natDegree_dvd_two_pow halg
  rw [← hmin, natDegree_X_pow_sub_C] at hn
  exact three_not_dvd_two_pow n hn

/-! ## Trisecting the angle -/

private def trisectionPoly : ℤ[X] := X ^ 3 - 3 * X - 1

private theorem trisectionPoly_monic : trisectionPoly.Monic := by
  unfold trisectionPoly; monicity!

private theorem trisectionPoly_natDegree : trisectionPoly.natDegree = 3 := by
  unfold trisectionPoly; compute_degree!

private theorem trisectionPoly_irreducible : Irreducible trisectionPoly := by
  rw [trisectionPoly_monic.irreducible_iff_roots_eq_zero_of_degree_le_three
    (by rw [trisectionPoly_natDegree]; omega) (by rw [trisectionPoly_natDegree])]
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro a ha
  have := (mem_roots trisectionPoly_monic.ne_zero).mp ha
  rw [IsRoot, trisectionPoly] at this
  simp only [eval_sub, eval_pow, eval_X, eval_mul, eval_ofNat, eval_one] at this
  have h1 : a ^ 3 - 3 * a = 1 := by omega
  have : a ∣ 1 := by
    have : a ∣ a ^ 3 - 3 * a := ⟨a ^ 2 - 3, by ring⟩; rwa [h1] at this
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one this) with rfl | rfl <;> omega

/-- No constructible real satisfies `α³ - 3α - 1 = 0`. -/
theorem not_constructible_trisection {α : ℝ} (hα : α ^ 3 - 3 * α - 1 = 0) :
    ¬IsConstructible α := by
  intro hc
  set p := trisectionPoly.map (Int.castRingHom ℚ)
  have haeval : aeval α p = 0 := by
    have : aeval α p = α ^ 3 - 3 * α - 1 := by
      simp [p, trisectionPoly, aeval_def, eval₂_sub, eval₂_pow, eval₂_mul, eval₂_X,
        eval₂_one, eval₂_ofNat]
    rw [this, hα]
  have hirr := (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    trisectionPoly_monic.isPrimitive).mp trisectionPoly_irreducible
  have halg : IsAlgebraic ℚ α := ⟨p, hirr.ne_zero, haeval⟩
  have hmin := minpoly.eq_of_irreducible_of_monic hirr haeval (trisectionPoly_monic.map _)
  obtain ⟨n, hn⟩ := hc.minpoly_natDegree_dvd_two_pow halg
  rw [← hmin, trisectionPoly_monic.natDegree_map, trisectionPoly_natDegree] at hn
  exact three_not_dvd_two_pow n hn

end
