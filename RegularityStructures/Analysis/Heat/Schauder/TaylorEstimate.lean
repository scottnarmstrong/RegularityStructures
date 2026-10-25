/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.Derivative
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# The Taylor-regime estimate for `K^α_{n;xy}`

For `Λ` of local order `γ` at `x` and `‖y - x‖_𝔰 ≤ 2^{-n}`,

  `|⟨Λ, K^α_{n;xy}⟩| ≤ C ∑_{ℓ ∈ 𝔈} κ_ℓ ‖y - x‖^{|ℓ|_𝔰} 2^{(|ℓ|_𝔰 - γ - 2) n}`  (`σ = γ + 2`),

with a finite list `𝔈` of derivative words, `|ℓ|_𝔰 ≥ γ + 2` for each `ℓ ∈ 𝔈`, and constants `κ_ℓ`
independent of `Λ, C, x, y, n` (`exists_abs_pairing_taylorKernel_le`).  Source: [Hai14, Lemma 5.18
and (5.33a)].
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

theorem two_rpow_deg_eq (a : ℕ) (γ : ℝ) (n : ℕ) :
    (2 : ℝ) ^ (((a : ℝ) - γ - 2) * n) =
      ((2 : ℝ) ^ n) ^ a * ((((2 : ℝ) ^ n)⁻¹ ^ 2) * ((2 : ℝ)⁻¹ ^ n) ^ γ) := by
  have : ((a : ℝ) - γ - 2) * n = (a : ℝ) * n + (-2 * n) + (-γ * n) := by ring
  rw [this, Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), two_rpow_natCast_mul,
    two_rpow_neg_two_mul, two_inv_pow_rpow]
  ring

theorem count_le_indexWeight (j : Fin 4) : ∀ ℓ : List (Fin 4), ℓ.count j ≤ indexWeight ℓ
  | [] => by simp
  | i :: ℓ => by
    have ih := count_le_indexWeight j ℓ
    have hw : 1 ≤ parabolicWeight i := by fin_cases i <;> simp [parabolicWeight]
    rw [List.count_cons, indexWeight_cons]
    split_ifs <;> simp_all <;> omega

theorem contDiff_taylorProfile {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g) (σ : ℝ)
    (z : ParabolicSpace) : ContDiff ℝ ∞ (taylorProfile g σ z) := by
  unfold taylorProfile
  exact (hg.comp (contDiff_id.add contDiff_const)).sub
    (ContDiff.sum fun k _ => contDiff_const.mul (contDiff_lineIter hg _))

theorem taylorProfile_eq_zero {h : ParabolicSpace → ℝ} (hs : ∀ z, 1 < parabolicNorm z → h z = 0)
    (n : ℕ) (σ : ℝ) {z u : ParabolicSpace} (hu : (2 : ℝ)⁻¹ ^ n + parabolicNorm z < parabolicNorm u) :
    taylorProfile (scaledShell h n) σ z u = 0 := by
  have h1 : scaledShell h n (u + z) = 0 := by
    refine scaledShell_eq_zero hs ?_
    have := parabolicNorm_add_le (u + z) (-z)
    rw [add_neg_cancel_right, parabolicNorm_neg] at this
    linarith
  have h2 : ∀ k : Fin 4 →₀ ℕ, lineIter (multiDirs k) (scaledShell h n) u = 0 := by
    intro k
    refine lineIter_eq_zero_of_isOpen (U := {w | (2 : ℝ)⁻¹ ^ n < parabolicNorm w})
      (isOpen_lt continuous_const continuous_parabolicNorm) _ _
      (fun w hw => scaledShell_eq_zero hs hw) u ?_
    have := parabolicNorm_nonneg z
    show (2 : ℝ)⁻¹ ^ n < parabolicNorm u
    linarith
  unfold taylorProfile
  simp [h1, h2]

end RegularityStructures

end
