/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.CrossMollifierDifference
public import Phi43.BPHZ.TreeI3PsiDifferenceAlgebra

/-!
# The `2 × 2` tables of cross covariances at two mollifiers

For the cross covariances `a = Q_{ρε,ρε}`, `b = Q_{ρε,ρ'ε'}`, `c = Q_{ρ'ε',ρε}`, `d = Q_{ρ'ε',ρ'ε'}`
at a point `x` (`hairerCrossCovarianceTwo`) the three tables `(a, b, c, d)`, `(a, a, d, d)` and
`(a, d, a, d)` satisfy the bound data `Bd μ (A s(x)⁻¹) (s(x)^(-θ))` of
`Phi43.BPHZ.TreeI3PsiDifferenceAlgebra`, with `μ = (max ε ε')^θ`
(`hairerCrossTwo_tables_bd_i3Psi`).
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem abs_div_four_le_cross {x B : ℝ} (h : |x| ≤ B) : |x / 4| ≤ B := by
  have hB : 0 ≤ B := (abs_nonneg _).trans h
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  linarith

private theorem abs_div_four_add_le_cross {x y B : ℝ} (hx : |x| ≤ B) (hy : |y| ≤ B) :
    |(x + y) / 4| ≤ B := by
  have hB : 0 ≤ B := (abs_nonneg _).trans hx
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have := abs_add_le x y
  linarith

/-- The three tables satisfy the bound data, given the seven bounds on the Walsh combinations. -/
private theorem tables_bd_of_bounds_cross {a b c d μ p q A : ℝ} (hA : 0 ≤ A) (hμ : 0 ≤ μ)
    (hp : 0 ≤ p)
    (hq : 0 ≤ q) (h1 : |a + b + c + d| ≤ A * p) (h2 : |a - b - c + d| ≤ A * p)
    (h3 : |a - b - c + d| ≤ A * (μ ^ 2 * p * q ^ 2)) (h4 : |a + b - c - d| ≤ A * p)
    (h5 : |a - b + c - d| ≤ A * p) (h6 : |a + b - c - d| ≤ A * (μ * p * q))
    (h7 : |a - b + c - d| ≤ A * (μ * p * q)) :
    I3PsiDiffTable.Bd μ (A * p) q ⟨a, b, c, d⟩ ∧ I3PsiDiffTable.Bd μ (A * p) q ⟨a, a, d, d⟩ ∧
      I3PsiDiffTable.Bd μ (A * p) q ⟨a, d, a, d⟩ := by
  have e1 : A * (μ * p * q) = μ * (A * p) * q := by ring
  have e2 : A * (μ ^ 2 * p * q ^ 2) = μ ^ 2 * (A * p) * q ^ 2 := by ring
  rw [e1] at h6 h7
  rw [e2] at h3
  have hAp : 0 ≤ A * p := mul_nonneg hA hp
  have hg : 0 ≤ μ * (A * p) * q := by positivity
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact abs_div_four_le_cross h1
  · exact abs_div_four_le_cross h4
  · exact abs_div_four_le_cross h5
  · exact abs_div_four_le_cross h2
  · exact abs_div_four_le_cross h6
  · exact abs_div_four_le_cross h7
  · exact abs_div_four_le_cross h3
  · have : (I3PsiDiffTable.mean ⟨a, a, d, d⟩) = ((a + b + c + d) + (a - b - c + d)) / 4 := by
      simp only [I3PsiDiffTable.mean]; ring
    rw [this]; exact abs_div_four_add_le_cross h1 h2
  · have : (I3PsiDiffTable.du ⟨a, a, d, d⟩) = ((a + b - c - d) + (a - b + c - d)) / 4 := by
      simp only [I3PsiDiffTable.du]; ring
    rw [this]; exact abs_div_four_add_le_cross h4 h5
  · simp only [I3PsiDiffTable.dv]
    have : a - a + d - d = 0 := by ring
    rw [this, zero_div, abs_zero]; exact hAp
  · simp only [I3PsiDiffTable.dw]
    have : a - a - d + d = 0 := by ring
    rw [this, zero_div, abs_zero]; exact hAp
  · have : (I3PsiDiffTable.du ⟨a, a, d, d⟩) = ((a + b - c - d) + (a - b + c - d)) / 4 := by
      simp only [I3PsiDiffTable.du]; ring
    rw [this]; exact abs_div_four_add_le_cross h6 h7
  · simp only [I3PsiDiffTable.dv]
    have : a - a + d - d = 0 := by ring
    rw [this, zero_div, abs_zero]; exact hg
  · simp only [I3PsiDiffTable.dw]
    have : a - a - d + d = 0 := by ring
    rw [this, zero_div, abs_zero]; positivity
  · have : (I3PsiDiffTable.mean ⟨a, d, a, d⟩) = ((a + b + c + d) + (a - b - c + d)) / 4 := by
      simp only [I3PsiDiffTable.mean]; ring
    rw [this]; exact abs_div_four_add_le_cross h1 h2
  · simp only [I3PsiDiffTable.du]
    have : a + d - a - d = 0 := by ring
    rw [this, zero_div, abs_zero]; exact hAp
  · have : (I3PsiDiffTable.dv ⟨a, d, a, d⟩) = ((a + b - c - d) + (a - b + c - d)) / 4 := by
      simp only [I3PsiDiffTable.dv]; ring
    rw [this]; exact abs_div_four_add_le_cross h4 h5
  · simp only [I3PsiDiffTable.dw]
    have : a - d - a + d = 0 := by ring
    rw [this, zero_div, abs_zero]; exact hAp
  · simp only [I3PsiDiffTable.du]
    have : a + d - a - d = 0 := by ring
    rw [this, zero_div, abs_zero]; exact hg
  · have : (I3PsiDiffTable.dv ⟨a, d, a, d⟩) = ((a + b - c - d) + (a - b + c - d)) / 4 := by
      simp only [I3PsiDiffTable.dv]; ring
    rw [this]; exact abs_div_four_add_le_cross h6 h7
  · simp only [I3PsiDiffTable.dw]
    have : a - d - a + d = 0 := by ring
    rw [this, zero_div, abs_zero]; positivity

/-- The seven bounds on the Walsh combinations of the cross covariances. -/
private theorem cross_data_two (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') {θ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ x : SpaceTime, 0 < torusParabolicSize x →
        let a := hairerCrossCovarianceTwo N ρ ε ρ ε x
        let b := hairerCrossCovarianceTwo N ρ ε ρ' ε' x
        let c := hairerCrossCovarianceTwo N ρ' ε' ρ ε x
        let d := hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x
        let p := torusParabolicSize x ^ (-(1 : ℝ))
        let q := torusParabolicSize x ^ (-θ)
        let μ := (max ε ε') ^ θ
        |a + b + c + d| ≤ A * p ∧ |a - b - c + d| ≤ A * p ∧
          |a - b - c + d| ≤ A * (μ ^ 2 * p * q ^ 2) ∧ |a + b - c - d| ≤ A * p ∧
          |a - b + c - d| ≤ A * p ∧ |a + b - c - d| ≤ A * (μ * p * q) ∧
          |a - b + c - d| ≤ A * (μ * p * q) := by
  obtain ⟨Cs, hCs, hS⟩ := hairerCrossTwo_comb_abs_le N ρ ρ' hρ hρ'
  obtain ⟨CΔ, hCΔ, hΔ⟩ := hairerKernelDiffCovarianceTwo_abs_le N ρ ρ' hρ hρ' hθ hθ1
  obtain ⟨CL, hCL, hL⟩ := hairerCrossTwo_diff_left_abs_le N ρ ρ' hρ hρ' hθ hθ1
  obtain ⟨CR, hCR, hR⟩ := hairerCrossTwo_diff_right_abs_le N ρ ρ' hρ hρ' hθ hθ1
  refine ⟨Cs + CΔ + CL + CR, by positivity, ?_⟩
  intro ε ε' hε hε1 hε' hε'1 x hx a b c d p q μ
  have hp : 0 ≤ p := Real.rpow_nonneg hx.le _
  have hq : 0 ≤ q := Real.rpow_nonneg hx.le _
  have hM : 0 < max ε ε' := lt_max_of_lt_left hε
  have hμ : 0 ≤ μ := Real.rpow_nonneg hM.le _
  have hpq : p * q = torusParabolicSize x ^ (-1 - θ) := by
    rw [← Real.rpow_add hx]
    congr 1
  have hμq : μ ^ 2 * p * q ^ 2 = (max ε ε') ^ (2 * θ) * torusParabolicSize x ^ (-1 - 2 * θ) := by
    have h1 : μ ^ 2 = (max ε ε') ^ (2 * θ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
      congr 1
      push_cast; ring
    have h2 : p * q ^ 2 = torusParabolicSize x ^ (-1 - 2 * θ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_add hx]
      congr 1
      push_cast; ring
    rw [mul_assoc, h1, h2]
  have s1 := hS hε hε1 hε' hε'1 (s := 1) (t := 1) (by norm_num) (by norm_num) x hx
  have s2 := hS hε hε1 hε' hε'1 (s := -1) (t := -1) (by norm_num) (by norm_num) x hx
  have s3 := hS hε hε1 hε' hε'1 (s := -1) (t := 1) (by norm_num) (by norm_num) x hx
  have s4 := hS hε hε1 hε' hε'1 (s := 1) (t := -1) (by norm_num) (by norm_num) x hx
  have d1 := hΔ hε hε1 hε' hε'1 x hx
  rw [hairerKernelDiffCovarianceTwo_eq_cross N ρ ρ' hρ hρ' hε hε1 hε' hε'1 x] at d1
  have l1 := hL hε hε1 hε' hε'1 (t := 1) (by norm_num) x hx
  have r1 := hR hε hε1 hε' hε'1 (s := 1) (by norm_num) x hx
  rw [← hpq] at l1 r1
  have mono : ∀ {C u : ℝ}, 0 ≤ u → C ≤ Cs + CΔ + CL + CR → C * u ≤ (Cs + CΔ + CL + CR) * u :=
    fun hu hC => mul_le_mul_of_nonneg_right hC hu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_trans (le_of_eq ?_) (s1.trans (mono hp (by linarith)))
    congr 1
    ring
  · refine le_trans (le_of_eq ?_) (s2.trans (mono hp (by linarith)))
    congr 1
    ring
  · refine d1.trans ?_
    have : 0 ≤ μ ^ 2 * p * q ^ 2 := by positivity
    calc CΔ * (max ε ε') ^ (2 * θ) * torusParabolicSize x ^ (-1 - 2 * θ) =
          CΔ * (μ ^ 2 * p * q ^ 2) := by
          rw [hμq]; ring
      _ ≤ _ := mono this (by linarith)
  · refine le_trans (le_of_eq ?_) (s3.trans (mono hp (by linarith)))
    congr 1
    ring
  · refine le_trans (le_of_eq ?_) (s4.trans (mono hp (by linarith)))
    congr 1
    ring
  · refine le_trans (le_of_eq ?_) (l1.trans ?_)
    · congr 1
      ring
    · have : 0 ≤ μ * (p * q) := by positivity
      calc CL * (max ε ε') ^ θ * (p * q) = CL * (μ * (p * q)) := by ring
        _ ≤ _ := mono this (by linarith)
        _ = _ := by ring
  · refine le_trans (le_of_eq ?_) (r1.trans ?_)
    · congr 1
      ring
    · have : 0 ≤ μ * (p * q) := by positivity
      calc CR * (max ε ε') ^ θ * (p * q) = CR * (μ * (p * q)) := by ring
        _ ≤ _ := mono this (by linarith)
        _ = _ := by ring

/-- **The three tables of cross covariances satisfy the bound data**, with a constant independent
of `ε, ε' ∈ (0, 1]` and of `x ≠ 0`. -/
theorem hairerCrossTwo_tables_bd_i3Psi (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') {θ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ x : SpaceTime, 0 < torusParabolicSize x →
        I3PsiDiffTable.Bd ((max ε ε') ^ θ) (A * torusParabolicSize x ^ (-(1 : ℝ)))
          (torusParabolicSize x ^ (-θ))
          ⟨hairerCrossCovarianceTwo N ρ ε ρ ε x, hairerCrossCovarianceTwo N ρ ε ρ' ε' x,
            hairerCrossCovarianceTwo N ρ' ε' ρ ε x, hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x⟩ ∧
        I3PsiDiffTable.Bd ((max ε ε') ^ θ) (A * torusParabolicSize x ^ (-(1 : ℝ)))
          (torusParabolicSize x ^ (-θ))
          ⟨hairerCrossCovarianceTwo N ρ ε ρ ε x, hairerCrossCovarianceTwo N ρ ε ρ ε x,
            hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x, hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x⟩ ∧
        I3PsiDiffTable.Bd ((max ε ε') ^ θ) (A * torusParabolicSize x ^ (-(1 : ℝ)))
          (torusParabolicSize x ^ (-θ))
          ⟨hairerCrossCovarianceTwo N ρ ε ρ ε x, hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x,
            hairerCrossCovarianceTwo N ρ ε ρ ε x, hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x⟩ := by
  obtain ⟨A, hA, hdata⟩ := cross_data_two N ρ ρ' hρ hρ' hθ hθ1
  refine ⟨A, hA, ?_⟩
  intro ε ε' hε hε1 hε' hε'1 x hx
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hdata hε hε1 hε' hε'1 x hx
  have hM : 0 < max ε ε' := lt_max_of_lt_left hε
  exact tables_bd_of_bounds_cross hA (Real.rpow_nonneg hM.le _) (Real.rpow_nonneg hx.le _)
    (Real.rpow_nonneg hx.le _) h1 h2 h3 h4 h5 h6 h7

end RegularityStructures.Phi43

end
