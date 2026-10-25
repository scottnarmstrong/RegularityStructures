/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.CrossMollifierCovariance
public import Phi43.BPHZ.TreeWickCrossAlgebra

/-!
# Second differences of the 2×2 table of cross covariances (two mollifiers)

With `a = Q(K, K)`, `b = Q(K, K')`, `c = Q(K', K)`, `d = Q(K', K')` for
`K = K_{ρ,ε}`, `K' = K_{ρ',ε'}` (`hairerCrossCovarianceTwo`) and `θ ∈ (0, 1]` we prove, away from
the origin,
* `a - b - c + d = Δ` is the covariance of `K - K'`, and `|Δ| ≲ (max ε ε')^(2θ) s^(-1-2θ)`,
* `|a² - b² - c² + d²| ≲ (max ε ε')^(2θ) s^(-2-2θ)`,
* `|a³ - b³ - c³ + d³| ≲ (max ε ε')^(2θ) s^(-3-2θ)`,
with constants depending on `ρ`, `ρ'` only; the bound comparing two mollifiers then does not depend
on `ρ`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- The kernel difference `K_{ρ,ε} - K_{ρ',ε'}`. -/
def hairerKernelDiffTwo (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (ε' : ℝ) (w : SpaceTime) : ℝ :=
  hairerMollifiedKernel N ρ ε w - hairerMollifiedKernel N ρ' ε' w

/-- The covariance `Δ(x) = ∫ D(x + w) D(w) dw` of `D = K_{ρ,ε} - K_{ρ',ε'}`. -/
def hairerKernelDiffCovarianceTwo (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (ε' : ℝ) (x : SpaceTime) : ℝ :=
  ∫ w, hairerKernelDiffTwo N ρ ε ρ' ε' (x + w) * hairerKernelDiffTwo N ρ ε ρ' ε' w

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The covariance `Δ` of the kernel difference is the second difference of the cross
covariances: `Δ(x) = a - b - c + d`. -/
theorem hairerKernelDiffCovarianceTwo_eq_cross (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {ε ε' : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hε' : 0 < ε') (hε'1 : ε' ≤ 1) (x : SpaceTime) :
    hairerKernelDiffCovarianceTwo N ρ ε ρ' ε' x =
      hairerCrossCovarianceTwo N ρ ε ρ ε x - hairerCrossCovarianceTwo N ρ ε ρ' ε' x -
        hairerCrossCovarianceTwo N ρ' ε' ρ ε x + hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x := by
  have h := integral_hairerKernelCombTwo_shift_mul N ρ ρ' hρ hρ' hε hε1 hε' hε'1 (-1) (-1) x
  have e : hairerKernelCombTwo N ρ ε ρ' ε' (-1) = hairerKernelDiffTwo N ρ ε ρ' ε' := by
    funext v
    simp [hairerKernelCombTwo, hairerKernelDiffTwo, sub_eq_add_neg]
  rw [e] at h
  rw [hairerKernelDiffCovarianceTwo, h]
  ring

/-- **Covariance of the cross-mollifier kernel difference.** For `θ ∈ (0, 1]`,
`|Δ(x)| ≲ (max ε ε')^(2θ) s(x)^(-1-2θ)` away from the origin. -/
theorem hairerKernelDiffCovarianceTwo_abs_le (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ x : SpaceTime, 0 < torusParabolicSize x →
        |hairerKernelDiffCovarianceTwo N ρ ε ρ' ε' x| ≤
          C * (max ε ε') ^ (2 * θ) * torusParabolicSize x ^ (-1 - 2 * θ) := by
  obtain ⟨C1, hC1, hD⟩ := hairerMollifiedKernel_sub_abs_le_cross_of_pos N ρ ρ' hρ hρ' hθ hθ1
  obtain ⟨Cp, hCp, hP⟩ := abs_integral_shift_mul_singular_le (a := 3 + θ) (b := 3 + θ)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨Cp * C1 * C1, by positivity, ?_⟩
  intro ε ε' hε hε1 hε' hε'1 x hx
  set M : ℝ := max ε ε' with hM
  have hMpos : 0 < M := lt_of_lt_of_le hε (le_max_left _ _)
  have hM0 : 0 ≤ M ^ θ := Real.rpow_nonneg hMpos.le _
  have hDb : ∀ v, 0 < torusParabolicSize v →
      |hairerKernelDiffTwo N ρ ε ρ' ε' v| ≤ (C1 * M ^ θ) * torusParabolicSize v ^ (-(3 + θ)) := by
    intro v hv
    have := hD hε hε1 hε' hε'1 v hv
    simpa only [hairerKernelDiffTwo, mul_assoc] using this
  have t := hP (mul_nonneg hC1 hM0) (mul_nonneg hC1 hM0) hDb hDb x hx
  have e : (5 : ℝ) - (3 + θ) - (3 + θ) = -1 - 2 * θ := by ring
  rw [e] at t
  refine t.trans (le_of_eq ?_)
  have hMM : M ^ (2 * θ) = M ^ θ * M ^ θ := by
    rw [two_mul, Real.rpow_add hMpos]
  rw [hMM]
  ring

/-- The common data of the second-difference bounds: constants and the five bounds on
`σ, r, e₁, eTwo`. -/
private theorem cmd_cross_data (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ}
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
    calc CΔ * (max ε ε') ^ (2 * θ) * torusParabolicSize x ^ (-1 - 2 * θ) = CΔ * (μ ^ 2 * p * q ^ 2) := by
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

private theorem cmd_rpow_pq {s θ : ℝ} (hs : 0 < s) (k : ℕ) :
    (s ^ (-(1 : ℝ))) ^ k * (s ^ (-θ)) ^ 2 = s ^ (-(k : ℝ) - 2 * θ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast (s ^ (-θ)), ← Real.rpow_mul hs.le,
    ← Real.rpow_mul hs.le, ← Real.rpow_add hs]
  congr 1
  push_cast
  ring

private theorem cmd_rpow_mu {M θ : ℝ} (hM : 0 < M) : (M ^ θ) ^ 2 = M ^ (2 * θ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
  congr 1
  push_cast
  ring

/-- **Second difference of squares of the cross covariances.**
`|a² - b² - c² + d²| ≲ (max ε ε')^(2θ) s(x)^(-2-2θ)`. -/
theorem hairerCrossTwo_sq_sub_abs_le (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ x : SpaceTime, 0 < torusParabolicSize x →
        |hairerCrossCovarianceTwo N ρ ε ρ ε x ^ 2 - hairerCrossCovarianceTwo N ρ ε ρ' ε' x ^ 2 -
            hairerCrossCovarianceTwo N ρ' ε' ρ ε x ^ 2 + hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x ^ 2| ≤
          C * (max ε ε') ^ (2 * θ) * torusParabolicSize x ^ (-2 - 2 * θ) := by
  obtain ⟨A, hA, hdata⟩ := cmd_cross_data N ρ ρ' hρ hρ' hθ hθ1
  refine ⟨A ^ 2, by positivity, ?_⟩
  intro ε ε' hε hε1 hε' hε'1 x hx
  obtain ⟨hσ, -, hr, -, -, h₁, hTwo⟩ := hdata hε hε1 hε' hε'1 x hx
  have hM : 0 < max ε ε' := lt_max_of_lt_left hε
  have h := treeWick_alg_sq hA (Real.rpow_nonneg hM.le θ) (Real.rpow_nonneg hx.le (-(1 : ℝ)))
    (Real.rpow_nonneg hx.le (-θ)) hσ hr h₁ hTwo
  have e : hairerCrossCovarianceTwo N ρ ε ρ ε x ^ 2 - hairerCrossCovarianceTwo N ρ ε ρ' ε' x ^ 2 -
      hairerCrossCovarianceTwo N ρ' ε' ρ ε x ^ 2 + hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x ^ 2 =
      ((hairerCrossCovarianceTwo N ρ ε ρ ε x - hairerCrossCovarianceTwo N ρ ε ρ' ε' x -
        hairerCrossCovarianceTwo N ρ' ε' ρ ε x + hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x) *
        (hairerCrossCovarianceTwo N ρ ε ρ ε x + hairerCrossCovarianceTwo N ρ ε ρ' ε' x +
        hairerCrossCovarianceTwo N ρ' ε' ρ ε x + hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x) +
        (hairerCrossCovarianceTwo N ρ ε ρ ε x + hairerCrossCovarianceTwo N ρ ε ρ' ε' x -
        hairerCrossCovarianceTwo N ρ' ε' ρ ε x - hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x) *
        (hairerCrossCovarianceTwo N ρ ε ρ ε x - hairerCrossCovarianceTwo N ρ ε ρ' ε' x +
        hairerCrossCovarianceTwo N ρ' ε' ρ ε x - hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x)) / 2 := by
    ring
  rw [e]
  refine h.trans (le_of_eq ?_)
  have := cmd_rpow_pq (θ := θ) hx 2
  rw [show (-2 : ℝ) - 2 * θ = -((2 : ℕ) : ℝ) - 2 * θ by norm_num, ← this, cmd_rpow_mu hM]
  ring

/-- **Second difference of cubes of the cross covariances.**
`|a³ - b³ - c³ + d³| ≲ (max ε ε')^(2θ) s(x)^(-3-2θ)`. -/
theorem hairerCrossTwo_cube_sub_abs_le (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ x : SpaceTime, 0 < torusParabolicSize x →
        |hairerCrossCovarianceTwo N ρ ε ρ ε x ^ 3 - hairerCrossCovarianceTwo N ρ ε ρ' ε' x ^ 3 -
            hairerCrossCovarianceTwo N ρ' ε' ρ ε x ^ 3 + hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x ^ 3| ≤
          C * (max ε ε') ^ (2 * θ) * torusParabolicSize x ^ (-3 - 2 * θ) := by
  obtain ⟨A, hA, hdata⟩ := cmd_cross_data N ρ ρ' hρ hρ' hθ hθ1
  refine ⟨A ^ 3, by positivity, ?_⟩
  intro ε ε' hε hε1 hε' hε'1 x hx
  obtain ⟨hσ, hr₁, hr, h₁, hTwo, h₁', hTwo'⟩ := hdata hε hε1 hε' hε'1 x hx
  have hM : 0 < max ε ε' := lt_max_of_lt_left hε
  have h := treeWick_alg_cube hA (Real.rpow_nonneg hM.le θ) (Real.rpow_nonneg hx.le (-(1 : ℝ)))
    (Real.rpow_nonneg hx.le (-θ)) hσ hr₁ hr h₁ hTwo h₁' hTwo'
  have e : hairerCrossCovarianceTwo N ρ ε ρ ε x ^ 3 - hairerCrossCovarianceTwo N ρ ε ρ' ε' x ^ 3 -
      hairerCrossCovarianceTwo N ρ' ε' ρ ε x ^ 3 + hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x ^ 3 =
      (3 * ((hairerCrossCovarianceTwo N ρ ε ρ ε x + hairerCrossCovarianceTwo N ρ ε ρ' ε' x -
        hairerCrossCovarianceTwo N ρ' ε' ρ ε x - hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x) ^ 2 *
        (hairerCrossCovarianceTwo N ρ ε ρ ε x - hairerCrossCovarianceTwo N ρ ε ρ' ε' x -
        hairerCrossCovarianceTwo N ρ' ε' ρ ε x + hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x) +
        (hairerCrossCovarianceTwo N ρ ε ρ ε x - hairerCrossCovarianceTwo N ρ ε ρ' ε' x +
        hairerCrossCovarianceTwo N ρ' ε' ρ ε x - hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x) ^ 2 *
        (hairerCrossCovarianceTwo N ρ ε ρ ε x - hairerCrossCovarianceTwo N ρ ε ρ' ε' x -
        hairerCrossCovarianceTwo N ρ' ε' ρ ε x + hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x) +
        2 * ((hairerCrossCovarianceTwo N ρ ε ρ ε x + hairerCrossCovarianceTwo N ρ ε ρ' ε' x -
        hairerCrossCovarianceTwo N ρ' ε' ρ ε x - hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x) *
        (hairerCrossCovarianceTwo N ρ ε ρ ε x - hairerCrossCovarianceTwo N ρ ε ρ' ε' x +
        hairerCrossCovarianceTwo N ρ' ε' ρ ε x - hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x) *
        (hairerCrossCovarianceTwo N ρ ε ρ ε x + hairerCrossCovarianceTwo N ρ ε ρ' ε' x +
        hairerCrossCovarianceTwo N ρ' ε' ρ ε x + hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x)) +
        (hairerCrossCovarianceTwo N ρ ε ρ ε x + hairerCrossCovarianceTwo N ρ ε ρ' ε' x +
        hairerCrossCovarianceTwo N ρ' ε' ρ ε x + hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x) ^ 2 *
        (hairerCrossCovarianceTwo N ρ ε ρ ε x - hairerCrossCovarianceTwo N ρ ε ρ' ε' x -
        hairerCrossCovarianceTwo N ρ' ε' ρ ε x + hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x)) +
        (hairerCrossCovarianceTwo N ρ ε ρ ε x - hairerCrossCovarianceTwo N ρ ε ρ' ε' x -
        hairerCrossCovarianceTwo N ρ' ε' ρ ε x + hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x) ^ 3) / 16 := by
    ring
  rw [e]
  refine h.trans (le_of_eq ?_)
  have := cmd_rpow_pq (θ := θ) hx 3
  rw [show (-3 : ℝ) - 2 * θ = -((3 : ℕ) : ℝ) - 2 * θ by norm_num, ← this, cmd_rpow_mu hM]
  ring

/-- **Second difference of the cross covariances.**
`|a - b - c + d| ≲ (max ε ε')^(2θ) s(x)^(-1-2θ)`, with `a, b, c, d` the 2×2 table of
`(ρ, ε), (ρ', ε')`. -/
theorem hairerCrossTwo_second_diff_abs_le (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ x : SpaceTime, 0 < torusParabolicSize x →
        |hairerCrossCovarianceTwo N ρ ε ρ ε x - hairerCrossCovarianceTwo N ρ ε ρ' ε' x -
            hairerCrossCovarianceTwo N ρ' ε' ρ ε x + hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x| ≤
          C * (max ε ε') ^ (2 * θ) * torusParabolicSize x ^ (-1 - 2 * θ) := by
  obtain ⟨C, hC, h⟩ := hairerKernelDiffCovarianceTwo_abs_le N ρ ρ' hρ hρ' hθ hθ1
  refine ⟨C, hC, fun {ε ε'} hε hε1 hε' hε'1 x hx => ?_⟩
  have := h hε hε1 hε' hε'1 x hx
  rwa [hairerKernelDiffCovarianceTwo_eq_cross N ρ ρ' hρ hρ' hε hε1 hε' hε'1 x] at this

end RegularityStructures.Phi43

end
