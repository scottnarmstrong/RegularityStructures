/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.KernelSmoothingComparison
public import GlobalPhi43.Local.SmallPastSeminorm

/-! Estimates with the actual finite Q_epsilon and exact 7/8-depth loss. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 MeasureTheory Set
open scoped ContDiff BigOperators

theorem source_smoothing_error {I : Type*} (A : Finset I) (β : I → ℝ)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (U : GermPoint → ℝ)
    {r d₀ d ε L R γ M : ℝ} (hr : 0 ≤ r) (hd : d ∈ Ioc (0 : ℝ) d₀)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hL : 0 < L) (hLd : L ≤ d / 8)
    (hR : 0 ≤ R) (hRL : R ≤ L) (hγ : 1 < γ) (hγ₂ : γ ≤ 2) (hM : 0 ≤ M)
    (hβ : ∀ i ∈ A, 0 ≤ β i) (hβγ : ∀ i ∈ A, β i ≤ γ)
    (hU : ∃ O : Set GermPoint, IsOpen O ∧
      closure (sourceCylinder r) ×ˢ closure (sourceCylinder r) ⊆ O ∧ ContDiffOn ℝ ∞ U O)
    (hdiag : ∀ x ∈ sourceCylinder r, U (x, x) = 0)
    {x y : ParabolicSpace} (hx : x ∈ cylinderInterior r d) (hy : y ∈ pastBall x R)
    (hthree : ∀ b ∈ sourceCylinder r, b ∈ symmetricBall x (d / 2) →
      ∀ z ∈ sourceCylinder r, z ∈ symmetricBall b (d / 4) →
      d ^ γ * |U (x, z) - U (x, b) - U (b, z)| ≤
        M * ∑ i ∈ A, pdist x b ^ β i * pdist b z ^ (γ - β i)) :
    |(∫ w, infiniteKernel Φ hΦ (ε ^ 2 * L) (mul_pos (sq_pos_of_pos hε) hL) w * U (x, y + w)) - U (x, y)| ≤
      (M / d ^ γ) * (∑ i ∈ A, R ^ β i * (ε ^ 2 * L) ^ (γ - β i)) +
        ((smallPastRemainderSeminorm U (diagonalSpatialCoefficient U) r d₀ (ε / 32) γ).toReal /
          (7 * d / 8) ^ γ) * (ε ^ 2 * L) ^ γ := by
  have hdpos : 0 < d := hd.1
  have hd₁ : d < 1 := by nlinarith [hx.1, hx.2.1, sq_nonneg r]
  have hεsq : ε ^ 2 ≤ 1 := by nlinarith
  have hT : 0 < ε ^ 2 * L := mul_pos (sq_pos_of_pos hε) hL
  have hTL : ε ^ 2 * L ≤ L := by nlinarith [mul_le_mul_of_nonneg_right hεsq hL.le]
  have hT₁ : ε ^ 2 * L ≤ 1 := by linarith
  have hTd : ε ^ 2 * L < d / 4 := by linarith
  have hfactor : 0 < ε * (7 / 16 - ε) := mul_pos hε (by linarith)
  have hTS : ε ^ 2 * L < ε * (7 * d / 8) / 16 := by
    have hm := mul_le_mul_of_nonneg_left hLd (sq_nonneg ε)
    nlinarith [mul_pos hfactor hdpos]
  have hQfinite := smallPastRemainderSeminorm_ne_top U (d₀ := d₀) hr
    (by positivity : 0 < ε / 32) (by linarith : ε / 32 ≤ 1 / 16) (by linarith) hγ₂ hU hdiag
  obtain ⟨O, hO, hKO, hs⟩ := hU
  have hcont : ContinuousOn U (sourceCylinder r ×ˢ sourceCylinder r) := by
    intro p hp
    exact (hs.contDiffAt (hO.mem_nhds (hKO ⟨subset_closure hp.1, subset_closure hp.2⟩))).continuousAt.continuousWithinAt
  have hydepth : y ∈ cylinderInterior r (7 * d / 8) :=
    pastBall_subset_interior (by positivity) hR (by linarith) hx hy
  have hd' : 7 * d / 8 ∈ Ioc (0 : ℝ) d₀ := ⟨by positivity, by linarith [hd.2]⟩
  have htrip : ∀ b ∈ sourceCylinder r, b ∈ symmetricBall x (d / 2) →
      ∀ z ∈ sourceCylinder r, z ∈ symmetricBall b (d / 4) →
      |U (x, z) - U (x, b) - U (b, z)| ≤
        (M / d ^ γ) * ∑ i ∈ A, pdist x b ^ β i * pdist b z ^ (γ - β i) := by
    intro b hb hbx z hz hzb
    have hh : |U (x, z) - U (x, b) - U (b, z)| ≤
        (M * ∑ i ∈ A, pdist x b ^ β i * pdist b z ^ (γ - β i)) / d ^ γ :=
      (le_div_iff₀ (Real.rpow_pos_of_pos hdpos γ)).2 (by
        rw [mul_comm]; exact hthree b hb hbx z hz hzb)
    convert hh using 1; ring
  apply kernel_smoothing_comparison A β Φ hΦ (fun a b => U (a, b)) (diagonalSpatialCoefficient U)
    hdpos hT hT₁ hR (by linarith) hTd hTS (by linarith)
    (div_nonneg hM (Real.rpow_nonneg hdpos.le _))
    (div_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg hd'.1.le _)) hβ hβγ
    (by simpa only [Prod.mk.eta] using hcont) hx hy htrip
  intro z hz
  have hcut : 2 * (ε / 32) * (7 * d / 8) = ε * (7 * d / 8) / 16 := by ring
  have hz' : z ∈ pastBall y (2 * (ε / 32) * (7 * d / 8)) := by rw [hcut]; exact hz
  have hb := smallPastRemainderSeminorm_bound U (diagonalSpatialCoefficient U) hQfinite hd' hydepth hz'
  rw [Real.div_rpow (pdist_nonneg y z) hd'.1.le] at hb
  unfold affineRemainder at hb
  convert hb using 1; ring

end GlobalPhi43.Local
