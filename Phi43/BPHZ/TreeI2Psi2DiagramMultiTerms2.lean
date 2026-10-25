/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramMultiTerms

/-!
# The product and cross monomials of the difference bound for `I(Ψ²) Ψ²`

Continuation of `TreeI2Psi2DiagramMultiTerms`: the product pairings with a raised exponent
(`i2Psi2LintBound_diff_prod_left`, `_prod_right`), and the cross pairings
(`i2Psi2LintBound_diff_cross_inner`, `_cross_outer`).
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- **Product pairing with the raised exponent on the left**:
`(∫ |A| s(y' - w)^(-(2+2θ))) (∫ |A'| s(y - w')^(-2)) ≲ B² F`. -/
theorem i2Psi2LintBound_diff_prod_left {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ x y y' : SpaceTime, i2Psi2PointCfg x y y' →
        i2Psi2LintBound volume (fun q => i2Psi2Triple K x y y' y' y (2 + 2 * θ) 0 2 q)
          (C * B ^ 2 * i2Psi2DiffF θ δ (torusParabolicSize (y - x)) (torusParabolicSize (y' - x))
            (torusParabolicSize (y - y'))) := by
  obtain ⟨C0, hC0, h0⟩ := i2Psi2LintBound_diag_prod_single (γ₁ := 0) (γ₂ := 2 * θ)
    (e₁ := 2 + 2 * θ) (e₂ := 2) le_rfl (by norm_num) (by linarith) (by linarith) (by linarith)
    (by norm_num) (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨136 * C0, by positivity, ?_⟩
  intro K B hK x y y' hc
  obtain ⟨hr, hr1, hr', hr1', hd⟩ := id hc
  obtain ⟨hdd, hr'd, -⟩ := hc.sizes
  have hB := hK.1
  have hb := h0 hK x y y' hr hr' hd
  refine hb.mono (fun q => ?_) ?_
  · unfold i2Psi2Triple
    simp only [neg_zero, Real.rpow_zero, mul_one]
    exact le_of_eq (by ring)
  · have e1 : (0 : ℝ) + (2 + 2 * θ) - 2 = 2 * θ := by ring
    have e2 : 2 * θ + 2 - 2 = 2 * θ := by ring
    rw [e1, e2, Real.rpow_zero]
    have hp := alg_pat hr hr1 hr' hr1' hd hdd hr'd (σ := 2 * θ) (ℓ := 2 * θ + δ) (by linarith)
      (by linarith) (by linarith) (by linarith)
    have hF := i2Psi2DiffF_ge_pat (θ := θ) (δ := δ) hr hr' hd
    have hCB : 0 ≤ C0 * B ^ 2 := by positivity
    calc C0 * B ^ 2 * 1 * torusParabolicSize (y' - x) ^ (2 * θ) *
          (torusParabolicSize (y - y') ^ (-(2 * θ)) + torusParabolicSize (y' - x) ^ (-(2 * θ))) *
          (torusParabolicSize (y - y') ^ (-(2 * θ)) + torusParabolicSize (y - x) ^ (-(2 * θ)))
        = C0 * B ^ 2 * ((torusParabolicSize (y - y') ^ (-(2 * θ)) +
            torusParabolicSize (y' - x) ^ (-(2 * θ))) * (torusParabolicSize (y' - x) ^ (2 * θ) *
            (torusParabolicSize (y - y') ^ (-(2 * θ)) + torusParabolicSize (y - x) ^ (-(2 * θ))))) :=
          by ring
      _ ≤ C0 * B ^ 2 * (136 * (torusParabolicSize (y - y') ^ (-(2 : ℝ)) *
            (torusParabolicSize (y - x) ^ (2 - (2 * θ + δ)) +
              torusParabolicSize (y' - x) ^ (2 - (2 * θ + δ))) +
            torusParabolicSize (y - y') ^ (-(2 * θ + δ)) +
            torusParabolicSize (y - x) ^ (-(2 * θ + δ)))) :=
          mul_le_mul_of_nonneg_left hp hCB
      _ ≤ C0 * B ^ 2 * (136 * i2Psi2DiffF θ δ (torusParabolicSize (y - x))
            (torusParabolicSize (y' - x)) (torusParabolicSize (y - y'))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF (by norm_num)) hCB
      _ = _ := by ring

/-- **Product pairing with the raised exponent on the right**:
`(∫ |A| s(y' - w)^(-2)) (∫ |A'| s(y - w')^(-(2+2θ))) ≲ B² F`. -/
theorem i2Psi2LintBound_diff_prod_right {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ x y y' : SpaceTime, i2Psi2PointCfg x y y' →
        i2Psi2LintBound volume (fun q => i2Psi2Triple K x y y' y' y 2 0 (2 + 2 * θ) q)
          (C * B ^ 2 * i2Psi2DiffF θ δ (torusParabolicSize (y - x)) (torusParabolicSize (y' - x))
            (torusParabolicSize (y - y'))) := by
  obtain ⟨C0, hC0, h0⟩ := i2Psi2LintBound_diag_prod_single (γ₁ := 2 * θ) (γ₂ := 0)
    (e₁ := 2) (e₂ := 2 + 2 * θ) (by linarith) (by linarith) le_rfl (by norm_num)
    (by norm_num) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨136 * C0, by positivity, ?_⟩
  intro K B hK x y y' hc
  obtain ⟨hr, hr1, hr', hr1', hd⟩ := id hc
  obtain ⟨hdd, -, hrd⟩ := hc.sizes
  have hB := hK.1
  have hb := h0 hK x y y' hr hr' hd
  refine hb.mono (fun q => ?_) ?_
  · unfold i2Psi2Triple
    simp only [neg_zero, Real.rpow_zero, mul_one]
    exact le_of_eq (by ring)
  · have e1 : 2 * θ + 2 - 2 = 2 * θ := by ring
    have e2 : (0 : ℝ) + (2 + 2 * θ) - 2 = 2 * θ := by ring
    rw [e1, e2, Real.rpow_zero]
    have hdd' : torusParabolicSize (y - y') ≤ 8 * (torusParabolicSize (y' - x) +
        torusParabolicSize (y - x)) := by linarith
    have hp := alg_pat hr' hr1' hr hr1 hd hdd' hrd (σ := 2 * θ) (ℓ := 2 * θ + δ) (by linarith)
      (by linarith) (by linarith) (by linarith)
    have hF := i2Psi2DiffF_ge_pat' (θ := θ) (δ := δ) hr hr' hd
    have hCB : 0 ≤ C0 * B ^ 2 := by positivity
    calc C0 * B ^ 2 * torusParabolicSize (y - x) ^ (2 * θ) * 1 *
          (torusParabolicSize (y - y') ^ (-(2 * θ)) + torusParabolicSize (y' - x) ^ (-(2 * θ))) *
          (torusParabolicSize (y - y') ^ (-(2 * θ)) + torusParabolicSize (y - x) ^ (-(2 * θ)))
        = C0 * B ^ 2 * ((torusParabolicSize (y - y') ^ (-(2 * θ)) +
            torusParabolicSize (y - x) ^ (-(2 * θ))) * (torusParabolicSize (y - x) ^ (2 * θ) *
            (torusParabolicSize (y - y') ^ (-(2 * θ)) + torusParabolicSize (y' - x) ^ (-(2 * θ))))) :=
          by ring
      _ ≤ C0 * B ^ 2 * (136 * (torusParabolicSize (y - y') ^ (-(2 : ℝ)) *
            (torusParabolicSize (y' - x) ^ (2 - (2 * θ + δ)) +
              torusParabolicSize (y - x) ^ (2 - (2 * θ + δ))) +
            torusParabolicSize (y - y') ^ (-(2 * θ + δ)) +
            torusParabolicSize (y' - x) ^ (-(2 * θ + δ)))) :=
          mul_le_mul_of_nonneg_left hp hCB
      _ ≤ C0 * B ^ 2 * (136 * i2Psi2DiffF θ δ (torusParabolicSize (y - x))
            (torusParabolicSize (y' - x)) (torusParabolicSize (y - y'))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF (by norm_num)) hCB
      _ = _ := by ring

/-- **Cross pairing with a raised exponent among the integrated weights**, times `d^(-1)`:
`e₁, e₂, e₃ ≥ 1` with `e₁, e₂ ≤ 1 + 2θ` and `e₁ + e₂ + e₃ = 3 + 2θ`. -/
theorem i2Psi2LintBound_diff_cross_inner {θ δ e₁ e₂ e₃ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) (h1 : 1 ≤ e₁) (h2 : 1 ≤ e₂) (h3 : 1 ≤ e₃)
    (h1' : e₁ ≤ 1 + 2 * θ) (h2' : e₂ ≤ 1 + 2 * θ)
    (hsum : e₁ + e₂ + e₃ = 3 + 2 * θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ x y y' g₁ h : SpaceTime, i2Psi2PointCfg x y y' → |g₁.1 - x.1| ≤ 2 → |h.1 - x.1| ≤ 2 →
        i2Psi2LintBound volume (fun q => i2Psi2Triple K x y y' g₁ h e₁ e₂ e₃ q *
          torusParabolicSize (y - y') ^ (-(1 : ℝ)))
          (C * B ^ 2 * i2Psi2DiffF θ δ (torusParabolicSize (y - x)) (torusParabolicSize (y' - x))
            (torusParabolicSize (y - y'))) := by
  obtain ⟨C0, hC0, h0⟩ := i2Psi2LintBound_diag_cross (γ := (1 - δ) / 2 - θ)
    (γ' := (1 - δ) / 2 - θ) (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)
  refine ⟨5 * C0, by positivity, ?_⟩
  intro K B hK x y y' g₁ h hc hg₁ hh
  obtain ⟨hr, hr1, hr', hr1', hd⟩ := id hc
  obtain ⟨hxy, hxy'⟩ := hc.time_le
  obtain ⟨hdd, -, -⟩ := hc.sizes
  have hB := hK.1
  have hb := (h0 hK x y y' g₁ h hxy hxy' hg₁ hh).const_mul
    (c := torusParabolicSize (y - y') ^ (-(1 : ℝ)))
    (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  refine hb.mono (fun q => ?_) ?_
  · unfold i2Psi2Triple
    exact le_of_eq (by ring)
  · have hk := alg_pair_key hr hr1 hr' hr1' hd hdd (g := (1 - δ) / 2 - θ) (β := 1) (p := 2)
      (ℓ := 2 * θ + δ) (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num)
      (by linarith)
    have hF1 := i2Psi2DiffF_ge_one (θ := θ) (δ := δ) hr hr' hd
    have hF2 := i2Psi2DiffF_ge_two (θ := θ) (δ := δ) hr hr' hd
    have hCB : 0 ≤ C0 * B ^ 2 := by positivity
    calc torusParabolicSize (y - y') ^ (-(1 : ℝ)) * (C0 * B ^ 2 *
          torusParabolicSize (y - x) ^ ((1 - δ) / 2 - θ) *
          torusParabolicSize (y' - x) ^ ((1 - δ) / 2 - θ))
        = C0 * B ^ 2 * (torusParabolicSize (y - x) ^ ((1 - δ) / 2 - θ) *
          torusParabolicSize (y' - x) ^ ((1 - δ) / 2 - θ) *
          torusParabolicSize (y - y') ^ (-(1 : ℝ))) := by ring
      _ ≤ C0 * B ^ 2 * (5 * i2Psi2DiffF θ δ (torusParabolicSize (y - x))
            (torusParabolicSize (y' - x)) (torusParabolicSize (y - y'))) :=
          mul_le_mul_of_nonneg_left (hk.trans (by linarith)) hCB
      _ = _ := by ring

/-- **Cross pairing times `d^(-(1+2θ))`**. -/
theorem i2Psi2LintBound_diff_cross_outer {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ x y y' g₁ h : SpaceTime, i2Psi2PointCfg x y y' → |g₁.1 - x.1| ≤ 2 → |h.1 - x.1| ≤ 2 →
        i2Psi2LintBound volume (fun q => i2Psi2Triple K x y y' g₁ h 1 1 1 q *
          torusParabolicSize (y - y') ^ (-(1 + 2 * θ)))
          (C * B ^ 2 * i2Psi2DiffF θ δ (torusParabolicSize (y - x)) (torusParabolicSize (y' - x))
            (torusParabolicSize (y - y'))) := by
  obtain ⟨C0, hC0, h0⟩ := i2Psi2LintBound_diag_cross (γ := (1 - δ) / 2)
    (γ' := (1 - δ) / 2) (e₁ := 1) (e₂ := 1) (e₃ := 1) (by linarith) (by linarith)
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num) (by linarith)
    (by norm_num) (by linarith) (by linarith)
  refine ⟨5 * C0, by positivity, ?_⟩
  intro K B hK x y y' g₁ h hc hg₁ hh
  obtain ⟨hr, hr1, hr', hr1', hd⟩ := id hc
  obtain ⟨hxy, hxy'⟩ := hc.time_le
  obtain ⟨hdd, -, -⟩ := hc.sizes
  have hB := hK.1
  have hb := (h0 hK x y y' g₁ h hxy hxy' hg₁ hh).const_mul
    (c := torusParabolicSize (y - y') ^ (-(1 + 2 * θ)))
    (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  refine hb.mono (fun q => ?_) ?_
  · unfold i2Psi2Triple
    exact le_of_eq (by ring)
  · have hk := alg_pair_key hr hr1 hr' hr1' hd hdd (g := (1 - δ) / 2) (β := 1 + 2 * θ)
      (p := 2 + 2 * θ) (ℓ := 2 * θ + δ) (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)
    have e : 2 + 2 * θ - (2 * θ + δ) = 2 - δ := by ring
    rw [e] at hk
    have hF1 := i2Psi2DiffF_ge_one (θ := θ) (δ := δ) hr hr' hd
    have hF3 := i2Psi2DiffF_ge_three (θ := θ) (δ := δ) hr hr' hd
    have hCB : 0 ≤ C0 * B ^ 2 := by positivity
    calc torusParabolicSize (y - y') ^ (-(1 + 2 * θ)) * (C0 * B ^ 2 *
          torusParabolicSize (y - x) ^ ((1 - δ) / 2) * torusParabolicSize (y' - x) ^ ((1 - δ) / 2))
        = C0 * B ^ 2 * (torusParabolicSize (y - x) ^ ((1 - δ) / 2) *
          torusParabolicSize (y' - x) ^ ((1 - δ) / 2) *
          torusParabolicSize (y - y') ^ (-(1 + 2 * θ))) := by ring
      _ ≤ C0 * B ^ 2 * (5 * i2Psi2DiffF θ δ (torusParabolicSize (y - x))
            (torusParabolicSize (y' - x)) (torusParabolicSize (y - y'))) :=
          mul_le_mul_of_nonneg_left (hk.trans (by linarith)) hCB
      _ = _ := by ring

end RegularityStructures

end
