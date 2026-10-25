/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramMultiChaosFour

/-!
# Chaos `2` of the difference bound for `I(Ψ²) Ψ²`

The second difference of the chaos-`2` kernel `16 c₀₁ c₂₃ (c₀₂ c₁₃ + c₀₃ c₁₂)` is dominated by the sum
`i2Psi2Maj2` of eight monomials, each a product of four covariance weights with the exponent of
exactly one raised by `2θ`: the four monomials of `c₀₁ c₂₃ c₀₂ c₁₃` (a cross pairing, times a power
of `d = c₁₃`) and the four of `c₀₁ c₂₃ c₀₃ c₁₂` (a product of two pair integrals).

`i2Psi2LintBound_diff_chaos2`: `∫∫ |A| |A'| (that sum) ≲ B² F`.
-/

@[expose] public section

namespace RegularityStructures

/-- The sum of the eight monomials of the chaos-`2` difference
(`c₀₁ = s(y - w)`, `c₂₃ = s(y' - w')`, `c₀₂ = s(w' - w)`, `c₀₃ = s(y' - w)`, `c₁₂ = s(y - w')`,
`c₁₃ = s(y - y')`). -/
noncomputable def i2Psi2Maj2 (θ : ℝ) (K : SpaceTime → ℝ) (x y y' : SpaceTime)
    (q : SpaceTime × SpaceTime) : ℝ :=
  i2Psi2Triple K x y y' y y' (1 + 2 * θ) 1 1 q * torusParabolicSize (y - y') ^ (-(1 : ℝ)) +
    i2Psi2Triple K x y y' y y' 1 (1 + 2 * θ) 1 q * torusParabolicSize (y - y') ^ (-(1 : ℝ)) +
    i2Psi2Triple K x y y' y y' 1 1 (1 + 2 * θ) q * torusParabolicSize (y - y') ^ (-(1 : ℝ)) +
    i2Psi2Triple K x y y' y y' 1 1 1 q * torusParabolicSize (y - y') ^ (-(1 + 2 * θ)) +
    i2Psi2Quad K x y y' (1 + 2 * θ) 1 1 1 q + i2Psi2Quad K x y y' 1 (1 + 2 * θ) 1 1 q +
    i2Psi2Quad K x y y' 1 1 (1 + 2 * θ) 1 q + i2Psi2Quad K x y y' 1 1 1 (1 + 2 * θ) q

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

/-- **Pair-product pairing with the raised exponent in the first pair**:
`a, b ≥ 1`, `a, b ≤ 1 + 2θ`, `a + b = 2 + 2θ`. -/
theorem i2Psi2LintBound_diff_quad_first {θ δ a b : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) (ha : 1 ≤ a) (hb : 1 ≤ b) (ha' : a ≤ 1 + 2 * θ)
    (hb' : b ≤ 1 + 2 * θ) (hab : a + b = 2 + 2 * θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ x y y' : SpaceTime, i2Psi2PointCfg x y y' →
        i2Psi2LintBound volume (i2Psi2Quad K x y y' a b 1 1)
          (C * B ^ 2 * i2Psi2DiffF θ δ (torusParabolicSize (y - x)) (torusParabolicSize (y' - x))
            (torusParabolicSize (y - y'))) := by
  obtain ⟨C0, hC0, h0⟩ := i2Psi2LintBound_diag_prod_pair (γ₁ := 0) (γ₂ := 2 * θ) (e₁ := a)
    (e₂ := b) (e₃ := 1) (e₄ := 1) le_rfl (by norm_num) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by norm_num) (by norm_num) (by linarith) (by norm_num) (by linarith) (by linarith)
    (by linarith)
  refine ⟨136 * C0, by positivity, ?_⟩
  intro K B hK x y y' hc
  obtain ⟨hr, hr1, hr', hr1', hd⟩ := id hc
  obtain ⟨hdd, hr'd, -⟩ := hc.sizes
  have hB := hK.1
  have hbd := h0 hK x y y' hr hr' hd
  refine hbd.mono (fun q => le_rfl) ?_
  have e1 : (0 : ℝ) + a + b - 2 = 2 * θ := by linarith
  have e2 : 2 * θ + 1 + 1 - 2 = 2 * θ := by ring
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

/-- **Pair-product pairing with the raised exponent in the second pair**:
`c, e ≥ 1`, `c, e ≤ 1 + 2θ`, `c + e = 2 + 2θ`. -/
theorem i2Psi2LintBound_diff_quad_second {θ δ c e : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) (hc1 : 1 ≤ c) (he1 : 1 ≤ e) (hc' : c ≤ 1 + 2 * θ)
    (he' : e ≤ 1 + 2 * θ) (hce : c + e = 2 + 2 * θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ x y y' : SpaceTime, i2Psi2PointCfg x y y' →
        i2Psi2LintBound volume (i2Psi2Quad K x y y' 1 1 c e)
          (C * B ^ 2 * i2Psi2DiffF θ δ (torusParabolicSize (y - x)) (torusParabolicSize (y' - x))
            (torusParabolicSize (y - y'))) := by
  obtain ⟨C0, hC0, h0⟩ := i2Psi2LintBound_diag_prod_pair (γ₁ := 2 * θ) (γ₂ := 0) (e₁ := 1)
    (e₂ := 1) (e₃ := c) (e₄ := e) (by linarith) (by linarith) le_rfl (by norm_num)
    (by norm_num) (by norm_num) (by linarith) (by norm_num) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨136 * C0, by positivity, ?_⟩
  intro K B hK x y y' hcf
  obtain ⟨hr, hr1, hr', hr1', hd⟩ := id hcf
  obtain ⟨hdd, -, hrd⟩ := hcf.sizes
  have hB := hK.1
  have hbd := h0 hK x y y' hr hr' hd
  refine hbd.mono (fun q => le_rfl) ?_
  have e1 : 2 * θ + 1 + 1 - 2 = 2 * θ := by ring
  have e2 : (0 : ℝ) + c + e - 2 = 2 * θ := by linarith
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

/-- **Chaos `2` of the difference bound**: `∫∫ |A| |A'| (sum of the eight monomials) ≲ B² F`. -/
theorem i2Psi2LintBound_diff_chaos2 {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ x y y' : SpaceTime, i2Psi2PointCfg x y y' →
        i2Psi2LintBound volume (i2Psi2Maj2 θ K x y y')
          (C * B ^ 2 * i2Psi2DiffF θ δ (torusParabolicSize (y - x)) (torusParabolicSize (y' - x))
            (torusParabolicSize (y - y'))) := by
  obtain ⟨C1, hC1, h1⟩ := i2Psi2LintBound_diff_cross_inner hθ hθ1 hδ hδ1 (e₁ := 1 + 2 * θ)
    (e₂ := 1) (e₃ := 1) (by linarith) le_rfl le_rfl le_rfl (by linarith) (by ring)
  obtain ⟨C2, hC2, h2⟩ := i2Psi2LintBound_diff_cross_inner hθ hθ1 hδ hδ1 (e₁ := 1)
    (e₂ := 1 + 2 * θ) (e₃ := 1) le_rfl (by linarith) le_rfl (by linarith) le_rfl (by ring)
  obtain ⟨C3, hC3, h3⟩ := i2Psi2LintBound_diff_cross_inner hθ hθ1 hδ hδ1 (e₁ := 1)
    (e₂ := 1) (e₃ := 1 + 2 * θ) le_rfl le_rfl (by linarith) (by linarith) (by linarith)
    (by ring)
  obtain ⟨C4, hC4, h4⟩ := i2Psi2LintBound_diff_cross_outer hθ hθ1 hδ hδ1
  obtain ⟨C5, hC5, h5⟩ := i2Psi2LintBound_diff_quad_first hθ hθ1 hδ hδ1 (a := 1 + 2 * θ) (b := 1)
    (by linarith) le_rfl le_rfl (by linarith) (by ring)
  obtain ⟨C6, hC6, h6⟩ := i2Psi2LintBound_diff_quad_first hθ hθ1 hδ hδ1 (a := 1) (b := 1 + 2 * θ)
    le_rfl (by linarith) (by linarith) le_rfl (by ring)
  obtain ⟨C7, hC7, h7⟩ := i2Psi2LintBound_diff_quad_second hθ hθ1 hδ hδ1 (c := 1 + 2 * θ)
    (e := 1) (by linarith) le_rfl le_rfl (by linarith) (by ring)
  obtain ⟨C8, hC8, h8⟩ := i2Psi2LintBound_diff_quad_second hθ hθ1 hδ hδ1 (c := 1)
    (e := 1 + 2 * θ) le_rfl (by linarith) (by linarith) le_rfl (by ring)
  refine ⟨C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8, by positivity, ?_⟩
  intro K B hK x y y' hc
  have hc' := hc
  obtain ⟨hr, -, hr', -, hd⟩ := hc'
  obtain ⟨hxy, hxy'⟩ := hc.time_le
  have hg1 : |y'.1 - x.1| ≤ 2 := by linarith
  have hh : |y.1 - x.1| ≤ 2 := by linarith
  obtain ⟨hB, hKm, -, -, -⟩ := id hK
  have hFn := i2Psi2DiffF_nonneg (θ := θ) (δ := δ) hr hr' hd
  have nd : ∀ e : ℝ, 0 ≤ torusParabolicSize (y - y') ^ e := fun e =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have nT := i2Psi2Triple_nonneg K x y y' y y'
  have mT := measurable_i2Psi2Triple hKm x y y' y y'
  have mQ := measurable_i2Psi2Quad hKm x y y'
  have nQ := i2Psi2Quad_nonneg K x y y'
  have key := i2Psi2LintBound.add_eight
    ((mT (1 + 2 * θ) 1 1).mul_const _) ((mT 1 (1 + 2 * θ) 1).mul_const _)
    ((mT 1 1 (1 + 2 * θ)).mul_const _) ((mT 1 1 1).mul_const _) (mQ (1 + 2 * θ) 1 1 1)
    (mQ 1 (1 + 2 * θ) 1 1) (mQ 1 1 (1 + 2 * θ) 1)
    (fun q => mul_nonneg (nT _ _ _ q) (nd _)) (fun q => mul_nonneg (nT _ _ _ q) (nd _))
    (fun q => mul_nonneg (nT _ _ _ q) (nd _)) (fun q => mul_nonneg (nT _ _ _ q) (nd _))
    (fun q => nQ _ _ _ _ q) (fun q => nQ _ _ _ _ q) (fun q => nQ _ _ _ _ q)
    (fun q => nQ _ _ _ _ q)
    (mul_nonneg (mul_nonneg hC1 (sq_nonneg B)) hFn) (mul_nonneg (mul_nonneg hC2 (sq_nonneg B)) hFn)
    (mul_nonneg (mul_nonneg hC3 (sq_nonneg B)) hFn) (mul_nonneg (mul_nonneg hC4 (sq_nonneg B)) hFn)
    (mul_nonneg (mul_nonneg hC5 (sq_nonneg B)) hFn) (mul_nonneg (mul_nonneg hC6 (sq_nonneg B)) hFn)
    (mul_nonneg (mul_nonneg hC7 (sq_nonneg B)) hFn) (mul_nonneg (mul_nonneg hC8 (sq_nonneg B)) hFn)
    (h1 hK x y y' y y' hc hh hg1) (h2 hK x y y' y y' hc hh hg1)
    (h3 hK x y y' y y' hc hh hg1) (h4 hK x y y' y y' hc hh hg1)
    (h5 hK x y y' hc) (h6 hK x y y' hc) (h7 hK x y y' hc) (h8 hK x y y' hc)
  refine key.mono (fun q => le_of_eq (by unfold i2Psi2Maj2; rfl)) (le_of_eq (by ring))

end RegularityStructures

end
