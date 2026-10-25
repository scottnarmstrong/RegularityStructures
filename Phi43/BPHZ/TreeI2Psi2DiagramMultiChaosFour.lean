/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramMultiTerms2

/-!
# Chaos `4` of the difference bound for `I(Ψ²) Ψ²`

The second difference of the chaos-`4` kernel is dominated by the sum `i2Psi2Maj4` of eight
monomials, each a product of four covariance weights with the exponent of exactly one of them
raised by `2θ` (in the notation `c₀₂ = s(w' - w)`, `c₀₃ = s(y' - w)`, `c₁₂ = s(y - w')`,
`c₁₃ = d = s(y - y')`):

`c₀₂^(-(2+2θ)) c₁₃^(-2) + c₀₂^(-2) c₁₃^(-(2+2θ)) + c₀₃^(-(2+2θ)) c₁₂^(-2) +
 c₀₃^(-2) c₁₂^(-(2+2θ)) + (c₀₃^(-(1+2θ)) c₀₂^(-1) c₁₂^(-1) + c₀₃^(-1) c₀₂^(-(1+2θ)) c₁₂^(-1) +
 c₀₃^(-1) c₀₂^(-1) c₁₂^(-(1+2θ))) c₁₃^(-1) + c₀₃^(-1) c₀₂^(-1) c₁₂^(-1) c₁₃^(-(1+2θ))`.

`i2Psi2LintBound_diff_chaos4`: `∫∫ |A| |A'| (that sum) ≲ B² F` with the majorant
`F = i2Psi2DiffF θ δ r r' d` (the block of eight terms is [Hai14, (10.3)] for the chaos-`4` part of
`τ = I(Ψ²) Ψ²`).
-/

@[expose] public section

namespace RegularityStructures

/-- The sum of the eight monomials of the chaos-`4` difference (with the weights
`c₀₃ = s(y' - w)`, `c₀₂ = s(w' - w)`, `c₁₂ = s(y - w')`, `c₁₃ = s(y - y')`). -/
noncomputable def i2Psi2Maj4 (θ : ℝ) (K : SpaceTime → ℝ) (x y y' : SpaceTime)
    (q : SpaceTime × SpaceTime) : ℝ :=
  i2Psi2Triple K x y y' y' y 0 (2 + 2 * θ) 0 q * torusParabolicSize (y - y') ^ (-(2 : ℝ)) +
    i2Psi2Triple K x y y' y' y 0 2 0 q * torusParabolicSize (y - y') ^ (-(2 + 2 * θ)) +
    i2Psi2Triple K x y y' y' y (2 + 2 * θ) 0 2 q + i2Psi2Triple K x y y' y' y 2 0 (2 + 2 * θ) q +
    i2Psi2Triple K x y y' y' y (1 + 2 * θ) 1 1 q * torusParabolicSize (y - y') ^ (-(1 : ℝ)) +
    i2Psi2Triple K x y y' y' y 1 (1 + 2 * θ) 1 q * torusParabolicSize (y - y') ^ (-(1 : ℝ)) +
    i2Psi2Triple K x y y' y' y 1 1 (1 + 2 * θ) q * torusParabolicSize (y - y') ^ (-(1 : ℝ)) +
    i2Psi2Triple K x y y' y' y 1 1 1 q * torusParabolicSize (y - y') ^ (-(1 + 2 * θ))

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Sum of eight lower-integral bounds. -/
theorem i2Psi2LintBound.add_eight {f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ : α → ℝ}
    {M₁ M₂ M₃ M₄ M₅ M₆ M₇ M₈ : ℝ} (m₁ : Measurable f₁) (m₂ : Measurable f₂)
    (m₃ : Measurable f₃) (m₄ : Measurable f₄) (m₅ : Measurable f₅) (m₆ : Measurable f₆)
    (m₇ : Measurable f₇) (n₁ : ∀ a, 0 ≤ f₁ a) (n₂ : ∀ a, 0 ≤ f₂ a) (n₃ : ∀ a, 0 ≤ f₃ a)
    (n₄ : ∀ a, 0 ≤ f₄ a) (n₅ : ∀ a, 0 ≤ f₅ a) (n₆ : ∀ a, 0 ≤ f₆ a) (n₇ : ∀ a, 0 ≤ f₇ a)
    (n₈ : ∀ a, 0 ≤ f₈ a) (p₁ : 0 ≤ M₁) (p₂ : 0 ≤ M₂) (p₃ : 0 ≤ M₃) (p₄ : 0 ≤ M₄) (p₅ : 0 ≤ M₅)
    (p₆ : 0 ≤ M₆) (p₇ : 0 ≤ M₇) (p₈ : 0 ≤ M₈) (b₁ : i2Psi2LintBound μ f₁ M₁)
    (b₂ : i2Psi2LintBound μ f₂ M₂) (b₃ : i2Psi2LintBound μ f₃ M₃)
    (b₄ : i2Psi2LintBound μ f₄ M₄) (b₅ : i2Psi2LintBound μ f₅ M₅)
    (b₆ : i2Psi2LintBound μ f₆ M₆) (b₇ : i2Psi2LintBound μ f₇ M₇)
    (b₈ : i2Psi2LintBound μ f₈ M₈) :
    i2Psi2LintBound μ (fun a => f₁ a + f₂ a + f₃ a + f₄ a + f₅ a + f₆ a + f₇ a + f₈ a)
      (M₁ + M₂ + M₃ + M₄ + M₅ + M₆ + M₇ + M₈) := by
  have s2 := b₁.add m₁.aemeasurable n₁ n₂ p₁ p₂ b₂
  have s3 := s2.add (g := f₃) (m₁.add m₂).aemeasurable (fun a => add_nonneg (n₁ a) (n₂ a)) n₃
    (add_nonneg p₁ p₂) p₃ b₃
  have s4 := s3.add (g := f₄) ((m₁.add m₂).add m₃).aemeasurable
    (fun a => add_nonneg (add_nonneg (n₁ a) (n₂ a)) (n₃ a)) n₄
    (add_nonneg (add_nonneg p₁ p₂) p₃) p₄ b₄
  have s5 := s4.add (g := f₅) (((m₁.add m₂).add m₃).add m₄).aemeasurable
    (fun a => add_nonneg (add_nonneg (add_nonneg (n₁ a) (n₂ a)) (n₃ a)) (n₄ a)) n₅
    (add_nonneg (add_nonneg (add_nonneg p₁ p₂) p₃) p₄) p₅ b₅
  have s6 := s5.add (g := f₆) ((((m₁.add m₂).add m₃).add m₄).add m₅).aemeasurable
    (fun a => add_nonneg (add_nonneg (add_nonneg (add_nonneg (n₁ a) (n₂ a)) (n₃ a)) (n₄ a))
      (n₅ a)) n₆
    (add_nonneg (add_nonneg (add_nonneg (add_nonneg p₁ p₂) p₃) p₄) p₅) p₆ b₆
  have s7 := s6.add (g := f₇) (((((m₁.add m₂).add m₃).add m₄).add m₅).add m₆).aemeasurable
    (fun a => add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (n₁ a) (n₂ a)) (n₃ a))
      (n₄ a)) (n₅ a)) (n₆ a)) n₇
    (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg p₁ p₂) p₃) p₄) p₅) p₆) p₇ b₇
  exact s7.add (g := f₈)
    ((((((m₁.add m₂).add m₃).add m₄).add m₅).add m₆).add m₇).aemeasurable
    (fun a => add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (n₁ a)
      (n₂ a)) (n₃ a)) (n₄ a)) (n₅ a)) (n₆ a)) (n₇ a)) n₈
    (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg p₁ p₂) p₃) p₄) p₅)
      p₆) p₇) p₈ b₈

/-- **Chaos `4` of the difference bound**: `∫∫ |A| |A'| (sum of the eight monomials) ≲ B² F`. -/
theorem i2Psi2LintBound_diff_chaos4 {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ x y y' : SpaceTime, i2Psi2PointCfg x y y' →
        i2Psi2LintBound volume (i2Psi2Maj4 θ K x y y')
          (C * B ^ 2 * i2Psi2DiffF θ δ (torusParabolicSize (y - x)) (torusParabolicSize (y' - x))
            (torusParabolicSize (y - y'))) := by
  obtain ⟨C1, hC1, h1⟩ := i2Psi2LintBound_diff_sq_inner hθ hθ1 hδ hδ1
  obtain ⟨C2, hC2, h2⟩ := i2Psi2LintBound_diff_sq_outer hθ hθ1 hδ hδ1
  obtain ⟨C3, hC3, h3⟩ := i2Psi2LintBound_diff_prod_left hθ hθ1 hδ hδ1
  obtain ⟨C4, hC4, h4⟩ := i2Psi2LintBound_diff_prod_right hθ hθ1 hδ hδ1
  obtain ⟨C5, hC5, h5⟩ := i2Psi2LintBound_diff_cross_inner hθ hθ1 hδ hδ1 (e₁ := 1 + 2 * θ)
    (e₂ := 1) (e₃ := 1) (by linarith) le_rfl le_rfl le_rfl (by linarith) (by ring)
  obtain ⟨C6, hC6, h6⟩ := i2Psi2LintBound_diff_cross_inner hθ hθ1 hδ hδ1 (e₁ := 1)
    (e₂ := 1 + 2 * θ) (e₃ := 1) le_rfl (by linarith) le_rfl (by linarith) le_rfl (by ring)
  obtain ⟨C7, hC7, h7⟩ := i2Psi2LintBound_diff_cross_inner hθ hθ1 hδ hδ1 (e₁ := 1)
    (e₂ := 1) (e₃ := 1 + 2 * θ) le_rfl le_rfl (by linarith) (by linarith) (by linarith)
    (by ring)
  obtain ⟨C8, hC8, h8⟩ := i2Psi2LintBound_diff_cross_outer hθ hθ1 hδ hδ1
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
  have nT := i2Psi2Triple_nonneg K x y y' y' y
  have mT := measurable_i2Psi2Triple hKm x y y' y' y
  have key := i2Psi2LintBound.add_eight
    ((mT 0 (2 + 2 * θ) 0).mul_const _) ((mT 0 2 0).mul_const _) (mT (2 + 2 * θ) 0 2)
    (mT 2 0 (2 + 2 * θ)) ((mT (1 + 2 * θ) 1 1).mul_const _) ((mT 1 (1 + 2 * θ) 1).mul_const _)
    ((mT 1 1 (1 + 2 * θ)).mul_const _)
    (fun q => mul_nonneg (nT _ _ _ q) (nd _)) (fun q => mul_nonneg (nT _ _ _ q) (nd _))
    (fun q => nT _ _ _ q) (fun q => nT _ _ _ q) (fun q => mul_nonneg (nT _ _ _ q) (nd _))
    (fun q => mul_nonneg (nT _ _ _ q) (nd _)) (fun q => mul_nonneg (nT _ _ _ q) (nd _))
    (fun q => mul_nonneg (nT _ _ _ q) (nd _))
    (mul_nonneg (mul_nonneg hC1 (sq_nonneg B)) hFn) (mul_nonneg (mul_nonneg hC2 (sq_nonneg B)) hFn)
    (mul_nonneg (mul_nonneg hC3 (sq_nonneg B)) hFn) (mul_nonneg (mul_nonneg hC4 (sq_nonneg B)) hFn)
    (mul_nonneg (mul_nonneg hC5 (sq_nonneg B)) hFn) (mul_nonneg (mul_nonneg hC6 (sq_nonneg B)) hFn)
    (mul_nonneg (mul_nonneg hC7 (sq_nonneg B)) hFn) (mul_nonneg (mul_nonneg hC8 (sq_nonneg B)) hFn)
    (h1 hK x y y' y' y hc) (h2 hK x y y' y' y hc) (h3 hK x y y' hc) (h4 hK x y y' hc)
    (h5 hK x y y' y' y hc hg1 hh) (h6 hK x y y' y' y hc hg1 hh) (h7 hK x y y' y' y hc hg1 hh)
    (h8 hK x y y' y' y hc hg1 hh)
  refine key.mono (fun q => le_of_eq (by unfold i2Psi2Maj4; rfl)) (le_of_eq (by ring))

end RegularityStructures

end
