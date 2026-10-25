/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI2Psi2Alg

/-!
# The product monomials of the difference of `I(Ψ²) Ψ²`, for arbitrary `x, y, y'`

`I2Psi2DiffSlab x y y' D` says that `D` bounds `s(a - b)` for all `a, b` with
`|a.1 - x.1|, |b.1 - x.1| ≤ |y.1 - x.1| + |y'.1 - x.1| + 2`.  Under it
`i2Psi2Diff_quad_global` bounds `∫∫ i2Psi2Quad K x y y' a b c e`, a product of two single
integrals (`i2Psi2Diff_single_global`), and `i2Psi2Diff_triple_slab` restates the bound for the
chain monomials.
-/

@[expose] public section

namespace RegularityStructures

/-- `D` bounds `s(a - b)` on the time slab of radius `|y.1 - x.1| + |y'.1 - x.1| + 2` around `x`. -/
def I2Psi2DiffSlab (x y y' : SpaceTime) (D : ℝ) : Prop :=
  ∀ a b : SpaceTime, |a.1 - x.1| ≤ |y.1 - x.1| + |y'.1 - x.1| + 2 →
    |b.1 - x.1| ≤ |y.1 - x.1| + |y'.1 - x.1| + 2 → torusParabolicSize (a - b) ≤ D

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem I2Psi2DiffSlab.pair {x y y' : SpaceTime} {D : ℝ} (h : I2Psi2DiffSlab x y y' D) :
    ∀ w v : SpaceTime, |w.1 - x.1| ≤ |y.1 - x.1| + 1 → |v.1 - x.1| ≤ |y'.1 - x.1| + 1 →
      torusParabolicSize (w - v) ≤ D := fun w v hw hv =>
  h w v (by linarith [abs_nonneg (y'.1 - x.1)]) (by linarith [abs_nonneg (y.1 - x.1)])

theorem I2Psi2DiffSlab.left {x y y' : SpaceTime} {D : ℝ} (h : I2Psi2DiffSlab x y y' D) :
    ∀ w : SpaceTime, |w.1 - x.1| ≤ |y.1 - x.1| + 1 → torusParabolicSize (y' - w) ≤ D :=
  fun w hw => h y' w (by linarith [abs_nonneg (y.1 - x.1)])
    (by linarith [abs_nonneg (y'.1 - x.1)])

theorem I2Psi2DiffSlab.right {x y y' : SpaceTime} {D : ℝ} (h : I2Psi2DiffSlab x y y' D) :
    ∀ w : SpaceTime, |w.1 - x.1| ≤ |y'.1 - x.1| + 1 → torusParabolicSize (y - w) ≤ D :=
  fun w hw => h y w (by linarith [abs_nonneg (y'.1 - x.1)])
    (by linarith [abs_nonneg (y.1 - x.1)])

/-- **The chain monomial, under the slab hypothesis.** -/
theorem i2Psi2Diff_triple_slab {a b c δ η : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c)
    (hδ : 0 < δ) (hη : 0 < η) (hc2 : 3 + c < 5) (hbδ : b + δ < 5)
    (hsum : 3 + c + b + δ = 5 + η) (haη : 3 + a + η < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ} {B : ℝ}, SingularKernelData K Q B →
      ∀ (x y y' g h : SpaceTime) {D : ℝ}, 0 ≤ D → I2Psi2DiffSlab x y y' D →
      I2Psi2DiffIntBd (i2Psi2Triple K x y y' g h a b c)
        (C * B ^ 2 * D ^ δ * (1 + |y.1 - x.1|)) := by
  obtain ⟨C, hC, h⟩ := i2Psi2Diff_triple_global ha hb hc hδ hη hc2 hbδ hsum haη
  exact ⟨C, hC, fun {K Q B} hK x y y' g h' {D} hD0 hD => h hK x y y' g h' hD0 hD.pair⟩

/-- **The product monomial, globally.** -/
theorem i2Psi2Diff_quad_global {a b c e δ η₁ η₂ : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c)
    (he : 0 < e) (hδ : 0 < δ) (hη₁ : 0 < η₁) (hη₂ : 0 < η₂) (haa : 3 + a < 5)
    (hbδ : b + δ < 5) (hcc : 3 + c < 5) (heδ : e + δ < 5) (hs₁ : 3 + a + b + δ = 5 + η₁)
    (hs₂ : 3 + c + e + δ = 5 + η₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ} {B : ℝ}, SingularKernelData K Q B →
      ∀ (x y y' : SpaceTime) {D : ℝ}, 0 ≤ D → I2Psi2DiffSlab x y y' D →
      0 < torusParabolicSize (y - y') → 0 < torusParabolicSize (x - y) →
      0 < torusParabolicSize (x - y') →
      I2Psi2DiffIntBd (i2Psi2Quad K x y y' a b c e)
        (C * B ^ 2 * D ^ δ * D ^ δ *
          ((torusParabolicSize (y - y') ^ (-η₁) + torusParabolicSize (x - y') ^ (-η₁)) *
            (torusParabolicSize (y' - y) ^ (-η₂) + torusParabolicSize (x - y) ^ (-η₂)))) := by
  obtain ⟨C1, hC1, h1⟩ := i2Psi2Diff_single_global ha hb hδ hη₁ haa hbδ hs₁
  obtain ⟨C2, hC2, h2⟩ := i2Psi2Diff_single_global hc he hδ hη₂ hcc heδ hs₂
  refine ⟨C1 * C2, by positivity, ?_⟩
  intro K Q B hK x y y' D hD0 hD hyy hxy hxy'
  have hyy' : 0 < torusParabolicSize (y' - y) := torusParabolicSize_sub_pos_symm hyy
  obtain ⟨i1, b1⟩ := h1 hK x y y' hD0 hyy hxy' hD.left
  obtain ⟨i2, b2⟩ := h2 hK x y' y hD0 hyy' hxy hD.right
  have := I2Psi2DiffIntBd.of_product i1 i2
    (fun w => mul_nonneg (abs_nonneg _) (mul_nonneg (singularPow_nonneg _ _ _)
      (singularPow_nonneg _ _ _)))
    (fun w => mul_nonneg (abs_nonneg _) (mul_nonneg (singularPow_nonneg _ _ _)
      (singularPow_nonneg _ _ _))) b1 b2
  refine (this.mono_right (le_of_eq ?_))
  ring

end RegularityStructures

end
