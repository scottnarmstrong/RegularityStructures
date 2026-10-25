/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiLeaves
public import Phi43.BPHZ.TreeI3PsiTwoLevel
public import Phi43.BPHZ.TreeI3Psi2DiagramBasic
public import Phi43.BPHZ.TreeI3PsiChain

/-!
# Two-level majorants with a `SingularIntLe` inner integral

If `|F w v| ≤ m w * g w v` with `∫ g w ≤ V w` (for almost every `w`) and `m V` integrable with
integral at most `X`, then `F` is integrable on the product and its iterated integral is at most
`X` in absolute value.  This packages `integrable_prod_of_two_level` in the form in which the
diagram bounds for `I(Ψ³)Ψ²` use it.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- `SingularIntLe` transfers along almost-everywhere equality. -/
theorem SingularIntLe.congr_ae {f g : SpaceTime → ℝ} {X : ℝ}
    (h : ∀ᵐ w : SpaceTime ∂volume, f w = g w) (hf : SingularIntLe f X) :
    SingularIntLe g X :=
  ⟨hf.1.congr h, by rw [← integral_congr_ae h]; exact hf.2⟩

theorem integrable_and_abs_le_of_majorant {F : SpaceTime → SpaceTime → ℝ} {m : SpaceTime → ℝ}
    {g : SpaceTime → SpaceTime → ℝ} {V : SpaceTime → ℝ} {X : ℝ}
    (hF : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume))
    (hm : ∀ w, 0 ≤ m w) (hg : ∀ᵐ w : SpaceTime ∂volume, SingularIntLe (g w) (V w))
    (hH : SingularIntLe (fun w => m w * V w) X)
    (hFG : ∀ᵐ w : SpaceTime ∂volume, ∀ᵐ v : SpaceTime ∂volume, |F w v| ≤ m w * g w v) :
    Integrable (Function.uncurry F) (volume.prod volume) ∧ |∫ w, ∫ v, F w v| ≤ X := by
  obtain ⟨hint, hbd⟩ := integrable_prod_of_two_level (F := F) (G := fun w v => m w * g w v)
    (H := fun w => m w * V w) hF
    (by filter_upwards [hg] with w h using h.1.const_mul (m w))
    (by
      filter_upwards [hg] with w h
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left h.2 (hm w))
    hH.1 hFG
  exact ⟨hint, hbd.trans hH.2⟩

end RegularityStructures

end
