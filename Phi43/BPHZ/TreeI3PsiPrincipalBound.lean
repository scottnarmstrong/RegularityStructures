/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiPrincipal
public import Phi43.BPHZ.TreeI3PsiChain

/-!
# Bound for the principal pairing

`i3PsiPrincipal_bound`: for `θ ∈ (0, 1)`, the double integral of `i3PsiPrincipal K Q z z'` is
absolutely integrable and bounded by `C s(z')^θ` whenever `s(z), s(z') ≤ 1`.

Source: [Hai14] = arXiv:1303.5113v4, p. 167, last display.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- Inner integral of the principal pairing. -/
theorem singularIntLe_inner_principal {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ Cin : ℝ, 0 ≤ Cin ∧ ∀ c₁ c₂ w : SpaceTime, 0 < torusParabolicSize (c₁ - w) →
      0 < torusParabolicSize (c₂ - w) →
      SingularIntLe (fun v => (singularPow (3 + θ) c₁ v + singularPow (3 + θ) c₂ v) *
          singularPow 3 w v)
        (Cin * (singularPow (1 + θ) c₁ w + singularPow (1 + θ) c₂ w)) := by
  obtain ⟨C, hC, h⟩ := singularIntLe_mul_two (a := 3 + θ) (b := 3) (η := 1 + θ)
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by linarith) (by ring)
  refine ⟨C, hC, fun c₁ c₂ w p₁ p₂ => ?_⟩
  have := (h c₁ w p₁).add (h c₂ w p₂)
  refine (this.congr_fun (fun v => by ring)).mono_right (le_of_eq ?_)
  simp only [singularPow]
  ring

end RegularityStructures

end
