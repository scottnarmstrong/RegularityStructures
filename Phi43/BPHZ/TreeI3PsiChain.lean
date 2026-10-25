/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiSigma
public import Phi43.BPHZ.TreeI3PsiTwoLevel

/-!
# The diagrams with a `Q²`-link between the two integration variables

Let `δK(z, w) = K(z - w) - K(-w)`.  For `(u, u') = (z, z')` (the chaos-two pairing
`Q(w - z) Q(w - w̄)² Q(w̄ - z̄)`) and `(u, u') = (z', z)` (the secondary pairing
`Q(w - w̄)² Q(w - z̄) Q(w̄ - z)`), the double integral of
`δK(z, w) δK(z', w̄) Q(w - u) Q(w - w̄)² Q(w̄ - u')` is absolutely integrable and bounded by
`s(z - z')^(-δ) + s(z)^(-δ) + s(z')^(-δ)`.

Source: [Hai14] = arXiv:1303.5113v4, p. 167--168 (secondary pairings: source gap, bounded by the
same lemmas).
-/

public section

open MeasureTheory Set

namespace RegularityStructures

theorem SingularIntLe.congr_fun {f g : SpaceTime → ℝ} {X : ℝ} (h : ∀ w, f w = g w)
    (hf : SingularIntLe f X) : SingularIntLe g X := by
  have : f = g := funext h
  rwa [this] at hf

/-- The inner integral over `v` of the chain diagram. -/
theorem singularIntLe_inner {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ Cin : ℝ, 0 ≤ Cin ∧ ∀ c₁ c₂ c₃ w : SpaceTime, 0 < torusParabolicSize (c₁ - w) →
      0 < torusParabolicSize (c₂ - w) → 0 < torusParabolicSize (c₃ - w) →
      SingularIntLe (fun v => (singularPow 4 c₁ v + singularPow 4 c₂ v +
          2 * singularPow 4 c₃ v) * singularPow (2 + δ) w v)
        (Cin * (singularPow (1 + δ) c₁ w + singularPow (1 + δ) c₂ w +
          2 * singularPow (1 + δ) c₃ w)) := by
  obtain ⟨C, hC, h⟩ := singularIntLe_mul_two (a := 4) (b := 2 + δ) (η := 1 + δ)
    (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) (by ring)
  refine ⟨C, hC, fun c₁ c₂ c₃ w p₁ p₂ p₃ => ?_⟩
  have h1 := h c₁ w p₁
  have h2 := h c₂ w p₂
  have h3 := h c₃ w p₃
  have := (h1.add h2).add (h3.const_mul (c := (2 : ℝ)) (by norm_num))
  refine (this.congr_fun (fun v => by ring)).mono_right (le_of_eq ?_)
  simp only [singularPow]
  ring

end RegularityStructures

end
