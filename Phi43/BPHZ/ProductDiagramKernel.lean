/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductDiagramChain
public import Phi43.BPHZ.TreeI3PsiPointwise
public import Phi43.BPHZ.SemigroupTestTreesI3PsiChain

/-!
# Gain kernels and propagator kernels for the product diagrams

A *gain kernel* at the point `z` (base point `0`) is a measurable `a` supported in the time slab
`|w₁| ≤ T` with the Hölder-gain bounds
`|a w| ≤ c s(z)^θ (s(z - w)^(-(3+θ)) + s(-w)^(-(3+θ)))` for all `θ ∈ [0, Θ]`.  The recentred kernel
`K(z - ·) - K(-·)` is a gain kernel with `Θ = 1` (`isGainKernel_dK`).  The product diagrams only use
these bounds, so they apply to any inner kernel with the same gains.  A *propagator kernel* is a
measurable `Q` with `|Q x| ≤ B s(x)^(-1)`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- A gain kernel at `z`: slab support and Hölder-gain majorants of every order `θ ∈ [0, Θ]`. -/
def IsGainKernel (Θ c T : ℝ) (z : SpaceTime) (a : SpaceTime → ℝ) : Prop :=
  Measurable a ∧ (∀ w : SpaceTime, T < |w.1| → a w = 0) ∧
    ∀ θ : ℝ, 0 ≤ θ → θ ≤ Θ → ∀ w : SpaceTime, 0 < torusParabolicSize (z - w) →
      0 < torusParabolicSize (0 - w) →
        |a w| ≤ c * torusParabolicSize z ^ θ *
          (singularPow (3 + θ) z w + singularPow (3 + θ) 0 w)

/-- A propagator kernel: measurable with `|Q x| ≤ B s(x)^(-1)`. -/
def IsPropKernel (B : ℝ) (Q : SpaceTime → ℝ) : Prop :=
  Measurable Q ∧ 0 ≤ B ∧
    ∀ x : SpaceTime, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

/-- The gain majorant without a slab indicator. -/
theorem IsGainKernel.ae_abs_le {Θ c T : ℝ} {z : SpaceTime} {a : SpaceTime → ℝ}
    (h : IsGainKernel Θ c T z a) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθΘ : θ ≤ Θ) :
    ∀ᵐ w : SpaceTime ∂volume, |a w| ≤ c * torusParabolicSize z ^ θ *
      spSum (3 + θ) [(1, z), (1, 0)] w := by
  filter_upwards [ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos 0] with w h1 h2
  have := h.2.2 θ hθ0 hθΘ w h1 h2
  simpa [spSum] using this

/-- The gain majorant with the slab indicator. -/
theorem IsGainKernel.ae_abs_le_indicator {Θ c T : ℝ} {z : SpaceTime} {a : SpaceTime → ℝ}
    (h : IsGainKernel Θ c T z a) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθΘ : θ ≤ Θ) :
    ∀ᵐ w : SpaceTime ∂volume, |a w| ≤ c * torusParabolicSize z ^ θ *
      Set.indicator {w : SpaceTime | |w.1 - 0| ≤ T} (spSum (3 + θ) [(1, z), (1, 0)]) w := by
  filter_upwards [h.ae_abs_le hθ0 hθΘ] with w hw
  by_cases hs : |w.1 - 0| ≤ T
  · rw [Set.indicator_of_mem (show w ∈ {w : SpaceTime | |w.1 - 0| ≤ T} from hs)]
    exact hw
  · rw [Set.indicator_of_notMem (show w ∉ {w : SpaceTime | |w.1 - 0| ≤ T} from hs)]
    have : a w = 0 := h.2.1 w (by simpa using not_le.1 hs)
    rw [this]; simp

/-- The recentred kernel `w ↦ K(z - w) - K(-w)` is a gain kernel with `Θ = 1`, `T = |z₁| + 1`. -/
theorem isGainKernel_dK {K : SpaceTime → ℝ} {B : ℝ} (hB : 0 ≤ B) (hKm : Measurable K)
    (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hinc : ∀ u h : SpaceTime, 0 < torusParabolicSize u →
      torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)))
    (z : SpaceTime) :
    IsGainKernel 1 (12 * B) (|z.1| + 1) z (fun w => K (z - w) - K (-w)) := by
  refine ⟨(hKm.comp (measurable_const.sub measurable_id)).sub (hKm.comp measurable_neg),
    fun w hw => dK_eq_zero_of_abs_lt hKs hw, ?_⟩
  intro θ h0 h1 w hz h0w
  have := abs_dK_le_holder hB h0 h1 hK hinc hz h0w
  simpa [mul_assoc] using this

/-- Flip: `|Q (w - c)| ≤ 2 B s(c - w)^(-1)`. -/
theorem IsPropKernel.abs_flip_le {B : ℝ} {Q : SpaceTime → ℝ} (h : IsPropKernel B Q)
    {c w : SpaceTime} (hc : 0 < torusParabolicSize (c - w)) :
    |Q (w - c)| ≤ 2 * B * singularPow 1 c w :=
  abs_Q_flip_le h.2.1 h.2.2 hc

/-- Direct: `|Q (c - w)| ≤ B s(c - w)^(-1)`. -/
theorem IsPropKernel.abs_direct_le {B : ℝ} {Q : SpaceTime → ℝ} (h : IsPropKernel B Q)
    {c w : SpaceTime} (hc : 0 < torusParabolicSize (c - w)) :
    |Q (c - w)| ≤ B * singularPow 1 c w := by
  simpa [singularPow] using h.2.2 _ hc

end RegularityStructures

end
