/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductDiagramGen

/-!
# Domination of a double integrand by three nonnegative integrable majorants

`abs_iterated_le_of_dominated3`: if `|F w v| ≤ H₁ + H₂ + H₃` almost everywhere with `F, Hᵢ`
measurable and `Hᵢ` integrable on `SpaceTime × SpaceTime`, then `F` is integrable and
`|∫∫ F| ≤ ∑ ∫∫ Hᵢ`.  Also the joint measurability of the centred powers.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- `(w, v) ↦ s(w - v)^(-γ)` is measurable. -/
theorem measurable_singularPow_pair (γ : ℝ) :
    Measurable (fun p : SpaceTime × SpaceTime => singularPow γ p.1 p.2) :=
  (Phi43.measurable_torusParabolicSize.comp (measurable_fst.sub measurable_snd)).pow_const _

/-- `(w, v) ↦ s(c - w)^(-γ)` is measurable. -/
theorem measurable_singularPow_fst (γ : ℝ) (c : SpaceTime) :
    Measurable (fun p : SpaceTime × SpaceTime => singularPow γ c p.1) :=
  (measurable_singularPow γ c).comp measurable_fst

/-- `(w, v) ↦ s(c - v)^(-γ)` is measurable. -/
theorem measurable_singularPow_snd (γ : ℝ) (c : SpaceTime) :
    Measurable (fun p : SpaceTime × SpaceTime => singularPow γ c p.2) :=
  (measurable_singularPow γ c).comp measurable_snd

/-- **Domination by three majorants.** -/
theorem abs_iterated_le_of_dominated3 {F H₁ H₂ H₃ : SpaceTime → SpaceTime → ℝ}
    (hF : Measurable (Function.uncurry F)) (h1m : Measurable (Function.uncurry H₁))
    (h2m : Measurable (Function.uncurry H₂)) (h3m : Measurable (Function.uncurry H₃))
    (i1 : Integrable (Function.uncurry H₁) (volume.prod volume))
    (i2 : Integrable (Function.uncurry H₂) (volume.prod volume))
    (i3 : Integrable (Function.uncurry H₃) (volume.prod volume))
    (hd : ∀ᵐ w : SpaceTime ∂volume, ∀ᵐ v : SpaceTime ∂volume,
      |F w v| ≤ H₁ w v + H₂ w v + H₃ w v) :
    Integrable (Function.uncurry F) (volume.prod volume) ∧
      |∫ w, ∫ v, F w v| ≤ (∫ w, ∫ v, H₁ w v) + (∫ w, ∫ v, H₂ w v) + ∫ w, ∫ v, H₃ w v := by
  have hS : MeasurableSet {p : SpaceTime × SpaceTime |
      |Function.uncurry F p| ≤ Function.uncurry H₁ p + Function.uncurry H₂ p +
        Function.uncurry H₃ p} :=
    measurableSet_le (continuous_abs.measurable.comp hF) ((h1m.add h2m).add h3m)
  have hae : ∀ᵐ p : SpaceTime × SpaceTime ∂(volume.prod volume),
      |Function.uncurry F p| ≤ Function.uncurry H₁ p + Function.uncurry H₂ p +
        Function.uncurry H₃ p := by
    have := (Measure.ae_prod_mem_iff_ae_ae_mem hS).2 hd
    exact this
  have hsum : Integrable (fun p => Function.uncurry H₁ p + Function.uncurry H₂ p +
      Function.uncurry H₃ p) (volume.prod volume) := (i1.add i2).add i3
  have hint : Integrable (Function.uncurry F) (volume.prod volume) := by
    refine Integrable.mono' hsum hF.aestronglyMeasurable ?_
    filter_upwards [hae] with p hp
    rwa [Real.norm_eq_abs]
  refine ⟨hint, ?_⟩
  have key : ∀ G : SpaceTime → SpaceTime → ℝ,
      Integrable (Function.uncurry G) (volume.prod volume) →
        ∫ w, ∫ v, G w v = ∫ p, Function.uncurry G p ∂(volume.prod volume) :=
    fun G hG => (integral_prod _ hG).symm
  rw [key F hint, key H₁ i1, key H₂ i2, key H₃ i3]
  calc |∫ p, Function.uncurry F p ∂(volume.prod volume)|
      = ‖∫ p, Function.uncurry F p ∂(volume.prod volume)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ p, ‖Function.uncurry F p‖ ∂(volume.prod volume) := norm_integral_le_integral_norm _
    _ ≤ ∫ p, (Function.uncurry H₁ p + Function.uncurry H₂ p + Function.uncurry H₃ p)
          ∂(volume.prod volume) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => norm_nonneg _)
          hsum ?_
        filter_upwards [hae] with p hp
        rwa [Real.norm_eq_abs]
    _ = _ := by
        have j12 : Integrable (fun p : SpaceTime × SpaceTime =>
            Function.uncurry H₁ p + Function.uncurry H₂ p) (volume.prod volume) := i1.add i2
        rw [integral_add j12 i3, integral_add i1 i2]

end RegularityStructures

end
