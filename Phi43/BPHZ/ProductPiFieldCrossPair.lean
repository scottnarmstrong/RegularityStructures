/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductPiFieldCrossMoment

/-!
# Pair integrability of the cross-mollifier difference `I₂Ψ_{ρ,ε} - I₂Ψ_{ρ',ε'}`

For fixed scales the product `Δ(y) Δ(ȳ)` of the difference field is integrable on `Ω` with first
moment bounded uniformly in `y, ȳ`, and `Δ(y) ∈ L²`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}

/-- **Pair integrability and a uniform first-moment bound for the difference field.** -/
theorem productISqPsiField_sub_pair_integrable_bound_cross (N : ℕ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ')
    (hε : 0 < ε)
    (hε' : 0 < ε') (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ' ε' ξ') (x : SpaceTime) :
    ∃ M : ℝ, ∀ y y' : SpaceTime,
      Integrable (fun ω => (productISqPsiField N ρ ε ξ x ω y - productISqPsiField N ρ' ε' ξ' x ω y) *
        (productISqPsiField N ρ ε ξ x ω y' - productISqPsiField N ρ' ε' ξ' x ω y')) P ∧
      ∫ ω, |(productISqPsiField N ρ ε ξ x ω y - productISqPsiField N ρ' ε' ξ' x ω y) *
        (productISqPsiField N ρ ε ξ x ω y' - productISqPsiField N ρ' ε' ξ' x ω y')| ∂P ≤ M := by
  refine ⟨(10 * (max (hairerWickConstant N ρ ε) (hairerWickConstant N ρ ε)) ^ 3 *
      ((2 * ∫ w, |hairerKernelTorus N w|) * (2 * ∫ w, |hairerKernelTorus N w|))) +
    (10 * (max (hairerWickConstant N ρ ε) (hairerWickConstant N ρ' ε')) ^ 3 *
      ((2 * ∫ w, |hairerKernelTorus N w|) * (2 * ∫ w, |hairerKernelTorus N w|))) +
    (10 * (max (hairerWickConstant N ρ' ε') (hairerWickConstant N ρ ε)) ^ 3 *
      ((2 * ∫ w, |hairerKernelTorus N w|) * (2 * ∫ w, |hairerKernelTorus N w|))) +
    (10 * (max (hairerWickConstant N ρ' ε') (hairerWickConstant N ρ' ε')) ^ 3 *
      ((2 * ∫ w, |hairerKernelTorus N w|) * (2 * ∫ w, |hairerKernelTorus N w|))), ?_⟩
  intro y y'
  obtain ⟨p11, b11⟩ := productISqPsiField_two_scale_pair_integrable_cross N hρ hρ hε hε hW hξ hξ x y y'
  obtain ⟨p12, b12⟩ := productISqPsiField_two_scale_pair_integrable_cross N hρ hρ' hε hε' hW hξ hξ' x y y'
  obtain ⟨p21, b21⟩ := productISqPsiField_two_scale_pair_integrable_cross N hρ' hρ hε' hε hW hξ' hξ x y y'
  obtain ⟨p22, b22⟩ := productISqPsiField_two_scale_pair_integrable_cross N hρ' hρ' hε' hε' hW hξ' hξ' x y y'
  have h3 : Integrable (fun ω => productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ ε ξ x ω y' -
      productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ' ε' ξ' x ω y') P := p11.sub p12
  have h5 : Integrable (fun ω => productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ ε ξ x ω y' -
      productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ' ε' ξ' x ω y' -
      productISqPsiField N ρ' ε' ξ' x ω y * productISqPsiField N ρ ε ξ x ω y') P := h3.sub p21
  have hI : Integrable (fun ω => productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ ε ξ x ω y' -
      productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ' ε' ξ' x ω y' -
      productISqPsiField N ρ' ε' ξ' x ω y * productISqPsiField N ρ ε ξ x ω y' +
      productISqPsiField N ρ' ε' ξ' x ω y * productISqPsiField N ρ' ε' ξ' x ω y') P := h5.add p22
  have e : ∀ ω, (productISqPsiField N ρ ε ξ x ω y - productISqPsiField N ρ' ε' ξ' x ω y) *
      (productISqPsiField N ρ ε ξ x ω y' - productISqPsiField N ρ' ε' ξ' x ω y') =
      productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ ε ξ x ω y' -
      productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ' ε' ξ' x ω y' -
      productISqPsiField N ρ' ε' ξ' x ω y * productISqPsiField N ρ ε ξ x ω y' +
      productISqPsiField N ρ' ε' ξ' x ω y * productISqPsiField N ρ' ε' ξ' x ω y' := fun ω => by ring
  refine ⟨hI.congr (Filter.Eventually.of_forall fun ω => (e ω).symm), ?_⟩
  have hs : Integrable (fun ω => |productISqPsiField N ρ ε ξ x ω y *
        productISqPsiField N ρ ε ξ x ω y'| +
      |productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ' ε' ξ' x ω y'| +
      |productISqPsiField N ρ' ε' ξ' x ω y * productISqPsiField N ρ ε ξ x ω y'| +
      |productISqPsiField N ρ' ε' ξ' x ω y * productISqPsiField N ρ' ε' ξ' x ω y'|) P :=
    (((p11.abs.add p12.abs).add p21.abs).add p22.abs)
  calc _ ≤ ∫ ω, (|productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ ε ξ x ω y'| +
      |productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ' ε' ξ' x ω y'| +
      |productISqPsiField N ρ' ε' ξ' x ω y * productISqPsiField N ρ ε ξ x ω y'| +
      |productISqPsiField N ρ' ε' ξ' x ω y * productISqPsiField N ρ' ε' ξ' x ω y'|) ∂P := by
        refine integral_mono (hI.congr (Filter.Eventually.of_forall fun ω => (e ω).symm)).abs hs
          fun ω => ?_
        rw [e ω]
        have a1 := abs_add_le (productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ ε ξ x ω y' -
          productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ' ε' ξ' x ω y' -
          productISqPsiField N ρ' ε' ξ' x ω y * productISqPsiField N ρ ε ξ x ω y')
          (productISqPsiField N ρ' ε' ξ' x ω y * productISqPsiField N ρ' ε' ξ' x ω y')
        have a2 := abs_sub (productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ ε ξ x ω y' -
          productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ' ε' ξ' x ω y')
          (productISqPsiField N ρ' ε' ξ' x ω y * productISqPsiField N ρ ε ξ x ω y')
        have a3 := abs_sub (productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ ε ξ x ω y')
          (productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ' ε' ξ' x ω y')
        linarith
    _ = (∫ ω, |productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ ε ξ x ω y'| ∂P) +
        (∫ ω, |productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ' ε' ξ' x ω y'| ∂P) +
        (∫ ω, |productISqPsiField N ρ' ε' ξ' x ω y * productISqPsiField N ρ ε ξ x ω y'| ∂P) +
        ∫ ω, |productISqPsiField N ρ' ε' ξ' x ω y * productISqPsiField N ρ' ε' ξ' x ω y'| ∂P := by
        have k2 : Integrable (fun ω => |productISqPsiField N ρ ε ξ x ω y *
              productISqPsiField N ρ ε ξ x ω y'| +
            |productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ' ε' ξ' x ω y'|) P :=
          p11.abs.add p12.abs
        have k3 : Integrable (fun ω => |productISqPsiField N ρ ε ξ x ω y *
              productISqPsiField N ρ ε ξ x ω y'| +
            |productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ' ε' ξ' x ω y'| +
            |productISqPsiField N ρ' ε' ξ' x ω y * productISqPsiField N ρ ε ξ x ω y'|) P :=
          k2.add p21.abs
        rw [integral_add k3 p22.abs, integral_add k2 p21.abs, integral_add p11.abs p12.abs]
    _ ≤ _ := by linarith

/-- The difference field is square integrable. -/
theorem productISqPsiField_sub_memLp_cross (N : ℕ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ')
    (hε : 0 < ε) (hε' : 0 < ε')
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ' ε' ξ') (x y : SpaceTime) :
    MemLp (fun ω => productISqPsiField N ρ ε ξ x ω y - productISqPsiField N ρ' ε' ξ' x ω y) 2 P := by
  have hm : Measurable (fun ω => productISqPsiField N ρ ε ξ x ω y - productISqPsiField N ρ' ε' ξ' x ω y) :=
    ((Measurable.comp (g := fun q : Ω × SpaceTime => productISqPsiField N ρ ε ξ x q.1 q.2)
      (f := fun ω : Ω => (ω, y)) (measurable_productISqPsiField_uncurry N hξ x)
      (measurable_id.prodMk measurable_const)).sub
      (Measurable.comp (g := fun q : Ω × SpaceTime => productISqPsiField N ρ' ε' ξ' x q.1 q.2)
      (f := fun ω : Ω => (ω, y)) (measurable_productISqPsiField_uncurry N hξ' x)
      (measurable_id.prodMk measurable_const)))
  obtain ⟨M, hM⟩ := productISqPsiField_sub_pair_integrable_bound_cross N hρ hρ' hε hε' hW hξ hξ' x
  have hi := (hM y y).1
  have hsq : Integrable (fun ω => (productISqPsiField N ρ ε ξ x ω y -
      productISqPsiField N ρ' ε' ξ' x ω y) ^ 2) P :=
    hi.congr (Filter.Eventually.of_forall fun ω => by simp only [sq])
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 hsq

end RegularityStructures.Phi43

end
