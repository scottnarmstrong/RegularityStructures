/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.RandomFieldFubini
public import RegularityStructures.Torus.Basic

/-!
# Fubini for the product of two tested random fields

For integrable kernels `g, ḡ`, jointly measurable fields `Y, Ȳ` and random variables `a, b`,
if `Y(w) a Ȳ(w̄) b` is integrable with `E|Y(w) a Ȳ(w̄) b| ≤ M` uniformly, then
`E[(∫ g Y) a ((∫ ḡ Ȳ) b)] = ∫∫ g(w) ḡ(w̄) E[Y(w) a Ȳ(w̄) b] dw dw̄`.
-/

public section

open MeasureTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
  {Y Y' : Ω → SpaceTime → ℝ} {a b : Ω → ℝ} {g g' : SpaceTime → ℝ}

/-- Integrability of the product integrand on `Ω × (SpaceTime × SpaceTime)`. -/
theorem integrable_testedPair_integrand
    (hY : Measurable fun q : Ω × SpaceTime => Y q.1 q.2)
    (hY' : Measurable fun q : Ω × SpaceTime => Y' q.1 q.2)
    (ha : Measurable a) (hb : Measurable b) (hg : Integrable g) (hg' : Integrable g')
    (hi : ∀ q : SpaceTime × SpaceTime,
      Integrable (fun ω => Y ω q.1 * a ω * (Y' ω q.2 * b ω)) P) {M : ℝ}
    (hM : ∀ q : SpaceTime × SpaceTime, ∫ ω, |Y ω q.1 * a ω * (Y' ω q.2 * b ω)| ∂P ≤ M) :
    Integrable (Function.uncurry fun (ω : Ω) (q : SpaceTime × SpaceTime) =>
      (g q.1 * g' q.2) * (Y ω q.1 * a ω * (Y' ω q.2 * b ω)))
      (P.prod (volume.prod volume)) := by
  have hm : Measurable (Function.uncurry fun (ω : Ω) (q : SpaceTime × SpaceTime) =>
      Y ω q.1 * a ω * (Y' ω q.2 * b ω)) :=
    ((hY.comp (measurable_fst.prodMk measurable_snd.fst)).mul (ha.comp measurable_fst)).mul
      ((hY'.comp (measurable_fst.prodMk measurable_snd.snd)).mul (hb.comp measurable_fst))
  exact integrable_uncurry_mul_of_bound (K := fun q : SpaceTime × SpaceTime => g q.1 * g' q.2)
    (hg.mul_prod hg') (Y := fun ω q => Y ω q.1 * a ω * (Y' ω q.2 * b ω))
    hm.aestronglyMeasurable hi hM

/-- **Second-order Fubini for two tested fields.** -/
theorem integral_testedPair_eq
    (hY : Measurable fun q : Ω × SpaceTime => Y q.1 q.2)
    (hY' : Measurable fun q : Ω × SpaceTime => Y' q.1 q.2)
    (ha : Measurable a) (hb : Measurable b) (hg : Integrable g) (hg' : Integrable g')
    (hi : ∀ q : SpaceTime × SpaceTime,
      Integrable (fun ω => Y ω q.1 * a ω * (Y' ω q.2 * b ω)) P) {M : ℝ}
    (hM : ∀ q : SpaceTime × SpaceTime, ∫ ω, |Y ω q.1 * a ω * (Y' ω q.2 * b ω)| ∂P ≤ M) :
    ∫ ω, (∫ w, g w * Y ω w) * a ω * ((∫ w, g' w * Y' ω w) * b ω) ∂P =
      ∫ q : SpaceTime × SpaceTime, g q.1 * g' q.2 *
        ∫ ω, Y ω q.1 * a ω * (Y' ω q.2 * b ω) ∂P := by
  have hF := integrable_testedPair_integrand hY hY' ha hb hg hg' hi hM
  have hsq : ∀ ω, (∫ w, g w * Y ω w) * a ω * ((∫ w, g' w * Y' ω w) * b ω) =
      ∫ q : SpaceTime × SpaceTime, (g q.1 * g' q.2) * (Y ω q.1 * a ω * (Y' ω q.2 * b ω)) := by
    intro ω
    have h := integral_prod_mul (μ := (volume : Measure SpaceTime)) (ν := volume)
      (fun w => g w * Y ω w) (fun w => g' w * Y' ω w)
    have h2 : ∫ q : SpaceTime × SpaceTime, (g q.1 * g' q.2) * (Y ω q.1 * a ω * (Y' ω q.2 * b ω)) =
        (∫ q : SpaceTime × SpaceTime, (g q.1 * Y ω q.1) * (g' q.2 * Y' ω q.2)) *
          (a ω * b ω) := by
      rw [← integral_mul_const]
      exact integral_congr_ae (Filter.Eventually.of_forall fun q => by simp only; ring)
    rw [h2, show (∫ q : SpaceTime × SpaceTime, g q.1 * Y ω q.1 * (g' q.2 * Y' ω q.2)) =
      (∫ x, g x * Y ω x) * ∫ y, g' y * Y' ω y from h]
    ring
  calc ∫ ω, (∫ w, g w * Y ω w) * a ω * ((∫ w, g' w * Y' ω w) * b ω) ∂P
      = ∫ ω, (∫ q : SpaceTime × SpaceTime,
          (g q.1 * g' q.2) * (Y ω q.1 * a ω * (Y' ω q.2 * b ω))) ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall hsq)
    _ = ∫ q : SpaceTime × SpaceTime, ∫ ω,
          (g q.1 * g' q.2) * (Y ω q.1 * a ω * (Y' ω q.2 * b ω)) ∂P :=
        integral_integral_swap hF
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
        simp only
        rw [integral_const_mul]

/-- The integrand `g(w) ḡ(w̄) E[Y(w) a Ȳ(w̄) b]` is integrable on `SpaceTime × SpaceTime`. -/
theorem integrable_testedPair_expectation
    (hY : Measurable fun q : Ω × SpaceTime => Y q.1 q.2)
    (hY' : Measurable fun q : Ω × SpaceTime => Y' q.1 q.2)
    (ha : Measurable a) (hb : Measurable b) (hg : Integrable g) (hg' : Integrable g')
    (hi : ∀ q : SpaceTime × SpaceTime,
      Integrable (fun ω => Y ω q.1 * a ω * (Y' ω q.2 * b ω)) P) {M : ℝ}
    (hM : ∀ q : SpaceTime × SpaceTime, ∫ ω, |Y ω q.1 * a ω * (Y' ω q.2 * b ω)| ∂P ≤ M) :
    Integrable (fun q : SpaceTime × SpaceTime => g q.1 * g' q.2 *
      ∫ ω, Y ω q.1 * a ω * (Y' ω q.2 * b ω) ∂P) (volume.prod volume) := by
  have hF := (integrable_testedPair_integrand hY hY' ha hb hg hg' hi hM).swap
  refine hF.integral_prod_left.congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [Function.comp_apply, Function.uncurry_apply_pair, Prod.swap_prod_mk]
  rw [integral_const_mul]

end RegularityStructures

end
