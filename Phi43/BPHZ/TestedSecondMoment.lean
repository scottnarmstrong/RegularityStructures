/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.RandomFieldFubini
public import RegularityStructures.Torus.Basic

/-!
# Second moment of a tested random field (Fubini)

For a jointly measurable random field `F` with square-integrable values and a measurable test
function `f`, if `∫∫ |f(w)| |f(w')| E|F(w) F(w')| dw dw' < ∞` then
`E |∫ F f|² = ∫∫ f(w) f(w') E[F(w) F(w')] dw dw'`, and in particular
`E |∫ F f|² ≤ ∫∫ |f(w)| |f(w')| |E[F(w) F(w')]|`.
-/

public section

open MeasureTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
  {F : Ω → SpaceTime → ℝ} {f : SpaceTime → ℝ}

/-- The absolute second moment `E|F(w) F(w')|` weighted by `|f(w)| |f(w')|` is the integrability
hypothesis of the second-moment Fubini theorem; under it the product integrand is integrable on
`Ω × (SpaceTime × SpaceTime)`. -/
theorem integrable_testedSecondMoment_integrand
    (hF : Measurable fun q : Ω × SpaceTime => F q.1 q.2) (hf : Measurable f)
    (hL2 : ∀ w, MemLp (fun ω => F ω w) 2 P)
    (hint : Integrable (fun q : SpaceTime × SpaceTime =>
      |f q.1| * |f q.2| * ∫ ω, |F ω q.1 * F ω q.2| ∂P)) :
    Integrable (Function.uncurry fun (ω : Ω) (q : SpaceTime × SpaceTime) =>
      (f q.1 * f q.2) * (F ω q.1 * F ω q.2)) (P.prod (volume.prod volume)) := by
  have hm : Measurable (Function.uncurry fun (ω : Ω) (q : SpaceTime × SpaceTime) =>
      (f q.1 * f q.2) * (F ω q.1 * F ω q.2)) :=
    ((hf.comp (measurable_snd.fst)).mul (hf.comp (measurable_snd.snd))).mul
      ((hF.comp (measurable_fst.prodMk measurable_snd.fst)).mul
        (hF.comp (measurable_fst.prodMk measurable_snd.snd)))
  rw [integrable_prod_iff' hm.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun q => ?_, ?_⟩
  · exact ((hL2 q.1).integrable_mul (hL2 q.2)).const_mul (f q.1 * f q.2)
  · refine hint.congr (Filter.Eventually.of_forall fun q => ?_)
    have e : ∀ ω : Ω, ‖(f q.1 * f q.2) * (F ω q.1 * F ω q.2)‖ =
        (|f q.1| * |f q.2|) * |F ω q.1 * F ω q.2| := fun ω => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    simp only [Function.uncurry_apply_pair]
    simp_rw [e]
    rw [integral_const_mul]

/-- The integrability hypothesis of the second-moment Fubini theorem holds for an integrable test
function `f` when `E|F(w) F(w')| ≤ M` uniformly (for instance `f` bounded with bounded support). -/
theorem integrable_testedSecondMoment_of_bound
    (hF : Measurable fun q : Ω × SpaceTime => F q.1 q.2) (hf : Integrable f) {M : ℝ}
    (hM : ∀ q : SpaceTime × SpaceTime, ∫ ω, |F ω q.1 * F ω q.2| ∂P ≤ M) :
    Integrable (fun q : SpaceTime × SpaceTime =>
      |f q.1| * |f q.2| * ∫ ω, |F ω q.1 * F ω q.2| ∂P) := by
  have hY : Measurable (Function.uncurry fun (ω : Ω) (q : SpaceTime × SpaceTime) =>
      |F ω q.1 * F ω q.2|) :=
    continuous_abs.measurable.comp ((hF.comp (measurable_fst.prodMk measurable_snd.fst)).mul
      (hF.comp (measurable_fst.prodMk measurable_snd.snd)))
  have hmeasI : Measurable (fun q : SpaceTime × SpaceTime => ∫ ω, |F ω q.1 * F ω q.2| ∂P) :=
    hY.stronglyMeasurable.integral_prod_left.measurable
  have hmaj : Integrable (fun q : SpaceTime × SpaceTime => |f q.1| * |f q.2| * M) :=
    (hf.abs.mul_prod hf.abs).mul_const M
  refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun q => ?_)
  · exact (((hf.abs.aestronglyMeasurable.comp_fst).mul
      (hf.abs.aestronglyMeasurable.comp_snd)).mul hmeasI.aestronglyMeasurable)
  · rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (integral_nonneg fun _ => abs_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hM q) (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- **Second moment of a tested random field.**
`E |∫ F f|² = ∫∫ f(w) f(w') E[F(w) F(w')] dw dw'`. -/
theorem integral_abs_integral_mul_sq_eq
    (hF : Measurable fun q : Ω × SpaceTime => F q.1 q.2) (hf : Measurable f)
    (hL2 : ∀ w, MemLp (fun ω => F ω w) 2 P)
    (hint : Integrable (fun q : SpaceTime × SpaceTime =>
      |f q.1| * |f q.2| * ∫ ω, |F ω q.1 * F ω q.2| ∂P)) :
    ∫ ω, |∫ w, F ω w * f w| ^ 2 ∂P =
      ∫ q : SpaceTime × SpaceTime, f q.1 * f q.2 * ∫ ω, F ω q.1 * F ω q.2 ∂P := by
  have hG := integrable_testedSecondMoment_integrand hF hf hL2 hint
  have hsq : ∀ ω, |∫ w, F ω w * f w| ^ 2 =
      ∫ q : SpaceTime × SpaceTime, (f q.1 * f q.2) * (F ω q.1 * F ω q.2) := by
    intro ω
    have := integral_prod_mul (μ := (volume : Measure SpaceTime)) (ν := volume)
      (fun w => F ω w * f w) (fun w => F ω w * f w)
    rw [sq_abs, sq]
    refine this.symm.trans (integral_congr_ae (Filter.Eventually.of_forall fun q => ?_))
    simp only
    ring
  calc ∫ ω, |∫ w, F ω w * f w| ^ 2 ∂P
      = ∫ ω, (∫ q : SpaceTime × SpaceTime, (f q.1 * f q.2) * (F ω q.1 * F ω q.2)) ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall hsq)
    _ = ∫ q : SpaceTime × SpaceTime, (∫ ω, (f q.1 * f q.2) * (F ω q.1 * F ω q.2) ∂P) :=
        integral_integral_swap hG
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
        simp only
        rw [integral_const_mul]

/-- **Second moment of a tested random field, inequality form.**
`E |∫ F f|² ≤ ∫∫ |f(w)| |f(w')| |E[F(w) F(w')]|`. -/
theorem integral_abs_integral_mul_sq_le
    (hF : Measurable fun q : Ω × SpaceTime => F q.1 q.2) (hf : Measurable f)
    (hL2 : ∀ w, MemLp (fun ω => F ω w) 2 P)
    (hint : Integrable (fun q : SpaceTime × SpaceTime =>
      |f q.1| * |f q.2| * ∫ ω, |F ω q.1 * F ω q.2| ∂P)) :
    ∫ ω, |∫ w, F ω w * f w| ^ 2 ∂P ≤
      ∫ q : SpaceTime × SpaceTime, |f q.1| * |f q.2| * |∫ ω, F ω q.1 * F ω q.2 ∂P| := by
  rw [integral_abs_integral_mul_sq_eq hF hf hL2 hint]
  have hpt : ∀ q : SpaceTime × SpaceTime, |f q.1| * |f q.2| * |∫ ω, F ω q.1 * F ω q.2 ∂P| ≤
      |f q.1| * |f q.2| * ∫ ω, |F ω q.1 * F ω q.2| ∂P := fun q =>
    mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := P) fun ω => F ω q.1 * F ω q.2)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hmeasI : Measurable (fun q : SpaceTime × SpaceTime => ∫ ω, F ω q.1 * F ω q.2 ∂P) :=
    ((hF.comp (measurable_fst.prodMk measurable_snd.fst)).mul
      (hF.comp (measurable_fst.prodMk measurable_snd.snd)) :
        Measurable fun p : Ω × (SpaceTime × SpaceTime) => F p.1 p.2.1 * F p.1 p.2.2
      ).stronglyMeasurable.integral_prod_left.measurable
  have hmaj : Integrable (fun q : SpaceTime × SpaceTime =>
      |f q.1| * |f q.2| * |∫ ω, F ω q.1 * F ω q.2 ∂P|) := by
    refine hint.mono' ?_ (Filter.Eventually.of_forall fun q => ?_)
    · exact (((continuous_abs.measurable.comp (hf.comp measurable_fst)).mul
        (continuous_abs.measurable.comp (hf.comp measurable_snd))).mul
        (continuous_abs.measurable.comp hmeasI)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]
      exact hpt q
  calc _ ≤ ∫ q : SpaceTime × SpaceTime, |f q.1 * f q.2 * ∫ ω, F ω q.1 * F ω q.2 ∂P| :=
        le_trans (le_abs_self _) (by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (fun q : SpaceTime × SpaceTime => f q.1 * f q.2 * ∫ ω, F ω q.1 * F ω q.2 ∂P))
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
        simp only [abs_mul]

end RegularityStructures

end
