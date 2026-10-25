/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.RandomFieldFubini
public import RegularityStructures.Probability.SpaceTimeMeasure

/-!
# A double Fubini identity for products of two kernel integrals

Let `Y₁, Y₃` be jointly measurable random fields and `A, B` random variables, and let
`g₁, g₃ ∈ L¹(SpaceTime)`.  If `E|Y₁(w) A Y₃(w') B| ≤ M` uniformly in `(w, w')` and each
`Y₁(w) A Y₃(w') B` is integrable, then
`E[(∫ g₁ Y₁) A ((∫ g₃ Y₃) B)] = ∫∫ g₁(w) g₃(w') E[Y₁(w) A Y₃(w') B] dw dw'`
and the integrand on the right is integrable on `SpaceTime × SpaceTime`.  This is the Fubini step
in the covariance of the tree `I(Ψ²) Ψ²` [Hai14, (10.39)-(10.42)].
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Double Fubini identity** for `E[(∫ g₁ Y₁) A ((∫ g₃ Y₃) B)]`. -/
theorem integral_integral_mul_mul_eq_integral_prod [IsProbabilityMeasure P]
    {Y₁ Y₃ : Ω → SpaceTime → ℝ} {A B : Ω → ℝ}
    (hY₁ : Measurable fun q : Ω × SpaceTime => Y₁ q.1 q.2)
    (hY₃ : Measurable fun q : Ω × SpaceTime => Y₃ q.1 q.2) (hA : Measurable A)
    (hB : Measurable B) {g₁ g₃ : SpaceTime → ℝ} (hg₁ : Integrable g₁) (hg₃ : Integrable g₃)
    {M : ℝ} (hi : ∀ w w', Integrable (fun ω => Y₁ ω w * A ω * Y₃ ω w' * B ω) P)
    (hM : ∀ w w', ∫ ω, |Y₁ ω w * A ω * Y₃ ω w' * B ω| ∂P ≤ M) :
    Integrable (fun ω => (∫ w, g₁ w * Y₁ ω w) * A ω * ((∫ w, g₃ w * Y₃ ω w) * B ω)) P ∧
    Integrable (fun q : SpaceTime × SpaceTime =>
        g₁ q.1 * g₃ q.2 * ∫ ω, Y₁ ω q.1 * A ω * Y₃ ω q.2 * B ω ∂P) ∧
      ∫ ω, (∫ w, g₁ w * Y₁ ω w) * A ω * ((∫ w, g₃ w * Y₃ ω w) * B ω) ∂P =
        ∫ q : SpaceTime × SpaceTime,
          g₁ q.1 * g₃ q.2 * ∫ ω, Y₁ ω q.1 * A ω * Y₃ ω q.2 * B ω ∂P := by
  have hZ : Measurable (fun q : Ω × (SpaceTime × SpaceTime) =>
      Y₁ q.1 q.2.1 * A q.1 * Y₃ q.1 q.2.2 * B q.1) :=
    (((hY₁.comp (measurable_fst.prodMk measurable_snd.fst)).mul (hA.comp measurable_fst)).mul
      (hY₃.comp (measurable_fst.prodMk measurable_snd.snd))).mul (hB.comp measurable_fst)
  have hG := integrable_uncurry_mul_of_bound (P := P)
    (μ := (volume.prod volume : Measure (SpaceTime × SpaceTime)))
    (K := fun q : SpaceTime × SpaceTime => g₁ q.1 * g₃ q.2) (hg₁.mul_prod hg₃)
    (Y := fun ω q => Y₁ ω q.1 * A ω * Y₃ ω q.2 * B ω) hZ.aestronglyMeasurable
    (fun q => hi q.1 q.2) (fun q => hM q.1 q.2)
  have hsq : ∀ ω, (∫ w, g₁ w * Y₁ ω w) * A ω * ((∫ w, g₃ w * Y₃ ω w) * B ω) =
      ∫ q : SpaceTime × SpaceTime,
        (g₁ q.1 * g₃ q.2) * (Y₁ ω q.1 * A ω * Y₃ ω q.2 * B ω) := by
    intro ω
    have h := integral_prod_mul (μ := (volume : Measure SpaceTime)) (ν := volume)
      (fun w => g₁ w * Y₁ ω w) (fun w => g₃ w * Y₃ ω w)
    have h2 : (∫ w, g₁ w * Y₁ ω w) * A ω * ((∫ w, g₃ w * Y₃ ω w) * B ω) =
        ((∫ w, g₁ w * Y₁ ω w) * (∫ w, g₃ w * Y₃ ω w)) * (A ω * B ω) := by ring
    rw [h2, ← h, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only
    ring
  have hrhs : ∀ q : SpaceTime × SpaceTime,
      ∫ ω, (g₁ q.1 * g₃ q.2) * (Y₁ ω q.1 * A ω * Y₃ ω q.2 * B ω) ∂P =
        g₁ q.1 * g₃ q.2 * ∫ ω, Y₁ ω q.1 * A ω * Y₃ ω q.2 * B ω ∂P :=
    fun q => integral_const_mul _ _
  refine ⟨?_, ?_, ?_⟩
  · refine (hG.integral_prod_left).congr (Filter.Eventually.of_forall fun ω => ?_)
    exact (hsq ω).symm
  · have := hG.integral_prod_right
    refine this.congr (Filter.Eventually.of_forall fun q => ?_)
    exact hrhs q
  · calc ∫ ω, (∫ w, g₁ w * Y₁ ω w) * A ω * ((∫ w, g₃ w * Y₃ ω w) * B ω) ∂P
        = ∫ ω, (∫ q : SpaceTime × SpaceTime,
          (g₁ q.1 * g₃ q.2) * (Y₁ ω q.1 * A ω * Y₃ ω q.2 * B ω)) ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall hsq)
      _ = ∫ q : SpaceTime × SpaceTime, (∫ ω,
          (g₁ q.1 * g₃ q.2) * (Y₁ ω q.1 * A ω * Y₃ ω q.2 * B ω) ∂P) :=
          integral_integral_swap hG
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall hrhs)

end RegularityStructures.Phi43

end
