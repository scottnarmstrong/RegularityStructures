/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.ChaosLimitMomentsTruncationL2

/-!
# Passing the moment inequality to the limit in the time truncation

Let `F` be a jointly measurable random field with `E F(y)² ≤ M`, satisfying the slab Cauchy-Schwarz
bound `SlabSecondMoment`, and let `g` be measurable and integrable on `ℝ × T³`. If the truncated
tested fields `Xₙ = ∫ truncₙ(g) F` have integrable `2p`-th moments with
`E Xₙ^(2p) ≤ A (E Xₙ²)^p`, then so does `X = ∫ g F`
(`integrable_and_integral_pow_two_mul_le_of_timeTruncation`): `Xₙ → X` almost surely and
`E Xₙ² → E X²` (`L²` convergence from `integrable_and_integral_sq_sub_le`), so Fatou's lemma applies.
-/

public section

open MeasureTheory Filter Topology

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F : Ω → SpaceTime → ℝ}
  {g : SpaceTime → ℝ}

/-- **Moment inequality for the full tested field from the truncated ones.** -/
theorem integrable_and_integral_pow_two_mul_le_of_timeTruncation [IsProbabilityMeasure P]
    {c M A : ℝ} {p : ℕ} (hFm : Measurable fun q : Ω × SpaceTime => F q.1 q.2)
    (hgm : Measurable g) (hgi : Integrable g)
    (hF2 : ∀ y, Integrable (fun ω => F ω y ^ 2) P ∧ ∫ ω, F ω y ^ 2 ∂P ≤ M)
    (hCS : SlabSecondMoment P F c M)
    (hmom : ∀ n : ℕ, Integrable (fun ω => (∫ y, timeTruncation c n g y * F ω y) ^ (2 * p)) P ∧
      ∫ ω, (∫ y, timeTruncation c n g y * F ω y) ^ (2 * p) ∂P ≤
        A * (∫ ω, (∫ y, timeTruncation c n g y * F ω y) ^ 2 ∂P) ^ p) :
    Integrable (fun ω => (∫ y, g y * F ω y) ^ (2 * p)) P ∧
      ∫ ω, (∫ y, g y * F ω y) ^ (2 * p) ∂P ≤ A * (∫ ω, (∫ y, g y * F ω y) ^ 2 ∂P) ^ p := by
  have hM0 : 0 ≤ M := (integral_nonneg fun ω => sq_nonneg _).trans (hF2 0).2
  set X : ℕ → Ω → ℝ := fun k ω => ∫ y, timeTruncation c k g y * F ω y with hX
  set Xg : Ω → ℝ := fun ω => ∫ y, g y * F ω y with hXg
  have hXm : ∀ k, Measurable (X k) := fun k =>
    measurable_integral_mul_field hFm (measurable_timeTruncation hgm c k)
  have hXgm : Measurable Xg := measurable_integral_mul_field hFm hgm
  have hae := ae_tendsto_integral_timeTruncation_mul c hFm hgm hgi hF2
  have hL2 := fun n => integrable_and_integral_sq_sub_le hFm hgm hgi hF2 hCS n
  -- `Xₙ` is square integrable
  have hXn2 : ∀ n : ℕ, MemLp (X n) 2 P := fun n =>
    (memLp_two_iff_integrable_sq (hXm n).aestronglyMeasurable).2
      (hCS n _ (measurable_timeTruncation hgm c n) (integrable_timeTruncation hgi c n)
        (fun y hy => abs_le_of_timeTruncation_ne_zero hy)).1
  -- so is `X`
  have hXg2 : MemLp Xg 2 P := by
    have h0 : MemLp (fun ω => X 0 ω - Xg ω) 2 P :=
      (memLp_two_iff_integrable_sq ((hXm 0).sub hXgm).aestronglyMeasurable).2 (hL2 0).1
    have e : Xg = fun ω => X 0 ω - (X 0 ω - Xg ω) := by funext ω; ring
    rw [e]
    exact (hXn2 0).sub h0
  -- convergence of the second moments
  have hτ := tendsto_integral_abs_sub_timeTruncation (c := c) hgm hgi
  have hsq : Tendsto (fun n : ℕ => ∫ ω, X n ω ^ 2 ∂P) atTop (𝓝 (∫ ω, Xg ω ^ 2 ∂P)) :=
    tendsto_integral_sq_of_tendsto_integral_sq_sub hXn2 hXg2
      (squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _) (fun n => (hL2 n).2)
        (by simpa using hτ.mul (hτ.mul_const M)))
  refine integrable_and_integral_le_of_ae_tendsto (μ := P)
    (G := fun k ω => X k ω ^ (2 * p)) (G' := fun ω => Xg ω ^ (2 * p))
    (b := fun k => A * (∫ ω, X k ω ^ 2 ∂P) ^ p) (B := A * (∫ ω, Xg ω ^ 2 ∂P) ^ p)
    (fun k => (hXm k).pow_const _) (fun k ω => by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)
    (fun k => (hmom k).1) ?_ (fun k => (hmom k).2) ((hsq.pow p).const_mul A)
  filter_upwards [hae] with ω hω
  exact hω.pow (2 * p)

end RegularityStructures

end
