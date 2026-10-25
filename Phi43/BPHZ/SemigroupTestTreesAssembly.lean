/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesCov
public import RegularityStructures.BPHZ.SemigroupTestSecondMoment

/-!
# Assembly of the second moment against a semigroup test profile

`secondMoment_le_of_semigroupDoubleBound`: for a jointly measurable family `Y` of square integrable
random variables and a test profile `g`, a `SemigroupDoubleBound` for the absolute covariance
`|E[Y(u) Y(v)]|` bounds `E|∫ Y g|²`.  The measurability of the covariance in `(u, v)` is supplied by
`aestronglyMeasurable_cov`, and `ae_pos_triple` records the almost everywhere positivity of the
sizes `s(u - x)`, `s(v - x)`, `s(u - v)` used to apply pointwise bounds.
-/

public section

open MeasureTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The covariance of a jointly measurable family is measurable in the two points. -/
theorem aestronglyMeasurable_cov [SFinite P] {Y : Ω → SpaceTime → ℝ}
    (hY : Measurable fun q : Ω × SpaceTime => Y q.1 q.2) :
    AEStronglyMeasurable (fun w : SpaceTime × SpaceTime => ∫ ω, Y ω w.1 * Y ω w.2 ∂P) volume := by
  have hYj : Measurable (fun q : Ω × (SpaceTime × SpaceTime) => Y q.1 q.2.1 * Y q.1 q.2.2) :=
    (hY.comp (measurable_fst.prodMk measurable_snd.fst)).mul
      (hY.comp (measurable_fst.prodMk measurable_snd.snd))
  exact (StronglyMeasurable.integral_prod_left (μ := P)
    (f := fun ω (q : SpaceTime × SpaceTime) => Y ω q.1 * Y ω q.2)
    hYj.stronglyMeasurable).aestronglyMeasurable

/-- **Second moment against a test profile from a double bound of the covariance.** -/
theorem secondMoment_le_of_semigroupDoubleBound [IsProbabilityMeasure P] {Y : Ω → SpaceTime → ℝ}
    (hY : Measurable fun q : Ω × SpaceTime => Y q.1 q.2)
    (hL2 : ∀ u, MemLp (fun ω => Y ω u) 2 P) {M : ℝ}
    (hM : ∀ u, ∫ ω, Y ω u * Y ω u ∂P ≤ M) {x : SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ}
    {g : SpaceTime → ℝ} (h : SemigroupTestProfile x lam B Mom g) {I : ℝ}
    (hbound : SemigroupDoubleBound g (fun u v => |∫ ω, Y ω u * Y ω v ∂P|) I) :
    ∫ ω, |∫ w, Y ω w * g w| ^ 2 ∂P ≤ I :=
  (secondMoment_le_integral_abs_cov hY hL2 hM (fun _ _ => rfl) h.integrable).trans hbound.2

/-- Almost everywhere on triples, the three sizes are positive. -/
theorem ae_pos_triple (x : SpaceTime) :
    ∀ᵐ w : SpaceTime × SpaceTime ∂volume, 0 < torusParabolicSize (w.1 - x) ∧
      0 < torusParabolicSize (w.2 - x) ∧ 0 < torusParabolicSize (w.1 - w.2) := by
  have hm := Phi43.measurable_torusParabolicSize
  set S : Set (SpaceTime × SpaceTime) := {q | 0 < torusParabolicSize (q.1 - x) ∧
      0 < torusParabolicSize (q.2 - x) ∧ 0 < torusParabolicSize (q.1 - q.2)} with hSdef
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const (hm.comp (measurable_fst.sub measurable_const))).inter
      ((measurableSet_lt measurable_const (hm.comp (measurable_snd.sub measurable_const))).inter
        (measurableSet_lt measurable_const (hm.comp (measurable_fst.sub measurable_snd))))
  have hne : ∀ a : SpaceTime, ∀ᵐ z : SpaceTime ∂volume, z ≠ a := fun a =>
    @Measure.ae_ne SpaceTime _ volume (Measure.IsAddHaarMeasure.nullSingletonClass volume) a
  rw [Measure.volume_eq_prod]
  change ∀ᵐ q : SpaceTime × SpaceTime ∂(volume.prod volume), q ∈ S
  rw [Measure.ae_prod_mem_iff_ae_ae_mem hS]
  filter_upwards [hne x] with y hy
  filter_upwards [hne x, hne y] with y' hy' hyy'
  exact ⟨torusParabolicSize_pos_of_ne_zero (sub_ne_zero.2 hy),
    torusParabolicSize_pos_of_ne_zero (sub_ne_zero.2 hy'),
    torusParabolicSize_pos_of_ne_zero (sub_ne_zero.2 (Ne.symm hyy'))⟩

/-- The global majorant factors as `(s_u^n + s_v^n)(s(u - v)^(-e) + s_u^(-a) + s_v^(-a) + 1)`. -/
theorem semigroupTestGlobalMajorant_eq {x u v : SpaceTime} {n e a : ℝ}
    (hu : 0 < torusParabolicSize (u - x)) (hv : 0 < torusParabolicSize (v - x)) :
    semigroupTestGlobalMajorant x n e a u v =
      (torusParabolicSize (u - x) ^ n + torusParabolicSize (v - x) ^ n) *
        (torusParabolicSize (u - v) ^ (-e) + torusParabolicSize (u - x) ^ (-a) +
          torusParabolicSize (v - x) ^ (-a) + 1) := by
  unfold semigroupTestGlobalMajorant
  have e1 : torusParabolicSize (u - x) ^ (n - a) =
      torusParabolicSize (u - x) ^ n * torusParabolicSize (u - x) ^ (-a) := by
    rw [show n - a = n + -a by ring, Real.rpow_add hu]
  have e2 : torusParabolicSize (v - x) ^ (n - a) =
      torusParabolicSize (v - x) ^ n * torusParabolicSize (v - x) ^ (-a) := by
    rw [show n - a = n + -a by ring, Real.rpow_add hv]
  rw [e1, e2, Real.rpow_zero]
  ring

theorem semigroupTestGlobalMajorant_nonneg (x : SpaceTime) (n e a : ℝ) (u v : SpaceTime) :
    0 ≤ semigroupTestGlobalMajorant x n e a u v := by
  unfold semigroupTestGlobalMajorant
  have h1 : ∀ a b : ℝ, 0 ≤ torusParabolicSize (u - x) ^ a * torusParabolicSize (u - v) ^ b :=
    fun a b => mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have h2 : ∀ a b : ℝ, 0 ≤ torusParabolicSize (v - x) ^ a * torusParabolicSize (u - v) ^ b :=
    fun a b => mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have h3 : ∀ a b : ℝ, 0 ≤ torusParabolicSize (u - x) ^ a * torusParabolicSize (v - x) ^ b :=
    fun a b => mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have := h1 n (-e)
  have := h2 n (-e)
  have := h1 (n - a) 0
  have := h2 (n - a) 0
  have := h3 (-a) n
  have := h3 n (-a)
  have := h1 n 0
  have := h2 n 0
  linarith

end RegularityStructures

end
