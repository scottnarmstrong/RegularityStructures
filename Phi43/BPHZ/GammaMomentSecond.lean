/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TestedSecondMoment
public import Phi43.BPHZ.TreePsiBallMass
public import RegularityStructures.BPHZ.TreeI2Psi2DiagramLint
public import Phi43.BPHZ.TreeI2Psi2DiagramCov
import Mathlib.Tactic

/-!
# Second moment of a kernel-tested random field from a lower-integral bound

Let `Y` be a jointly measurable random field with `E[Y(u) Y(v)] = R(u - v)` and let `f` be an
integrable test function.  Suppose `|R(u - v)| ≤ A s(v - u)^(-p)` and that the double integral
`∬ |f(w)| |f(w')| s(w' - w)^(-p)` has lower-integral bound `M` (`i2Psi2LintBound`).  Then
`E |∫ Y f|² ≤ A M`.

This is the second-moment step for the recentred convolutions `v₂ = ∫ δK :Ψ²:` and
`v₃ = ∫ δK :Ψ³:` entering the structure-group entries `Γ_{yx}` ([Hai14, (10.2)]).
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Pair integrability: `E|Y(u) Y(v)| ≤ M₀` when `E Y(u)² ≤ M₀`. -/
theorem gammaMoment_integral_abs_mul_le [IsProbabilityMeasure P] {Y : Ω → SpaceTime → ℝ}
    (hL2 : ∀ u, MemLp (fun ω => Y ω u) 2 P) {M₀ : ℝ}
    (hM₀ : ∀ u, ∫ ω, Y ω u * Y ω u ∂P ≤ M₀) (q : SpaceTime × SpaceTime) :
    ∫ ω, |Y ω q.1 * Y ω q.2| ∂P ≤ M₀ := by
  have hx : Integrable (fun ω => Y ω q.1 * Y ω q.1) P := (hL2 q.1).integrable_mul (hL2 q.1)
  have hy : Integrable (fun ω => Y ω q.2 * Y ω q.2) P := (hL2 q.2).integrable_mul (hL2 q.2)
  have hxy : Integrable (fun ω => Y ω q.1 * Y ω q.2) P := (hL2 q.1).integrable_mul (hL2 q.2)
  calc ∫ ω, |Y ω q.1 * Y ω q.2| ∂P
      ≤ ∫ ω, (Y ω q.1 * Y ω q.1 + Y ω q.2 * Y ω q.2) / 2 ∂P := by
        refine integral_mono hxy.abs ((hx.add hy).div_const 2) fun ω => ?_
        rw [abs_mul]
        nlinarith [sq_nonneg (|Y ω q.1| - |Y ω q.2|), abs_mul_abs_self (Y ω q.1),
          abs_mul_abs_self (Y ω q.2)]
    _ ≤ M₀ := by
        rw [integral_div, integral_add hx hy]
        linarith [hM₀ q.1, hM₀ q.2]

/-- The set of pairs `(w, w')` with `w ≠ w'` has full measure for the product volume. -/
theorem gammaMoment_ae_prod_pos :
    ∀ᵐ q : SpaceTime × SpaceTime ∂(volume.prod volume), 0 < torusParabolicSize (q.2 - q.1) := by
  have hm := Phi43.measurable_torusParabolicSize
  have hS : MeasurableSet {q : SpaceTime × SpaceTime | 0 < torusParabolicSize (q.2 - q.1)} :=
    measurableSet_lt measurable_const (hm.comp (measurable_snd.sub measurable_fst))
  have hne : ∀ a : SpaceTime, ∀ᵐ z : SpaceTime ∂volume, z ≠ a := fun a =>
    @Measure.ae_ne SpaceTime _ volume (Measure.IsAddHaarMeasure.nullSingletonClass volume) a
  change ∀ᵐ q : SpaceTime × SpaceTime ∂(volume.prod volume),
    q ∈ {q : SpaceTime × SpaceTime | 0 < torusParabolicSize (q.2 - q.1)}
  rw [Measure.ae_prod_mem_iff_ae_ae_mem hS]
  refine Filter.Eventually.of_forall fun a => ?_
  filter_upwards [hne a] with z hz
  exact torusParabolicSize_pos_of_ne_zero (sub_ne_zero.2 hz)

/-- **Second moment of a kernel-tested random field from a lower-integral bound.** -/
theorem gammaMoment_second_le_of_lintBound [IsProbabilityMeasure P] {Y : Ω → SpaceTime → ℝ}
    (hY : Measurable fun q : Ω × SpaceTime => Y q.1 q.2)
    (hL2 : ∀ u, MemLp (fun ω => Y ω u) 2 P) {M₀ : ℝ}
    (hM₀ : ∀ u, ∫ ω, Y ω u * Y ω u ∂P ≤ M₀) {R : SpaceTime → ℝ}
    (hcov : ∀ u v, ∫ ω, Y ω u * Y ω v ∂P = R (u - v)) {p A : ℝ} (hA : 0 ≤ A)
    (hRb : ∀ u v : SpaceTime, 0 < torusParabolicSize (v - u) →
      |R (u - v)| ≤ A * torusParabolicSize (v - u) ^ (-p))
    {f : SpaceTime → ℝ} (hf : Measurable f) (hf1 : Integrable f) {M : ℝ} (hM : 0 ≤ M)
    (hlint : i2Psi2LintBound (volume.prod volume) (fun q : SpaceTime × SpaceTime =>
      |f q.1| * |f q.2| * torusParabolicSize (q.2 - q.1) ^ (-p)) M) :
    ∫ ω, |∫ w, Y ω w * f w| ^ 2 ∂P ≤ A * M := by
  have hint := integrable_testedSecondMoment_of_bound hY hf1
    (gammaMoment_integral_abs_mul_le hL2 hM₀)
  have h1 := integral_abs_integral_mul_sq_le hY hf hL2 hint
  simp only [hcov] at h1
  set H : SpaceTime × SpaceTime → ℝ := fun q =>
    |f q.1| * |f q.2| * torusParabolicSize (q.2 - q.1) ^ (-p) with hH
  have hHm : Measurable H :=
    ((continuous_abs.measurable.comp (hf.comp measurable_fst)).mul
      (continuous_abs.measurable.comp (hf.comp measurable_snd))).mul
      ((Phi43.measurable_torusParabolicSize.comp (measurable_snd.sub measurable_fst)).pow_const _)
  have hH0 : ∀ q, 0 ≤ H q := fun q =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  obtain ⟨hHi, hHb⟩ := abs_integral_le_of_i2Psi2LintBound hHm.aestronglyMeasurable
    (hlint.mono (fun q => le_of_eq (abs_of_nonneg (hH0 q))) le_rfl) hM
  have hHb' : ∫ q, H q ∂(volume.prod volume) ≤ M := (le_abs_self _).trans hHb
  refine h1.trans ?_
  calc ∫ q : SpaceTime × SpaceTime, |f q.1| * |f q.2| * |R (q.1 - q.2)|
      ≤ ∫ q : SpaceTime × SpaceTime, A * H q := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun q =>
          mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))
          (hHi.const_mul A) ?_
        filter_upwards [gammaMoment_ae_prod_pos] with q hq
        have hb := hRb q.1 q.2 hq
        calc |f q.1| * |f q.2| * |R (q.1 - q.2)|
            ≤ |f q.1| * |f q.2| * (A * torusParabolicSize (q.2 - q.1) ^ (-p)) :=
              mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          _ = A * H q := by simp only [hH]; ring
    _ = A * ∫ q, H q ∂(volume.prod volume) := integral_const_mul _ _
    _ ≤ A * M := mul_le_mul_of_nonneg_left hHb' hA

end RegularityStructures.Phi43

end
