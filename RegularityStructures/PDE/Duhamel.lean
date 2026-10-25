/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.HeatOp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Duhamel integral

For a continuous path `h : ℝ → C(T³, E)`,
`duhamel h t = ∫₀ᵗ P_{t-s} h(s) ds`, a Bochner integral in the Banach space `C(T³, E)`. This is the
solution operator of the inhomogeneous heat equation `∂_t v = Δv + h`, `v(0) = 0`, in mild form.

## Main results

* `continuous_duhamel`: `t ↦ duhamel h t` is continuous;
* `duhamel_apply`: the integral may be evaluated pointwise in `x`;
* `norm_duhamel_le`: `‖duhamel h t‖ ≤ ∫₀ᵗ ‖h s‖ ds`;
* linearity in `h`, commutation with translations and with linear maps of the values;
* `duhamel_congr`: `duhamel h t` only depends on `h` on `[0, t]`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.PDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Duhamel integral `∫₀ᵗ P_{t-s} h(s) ds` in `C(T³, E)`. -/
def duhamel (h : ℝ → C(Torus3, E)) (t : ℝ) : C(Torus3, E) :=
  ∫ s in (0 : ℝ)..t, heatOp (t - s) (h s)

end RegularityStructures.PDE

end

public section

open MeasureTheory Set Filter Topology

namespace RegularityStructures.PDE

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem continuous_duhamel_integrand {h : ℝ → C(Torus3, E)} (hh : Continuous h) :
    Continuous fun p : ℝ × ℝ => heatOp (p.1 - p.2) (h p.2) :=
  (continuous_fst.sub continuous_snd).heatOp (hh.comp continuous_snd)

theorem intervalIntegrable_duhamel_integrand {h : ℝ → C(Torus3, E)} (hh : Continuous h)
    (t a b : ℝ) : IntervalIntegrable (fun s => heatOp (t - s) (h s)) volume a b :=
  ((continuous_duhamel_integrand hh).comp (Continuous.prodMk continuous_const
    continuous_id)).intervalIntegrable a b

/-- The Duhamel integral of a continuous path is a continuous path. -/
theorem continuous_duhamel {h : ℝ → C(Torus3, E)} (hh : Continuous h) :
    Continuous (duhamel h) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun t s => heatOp (t - s) (h s)) (continuous_duhamel_integrand hh) continuous_id

theorem duhamel_zero (h : ℝ → C(Torus3, E)) : duhamel h 0 = 0 := by
  simp [duhamel]

/-- Pointwise evaluation of the Duhamel integral. -/
theorem duhamel_apply [CompleteSpace E] {h : ℝ → C(Torus3, E)} (hh : Continuous h) (t : ℝ) (x : Torus3) :
    duhamel h t x = ∫ s in (0 : ℝ)..t, heatOp (t - s) (h s) x := by
  have := (ContinuousMap.evalCLM ℝ x : C(Torus3, E) →L[ℝ] E).intervalIntegral_comp_comm
    (intervalIntegrable_duhamel_integrand hh t 0 t)
  rw [duhamel]
  simpa using this.symm

theorem norm_duhamel_le {h : ℝ → C(Torus3, E)} (hh : Continuous h) {t : ℝ} (ht : 0 ≤ t) :
    ‖duhamel h t‖ ≤ ∫ s in (0 : ℝ)..t, ‖h s‖ := by
  refine (intervalIntegral.norm_integral_le_integral_norm ht).trans ?_
  refine intervalIntegral.integral_mono_on ht
    ((intervalIntegrable_duhamel_integrand hh t 0 t).norm) (hh.norm.intervalIntegrable 0 t)
    fun s _ => norm_heatOp_le _ _

theorem norm_duhamel_le_mul {h : ℝ → C(Torus3, E)} (hh : Continuous h) {t M : ℝ} (ht : 0 ≤ t)
    (hM : ∀ s ∈ Icc 0 t, ‖h s‖ ≤ M) : ‖duhamel h t‖ ≤ M * t := by
  refine (norm_duhamel_le hh ht).trans ?_
  calc ∫ s in (0 : ℝ)..t, ‖h s‖ ≤ ∫ _ in (0 : ℝ)..t, M :=
        intervalIntegral.integral_mono_on ht (hh.norm.intervalIntegrable 0 t)
          intervalIntegrable_const hM
    _ = M * t := by simp [mul_comm]

theorem duhamel_sub {h₁ h₂ : ℝ → C(Torus3, E)} (hh₁ : Continuous h₁) (hh₂ : Continuous h₂)
    (t : ℝ) : duhamel (fun s => h₁ s - h₂ s) t = duhamel h₁ t - duhamel h₂ t := by
  unfold duhamel
  simp_rw [heatOp_sub]
  exact intervalIntegral.integral_sub (intervalIntegrable_duhamel_integrand hh₁ t 0 t)
    (intervalIntegrable_duhamel_integrand hh₂ t 0 t)

/-- `duhamel h t` only depends on the values of `h` on `[0, t]`. -/
theorem duhamel_congr {h₁ h₂ : ℝ → C(Torus3, E)} {t : ℝ} (ht : 0 ≤ t)
    (hh : ∀ s ∈ Icc 0 t, h₁ s = h₂ s) : duhamel h₁ t = duhamel h₂ t := by
  unfold duhamel
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht] at hs
  simp only [hh s hs]

variable [CompleteSpace E] [CompleteSpace F]

theorem duhamel_torusShift {h : ℝ → C(Torus3, E)} (hh : Continuous h) (a : Torus3) (t : ℝ) :
    duhamel (fun s => torusShift a (h s)) t = torusShift a (duhamel h t) := by
  unfold duhamel
  simp_rw [heatOp_torusShift]
  exact (torusShift a).intervalIntegral_comp_comm (intervalIntegrable_duhamel_integrand hh t 0 t)

theorem duhamel_compLeftContinuous {h : ℝ → C(Torus3, E)} (hh : Continuous h) (L : E →L[ℝ] F)
    (t : ℝ) : duhamel (fun s => L.compLeftContinuous ℝ Torus3 (h s)) t =
      L.compLeftContinuous ℝ Torus3 (duhamel h t) := by
  unfold duhamel
  simp_rw [heatOp_compLeftContinuous]
  exact (L.compLeftContinuous ℝ Torus3).intervalIntegral_comp_comm
    (intervalIntegrable_duhamel_integrand hh t 0 t)

end RegularityStructures.PDE

end
