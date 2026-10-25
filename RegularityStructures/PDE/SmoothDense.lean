/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.TorusLift
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth functions are dense in `C(T³, ℝ)`

The functions on `T³` with smooth periodic lift form a subalgebra of `C(T³, ℝ)`
(`smoothSubalgebra`). It contains the coordinate functions `cos 2πxᵢ` and `sin 2πxᵢ`, which
separate the points of `T³`, so it is dense by the Stone–Weierstrass theorem
(`exists_smooth_near`).
-/

open scoped ContDiff

public section

namespace RegularityStructures.PDE

open Real Set

theorem contDiff_lift_mul {g h : C(Torus3, ℝ)} (hg : ContDiff ℝ ∞ fun y => g (torusProj y))
    (hh : ContDiff ℝ ∞ fun y => h (torusProj y)) :
    ContDiff ℝ ∞ fun y => (g * h) (torusProj y) := hg.mul hh

theorem contDiff_lift_add {g h : C(Torus3, ℝ)} (hg : ContDiff ℝ ∞ fun y => g (torusProj y))
    (hh : ContDiff ℝ ∞ fun y => h (torusProj y)) :
    ContDiff ℝ ∞ fun y => (g + h) (torusProj y) := hg.add hh

theorem contDiff_lift_algebraMap (r : ℝ) :
    ContDiff ℝ ∞ fun y => (algebraMap ℝ C(Torus3, ℝ) r) (torusProj y) := contDiff_const

end RegularityStructures.PDE

end

@[expose] public noncomputable section

namespace RegularityStructures.PDE

/-- The functions on `T³` whose periodic lift is smooth. -/
def smoothSubalgebra : Subalgebra ℝ C(Torus3, ℝ) where
  carrier := {g | ContDiff ℝ ∞ fun y => g (torusProj y)}
  mul_mem' ha hb := contDiff_lift_mul ha hb
  add_mem' ha hb := contDiff_lift_add ha hb
  algebraMap_mem' r := contDiff_lift_algebraMap r

end RegularityStructures.PDE

end

public section

namespace RegularityStructures.PDE

open Real Set

/-- Points of `ℝ³` with the same image in `T³` differ by an integer vector. -/
theorem exists_int_of_torusProj_eq {a b : Fin 3 → ℝ} (hab : torusProj a = torusProj b)
    (i : Fin 3) : ∃ n : ℤ, b i = a i + n := by
  have h := congrFun hab i
  simp only [torusProj] at h
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 h)
  exact ⟨n, by simp at hn; linarith⟩

theorem torusProj_apply_eq_of_exists_int {a b : Fin 3 → ℝ} {i : Fin 3} {n : ℤ}
    (h : b i = a i + n) : torusProj a i = torusProj b i := by
  simp only [torusProj]
  refine QuotientAddGroup.eq.2 (AddSubgroup.mem_zmultiples_iff.2 ⟨n, ?_⟩)
  simp [h]

theorem continuous_cos_coord (i : Fin 3) : Continuous fun y : Fin 3 → ℝ => cos (2 * π * y i) := by
  fun_prop

theorem continuous_sin_coord (i : Fin 3) : Continuous fun y : Fin 3 → ℝ => sin (2 * π * y i) := by
  fun_prop

theorem cos_coord_eq_of_torusProj_eq (i : Fin 3) {a b : Fin 3 → ℝ}
    (hab : torusProj a = torusProj b) : cos (2 * π * a i) = cos (2 * π * b i) := by
  obtain ⟨n, hn⟩ := exists_int_of_torusProj_eq hab i
  rw [hn, mul_add, mul_comm (2 * π) (n : ℝ), cos_add_int_mul_two_pi]

theorem sin_coord_eq_of_torusProj_eq (i : Fin 3) {a b : Fin 3 → ℝ}
    (hab : torusProj a = torusProj b) : sin (2 * π * a i) = sin (2 * π * b i) := by
  obtain ⟨n, hn⟩ := exists_int_of_torusProj_eq hab i
  rw [hn, mul_add, mul_comm (2 * π) (n : ℝ), sin_add_int_mul_two_pi]

end RegularityStructures.PDE

end

@[expose] public noncomputable section

namespace RegularityStructures.PDE

open Real

/-- The function `x ↦ cos 2πxᵢ` on `T³`. -/
def torusCos (i : Fin 3) : C(Torus3, ℝ) :=
  torusDescend (fun y => cos (2 * π * y i)) (continuous_cos_coord i)
    fun _ _ hab => cos_coord_eq_of_torusProj_eq i hab

/-- The function `x ↦ sin 2πxᵢ` on `T³`. -/
def torusSin (i : Fin 3) : C(Torus3, ℝ) :=
  torusDescend (fun y => sin (2 * π * y i)) (continuous_sin_coord i)
    fun _ _ hab => sin_coord_eq_of_torusProj_eq i hab

end RegularityStructures.PDE

end

public section

namespace RegularityStructures.PDE

open Real Set

theorem torusCos_mem (i : Fin 3) : torusCos i ∈ smoothSubalgebra := by
  show ContDiff ℝ ∞ fun y => torusCos i (torusProj y)
  simp only [torusCos, torusDescend_torusProj]
  fun_prop

theorem torusSin_mem (i : Fin 3) : torusSin i ∈ smoothSubalgebra := by
  show ContDiff ℝ ∞ fun y => torusSin i (torusProj y)
  simp only [torusSin, torusDescend_torusProj]
  fun_prop

/-- If `cos 2πa = cos 2πb` and `sin 2πa = sin 2πb` then `b - a` is an integer. -/
theorem exists_int_of_cos_sin_eq {a b : ℝ} (hc : cos (2 * π * a) = cos (2 * π * b))
    (hs : sin (2 * π * a) = sin (2 * π * b)) : ∃ n : ℤ, b = a + n := by
  have he : Complex.exp (↑(2 * π * b) * Complex.I) = Complex.exp (↑(2 * π * a) * Complex.I) := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
  refine ⟨n, ?_⟩
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 pi_ne_zero
  have h2 : (2 * π * b : ℂ) = 2 * π * a + n * (2 * π) := by
    have := hn
    push_cast at this
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have := mul_right_cancel₀ hI (by rw [this]; ring : (2 * π * b : ℂ) * Complex.I =
      (2 * π * a + n * (2 * π)) * Complex.I)
    exact this
  have h3 : (b : ℂ) = a + n := by
    have h4 : (2 * π : ℂ) * b = (2 * π) * (a + n) := by rw [mul_assoc] at h2; linear_combination h2
    exact mul_left_cancel₀ (mul_ne_zero two_ne_zero hπ) h4
  exact_mod_cast h3

theorem smoothSubalgebra_separatesPoints : smoothSubalgebra.SeparatesPoints := by
  intro x x' hxx'
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hxx'
  by_contra hcon
  push Not at hcon
  have hc := hcon (torusCos i) ⟨torusCos i, torusCos_mem i, rfl⟩
  have hs := hcon (torusSin i) ⟨torusSin i, torusSin_mem i, rfl⟩
  rw [← torusProj_torusRep x, ← torusProj_torusRep x'] at hc hs hi
  simp only [torusCos, torusSin, torusDescend_torusProj] at hc hs
  obtain ⟨n, hn⟩ := exists_int_of_cos_sin_eq hc hs
  exact hi (torusProj_apply_eq_of_exists_int hn)

/-- **Smooth functions are dense in `C(T³, ℝ)`.** -/
theorem exists_smooth_near (g : C(Torus3, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : C(Torus3, ℝ), ContDiff ℝ ∞ (fun y => h (torusProj y)) ∧ ‖g - h‖ < ε := by
  have hg : g ∈ smoothSubalgebra.topologicalClosure := by
    rw [ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
      smoothSubalgebra_separatesPoints]
    trivial
  obtain ⟨h, hh, hgh⟩ := Metric.mem_closure_iff.1 hg ε hε
  exact ⟨h, hh, by rwa [dist_eq_norm] at hgh⟩

end RegularityStructures.PDE

end
