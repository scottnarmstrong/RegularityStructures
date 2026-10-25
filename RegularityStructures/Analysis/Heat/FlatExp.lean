/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# The flat function `u ^ a * exp (-u⁻¹)`

`flatExp a u = u ^ a * exp (-1/u)` for `u > 0` and `0` otherwise (real power `a`). It is smooth
on all of `ℝ` for every real `a`, by the derivative identity
`flatExp a ' = a * flatExp (a - 1) + flatExp (a - 2)`. It is the building block for the smoothness
of the heat kernel on the hyperplane `t = 0` away from the origin
(`RegularityStructures.Analysis.Heat.Kernel`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The flat function `u ^ a * exp (-u⁻¹)` for `u > 0`, extended by `0`. -/
def flatExp (a u : ℝ) : ℝ := if 0 < u then u ^ a * Real.exp (-u⁻¹) else 0

end RegularityStructures

end

public section

open Filter Topology

namespace RegularityStructures

theorem flatExp_of_pos (a : ℝ) {u : ℝ} (hu : 0 < u) : flatExp a u = u ^ a * Real.exp (-u⁻¹) := by
  simp [flatExp, hu]

theorem flatExp_of_nonpos (a : ℝ) {u : ℝ} (hu : u ≤ 0) : flatExp a u = 0 := by
  simp [flatExp, not_lt.mpr hu]

theorem tendsto_flatExp_nhdsGT (a : ℝ) : Tendsto (flatExp a) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-a) 1 one_pos).comp
    tendsto_inv_nhdsGT_zero
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
  rw [flatExp_of_pos a hu]
  simp only [Function.comp_apply]
  rw [Real.inv_rpow hu.le, Real.rpow_neg hu.le, inv_inv, neg_one_mul]

theorem tendsto_flatExp_nhds_zero (a : ℝ) : Tendsto (flatExp a) (𝓝 0) (𝓝 0) := by
  have h : Tendsto (flatExp a) (𝓝[≤] 0 ⊔ 𝓝[>] 0) (𝓝 0) := by
    refine tendsto_sup.2 ⟨?_, tendsto_flatExp_nhdsGT a⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u (hu : u ≤ 0)
    exact (flatExp_of_nonpos a hu).symm
  rwa [nhdsLE_sup_nhdsGT] at h

theorem hasDerivAt_flatExp_of_pos (a : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (flatExp a) (a * flatExp (a - 1) u + flatExp (a - 2) u) u := by
  have h1 : HasDerivAt (fun v : ℝ => v ^ a) (a * u ^ (a - 1)) u :=
    Real.hasDerivAt_rpow_const (Or.inl hu.ne')
  have h2 : HasDerivAt (fun v : ℝ => Real.exp (-v⁻¹))
      (Real.exp (-u⁻¹) * (-(-(u ^ 2)⁻¹))) u :=
    ((hasDerivAt_inv hu.ne').neg).exp
  have h3 := h1.mul h2
  have h4 : u ^ (a - 2) = u ^ a * (u ^ 2)⁻¹ := by
    rw [Real.rpow_sub hu, Real.rpow_two]
    ring
  refine (h3.congr_deriv ?_).congr_of_eventuallyEq ?_
  · rw [flatExp_of_pos _ hu, flatExp_of_pos _ hu, h4]
    ring
  · filter_upwards [Ioi_mem_nhds hu] with v (hv : 0 < v)
    exact flatExp_of_pos a hv

theorem hasDerivAt_flatExp_of_neg (a : ℝ) {u : ℝ} (hu : u < 0) :
    HasDerivAt (flatExp a) (a * flatExp (a - 1) u + flatExp (a - 2) u) u := by
  rw [flatExp_of_nonpos _ hu.le, flatExp_of_nonpos _ hu.le, mul_zero, add_zero]
  refine (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds hu] with v (hv : v < 0)
  exact flatExp_of_nonpos a hv.le

theorem hasDerivAt_flatExp_zero (a : ℝ) :
    HasDerivAt (flatExp a) (a * flatExp (a - 1) 0 + flatExp (a - 2) 0) 0 := by
  rw [flatExp_of_nonpos _ le_rfl, flatExp_of_nonpos _ le_rfl, mul_zero, add_zero,
    hasDerivAt_iff_tendsto_slope]
  refine ((tendsto_flatExp_nhds_zero (a - 1)).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u (hu : u ≠ 0)
  rcases hu.lt_or_gt with hu | hu
  · rw [flatExp_of_nonpos _ hu.le, slope_def_field, flatExp_of_nonpos _ hu.le,
      flatExp_of_nonpos _ le_rfl]
    simp
  · rw [slope_def_field, flatExp_of_pos _ hu, flatExp_of_pos _ hu, flatExp_of_nonpos _ le_rfl,
      Real.rpow_sub_one hu.ne']
    field_simp
    simp
    ring

theorem hasDerivAt_flatExp (a u : ℝ) :
    HasDerivAt (flatExp a) (a * flatExp (a - 1) u + flatExp (a - 2) u) u := by
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · exact hasDerivAt_flatExp_of_neg a hu
  · exact hasDerivAt_flatExp_zero a
  · exact hasDerivAt_flatExp_of_pos a hu

theorem deriv_flatExp (a : ℝ) :
    deriv (flatExp a) = fun u => a * flatExp (a - 1) u + flatExp (a - 2) u :=
  funext fun u => (hasDerivAt_flatExp a u).deriv

theorem contDiff_flatExp_nat (n : ℕ) : ∀ a : ℝ, ContDiff ℝ n (flatExp a) := by
  induction n with
  | zero =>
    intro a
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun u => (hasDerivAt_flatExp a u).continuousAt
  | succ n ih =>
    intro a
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun u => (hasDerivAt_flatExp a u).differentiableAt, by simp, ?_⟩
    rw [deriv_flatExp]
    exact ((ih (a - 1)).const_smul a).add (ih (a - 2))

open scoped ContDiff in
/-- The flat function `u ^ a * exp (-u⁻¹)` (extended by `0`) is smooth on `ℝ`. -/
theorem contDiff_flatExp (a : ℝ) : ContDiff ℝ ∞ (flatExp a) :=
  contDiff_infty.2 fun n => contDiff_flatExp_nat n a

end RegularityStructures

end
