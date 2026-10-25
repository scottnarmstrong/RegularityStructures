/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesovMultiplierProfiles
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Uniform bounds for the actual finite dyadic multiplier kernels

For profiles supported in `[-2,2]`, the dyadic frequency cube contains every nonzero
sample. Finite-product expansion identifies the finite three-dimensional Fourier sum
with the product of the one-dimensional Schwartz multiplier series. Poisson summation
then gives the scale-independent L1 bound for the literal LP cutoffs.

This is the Fourier multiplier estimate used in the equivalence of the heat norm (2.3) of the
statement with the Littlewood--Paley norm.
-/

@[expose] public noncomputable section

open MeasureTheory Set UnitAddTorus
open scoped ENNReal SchwartzMap

namespace RegularityStructures

/-- A finite tensor-profile Fourier kernel at frequency scale `2^n`. -/
def torusTensorFiniteKernel (m : Fin 3 → 𝓢(ℝ, ℂ)) (n : ℕ) : C(Torus3, ℂ) :=
  ∑ k ∈ torusLPFrequencyBox n,
    (∏ i : Fin 3, m i ((k i : ℝ) / (2 : ℝ) ^ n)) • mFourier k

private theorem two_le_abs_scaled_int_of_notMem {n : ℕ} {k : ℤ}
    (hk : k ∉ Finset.Icc (-((2 ^ (n + 1) : ℕ) : ℤ)) ((2 ^ (n + 1) : ℕ) : ℤ)) :
    2 ≤ |(k : ℝ) / (2 : ℝ) ^ n| := by
  have hlarge : (((2 ^ (n + 1) : ℕ) : ℝ)) < |(k : ℝ)| := by
    by_contra! h
    apply hk
    apply Finset.mem_Icc.mpr
    constructor
    · exact_mod_cast (abs_le.mp h).1
    · exact_mod_cast (abs_le.mp h).2
  have hp : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  rw [abs_div, abs_of_pos hp]
  apply (le_div_iff₀ hp).mpr
  have he : (((2 ^ (n + 1) : ℕ) : ℝ)) = 2 * (2 : ℝ) ^ n := by
    push_cast
    rw [pow_succ, mul_comm]
  exact he ▸ hlarge.le

theorem torusTensorFiniteKernel_apply (m : Fin 3 → 𝓢(ℝ, ℂ))
    (hm : ∀ i u, 2 ≤ |u| → m i u = 0) (n : ℕ) (x : Torus3) :
    torusTensorFiniteKernel m n x =
      ∏ i : Fin 3, ∑' k : ℤ, m i ((k : ℝ) / (2 : ℝ) ^ n) * fourier k (x i) := by
  simp only [torusTensorFiniteKernel, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, mFourier, ContinuousMap.coe_mk, ← Finset.prod_mul_distrib, torusLPFrequencyBox]
  have hfactor := Finset.sum_prod_piFinset (ι := Fin 3)
    (Finset.Icc (-((2 ^ (n + 1) : ℕ) : ℤ)) ((2 ^ (n + 1) : ℕ) : ℤ))
    (fun i : Fin 3 => fun k : ℤ => m i ((k : ℝ) / (2 : ℝ) ^ n) * fourier k (x i))
  rw [hfactor]
  apply Finset.prod_congr rfl
  intro i _
  symm
  apply tsum_eq_sum
  intro k hk
  rw [hm i _ (two_le_abs_scaled_int_of_notMem hk), zero_mul]

theorem torusTensorFiniteKernel_bound_uniform (m : Fin 3 → 𝓢(ℝ, ℂ))
    (hm : ∀ i u, 2 ≤ |u| → m i u = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      (∫⁻ x : Torus3, ‖torusTensorFiniteKernel m n x‖ₑ) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hbound⟩ := schwartz_torus_tensor_multiplier_bound_uniform m
  refine ⟨C, hC, fun n => ?_⟩
  simp_rw [torusTensorFiniteKernel_apply m hm]
  exact hbound _ (pow_pos (by norm_num : (0 : ℝ) < 2) n)

end RegularityStructures

end
