/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesovLittlewoodPaley
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Frequency geometry of the fixed Littlewood--Paley partition

The boxes are nested, the low cutoffs lie in `[0,1]`, and every fixed frequency eventually belongs
to their plateau. Finite partial sums of the literal blocks therefore telescope in a common
frequency box. These are reconstruction inputs for the equivalence of the heat norm (2.3) of the
statement with the Littlewood--Paley norm.
-/

public noncomputable section

open Filter UnitAddTorus
open scoped Topology

namespace RegularityStructures

theorem torusLPFrequencyBox_mono {m n : ℕ} (hmn : m ≤ n) :
    torusLPFrequencyBox m ⊆ torusLPFrequencyBox n := by
  intro k hk
  have hp : (2 : ℕ) ^ (m + 1) ≤ 2 ^ (n + 1) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.add_le_add_right hmn 1)
  apply Fintype.mem_piFinset.mpr
  intro i
  have hi := Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hk) i)
  apply Finset.mem_Icc.mpr
  have hp' : ((2 ^ (m + 1) : ℕ) : ℤ) ≤ ((2 ^ (n + 1) : ℕ) : ℤ) := by exact_mod_cast hp
  exact ⟨(neg_le_neg hp').trans hi.1, hi.2.trans hp'⟩

theorem torusLowFrequencySymbol_nonneg (n : ℕ) (k : Fin 3 → ℤ) :
    0 ≤ torusLowFrequencySymbol n k :=
  Finset.prod_nonneg fun _ _ => torusLPBump.nonneg

theorem torusLowFrequencySymbol_le_one (n : ℕ) (k : Fin 3 → ℤ) :
    torusLowFrequencySymbol n k ≤ 1 := by
  apply Finset.prod_le_one₀
  · exact fun _ _ => torusLPBump.nonneg
  · exact fun _ _ => torusLPBump.le_one

theorem torusLowFrequencySymbol_eq_zero_of_notMem_box (n : ℕ) (k : Fin 3 → ℤ)
    (hk : k ∉ torusLPFrequencyBox n) : torusLowFrequencySymbol n k = 0 := by
  by_contra h
  apply hk
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_Icc.mpr
  have hi : |(k i : ℝ)| < (2 : ℝ) ^ (n + 1) := by
    by_contra! hh
    exact h (torusLowFrequencySymbol_eq_zero_of_large_coord n k i hh)
  have hi' := abs_le.mp hi.le
  constructor
  · exact_mod_cast hi'.1
  · exact_mod_cast hi'.2

theorem torusLowFrequencySymbol_eventually_eq_one (k : Fin 3 → ℤ) :
    ∀ᶠ n : ℕ in atTop, torusLowFrequencySymbol n k = 1 := by
  have ht : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [(tendsto_atTop.mp ht) (∑ i : Fin 3, |(k i : ℝ)|)] with n hn
  apply torusLowFrequencySymbol_eq_one
  intro i
  exact (Finset.single_le_sum (fun j _ => abs_nonneg (k j : ℝ)) (Finset.mem_univ i)).trans hn

theorem torusDyadicFrequencySymbol_succ_eq_zero_of_small (n : ℕ) (k : Fin 3 → ℤ)
    (hk : ∀ i, |(k i : ℝ)| ≤ (2 : ℝ) ^ n) : torusDyadicFrequencySymbol (n + 1) k = 0 := by
  rw [torusDyadicFrequencySymbol_succ, torusLowFrequencySymbol_eq_one n k hk,
    torusLowFrequencySymbol_eq_one (n + 1) k]
  · exact sub_self _
  · intro i
    exact (hk i).trans (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n))

theorem sum_torusLittlewoodPaleyBlock_apply (n : ℕ) (f : C(Torus3, ℝ)) (x : Torus3) :
    (∑ j ∈ Finset.range (n + 1), torusLittlewoodPaleyBlock j f x) =
      ∑ k ∈ torusLPFrequencyBox n,
        ((torusLowFrequencySymbol n k : ℂ) *
          mFourierCoeff (fun y : Torus3 => (f y : ℂ)) k) * mFourier k x := by
  have hblock (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      torusLittlewoodPaleyBlock j f x = ∑ k ∈ torusLPFrequencyBox n,
        ((torusDyadicFrequencySymbol j k : ℂ) *
          mFourierCoeff (fun y : Torus3 => (f y : ℂ)) k) * mFourier k x := by
    simp only [torusLittlewoodPaleyBlock, ContinuousMap.sum_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
    apply Finset.sum_subset (torusLPFrequencyBox_mono (by simpa using Finset.mem_range.mp hj))
    intro k _ hk
    rw [torusDyadicFrequencySymbol_eq_zero_of_notMem_box j k hk,
      Complex.ofReal_zero, zero_mul, zero_mul]
  simp_rw [Finset.sum_congr rfl hblock]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Complex.ofReal_sum, sum_torusDyadicFrequencySymbol]

end RegularityStructures

end
