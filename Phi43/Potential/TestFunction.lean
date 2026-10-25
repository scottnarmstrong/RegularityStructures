/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.Convolution
public import RegularityStructures.Abstract.Singular.ModelPairing.Single

/-!
# The derivatives of `Q` as scaled test functions

For every word `l` the function `y ↦ ddA l Q (z - y)` is a test function scaled at `z` with radius
`1` (`isScaledTest_ddA_potQ`), with a constant `potTestConst N l` independent of `z`: its
derivatives up to order `4` are those of `v ↦ ddA l Q (-v)`, which is smooth with compact support.
-/

open scoped ContDiff

public section

open MeasureTheory Filter Topology Set

namespace RegularityStructures.Potential

open RegularityStructures.Inhomogeneity

/-- The reflected derivative kernel `v ↦ ddA l Q (-v)`. -/
@[expose] noncomputable def potQRefl (N : ℕ) (l : List (Fin 4)) (v : ParabolicSpace) : ℝ :=
  ddA l (potQ N) (-v)

theorem contDiff_potQRefl (N : ℕ) (l : List (Fin 4)) : ContDiff ℝ ∞ (potQRefl N l) :=
  (contDiff_ddA (contDiff_potQ N) l).comp contDiff_neg

theorem hasCompactSupport_potQRefl (N : ℕ) (l : List (Fin 4)) :
    HasCompactSupport (potQRefl N l) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ParabolicSpace) 1) fun v hv =>
    ddA_potQ_eq_zero_of_one_lt N l (one_lt_parabolicNorm_of_not_mem_closedBall (by
      rwa [mem_closedBall_zero_iff, norm_neg, ← mem_closedBall_zero_iff]))

theorem exists_bound_iteratedFDeriv_potQRefl (N : ℕ) (l : List (Fin 4)) :
    ∃ A : ℝ, 0 < A ∧ ∀ k ≤ 4, ∀ v, ‖iteratedFDeriv ℝ k (potQRefl N l) v‖ ≤ A := by
  have h : ∀ k : ℕ, ∃ C : ℝ, ∀ v, ‖iteratedFDeriv ℝ k (potQRefl N l) v‖ ≤ C := by
    intro k
    have hc := ((contDiff_potQRefl N l).continuous_iteratedFDeriv (m := k)
      (by exact_mod_cast le_top)).norm
    obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support
      ((hasCompactSupport_potQRefl N l).iteratedFDeriv k).norm
    exact ⟨C, fun v => by simpa using hC v⟩
  choose C hC using h
  refine ⟨1 + ∑ k ∈ Finset.range 5, |C k|, ?_, fun k hk v => ?_⟩
  · have := Finset.sum_nonneg (s := Finset.range 5) (f := fun k => |C k|) fun _ _ => abs_nonneg _
    linarith
  have h1 : |C k| ≤ ∑ k ∈ Finset.range 5, |C k| :=
    Finset.single_le_sum (f := fun k => |C k|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
  linarith [(hC k v).trans (le_abs_self (C k))]

/-- The constant of the scaled-test-function bound for `ddA l Q`. -/
@[expose] noncomputable def potTestConst (N : ℕ) (l : List (Fin 4)) : ℝ :=
  Classical.choose (exists_bound_iteratedFDeriv_potQRefl N l)

theorem potTestConst_pos (N : ℕ) (l : List (Fin 4)) : 0 < potTestConst N l :=
  (Classical.choose_spec (exists_bound_iteratedFDeriv_potQRefl N l)).1

theorem iteratedFDeriv_potQRefl_le (N : ℕ) (l : List (Fin 4)) {k : ℕ} (hk : k ≤ 4)
    (v : ParabolicSpace) : ‖iteratedFDeriv ℝ k (potQRefl N l) v‖ ≤ potTestConst N l :=
  (Classical.choose_spec (exists_bound_iteratedFDeriv_potQRefl N l)).2 k hk v

/-- `y ↦ ddA l Q (z - y)` is a test function scaled at `z` with radius `1`. -/
theorem isScaledTest_ddA_potQ (N : ℕ) (l : List (Fin 4)) (z : ParabolicSpace) :
    IsScaledTest (fun y => ddA l (potQ N) (z - y)) z 1 (potTestConst N l) where
  contDiff := ((contDiff_ddA (contDiff_potQ N) l).comp (contDiff_const.sub contDiff_id)).of_le
    (by exact_mod_cast le_top)
  radius_pos := one_pos
  radius_le_one := le_rfl
  const_pos := potTestConst_pos N l
  supp w hw := by
    refine ddA_potQ_eq_zero_of_one_lt N l ?_
    rwa [parabolicNorm_sub_comm]
  deriv k hk v := by
    have e : (fun v => (fun y => ddA l (potQ N) (z - y)) (z + parabolicDilate 1 v)) =
        potQRefl N l := by
      funext v
      simp [potQRefl, parabolicDilate]
    rw [e]
    exact iteratedFDeriv_potQRefl_le N l hk v

end RegularityStructures.Potential

end
