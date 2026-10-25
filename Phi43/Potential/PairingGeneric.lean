/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.DerivHyp
public import Phi43.Potential.QKernel
public import RegularityStructures.Abstract.Singular.ModelPairing.Single

/-!
# Pairing of the noise coordinate with a smooth kernel of lag and range at most `1`

For `h` smooth with `h = 0` outside the closed unit parabolic ball, the function `y ↦ h(z - y)` is
a test function scaled at `z` with radius `1` and a constant `potKernelConst h` independent of `z`
(`isScaledTest_kernel`).  Under the hypotheses of `abs_ddA_potConv_le`
(window model bounds, qualitative growth, `Q_t Π_x e_o = Q_t ξ`),

  `|(ξ ⋆ h)(z)| ≤ r4ModelConst 𝒯 γ · max(1, C_Γ) C_Π · potKernelConst h`

for `0 ≤ z.1 ≤ 1` (`abs_potConv_le`).  This is the form needed for the smooth part of the
decomposition of `K ∗ f`.
-/

open scoped ContDiff

public section

open MeasureTheory Filter Topology Set

namespace RegularityStructures.Potential

/-- `h` is smooth and vanishes outside the closed unit parabolic ball. -/
structure IsUnitKernel (h : ParabolicSpace → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ h
  supp : ∀ w, 1 < parabolicNorm w → h w = 0

namespace IsUnitKernel

variable {h : ParabolicSpace → ℝ} (hh : IsUnitKernel h)
include hh

theorem hasCompactSupport_refl : HasCompactSupport (fun v => h (-v)) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ParabolicSpace) 1) fun v hv =>
    hh.supp _ (one_lt_parabolicNorm_of_not_mem_closedBall (by
      rwa [mem_closedBall_zero_iff, norm_neg, ← mem_closedBall_zero_iff]))

theorem exists_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ k ≤ 4, ∀ v, ‖iteratedFDeriv ℝ k (fun v => h (-v)) v‖ ≤ A := by
  have hs : ContDiff ℝ ∞ (fun v => h (-v)) := hh.smooth.comp contDiff_neg
  have hb : ∀ k : ℕ, ∃ C : ℝ, ∀ v, ‖iteratedFDeriv ℝ k (fun v => h (-v)) v‖ ≤ C := by
    intro k
    have hc := (hs.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)).norm
    obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support
      (hh.hasCompactSupport_refl.iteratedFDeriv k).norm
    exact ⟨C, fun v => by simpa using hC v⟩
  choose C hC using hb
  refine ⟨1 + ∑ k ∈ Finset.range 5, |C k|, ?_, fun k hk v => ?_⟩
  · have := Finset.sum_nonneg (s := Finset.range 5) (f := fun k => |C k|) fun _ _ => abs_nonneg _
    linarith
  · have h1 : |C k| ≤ ∑ k ∈ Finset.range 5, |C k| :=
      Finset.single_le_sum (f := fun k => |C k|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
    linarith [(hC k v).trans (le_abs_self (C k))]

end IsUnitKernel

theorem exists_bound' (h : ParabolicSpace → ℝ) :
    ∃ A : ℝ, IsUnitKernel h →
      0 < A ∧ ∀ k ≤ 4, ∀ v, ‖iteratedFDeriv ℝ k (fun v => h (-v)) v‖ ≤ A := by
  by_cases hh : IsUnitKernel h
  · obtain ⟨A, hA⟩ := hh.exists_bound
    exact ⟨A, fun _ => hA⟩
  · exact ⟨1, fun h' => absurd h' hh⟩

/-- The constant of the scaled-test-function bound for the kernel `h`. -/
@[expose] noncomputable def potKernelConst (h : ParabolicSpace → ℝ) : ℝ :=
  Classical.choose (exists_bound' h)

theorem potKernelConst_pos {h : ParabolicSpace → ℝ} (hh : IsUnitKernel h) :
    0 < potKernelConst h :=
  (Classical.choose_spec (exists_bound' h) hh).1

theorem iteratedFDeriv_refl_le {h : ParabolicSpace → ℝ} (hh : IsUnitKernel h) {k : ℕ} (hk : k ≤ 4)
    (v : ParabolicSpace) : ‖iteratedFDeriv ℝ k (fun v => h (-v)) v‖ ≤ potKernelConst h :=
  (Classical.choose_spec (exists_bound' h) hh).2 k hk v

/-- `y ↦ h(z - y)` is a test function scaled at `z` with radius `1`. -/
theorem isScaledTest_kernel {h : ParabolicSpace → ℝ} (hh : IsUnitKernel h) (z : ParabolicSpace) :
    IsScaledTest (fun y => h (z - y)) z 1 (potKernelConst h) where
  contDiff := (hh.smooth.comp (contDiff_const.sub contDiff_id)).of_le (by exact_mod_cast le_top)
  radius_pos := one_pos
  radius_le_one := le_rfl
  const_pos := potKernelConst_pos hh
  supp w hw := by
    refine hh.supp _ ?_
    rwa [parabolicNorm_sub_comm]
  deriv k hk v := by
    have e : (fun v => (fun y => h (z - y)) (z + parabolicDilate 1 v)) = fun v => h (-v) := by
      funext v
      simp [parabolicDilate]
    rw [e]
    exact iteratedFDeriv_refl_le hh hk v

end RegularityStructures.Potential

end
