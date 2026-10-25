/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# One- and four-dimensional lattice bumps

`latticeBump s = σ(s) - σ(s - 1)` with `σ = Real.smoothTransition` is a smooth function with values
in `[0, 1]` supported in `[0, 2]` whose integer translates telescope to a partition of unity
(`sum_latticeBump_Icc`). Its tensor power `latticeBump4` on `ℝ × ℝ³` is the building block of the
causal lattice partition of unity used for finite-sum reconstruction (Hairer, arXiv:1303.5113v4,
proof of Prop. 7.2).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- `b(s) = σ(s) − σ(s − 1)`, `σ = Real.smoothTransition`; supported in `(0, 2)`. -/
def latticeBump (s : ℝ) : ℝ := Real.smoothTransition s - Real.smoothTransition (s - 1)

/-- Indices of the space-time lattice `ℤ × ℤ³`. -/
abbrev LatticeIndex : Type := ℤ × (Fin 3 → ℤ)

/-- The embedding of a lattice index into `ℝ × ℝ³`. -/
def latticeCoe (k : LatticeIndex) : ParabolicSpace := ((k.1 : ℝ), fun i => (k.2 i : ℝ))

/-- The tensor-product bump on `ℝ × ℝ³`. -/
def latticeBump4 (v : ParabolicSpace) : ℝ := latticeBump v.1 * ∏ i, latticeBump (v.2 i)

end RegularityStructures

end

public section

namespace RegularityStructures

open scoped ContDiff in
theorem contDiff_latticeBump : ContDiff ℝ ∞ latticeBump :=
  Real.smoothTransition.contDiff.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

theorem latticeBump_nonneg (s : ℝ) : 0 ≤ latticeBump s := by
  unfold latticeBump
  have := Real.smoothTransition.monotone (show s - 1 ≤ s by linarith)
  linarith

theorem latticeBump_eq_zero_of_nonpos {s : ℝ} (hs : s ≤ 0) : latticeBump s = 0 := by
  unfold latticeBump
  rw [Real.smoothTransition.zero_of_nonpos hs, Real.smoothTransition.zero_of_nonpos (by linarith)]
  simp

theorem latticeBump_eq_zero_of_two_le {s : ℝ} (hs : 2 ≤ s) : latticeBump s = 0 := by
  unfold latticeBump
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith)]
  simp

theorem latticeBump_ne_zero {s : ℝ} (h : latticeBump s ≠ 0) : 0 < s ∧ s < 2 := by
  constructor
  · by_contra h'
    exact h (latticeBump_eq_zero_of_nonpos (not_lt.1 h'))
  · by_contra h'
    exact h (latticeBump_eq_zero_of_two_le (not_lt.1 h'))

private theorem sum_latticeBump_Icc_aux (a : ℤ) (s : ℝ) :
    ∀ b : ℤ, a - 1 ≤ b →
      ∑ k ∈ Finset.Icc a b, latticeBump (s - k) =
        Real.smoothTransition (s - a) - Real.smoothTransition (s - b - 1) := by
  intro b hb
  induction b, hb using Int.leInduction with
  | base =>
    rw [Finset.Icc_eq_empty (by omega)]
    have : s - ((a - 1 : ℤ) : ℝ) - 1 = s - a := by push_cast; ring
    rw [this]; simp
  | succ b hb ih =>
    have : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [this, Finset.sum_insert (by simp), ih]
    unfold latticeBump
    push_cast
    ring_nf

/-- Telescoping: the integer translates of `latticeBump` sum to one in the bulk. -/
theorem sum_latticeBump_Icc {a b : ℤ} {s : ℝ} (h1 : (a : ℝ) + 1 ≤ s) (h2 : s ≤ b + 1) :
    ∑ k ∈ Finset.Icc a b, latticeBump (s - k) = 1 := by
  have hab : a - 1 ≤ b := by
    have : (a : ℝ) < b + 1 := by linarith
    have : a < b + 1 := by exact_mod_cast this
    omega
  rw [sum_latticeBump_Icc_aux a s b hab, Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith)]
  simp

open scoped ContDiff in
theorem contDiff_latticeBump4 : ContDiff ℝ ∞ latticeBump4 := by
  unfold latticeBump4
  refine (contDiff_latticeBump.comp contDiff_fst).mul (contDiff_prod fun i _ => ?_)
  exact contDiff_latticeBump.comp ((contDiff_apply ℝ ℝ i).comp contDiff_snd)

theorem latticeBump4_nonneg (v : ParabolicSpace) : 0 ≤ latticeBump4 v :=
  mul_nonneg (latticeBump_nonneg _) (Finset.prod_nonneg fun _ _ => latticeBump_nonneg _)

theorem latticeBump4_ne_zero {v : ParabolicSpace} (h : latticeBump4 v ≠ 0) :
    (0 < v.1 ∧ v.1 < 2) ∧ ∀ i, 0 < v.2 i ∧ v.2 i < 2 := by
  unfold latticeBump4 at h
  rw [mul_ne_zero_iff, Finset.prod_ne_zero_iff] at h
  exact ⟨latticeBump_ne_zero h.1, fun i => latticeBump_ne_zero (h.2 i (Finset.mem_univ i))⟩

theorem hasCompactSupport_latticeBump4 : HasCompactSupport latticeBump4 := by
  have hc : IsCompact (Set.Icc (0 : ℝ) 2 ×ˢ Set.pi Set.univ fun _ : Fin 3 => Set.Icc (0 : ℝ) 2) :=
    isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  refine HasCompactSupport.intro hc fun v hv => ?_
  by_contra h
  obtain ⟨⟨h1, h2⟩, h3⟩ := latticeBump4_ne_zero h
  exact hv ⟨⟨h1.le, h2.le⟩, fun i _ => ⟨(h3 i).1.le, (h3 i).2.le⟩⟩

theorem parabolicNorm_le_of_latticeBump4_ne_zero {v : ParabolicSpace}
    (h : latticeBump4 v ≠ 0) : parabolicNorm v ≤ 8 := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := latticeBump4_ne_zero h
  unfold parabolicNorm
  have hs : Real.sqrt |v.1| ≤ 2 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    rw [abs_of_pos h1]; nlinarith
  have hsum : ∑ i, |v.2 i| ≤ ∑ _i : Fin 3, (2 : ℝ) :=
    Finset.sum_le_sum fun i _ => by rw [abs_of_pos (h3 i).1]; exact (h3 i).2.le
  simp at hsum
  linarith

theorem exists_bound_iteratedFDeriv_latticeBump4 (r : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ k ≤ r, ∀ v, ‖iteratedFDeriv ℝ k latticeBump4 v‖ ≤ C :=
  hasCompactSupport_latticeBump4.exists_bound_iteratedFDeriv contDiff_latticeBump4 r

end RegularityStructures

end
