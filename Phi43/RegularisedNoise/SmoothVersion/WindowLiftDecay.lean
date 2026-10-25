/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.WindowKernelSmoothness
public import Phi43.RegularisedNoise.SmoothVersion.PeriodicDerivative
public import Phi43.RegularisedNoise.SmoothVersion.CoordinateDecay
public import Phi43.RegularisedNoise.SmoothVersion.WindowCoefficientTranslation
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Decay of finite-window coefficients

The smooth finite-window lift has uniformly bounded derivatives on one fundamental cube.  This
module packages the coordinatewise integration-by-parts estimate for its torus Fourier
coefficients.  The resulting estimate is the deterministic input for the random Fourier-series
construction of a smooth regularised noise (Definition 2.4 and the existence part of item (W2) of
Lemma 4.1 of the statement).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped BigOperators ContDiff Topology

namespace RegularityStructures.Phi43

private theorem torusProj_torusRep_windowLiftDecay (x : Torus3) :
    torusProj (torusRep x) = x := by
  ext i
  dsimp [torusProj, torusRep]
  exact AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ)) (y := x i)

private def coordinateInsertRealVector (i : Fin 4) (x : UnitAddTorus (Fin 3))
    (t : ℝ) : Fin 4 → ℝ :=
  @Fin.insertNth 3 (fun _ : Fin 4 => ℝ) i t (fun q => torusRep x q)

private theorem coordinateInsert_realLift_eq
    (i : Fin 4) (t : ℝ) (x : UnitAddTorus (Fin 3)) :
    coordinateInsert 0
        ((coordinateInsertRealVector i x t 0 : ℝ) : UnitAddCircle)
        (fun (j : Fin 3) =>
          ((coordinateInsertRealVector i x t j.succ : ℝ) : UnitAddCircle)) =
      coordinateInsert i (t : UnitAddCircle) x := by
  have hvec : (fun r : Fin 4 =>
      ((coordinateInsertRealVector i x t r : ℝ) : UnitAddCircle)) =
      coordinateInsert i (t : UnitAddCircle) x := by
    funext r
    refine Fin.succAboveCases i ?_ (fun q => ?_) r
    · simp [coordinateInsert, coordinateInsertRealVector]
    · simp only [coordinateInsert, coordinateInsertRealVector,
        Fin.insertNth_apply_succAbove]
      exact congrFun (torusProj_torusRep_windowLiftDecay x) q
  ext r
  unfold coordinateInsert
  refine Fin.succAboveCases 0 ?_ (fun j => ?_) r
  · simpa only [coordinateInsert, Fin.insertNth_apply_same] using congrFun hvec 0
  · rw [Fin.insertNth_apply_succAbove]
    exact congrFun hvec j.succ

private theorem contDiff_coordinateInsert_realLift
    (i : Fin 4) (x : UnitAddTorus (Fin 3)) :
    ContDiff ℝ ∞ (fun t : ℝ =>
      ((coordinateInsertRealVector i x t 0),
        (fun (j : Fin 3) =>
          coordinateInsertRealVector i x t j.succ))) := by
  have hv : ∀ r : Fin 4,
      ContDiff ℝ ∞
        (fun t : ℝ => coordinateInsertRealVector i x t r) := by
    intro r
    rcases Fin.eq_self_or_eq_succAbove i r with hri | ⟨j, rfl⟩
    · subst r
      simp only [coordinateInsertRealVector, Fin.insertNth_apply_same]
      fun_prop
    · simp [coordinateInsertRealVector, Fin.insertNth_apply_succAbove]
      exact contDiff_const
  exact (hv 0).prodMk (by
    apply contDiff_pi.2
    intro j
    exact hv j.succ)

theorem smoothVersion_contDiff_windowKernelLift_coordinateSlice
    {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi)
    {R N : ℝ} (hR : ∀ q : SpaceTime, R < |q.1| → Phi q = 0)
    {z : SpaceTime} (hz : |z.1| < N) {a b : ℝ}
    (hR0 : 0 ≤ R) (ha : a = -N - R - 1) (hb : b = N + R + 1)
    (hends : windowKernelTimeMap Phi hPhi z a b 0 =
      windowKernelTimeMap Phi hPhi z a b 1)
    (i : Fin 4) (x : UnitAddTorus (Fin 3)) :
    ContDiff ℝ ∞ (fun t : ℝ =>
      windowKernelLift Phi hPhi z a b hends
        (coordinateInsert i (t : UnitAddCircle) x)) := by
  let g : ℝ × (Fin 3 → ℝ) → ℝ := fun p =>
    windowKernelLift Phi hPhi z a b hends
      (coordinateInsert 0 (p.1 : UnitAddCircle)
        (fun j => ((p.2 j : ℝ) : UnitAddCircle)))
  have hg : ContDiff ℝ ∞ g := contDiff_windowKernelLift_realLift
    hPhi hR hz hR0 ha hb hends
  have hp : ContDiff ℝ ∞ (fun t : ℝ =>
      ((coordinateInsertRealVector i x t 0),
        (fun (j : Fin 3) =>
          coordinateInsertRealVector i x t j.succ))) :=
    contDiff_coordinateInsert_realLift i x
  have hcomp := hg.comp hp
  change ContDiff ℝ ∞ (fun t : ℝ =>
    g (coordinateInsertRealVector i x t 0,
      fun (j : Fin 3) => coordinateInsertRealVector i x t j.succ)) at hcomp
  have heq : (fun t : ℝ =>
      g ((coordinateInsertRealVector i x t 0),
        (fun (j : Fin 3) =>
          coordinateInsertRealVector i x t j.succ))) =
      (fun t : ℝ => windowKernelLift Phi hPhi z a b hends
        (coordinateInsert i (t : UnitAddCircle) x)) := by
    funext t
    exact congrArg (fun y : UnitAddTorus (Fin 4) =>
      windowKernelLift Phi hPhi z a b hends y)
      (coordinateInsert_realLift_eq i t x)
  rw [heq] at hcomp
  exact hcomp

theorem smoothVersion_periodic_windowKernelLift_coordinateSlice
    {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi)
    {R N : ℝ} (_hR : ∀ q : SpaceTime, R < |q.1| → Phi q = 0)
    {z : SpaceTime} (_hz : |z.1| < N) {a b : ℝ}
    (_hR0 : 0 ≤ R) (_ha : a = -N - R - 1) (_hb : b = N + R + 1)
    (hends : windowKernelTimeMap Phi hPhi z a b 0 =
      windowKernelTimeMap Phi hPhi z a b 1)
    (i : Fin 4) (x : UnitAddTorus (Fin 3)) :
    Function.Periodic (fun t : ℝ =>
      windowKernelLift Phi hPhi z a b hends
        (coordinateInsert i (t : UnitAddCircle) x)) 1 := by
  intro t
  apply congrArg (fun y : UnitAddTorus (Fin 4) =>
    windowKernelLift Phi hPhi z a b hends y)
  ext r
  refine Fin.succAboveCases i ?_ (fun j => ?_) r
  · simp [coordinateInsert]
  · simp [coordinateInsert]

private theorem norm_iteratedFDeriv_id_le_one_local (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (fun y : ℝ => y) x‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change |iteratedDeriv n id x| ≤ 1
  rw [iteratedDeriv_id]
  have hn0 : n ≠ 0 := by omega
  by_cases hn1 : n = 1
  · simp [hn1]
  · simp [hn0, hn1]

private theorem norm_iteratedFDeriv_coordinateInsertRealLift_le
    (i : Fin 4) (x : UnitAddTorus (Fin 3)) (n : ℕ) (hn : 1 ≤ n) (s : ℝ) :
    ‖iteratedFDeriv ℝ n (fun t : ℝ =>
      ((coordinateInsertRealVector i x t 0),
        (fun (j : Fin 3) => coordinateInsertRealVector i x t j.succ))) s‖ ≤
      (1 : ℝ) ^ n := by
  let v : ℝ → Fin 4 → ℝ := fun t => coordinateInsertRealVector i x t
  let p : ℝ → ℝ × (Fin 3 → ℝ) := fun t =>
    (v t 0, fun j => v t j.succ)
  let A₀ : ℝ →L[ℝ] ℝ := if i = 0 then ContinuousLinearMap.id ℝ ℝ else 0
  let A₁ : ℝ →L[ℝ] (Fin 3 → ℝ) :=
    ContinuousLinearMap.pi (fun j =>
      if i = j.succ then ContinuousLinearMap.id ℝ ℝ else 0)
  let A : ℝ →L[ℝ] (ℝ × (Fin 3 → ℝ)) := A₀.prod A₁
  have hA₀ : ‖A₀‖ ≤ 1 := by
    dsimp [A₀]
    split <;> simp
  have hA₁ : ‖A₁‖ ≤ 1 := by
    dsimp [A₁]
    apply ContinuousLinearMap.norm_pi_le_of_le
    · intro j
      split <;> simp
    · norm_num
  have hA : ‖A‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro t
    rw [ContinuousLinearMap.prod_apply, Prod.norm_mk]
    apply max_le
    · exact (ContinuousLinearMap.le_opNorm A₀ t).trans
        (mul_le_mul_of_nonneg_right hA₀ (norm_nonneg t))
    · exact (ContinuousLinearMap.le_opNorm A₁ t).trans
        (mul_le_mul_of_nonneg_right hA₁ (norm_nonneg t))
  have hv_affine : ∀ r : Fin 4, ∀ t : ℝ,
      v t r = v 0 r + (if r = i then t else 0) := by
    intro r t
    rcases Fin.eq_self_or_eq_succAbove i r with hri | ⟨j, rfl⟩
    · subst r
      simp [v, coordinateInsertRealVector]
    · simp [v, coordinateInsertRealVector]
  have hp_affine : p = fun t => A t + p 0 := by
    funext t
    apply Prod.ext
    · dsimp [p, A, A₀, A₁]
      by_cases hi : i = 0
      · subst i
        simp [v, coordinateInsertRealVector]
      · have h0i : (0 : Fin 4) ≠ i := Ne.symm hi
        simpa [p, A, A₀, A₁, hi, h0i] using hv_affine 0 t
    · funext j
      dsimp [p, A, A₁]
      by_cases hij : i = j.succ
      · simp [v, coordinateInsertRealVector, hij]
      · have hj : j.succ ≠ i := Ne.symm hij
        simpa [p, A, A₀, A₁, hij, hj] using hv_affine j.succ t
  have hp_smooth : ContDiff ℝ ∞ p := by
    rw [hp_affine]
    fun_prop
  change ‖iteratedFDeriv ℝ n p s‖ ≤ (1 : ℝ) ^ n
  rw [hp_affine]
  change ‖iteratedFDeriv ℝ n
      ((fun t : ℝ => A t) + (fun _ : ℝ => p 0)) s‖ ≤ (1 : ℝ) ^ n
  rw [iteratedFDeriv_add_apply
      (A.contDiff.contDiffAt.of_le (by exact_mod_cast le_top))
      contDiff_const.contDiffAt]
  rw [iteratedFDeriv_const_of_ne (Nat.ne_of_gt hn) (p 0)]
  simp only [Pi.zero_apply, add_zero]
  have hcomp := A.norm_iteratedFDeriv_comp_left (n := n) (x := s)
    (contDiff_id.contDiffAt) (by exact_mod_cast le_top)
  have hid := norm_iteratedFDeriv_id_le_one_local n s hn
  have hcomp' : ‖iteratedFDeriv ℝ n A s‖ ≤ ‖A‖ *
      ‖iteratedFDeriv ℝ n id s‖ := by
    simpa [Function.comp_def] using hcomp
  have hid' : ‖iteratedFDeriv ℝ n id s‖ ≤ 1 := by
    change ‖iteratedFDeriv ℝ n (fun y : ℝ => y) s‖ ≤ 1
    exact hid
  calc
    ‖iteratedFDeriv ℝ n A s‖ ≤ ‖A‖ *
        ‖iteratedFDeriv ℝ n id s‖ := hcomp'
    _ ≤ 1 * ‖iteratedFDeriv ℝ n id s‖ := by
      exact mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    _ ≤ 1 := by simpa only [one_mul] using hid'
    _ ≤ (1 : ℝ) ^ n := by simp

theorem smoothVersion_norm_iteratedDeriv_windowKernelLift_coordinateSlice_le
    {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi)
    {R N : ℝ} (hR : ∀ q : SpaceTime, R < |q.1| → Phi q = 0)
    {z : SpaceTime} (hz : |z.1| < N) {a b : ℝ}
    (hR0 : 0 ≤ R) (ha : a = -N - R - 1) (hb : b = N + R + 1)
    (hends : windowKernelTimeMap Phi hPhi z a b 0 =
      windowKernelTimeMap Phi hPhi z a b 1)
    (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : Fin 4, ∀ x : UnitAddTorus (Fin 3),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedDeriv m (fun s : ℝ =>
          windowKernelLift Phi hPhi z a b hends
            (coordinateInsert i (s : UnitAddCircle) x)) t‖ ≤ C := by
  let g : ℝ × (Fin 3 → ℝ) → ℝ := fun p =>
    windowKernelLift Phi hPhi z a b hends
      (coordinateInsert 0 (p.1 : UnitAddCircle)
        (fun j => ((p.2 j : ℝ) : UnitAddCircle)))
  have hg : ContDiff ℝ ∞ g := contDiff_windowKernelLift_realLift
    hPhi hR hz hR0 ha hb hends
  let K : Set (ℝ × (Fin 3 → ℝ)) :=
    Icc (0 : ℝ) 1 ×ˢ Set.univ.pi (fun _ : Fin 3 => Icc (0 : ℝ) 1)
  have hKcompact : IsCompact K := by
    exact isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have hB : ∀ n : Fin (m + 1), ∃ B : ℝ, 0 ≤ B ∧
      ∀ p ∈ K, ‖iteratedFDeriv ℝ n (fun q => g q) p‖ ≤ B := by
    intro n
    obtain ⟨B, hB⟩ := hKcompact.exists_bound_of_continuousOn
      (hg.continuous_iteratedFDeriv (m := n.val) (by exact_mod_cast le_top)).norm.continuousOn
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      (hB p hp).trans (le_max_left _ _)
  choose B hB0 hB using hB
  let Bsum : ℝ := ∑ n : Fin (m + 1), B n
  let C : ℝ := (m.factorial : ℝ) * Bsum
  have hC : 0 ≤ C := by
    dsimp [C, Bsum]
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun n _ => hB0 n)
  have hCbound : ∀ n : ℕ, n ≤ m → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ n (fun q => g q) p‖ ≤ Bsum := by
    intro n hnm p hp
    let n' : Fin (m + 1) := ⟨n, Nat.lt_succ_of_le hnm⟩
    have hn' := hB n' p hp
    have hsum := Finset.single_le_sum (fun j _ => hB0 j)
      (Finset.mem_univ n')
    exact hn'.trans (by simpa [Bsum] using
      (hsum : B n' ≤ ∑ j : Fin (m + 1), B j))
  have htorusRep : ∀ x : UnitAddTorus (Fin 3), ∀ j : Fin 3,
      torusRep x j ∈ Icc (0 : ℝ) 1 := by
    intro x j
    change (AddCircle.equivIco (1 : ℝ) 0 (x j) : ℝ) ∈ Icc (0 : ℝ) 1
    have hj := (AddCircle.equivIco (1 : ℝ) 0 (x j)).property
    exact ⟨hj.1, by simpa using hj.2.le⟩
  refine ⟨C, hC, ?_⟩
  intro i' x' t ht
  let g' : ℝ × (Fin 3 → ℝ) → ℝ := fun p =>
    windowKernelLift Phi hPhi z a b hends
      (coordinateInsert 0 (p.1 : UnitAddCircle)
        (fun j => ((p.2 j : ℝ) : UnitAddCircle)))
  have hg' : ContDiff ℝ ∞ g' := contDiff_windowKernelLift_realLift
    hPhi hR hz hR0 ha hb hends
  let v' : ℝ → Fin 4 → ℝ := fun s => coordinateInsertRealVector i' x' s
  let p' : ℝ → ℝ × (Fin 3 → ℝ) := fun s =>
    (v' s 0, fun j => v' s j.succ)
  have hp'_smooth : ContDiff ℝ ∞ p' := by
    exact contDiff_coordinateInsert_realLift i' x'
  have hv'_mem : ∀ r : Fin 4, v' t r ∈ Icc (0 : ℝ) 1 := by
    intro r
    rcases Fin.eq_self_or_eq_succAbove i' r with hri | ⟨j, rfl⟩
    · subst r
      simpa [v', coordinateInsertRealVector] using ht
    · simpa [v', coordinateInsertRealVector, Fin.insertNth_apply_succAbove] using
        htorusRep x' j
  have hp'_mem : p' t ∈ K := by
    refine ⟨⟨(hv'_mem 0).1, (hv'_mem 0).2⟩, ?_⟩
    exact Set.mem_pi.2 (fun j _ => hv'_mem j.succ)
  have hcomp := norm_iteratedFDeriv_comp_le
    (n := m) (N := (∞ : ℕ∞ω)) hg' hp'_smooth (by exact_mod_cast le_top) t
    (C := Bsum) (D := 1)
    (fun n hn => hCbound n (by exact_mod_cast hn) (p' t) hp'_mem)
    (fun n hn hnm => by
      simpa [p', v'] using
        (norm_iteratedFDeriv_coordinateInsertRealLift_le i' x' n hn t))
  have hfun : (fun s : ℝ => g' (p' s)) = (fun s : ℝ =>
      windowKernelLift Phi hPhi z a b hends
        (coordinateInsert i' (s : UnitAddCircle) x')) := by
    funext s
    exact congrArg (fun y : UnitAddTorus (Fin 4) =>
      windowKernelLift Phi hPhi z a b hends y)
      (coordinateInsert_realLift_eq i' s x')
  rw [show g' ∘ p' = fun s => g' (p' s) by rfl, hfun] at hcomp
  simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv, C, Bsum, one_pow,
    mul_one, Function.comp_def] using hcomp

end RegularityStructures.Phi43

end
