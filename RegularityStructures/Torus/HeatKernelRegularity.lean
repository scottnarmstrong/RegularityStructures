/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HeatKernelIntegral
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Uniform Gaussian bounds for the torus heat kernel

The Gaussian series is controlled uniformly on the half-open fundamental cube.  This file contains
the summable majorant used to prove boundedness and continuity of the kernel.
-/

@[expose] public noncomputable section

open MeasureTheory Real Set
open scoped Topology

namespace RegularityStructures

theorem summable_pi_fin3_prod {u : ℤ → ℝ} (hu : Summable u)
    (hnu : ∀ n, 0 ≤ u n) :
    Summable (fun k : Fin 3 → ℤ => ∏ i, u (k i)) := by
  classical
  have h01 : Summable (fun p : ℤ × ℤ => u p.1 * u p.2) :=
    hu.mul_of_nonneg hu (by intro; exact hnu _) (by intro; exact hnu _)
  have h012 : Summable (fun q : (ℤ × ℤ) × ℤ =>
      (u q.1.1 * u q.1.2) * u q.2) :=
    h01.mul_of_nonneg hu
      (by intro q; exact mul_nonneg (hnu _) (hnu _)) (by intro; exact hnu _)
  let e2 : (ℤ × ℤ) ≃ (Fin 2 → ℤ) :=
    (piFinTwoEquiv (fun _ : Fin 2 => ℤ)).symm
  let e3 : ((ℤ × ℤ) × ℤ) ≃ (Fin 3 → ℤ) :=
    ((Equiv.prodAssoc ℤ ℤ ℤ).trans
      (Equiv.prodCongr (Equiv.refl ℤ) e2)).trans
      (Fin.consEquiv (fun _ : Fin 3 => ℤ))
  rw [← e3.summable_iff]
  convert h012 using 1
  funext q
  simp [e3, e2, Fin.prod_univ_succ, piFinTwoEquiv]
  ring

def gaussianOneDimMajorant (a : ℝ) (n : ℤ) : ℝ :=
  (if n ∈ ({-3, -2, -1, 0, 1, 2} : Finset ℤ) then 1 else 0) +
    exp (-(a / 4) * (n : ℝ) ^ 2)

theorem summable_gaussianOneDimMajorant {a : ℝ} (ha : 0 < a) :
    Summable (gaussianOneDimMajorant a) := by
  apply Summable.add
  · apply summable_of_ne_finset_zero (s := {-3, -2, -1, 0, 1, 2})
    intro n hn
    simp [hn]
  · have h := summable_exp_neg_mul_sq_int (show 0 < a / 4 by positivity)
      (show (0 : ℝ) ∈ Set.Ico 0 1 by simp)
    convert h using 1
    funext n
    congr 2
    ring

theorem gaussianOneDimMajorant_nonneg {a : ℝ} (n : ℤ) :
    0 ≤ gaussianOneDimMajorant a n := by
  unfold gaussianOneDimMajorant
  positivity

theorem gaussian_exp_shift_le_majorant {a b : ℝ} (ha : 0 < a)
    (hb : b ∈ Set.Icc (-1 : ℝ) 2) (n : ℤ) :
    exp (-a * (b + n) ^ 2) ≤ gaussianOneDimMajorant a n := by
  let S : Finset ℤ := {-3, -2, -1, 0, 1, 2}
  have hmajor : gaussianOneDimMajorant a n =
      (if n ∈ S then 1 else 0) + exp (-(a / 4) * (n : ℝ) ^ 2) := by
    rfl
  rw [hmajor]
  by_cases hn : n ∈ S
  · have hleft : exp (-a * (b + n) ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      rw [show -a * (b + (n : ℝ)) ^ 2 = -(a * (b + (n : ℝ)) ^ 2) by ring]
      exact neg_nonpos.mpr (mul_nonneg ha.le (sq_nonneg _))
    simp only [hn, ↓reduceIte]
    exact hleft.trans (by linarith [exp_nonneg (-(a / 4) * (n : ℝ) ^ 2)])
  · simp only [hn, ↓reduceIte, zero_add]
    have hnlarge : n ≤ -4 ∨ 3 ≤ n := by
      have hn' : n ≠ -3 ∧ n ≠ -2 ∧ n ≠ -1 ∧ n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2 := by
        simpa [S] using hn
      omega
    apply Real.exp_le_exp.mpr
    rcases hnlarge with hnlarge | hnlarge
    · have hnreal : (n : ℝ) ≤ -4 := by exact_mod_cast hnlarge
      have hnonpos : 0 ≤ -(b + (n : ℝ)) := by nlinarith [hb.2]
      have hhalf : -(n : ℝ) / 2 ≤ -(b + (n : ℝ)) := by nlinarith [hb.2]
      have hsquare : (-(n : ℝ) / 2) ^ 2 ≤ (b + (n : ℝ)) ^ 2 := by
        calc
          (-(n : ℝ) / 2) ^ 2 ≤ (-(b + (n : ℝ))) ^ 2 :=
            (sq_le_sq₀ (by nlinarith) hnonpos).2 hhalf
          _ = (b + (n : ℝ)) ^ 2 := by ring
      nlinarith
    · have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hnlarge
      have hnonneg : 0 ≤ b + (n : ℝ) := by nlinarith [hb.1]
      have hhalf : (n : ℝ) / 2 ≤ b + (n : ℝ) := by nlinarith [hb.1]
      have hsquare : ((n : ℝ) / 2) ^ 2 ≤ (b + (n : ℝ)) ^ 2 :=
        (sq_le_sq₀ (by nlinarith) hnonneg).2 hhalf
      nlinarith

theorem summable_gaussian_vector_majorant {t : ℝ} (ht : 0 < t) :
    Summable (fun k : Fin 3 → ℤ =>
      (4 * π * t) ^ (-(3 : ℝ) / 2) *
        ∏ i, gaussianOneDimMajorant ((4 * t)⁻¹) (k i)) := by
  apply (summable_pi_fin3_prod (summable_gaussianOneDimMajorant (by positivity))
    (gaussianOneDimMajorant_nonneg)).mul_left

theorem gaussKernel_le_uniform_majorant {t : ℝ} (ht : 0 < t)
    {y : Fin 3 → ℝ} (hy : ∀ i, y i ∈ Set.Icc (-1 : ℝ) 2) (k : Fin 3 → ℤ) :
    ‖gaussKernel t (y + fun i => (k i : ℝ))‖ ≤
      (4 * π * t) ^ (-(3 : ℝ) / 2) *
        ∏ i, gaussianOneDimMajorant ((4 * t)⁻¹) (k i) := by
  rw [Real.norm_of_nonneg (gaussKernel_nonneg ht _), gaussKernel_eq_prod]
  have hpref : 0 ≤ (4 * π * t) ^ (-(3 : ℝ) / 2) := by positivity
  apply mul_le_mul_of_nonneg_left _ hpref
  apply Finset.prod_le_prod₀
  · intro i hi
    exact exp_nonneg _
  · intro i hi
    apply gaussian_exp_shift_le_majorant (by positivity) (hy i)

def heatKernelLift (t : ℝ) (y : Fin 3 → ℝ) : ℝ :=
  ∑' k : Fin 3 → ℤ, gaussKernel t (fun i => y i + (k i : ℝ))

theorem heatKernelLift_add_integer {t : ℝ} (m : Fin 3 → ℤ) (y : Fin 3 → ℝ) :
    heatKernelLift t (y + fun i => (m i : ℝ)) = heatKernelLift t y := by
  unfold heatKernelLift
  calc
    (∑' k : Fin 3 → ℤ, gaussKernel t
        (fun i => (y i + (m i : ℝ)) + (k i : ℝ))) =
        ∑' k : Fin 3 → ℤ, gaussKernel t
          (fun i => y i + (m i : ℝ) + (k i : ℝ)) := by
      apply tsum_congr
      intro k
      congr 1
    _ =
        ∑' k : Fin 3 → ℤ, gaussKernel t
          (fun i => y i + ((m i + k i : ℤ) : ℝ)) := by
      apply tsum_congr
      intro k
      congr 1
      funext i
      rw [Int.cast_add]
      ring
    _ = ∑' k : Fin 3 → ℤ, gaussKernel t (fun i => y i + (k i : ℝ)) := by
      simpa [Equiv.addRight, Int.cast_add, add_comm, add_left_comm, add_assoc] using
        (Equiv.addRight m).tsum_eq
          (fun k : Fin 3 → ℤ => gaussKernel t (fun i => y i + (k i : ℝ)))

theorem continuousOn_heatKernelLift {t : ℝ} (ht : 0 < t) :
    ContinuousOn (heatKernelLift t)
      (Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 2)) := by
  unfold heatKernelLift
  apply continuousOn_tsum
  · intro k
    exact (continuous_gaussKernel_fixed ht).comp
      (continuous_id.add continuous_const)
      |>.continuousOn
  · exact summable_gaussian_vector_majorant ht
  · intro k y hy
    exact gaussKernel_le_uniform_majorant ht (fun i =>
      (Set.mem_pi.mp hy) i (Set.mem_univ i)) k

theorem continuous_heatKernelLift {t : ℝ} (ht : 0 < t) :
    Continuous (heatKernelLift t) := by
  apply continuous_iff_continuousAt.2
  intro y
  let m : Fin 3 → ℤ := fun i => ⌊y i⌋
  let r : Fin 3 → ℝ := y - fun i => (m i : ℝ)
  have hr : ∀ i, r i ∈ Set.Ico (0 : ℝ) 1 := by
    intro i
    constructor
    · dsimp [r, m]
      change 0 ≤ y i - (⌊y i⌋ : ℝ)
      exact sub_nonneg.mpr (Int.floor_le (y i))
    · dsimp [r, m]
      change y i - (⌊y i⌋ : ℝ) < 1
      linarith [Int.lt_floor_add_one (y i)]
  have hrK : r ∈ Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 2) := by
    apply Set.mem_pi.mpr
    intro i hi
    exact ⟨by linarith [(hr i).1], by linarith [(hr i).2]⟩
  have hKnhds : Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 2) ∈ 𝓝 r := by
    let U : Set (Fin 3 → ℝ) := Set.pi Set.univ (fun _ : Fin 3 => Set.Ioo (-1 : ℝ) 2)
    have hUopen : IsOpen U := isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
    have hrU : r ∈ U := by
      apply Set.mem_pi.mpr
      intro i hi
      exact ⟨by linarith [(hr i).1], by linarith [(hr i).2]⟩
    apply Filter.mem_of_superset (hUopen.mem_nhds hrU)
    apply Set.pi_mono
    intro i hi z hz
    exact ⟨hz.1.le, hz.2.le⟩
  have hcr : ContinuousAt (heatKernelLift t) r :=
    (continuousOn_heatKernelLift ht r hrK).continuousAt hKnhds
  have hsub : ContinuousAt (fun z => heatKernelLift t (z - fun i => (m i : ℝ))) y :=
    hcr.comp (continuousAt_id.sub continuousAt_const)
  apply hsub.congr
  exact Filter.Eventually.of_forall (fun z => by
    have hz := heatKernelLift_add_integer (t := t) m
      (z - fun i => (m i : ℝ))
    calc
      heatKernelLift t (z - fun i => (m i : ℝ)) = heatKernelLift t
          ((z - fun i => (m i : ℝ)) + fun i => (m i : ℝ)) := hz.symm
      _ = heatKernelLift t z := by
            congr 1
            funext i
            simp [sub_eq_add_neg, add_assoc]
      )

theorem heatKernel_comp_torusProj_eq_lift {t : ℝ} (y : Fin 3 → ℝ) :
    heatKernel t (torusProj y) = heatKernelLift t y := by
  let r := torusRep (torusProj y)
  have hcoord : ∀ i, ∃ m : ℤ, y i = r i + (m : ℝ) := by
    intro i
    have hi : ((r i : ℝ) : UnitAddCircle) = (y i : UnitAddCircle) := by
      dsimp [r, torusRep, torusProj]
      exact AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ))
        (y := (y i : UnitAddCircle))
    have himem : r i - y i ∈ AddSubgroup.zmultiples (1 : ℝ) :=
      (QuotientAddGroup.eq_iff_sub_mem.mp hi)
    rcases AddSubgroup.mem_zmultiples_iff.mp himem with ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    have hm' : (m : ℝ) = r i - y i := by simpa using hm
    rw [Int.cast_neg]
    linarith
  choose m hm using hcoord
  have hym : y = r + fun i => (m i : ℝ) := by
    funext i
    exact hm i
  unfold heatKernel heatKernelLift
  rw [show torusRep (torusProj y) = r by rfl]
  calc
    (∑' k : Fin 3 → ℤ, gaussKernel t (r + fun i => (k i : ℝ))) =
        heatKernelLift t (r + fun i => (m i : ℝ)) :=
      (heatKernelLift_add_integer (t := t) m r).symm
    _ = heatKernelLift t y := by rw [hym]

theorem continuous_heatKernel_fixed {t : ℝ} (ht : 0 < t) :
    Continuous (heatKernel t) := by
  have hq : IsOpenQuotientMap torusProj := by
    change IsOpenQuotientMap (Pi.map (fun _ : Fin 3 => QuotientAddGroup.mk))
    exact IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  apply (hq.continuous_comp_iff).mp
  rw [show heatKernel t ∘ torusProj = heatKernelLift t by
    funext y; exact heatKernel_comp_torusProj_eq_lift y]
  exact continuous_heatKernelLift ht

theorem heatKernel_le_uniform_majorant {t : ℝ} (ht : 0 < t) (x : Torus3) :
    heatKernel t x ≤ ∑' k : Fin 3 → ℤ,
      (4 * π * t) ^ (-(3 : ℝ) / 2) *
        ∏ i, gaussianOneDimMajorant ((4 * t)⁻¹) (k i) := by
  have hy : ∀ i, torusRep x i ∈ Set.Ico (0 : ℝ) 1 := by
    intro i
    change (AddCircle.equivIco (1 : ℝ) 0 (x i) : ℝ) ∈ Set.Ico 0 1
    simpa using (AddCircle.equivIco (1 : ℝ) 0 (x i)).property
  have hycc : ∀ i, torusRep x i ∈ Set.Icc (-1 : ℝ) 2 := by
    intro i
    exact ⟨by linarith [(hy i).1], by linarith [(hy i).2]⟩
  have hf := summable_gaussKernel_shift ht (torusRep x) hy
  have hg := summable_gaussian_vector_majorant ht
  unfold heatKernel
  apply hf.tsum_le_tsum _ hg
  intro k
  have h := gaussKernel_le_uniform_majorant ht hycc k
  rw [Real.norm_of_nonneg (gaussKernel_nonneg ht _)] at h
  exact h

theorem bounded_heatKernel {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, ∀ x : Torus3, |heatKernel t x| ≤ C := by
  refine ⟨∑' k : Fin 3 → ℤ,
      (4 * π * t) ^ (-(3 : ℝ) / 2) *
        ∏ i, gaussianOneDimMajorant ((4 * t)⁻¹) (k i), ?_⟩
  intro x
  rw [abs_of_nonneg (heatKernel_nonneg ht x)]
  exact heatKernel_le_uniform_majorant ht x
  
end RegularityStructures

end
