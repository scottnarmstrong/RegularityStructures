/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KernelBoundsGeometry
public import Phi43.Torus.KernelBoundsMollifier
public import Phi43.Mollifier

/-!
# Parabolic support of a periodised mollifier

The support of the periodised rescaling is contained in a parabolic ball of radius `O(ε)`.  The
only quotient input is that the centered representative is the shortest coordinate representative
among all integer translates.
-/

@[expose] public noncomputable section

open Real Set

namespace RegularityStructures

namespace Phi43

theorem periodise_support_parabolic_bound (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    ∃ B : ℝ, 0 < B ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ z : SpaceTime,
      periodise ρ ε z ≠ 0 → torusParabolicSize z ≤ B * ε := by
  obtain ⟨R, hR, hbox⟩ := exists_mollifier_support_box ρ hρ
  let B : ℝ := 1 + √R + 2 * R
  have hB : 0 < B := by
    dsimp [B]
    nlinarith [Real.sqrt_nonneg R]
  refine ⟨B, hB, ?_⟩
  intro ε hε hε1 z hP
  obtain ⟨s, hs⟩ := periodise_eq_finset_sum_uniform ρ hρ
  have hsome : ∃ k : Fin 3 → ℤ,
      rescale ρ ε (z.1, torusRep z.2 + fun i => (k i : ℝ)) ≠ 0 := by
    by_contra h
    push Not at h
    have hsum := (hs hε hε1 z).1
    apply hP
    rw [hsum]
    simp [h]
  obtain ⟨k, hk⟩ := hsome
  have harg :
      (ε ^ (-2 : ℤ) * z.1,
        ε⁻¹ • (torusRep z.2 + fun i => (k i : ℝ))) ∈ tsupport ρ := by
    by_contra hnot
    have hzero := image_eq_zero_of_notMem_tsupport hnot
    apply hk
    unfold rescale
    rw [hzero, mul_zero]
  have htime := (hbox _ harg).1
  have hspace := (hbox _ harg).2
  have htime' : |z.1| ≤ R * ε ^ 2 := by
    have hmul : ε ^ (-2 : ℤ) * |z.1| ≤ R := by
      simpa only [abs_mul, abs_of_pos (zpow_pos hε _)] using htime
    calc
      |z.1| = (ε ^ (-2 : ℤ) * ε ^ 2) * |z.1| := by
        have hpow : ε ^ (-2 : ℤ) * ε ^ 2 = 1 := by
          rw [show ε ^ 2 = ε ^ (2 : ℤ) by norm_num, ← zpow_add₀ (ne_of_gt hε)]
          norm_num
        rw [hpow, one_mul]
      _ = ε ^ 2 * (ε ^ (-2 : ℤ) * |z.1|) := by ring
      _ ≤ ε ^ 2 * R := mul_le_mul_of_nonneg_left hmul (sq_nonneg ε)
      _ = R * ε ^ 2 := by ring
  have hcenter : ∀ i, |torusCenteredRep z.2 i| ≤ R * ε := by
    obtain ⟨m, hm⟩ := torusRep_eq_centered_add_int z.2
    intro i
    have hi := hspace i
    have hi' : |torusRep z.2 i + (k i : ℝ)| ≤ R * ε := by
      have hmul : ε * |ε⁻¹ * (torusRep z.2 i + (k i : ℝ))| ≤ ε * R :=
        mul_le_mul_of_nonneg_left hi hε.le
      have heq : ε * |ε⁻¹ * (torusRep z.2 i + (k i : ℝ))| =
          |torusRep z.2 i + (k i : ℝ)| := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr hε)]
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hε), one_mul]
      rw [heq] at hmul
      simpa only [mul_comm] using hmul
    have hsq := sq_centered_add_int_ge (torusCenteredRep_mem_Icc z.2 i) (m i + k i)
    have heq : torusCenteredRep z.2 i + ((m i + k i : ℤ) : ℝ) =
        torusRep z.2 i + (k i : ℝ) := by
      rw [hm]
      simp only [Pi.add_apply, Int.cast_add]
      ring
    rw [heq] at hsq
    have hsq' : |torusCenteredRep z.2 i| ^ 2 ≤
        |torusRep z.2 i + (k i : ℝ)| ^ 2 := by
      calc
        |torusCenteredRep z.2 i| ^ 2 = torusCenteredRep z.2 i ^ 2 :=
          sq_abs _
        _ ≤ (torusRep z.2 i + (k i : ℝ)) ^ 2 := hsq
        _ = |torusRep z.2 i + (k i : ℝ)| ^ 2 := (sq_abs _).symm
    exact (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp hsq' |>.trans hi'
  have hspatial : torusSpatialNorm z.2 ≤ 2 * R * ε := by
    have hsum : sqNorm3 (torusCenteredRep z.2) ≤ 3 * (R * ε) ^ 2 := by
      unfold sqNorm3
      calc
        ∑ i, torusCenteredRep z.2 i ^ 2 ≤ ∑ _i : Fin 3, (R * ε) ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          rw [← sq_abs]
          exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hR hε.le)).2 (hcenter i)
        _ = 3 * (R * ε) ^ 2 := by simp
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (by positivity) hε.le)).mp
    rw [Real.sq_sqrt]
    · nlinarith [hsum]
    · exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have htimeS : √|z.1| ≤ √R * ε := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hε.le)).mp
    rw [Real.sq_sqrt (abs_nonneg _), mul_pow, Real.sq_sqrt hR]
    nlinarith [htime']
  unfold torusParabolicSize
  dsimp [B]
  nlinarith [torusSpatialNorm_nonneg z.2, Real.sqrt_nonneg R]

end Phi43

end RegularityStructures

end
