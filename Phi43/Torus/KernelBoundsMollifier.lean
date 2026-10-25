/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KernelBoundsBasic
public import Phi43.Mollifier

/-!
# Quantitative support of a rescaled periodised mollifier

The compact support of a mollifier gives a support box independent of the scale.  After parabolic
rescaling, every nonzero summand of the spatial periodisation lies in the corresponding box of
width `ε²` in time and `ε` in each spatial coordinate.  These are the support estimates used by
the uniform singular-kernel bounds.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

namespace Phi43

theorem exists_mollifier_support_box (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ q ∈ tsupport ρ,
      |q.1| ≤ R ∧ ∀ i, |q.2 i| ≤ R := by
  have hK : IsCompact (tsupport ρ) := hρ.hasCompactSupport
  let h : ℝ × (Fin 3 → ℝ) → ℝ := fun q => |q.1| + ‖q.2‖
  have hcont : Continuous h := by
    fun_prop
  obtain ⟨A, hA⟩ := hK.bddAbove_image hcont.continuousOn
  refine ⟨max A 0, le_max_right A 0, ?_⟩
  intro q hq
  have hqA : h q ≤ A := hA ⟨q, hq, rfl⟩
  have hqnonneg : 0 ≤ h q := add_nonneg (abs_nonneg _) (norm_nonneg _)
  have hA0 : 0 ≤ max A 0 := le_max_right A 0
  constructor
  · exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hqA.trans (le_max_left A 0))
  · intro i
    have hi : ‖q.2 i‖ ≤ ‖q.2‖ := norm_le_pi_norm q.2 i
    have hi' : |q.2 i| ≤ h q := by
      simpa only [Real.norm_eq_abs] using hi.trans (le_add_of_nonneg_left (abs_nonneg _))
    exact hi'.trans (hqA.trans (le_max_left A 0))

theorem bounded_mollifier (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q, |ρ q| ≤ M := by
  have hK : IsCompact (tsupport ρ) := hρ.hasCompactSupport
  have hcont : Continuous (fun q : ℝ × (Fin 3 → ℝ) => ‖ρ q‖) :=
    hρ.contDiff.continuous.norm
  obtain ⟨A, hA⟩ := hK.bddAbove_image hcont.continuousOn
  refine ⟨max A 0, le_max_right A 0, ?_⟩
  intro q
  by_cases hq : q ∈ tsupport ρ
  · have hqA : ‖ρ q‖ ≤ A := hA ⟨q, hq, rfl⟩
    simpa only [Real.norm_eq_abs] using hqA.trans (le_max_left A 0)
  · rw [image_eq_zero_of_notMem_tsupport hq]
    simp [le_max_right A 0]

theorem rescale_support_box (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ q, rescale ρ ε q ≠ 0 →
      |q.1| ≤ R * ε ^ 2 ∧ ∀ i, |q.2 i| ≤ R * ε := by
  obtain ⟨R, hR, hbox⟩ := exists_mollifier_support_box ρ hρ
  refine ⟨R, hR, ?_⟩
  intro q hq
  have harg :
      (ε ^ (-2 : ℤ) * q.1, ε⁻¹ • q.2) ∈ tsupport ρ := by
    by_contra hnot
    have hzero := image_eq_zero_of_notMem_tsupport hnot
    apply hq
    unfold rescale
    rw [hzero, mul_zero]
  have htime := (hbox _ harg).1
  have hspatial := (hbox _ harg).2
  have hscale2 : 0 < ε ^ (-2 : ℤ) := zpow_pos hε _
  have hscale1 : 0 < ε⁻¹ := inv_pos.mpr hε
  constructor
  · have hmul : ε ^ (-2 : ℤ) * |q.1| ≤ R := by
      simpa only [abs_mul, abs_of_pos hscale2] using htime
    calc
      |q.1| = 1 * |q.1| := by rw [one_mul]
      _ = (ε ^ (-2 : ℤ) * ε ^ 2) * |q.1| := by
        have hpow : ε ^ (-2 : ℤ) * ε ^ 2 = 1 := by
          rw [show ε ^ 2 = ε ^ (2 : ℤ) by norm_num]
          rw [← zpow_add₀ (ne_of_gt hε)]
          norm_num
        rw [hpow]
      _ = ε ^ 2 * (ε ^ (-2 : ℤ) * |q.1|) := by ac_rfl
      _ ≤ R * ε ^ 2 := by
        simpa only [mul_comm] using
          (mul_le_mul_of_nonneg_left hmul (sq_nonneg ε))
  · intro i
    have hi := hspatial i
    have hmul : ε⁻¹ * |q.2 i| ≤ R := by
      change |ε⁻¹ * q.2 i| ≤ R at hi
      simpa only [abs_mul, abs_of_pos hscale1] using hi
    calc
      |q.2 i| = ε * (ε⁻¹ * |q.2 i|) := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hε), one_mul]
      _ ≤ R * ε := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hmul hε.le

theorem periodise_uniform_bound (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
      ∀ z : SpaceTime, |periodise ρ ε z| ≤ C * ε ^ (-5 : ℤ) := by
  obtain ⟨M, hM, hMb⟩ := bounded_mollifier ρ hρ
  obtain ⟨R, hR, hbox⟩ := exists_mollifier_support_box ρ hρ
  let N : ℤ := ⌈R + 1⌉
  let Sset : Set (Fin 3 → ℤ) :=
    Set.pi Set.univ (fun _ : Fin 3 => (Finset.Icc (-N) N : Set ℤ))
  have hN : R + 1 ≤ (N : ℝ) := by
    exact_mod_cast (Int.le_ceil (R + 1))
  have hSfinite : Sset.Finite := by
    apply Set.Finite.pi
    intro i
    exact (Finset.Icc (-N) N).finite_toSet
  let s : Finset (Fin 3 → ℤ) := hSfinite.toFinset
  let C : ℝ := s.card * M
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro ε hε hε1 z
    have hzero : ∀ k ∉ s,
        rescale ρ ε (z.1, torusRep z.2 + fun i => (k i : ℝ)) = 0 := by
      intro k hk
      by_contra hne
      have harg :
          (ε ^ (-2 : ℤ) * z.1,
            ε⁻¹ • (torusRep z.2 + fun i => (k i : ℝ))) ∈ tsupport ρ := by
        by_contra hnot
        have hρzero := image_eq_zero_of_notMem_tsupport hnot
        apply hne
        unfold rescale
        rw [hρzero, mul_zero]
      have hcoord := (hbox _ harg).2
      have hkS : k ∈ s := by
        apply hSfinite.mem_toFinset.mpr
        apply Set.mem_pi.mpr
        intro i hi
        apply Finset.mem_Icc.mpr
        have hri := torusRep_mem_Ico z.2 i
        have hki : |torusRep z.2 i + (k i : ℝ)| ≤ R := by
          have hki' := hcoord i
          have hki'' : |torusRep z.2 i + (k i : ℝ)| ≤ R * ε := by
            have hmul : ε * |ε⁻¹ *
                (torusRep z.2 i + (k i : ℝ))| ≤ ε * R :=
              mul_le_mul_of_nonneg_left hki' hε.le
            have hident : ε * |ε⁻¹ *
                (torusRep z.2 i + (k i : ℝ))| =
                |torusRep z.2 i + (k i : ℝ)| := by
              rw [abs_mul, abs_of_pos (inv_pos.mpr hε)]
              rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hε), one_mul]
            rw [hident] at hmul
            simpa only [mul_comm] using hmul
          simpa only [mul_comm] using hki''.trans (mul_le_of_le_one_right hR (by linarith))
        have hki_le : (k i : ℝ) ≤ R := by
          have hupper := (abs_le.mp hki).2
          linarith [hri.1]
        have hki_ge : -(R + 1) ≤ (k i : ℝ) := by
          have hlower := (abs_le.mp hki).1
          linarith [hri.2]
        have hupperN : (k i : ℝ) ≤ (N : ℝ) := by
          linarith
        have hlowerN : (-(N : ℝ)) ≤ (k i : ℝ) := by
          linarith
        constructor
        · exact_mod_cast hlowerN
        · exact_mod_cast hupperN
      exact hk hkS
    have hsum : periodise ρ ε z =
        ∑ k ∈ s, rescale ρ ε (z.1, torusRep z.2 + fun i => (k i : ℝ)) := by
      unfold periodise
      rw [tsum_eq_sum]
      intro k hk
      exact hzero k hk
    have hterm : ∀ k : Fin 3 → ℤ,
        |rescale ρ ε (z.1, torusRep z.2 + fun i => (k i : ℝ))| ≤
          M * ε ^ (-5 : ℤ) := by
      intro k
      rw [rescale, abs_mul, abs_of_pos (zpow_pos hε _)]
      exact (mul_le_mul_of_nonneg_left (hMb _) (zpow_pos hε _).le).trans_eq
        (by ring)
    rw [hsum]
    have hsum_norm := norm_sum_le s
      (fun k => rescale ρ ε (z.1, torusRep z.2 + fun i => (k i : ℝ)))
    calc
      |∑ k ∈ s, rescale ρ ε (z.1, torusRep z.2 + fun i => (k i : ℝ))| ≤
          ∑ k ∈ s, |rescale ρ ε (z.1, torusRep z.2 + fun i => (k i : ℝ))| := by
            simpa only [Real.norm_eq_abs] using hsum_norm
      _ ≤ ∑ _k ∈ s, M * ε ^ (-5 : ℤ) := by
        exact Finset.sum_le_sum fun k hk => hterm k
      _ = C * ε ^ (-5 : ℤ) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        dsimp [C]
        ring

theorem periodise_eq_finset_sum_uniform (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    ∃ s : Finset (Fin 3 → ℤ), ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
      ∀ z : SpaceTime, (periodise ρ ε z =
        ∑ k ∈ s, rescale ρ ε (z.1, torusRep z.2 + fun i => (k i : ℝ))) ∧
        (∀ k ∉ s, rescale ρ ε (z.1, torusRep z.2 + fun i => (k i : ℝ)) = 0) := by
  obtain ⟨R, hR, hbox⟩ := exists_mollifier_support_box ρ hρ
  let N : ℤ := ⌈R + 1⌉
  let Sset : Set (Fin 3 → ℤ) :=
    Set.pi Set.univ (fun _ : Fin 3 => (Finset.Icc (-N) N : Set ℤ))
  have hN : R + 1 ≤ (N : ℝ) := by
    exact_mod_cast (Int.le_ceil (R + 1))
  have hSfinite : Sset.Finite := by
    apply Set.Finite.pi
    intro i
    exact (Finset.Icc (-N) N).finite_toSet
  let s : Finset (Fin 3 → ℤ) := hSfinite.toFinset
  refine ⟨s, ?_⟩
  intro ε hε hε1 z
  have hzero : ∀ k ∉ s,
      rescale ρ ε (z.1, torusRep z.2 + fun i => (k i : ℝ)) = 0 := by
    intro k hk
    by_contra hne
    have harg :
        (ε ^ (-2 : ℤ) * z.1,
          ε⁻¹ • (torusRep z.2 + fun i => (k i : ℝ))) ∈ tsupport ρ := by
      by_contra hnot
      have hρzero := image_eq_zero_of_notMem_tsupport hnot
      apply hne
      unfold rescale
      rw [hρzero, mul_zero]
    have hcoord := (hbox _ harg).2
    have hkS : k ∈ s := by
      apply hSfinite.mem_toFinset.mpr
      apply Set.mem_pi.mpr
      intro i hi
      apply Finset.mem_Icc.mpr
      have hri := torusRep_mem_Ico z.2 i
      have hki : |torusRep z.2 i + (k i : ℝ)| ≤ R := by
        have hki' := hcoord i
        have hki'' : |torusRep z.2 i + (k i : ℝ)| ≤ R * ε := by
          have hmul : ε * |ε⁻¹ *
              (torusRep z.2 i + (k i : ℝ))| ≤ ε * R :=
            mul_le_mul_of_nonneg_left hki' hε.le
          have hident : ε * |ε⁻¹ *
              (torusRep z.2 i + (k i : ℝ))| =
              |torusRep z.2 i + (k i : ℝ)| := by
            rw [abs_mul, abs_of_pos (inv_pos.mpr hε)]
            rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hε), one_mul]
          rw [hident] at hmul
          simpa only [mul_comm] using hmul
        simpa only [mul_comm] using hki''.trans
          (mul_le_of_le_one_right hR (by linarith))
      have hki_le : (k i : ℝ) ≤ R := by
        have hupper := (abs_le.mp hki).2
        linarith [hri.1]
      have hki_ge : -(R + 1) ≤ (k i : ℝ) := by
        have hlower := (abs_le.mp hki).1
        linarith [hri.2]
      have hupperN : (k i : ℝ) ≤ (N : ℝ) := by
        linarith
      have hlowerN : (-(N : ℝ)) ≤ (k i : ℝ) := by
        linarith
      constructor
      · exact_mod_cast hlowerN
      · exact_mod_cast hupperN
    exact hk hkS
  exact ⟨by
    unfold periodise
    rw [tsum_eq_sum]
    intro k hk
    exact hzero k hk, hzero⟩

end Phi43

end RegularityStructures

end
