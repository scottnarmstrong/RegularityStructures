/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decay.Kernel
public import RegularityStructures.Analysis.Heat.Decomposition.Support
public import RegularityStructures.Analysis.Heat.Causal.Support
public import RegularityStructures.Analysis.Heat.Schauder.TaylorDeriv

/-!
# Global spatial decay of derivatives of the smooth remainders

For `heatRemainder` and `annRemainderC N`, every derivative `D^k` satisfies
`|D^k f (t, x)| ≤ C (1 + |x|²)^{-m}` for all `t ≤ T₀` and all `x`
(`exists_abs_lineIter_heatRemainder_le`, `exists_abs_lineIter_annRemainderC_le`).  Both functions
vanish for `t ≤ 0` together with all their derivatives; for `|x| ≥ 1` the remainder agrees with the
heat kernel near the point (the cutoff `1 - dyadicCutoff (8 N)` equals `1` for `N ≥ 1/4`), and the
region `|x| ≤ 1`, `0 ≤ t ≤ T₀` is compact.
-/

public section

open scoped ContDiff
open Filter Topology

namespace RegularityStructures

/-- Glue a decay bound for `|x| ≥ 1` with a compactness bound on `{|x| ≤ 1, 0 ≤ t ≤ T₀}`. -/
theorem exists_abs_lineIter_le_of_decay {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (L : List ParabolicSpace) (m : ℕ) {T₀ : ℝ}
    (h0 : ∀ z : ParabolicSpace, z.1 ≤ 0 → lineIter L f z = 0)
    (hdec : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ParabolicSpace, z.1 ≤ T₀ → 1 ≤ sqNorm3 z.2 →
      |lineIter L f z| ≤ C * (sqNorm3 z.2)⁻¹ ^ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ParabolicSpace, z.1 ≤ T₀ →
      |lineIter L f z| ≤ C * (1 + sqNorm3 z.2)⁻¹ ^ m := by
  obtain ⟨C₂, hC₂, h2⟩ := hdec
  have hK : IsCompact (Set.Icc (0 : ℝ) T₀ ×ˢ Metric.closedBall (0 : Fin 3 → ℝ) 1) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn
    (contDiff_lineIter hf L).continuous.continuousOn
  refine ⟨(max C₁ 0 + C₂) * 2 ^ m, by positivity, fun z hzT => ?_⟩
  set S := sqNorm3 z.2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hq : 0 < (1 + S)⁻¹ := inv_pos.2 (by linarith)
  have hq0 : 0 ≤ (1 + S)⁻¹ ^ m := by positivity
  by_cases hS1 : 1 ≤ S
  · have hSpos : 0 < S := by linarith
    have hinv : S⁻¹ ≤ 2 * (1 + S)⁻¹ := by
      have e : 2 * (1 + S)⁻¹ = (2⁻¹ * (1 + S))⁻¹ := by rw [mul_inv, inv_inv]
      rw [e]
      exact inv_anti₀ (by positivity) (by linarith)
    have h3 : S⁻¹ ^ m ≤ 2 ^ m * (1 + S)⁻¹ ^ m := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (inv_nonneg.2 hSpos.le) hinv m
    calc |lineIter L f z| ≤ C₂ * S⁻¹ ^ m := h2 z hzT hS1
      _ ≤ C₂ * (2 ^ m * (1 + S)⁻¹ ^ m) := mul_le_mul_of_nonneg_left h3 hC₂
      _ ≤ (max C₁ 0 + C₂) * 2 ^ m * (1 + S)⁻¹ ^ m := by
        have : 0 ≤ max C₁ 0 * (2 ^ m * (1 + S)⁻¹ ^ m) := by positivity
        nlinarith
  · push Not at hS1
    by_cases ht : z.1 ≤ 0
    · rw [h0 z ht, abs_zero]
      positivity
    · push Not at ht
      have hmem : z ∈ Set.Icc (0 : ℝ) T₀ ×ˢ Metric.closedBall (0 : Fin 3 → ℝ) 1 := by
        refine ⟨⟨ht.le, hzT⟩, ?_⟩
        rw [mem_closedBall_zero_iff]
        refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
        rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one]
        exact (Finset.single_le_sum (f := fun j => z.2 j ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_univ i)).trans hS1.le
      have hb := (hC₁ z hmem).trans (le_max_left C₁ 0)
      rw [Real.norm_eq_abs] at hb
      have h2q : 1 ≤ 2 * (1 + S)⁻¹ := by
        rw [← div_eq_mul_inv, one_le_div (by linarith)]
        linarith
      have h3 : 1 ≤ 2 ^ m * (1 + S)⁻¹ ^ m := by
        rw [← mul_pow]
        exact one_le_pow₀ h2q
      have h4 : 0 ≤ max C₁ 0 := le_max_right _ _
      calc |lineIter L f z| ≤ max C₁ 0 := hb
        _ ≤ max C₁ 0 * (2 ^ m * (1 + S)⁻¹ ^ m) := le_mul_of_one_le_right h4 h3
        _ ≤ (max C₁ 0 + C₂) * 2 ^ m * (1 + S)⁻¹ ^ m := by
          have : 0 ≤ C₂ * (2 ^ m * (1 + S)⁻¹ ^ m) := by positivity
          nlinarith

theorem heatRemainder_eq_heatKernelR4_of_lt {z : ParabolicSpace}
    (h : 1 / 4 < smoothParabolicNorm z) : heatRemainder z = heatKernelR4 z := by
  have : (2 : ℝ) ≤ 2 ^ 3 * smoothParabolicNorm z := by linarith
  simp [heatRemainder, dyadicCutoff_eq_zero this]

theorem one_le_smoothParabolicNorm_of_one_le {z : ParabolicSpace} (h : 1 ≤ sqNorm3 z.2) :
    1 ≤ smoothParabolicNorm z := by
  by_contra hlt
  push Not at hlt
  have h4 := smoothParabolicNorm_pow_four z
  have h1 : smoothParabolicNorm z ^ 4 < 1 :=
    pow_lt_one₀ (smoothParabolicNorm_nonneg z) hlt (by norm_num)
  nlinarith [sq_nonneg z.1]

theorem lineIter_heatRemainder_eq_zero_of_nonpos (L : List ParabolicSpace) {z : ParabolicSpace}
    (hz : z.1 ≤ 0) : lineIter L heatRemainder z = 0 :=
  lineIter_eq_zero_of_nonpos contDiff_heatRemainder
    (fun _ h => heatRemainder_eq_zero_of_nonpos h) L hz

/-- Derivatives of the smooth heat remainder decay faster than any power of `1 + |x|²`,
uniformly for `t ≤ T₀`. -/
theorem exists_abs_lineIter_heatRemainder_le_of_list (L : List ParabolicSpace) (m : ℕ) {T₀ : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ParabolicSpace, z.1 ≤ T₀ →
      |lineIter L heatRemainder z| ≤ C * (1 + sqNorm3 z.2) ⁻¹ ^ m := by
  refine exists_abs_lineIter_le_of_decay contDiff_heatRemainder L m
    (fun z hz => lineIter_heatRemainder_eq_zero_of_nonpos L hz) ?_
  obtain ⟨C, hC, h⟩ := exists_abs_lineIter_heatKernelR4_le_of_list L m (T₀ := T₀)
  refine ⟨C, hC, fun z hzT hS => ?_⟩
  have hU : IsOpen {w : ParabolicSpace | 1 / 4 < smoothParabolicNorm w} :=
    isOpen_lt continuous_const continuous_smoothParabolicNorm
  have := lineIter_congr_of_isOpen hU (fun w hw => heatRemainder_eq_heatKernelR4_of_lt hw) L z
    (by
      show 1 / 4 < smoothParabolicNorm z
      linarith [one_le_smoothParabolicNorm_of_one_le hS])
  rw [this]
  exact h z hzT hS

/-- A smooth compactly supported function has derivatives with arbitrary spatial decay. -/
theorem exists_abs_lineIter_le_of_hasCompactSupport {f : ParabolicSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (L : List ParabolicSpace) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ParabolicSpace, |lineIter L f z| ≤ C * (1 + sqNorm3 z.2) ⁻¹ ^ m := by
  have hcs := hasCompactSupport_lineIter hc L
  have hcont := (contDiff_lineIter hf L).continuous
  obtain ⟨B, hB⟩ := hcs.isCompact.exists_bound_of_continuousOn hcont.continuousOn
  obtain ⟨R, hR⟩ := hcs.isCompact.exists_bound_of_continuousOn
    (contDiff_sqNorm3.continuous.comp continuous_snd).continuousOn
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hR0 : 0 ≤ max R 0 := le_max_right _ _
  refine ⟨max B 0 * (1 + max R 0) ^ m, by positivity, fun z => ?_⟩
  by_cases hz : z ∈ tsupport (lineIter L f)
  · have hS : sqNorm3 z.2 ≤ max R 0 := by
      have := hR z hz
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_left _ _))
    have hS0 : 0 ≤ sqNorm3 z.2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hb := (hB z hz).trans (le_max_left B 0)
    rw [Real.norm_eq_abs] at hb
    have h1 : 1 ≤ (1 + max R 0) ^ m * (1 + sqNorm3 z.2)⁻¹ ^ m := by
      rw [← mul_pow]
      refine one_le_pow₀ ?_
      rw [← div_eq_mul_inv, one_le_div (by linarith)]
      linarith
    calc |lineIter L f z| ≤ max B 0 := hb
      _ ≤ max B 0 * ((1 + max R 0) ^ m * (1 + sqNorm3 z.2)⁻¹ ^ m) :=
        le_mul_of_one_le_right hB0 h1
      _ = _ := by ring
  · have hS0 : 0 ≤ sqNorm3 z.2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [image_eq_zero_of_notMem_tsupport hz, abs_zero]
    exact mul_nonneg (by positivity) (pow_nonneg (inv_nonneg.2 (by linarith)) _)

theorem exists_abs_lineIter_annBumpC_le (N : ℕ) (L : List ParabolicSpace) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ParabolicSpace, |lineIter L (annBumpC N) z| ≤
      C * (1 + sqNorm3 z.2) ⁻¹ ^ m :=
  exists_abs_lineIter_le_of_hasCompactSupport (contDiff_annBumpC N)
    (HasCompactSupport.intro (isCompact_parabolicNorm_le 1) fun _ hz =>
      annBumpC_eq_zero (not_le.1 hz)) L m

/-- Derivatives of the causal remainder `annRemainderC N` decay faster than any power of
`1 + |x|²`, uniformly for `t ≤ T₀`.  (It vanishes, with all derivatives, for `t ≤ 0`:
`lineIter_multiDirs_annRemainderC_eq_zero`.) -/
theorem exists_abs_lineIter_annRemainderC_le_of_list (N : ℕ) (L : List ParabolicSpace) (m : ℕ)
    {T₀ : ℝ} : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ParabolicSpace, z.1 ≤ T₀ →
      |lineIter L (annRemainderC N) z| ≤ C * (1 + sqNorm3 z.2) ⁻¹ ^ m := by
  obtain ⟨C₁, hC₁, h1⟩ := exists_abs_lineIter_heatRemainder_le_of_list L m (T₀ := T₀)
  obtain ⟨C₂, hC₂, h2⟩ := exists_abs_lineIter_annBumpC_le N L m
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun z hz => ?_⟩
  have hsum := congrFun (lineIter_add contDiff_heatRemainder (contDiff_annBumpC N) L) z
  have e : lineIter L (annRemainderC N) z = lineIter L heatRemainder z + lineIter L (annBumpC N) z :=
    hsum
  rw [e]
  calc |lineIter L heatRemainder z + lineIter L (annBumpC N) z|
      ≤ |lineIter L heatRemainder z| + |lineIter L (annBumpC N) z| := abs_add_le _ _
    _ ≤ C₁ * (1 + sqNorm3 z.2)⁻¹ ^ m + C₂ * (1 + sqNorm3 z.2)⁻¹ ^ m :=
      add_le_add (h1 z hz) (h2 z)
    _ = _ := by ring

end RegularityStructures

end
