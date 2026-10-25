/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.SingularPart
public import Phi43.Potential.PairingSum2
public import Phi43.Potential.KernelTail
public import Phi43.Potential.TailTest

/-!
# The kernel `χ (K - G^m)` as a sum of scaled test functions

For `w ≠ 0`, with `K = ∑ₙ annShellC N n`, `G` the heat kernel, `R = annRemainderC N`,
`ψ_b = annBumpC N`, `G = ∑ₙ heatShell n + R - ψ_b`, `K = G - R`:

  `K - e^{-t} G = ∑ₙ (1 - e^{-t}) heatShell n - (1 - e^{-t}) ψ_b - e^{-t} R`.

`potK1 N` is `χ` times this expression, written as the sum of
* the singular shells `potSing 2` (for `n ≥ 2` the cutoff `χ` is `1` on the support),
* three smooth unit kernels (`n = 0, 1` and `ψ_b`),
* the spatial tail `-χ e^{-t} R` (`IsTailKernel`).
Each part is a family of scaled test functions, so the pairing with the noise coordinate is bounded
(`abs_potConv_potK1_le`).
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace RegularityStructures.Potential

/-- `χ(t) (1 - e^{-t}) heatShell n`, for the finitely many shells `n < 2`. -/
def potUnit (n : ℕ) (w : ParabolicSpace) : ℝ := potCutoff w.1 * potShellKernel n w

/-- `-χ(t) (1 - e^{-t}) ψ_b`. -/
def potUnitBump (N : ℕ) (w : ParabolicSpace) : ℝ :=
  -(potCutoff w.1 * (1 - Real.exp (-w.1)) * annBumpC N w)

/-- `-χ(t) e^{-t} R`. -/
def potTailPhi (N : ℕ) (w : ParabolicSpace) : ℝ :=
  -(potCutoff w.1 * Real.exp (-w.1) * annRemainderC N w)

/-- The smooth-and-singular decomposition of `χ (K - G^m)`. -/
def potK1 (N : ℕ) (w : ParabolicSpace) : ℝ :=
  potSing 2 w + (potUnit 0 w + potUnit 1 w + potUnitBump N w) + potTailPhi N w

end RegularityStructures.Potential

end

public section

open Set

namespace RegularityStructures.Potential

theorem isUnitKernel_potUnit (n : ℕ) : IsUnitKernel (potUnit n) where
  smooth := (contDiff_potCutoff.comp contDiff_fst).mul (contDiff_potShellKernel n)
  supp w hw := by
    have : heatShell n w = 0 := heatShell_eq_zero (lt_of_le_of_lt
      (pow_le_one₀ (by norm_num) (by norm_num)) hw)
    simp [potUnit, potShellKernel, this]

theorem isUnitKernel_potUnitBump (N : ℕ) : IsUnitKernel (potUnitBump N) where
  smooth := (((contDiff_potCutoff.comp contDiff_fst).mul
    (contDiff_const.sub (Real.contDiff_exp.comp contDiff_fst.neg))).mul (contDiff_annBumpC N)).neg
  supp w hw := by simp [potUnitBump, annBumpC_eq_zero hw]

/-- The time profile `E(w) = χ(w₀) e^{-w₀}`. -/
@[expose] noncomputable def potE (w : ParabolicSpace) : ℝ := potCutoff w.1 * Real.exp (-w.1)

theorem contDiff_potE : ContDiff ℝ ∞ potE :=
  (contDiff_potCutoff.comp contDiff_fst).mul (Real.contDiff_exp.comp contDiff_fst.neg)

theorem exists_bound_potE :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ 4, ∀ w : ParabolicSpace, 0 ≤ w.1 → w.1 ≤ 1 / 4 →
      ‖iteratedFDeriv ℝ j potE w‖ ≤ C := by
  have hE₁ : ContDiff ℝ ∞ (fun t : ℝ => potCutoff t * Real.exp (-t)) :=
    contDiff_potCutoff.mul (Real.contDiff_exp.comp contDiff_neg)
  have e : potE = (fun t : ℝ => potCutoff t * Real.exp (-t)) ∘
      (ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)) := rfl
  have hb : ∀ j : ℕ, ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) (1 / 4),
      ‖iteratedFDeriv ℝ j (fun t : ℝ => potCutoff t * Real.exp (-t)) t‖ ≤ C := by
    intro j
    exact isCompact_Icc.exists_bound_of_continuousOn
      ((hE₁.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).continuousOn)
  choose C hC using hb
  refine ⟨∑ j ∈ Finset.range 5, |C j|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    fun j hj w h0 h1 => ?_⟩
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right (n := j) (ContinuousLinearMap.fst ℝ ℝ
    (Fin 3 → ℝ)) (hE₁.of_le (by exact_mod_cast le_top)) w (by exact_mod_cast le_refl j)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hL : ‖ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)‖ ≤ 1 := ContinuousLinearMap.norm_fst_le _ _ _
  have hp : ∏ _i : Fin j, ‖ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)‖ ≤ 1 := by
    rw [Finset.prod_const]; exact pow_le_one₀ (norm_nonneg _) hL
  have h2 : ‖iteratedFDeriv ℝ j (fun t : ℝ => potCutoff t * Real.exp (-t))
      ((ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)) w)‖ ≤ ∑ j ∈ Finset.range 5, |C j| := by
    have h3 := hC j w.1 ⟨h0, h1⟩
    have h4 : |C j| ≤ ∑ j ∈ Finset.range 5, |C j| :=
      Finset.single_le_sum (f := fun j => |C j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
    exact (h3.trans (le_abs_self _)).trans h4
  calc _ ≤ ‖iteratedFDeriv ℝ j (fun t : ℝ => potCutoff t * Real.exp (-t))
        ((ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)) w)‖ * 1 := by gcongr
    _ ≤ _ := by rw [mul_one]; exact h2

theorem iteratedFDeriv_annRemainderC_eq_zero_of_neg (N k : ℕ) {w : ParabolicSpace}
    (hw : w.1 < 0) : iteratedFDeriv ℝ k (annRemainderC N) w = 0 := by
  have hs : tsupport (annRemainderC N) ⊆ {w : ParabolicSpace | 0 ≤ w.1} := by
    refine closure_minimal (fun x hx => ?_) (isClosed_le continuous_const continuous_fst)
    by_contra hc
    exact hx (annRemainderC_eq_zero_of_nonpos N (not_le.1 hc).le)
  by_contra hne
  exact absurd (hs (support_iteratedFDeriv_subset (𝕜 := ℝ) (n := k) hne)) (not_le.2 hw)

theorem exists_isTailKernel_potTailPhi (N : ℕ) : ∃ B : ℝ, IsTailKernel (potTailPhi N) B := by
  obtain ⟨CE, hCE0, hCE⟩ := exists_bound_potE
  obtain ⟨BR, hBR0, hBR⟩ := exists_remDecay_lineIter_annRemainderC N 0 4 (1 / 4)
  rw [multiDirs_zero, lineIter_nil] at hBR
  have hR := contDiff_annRemainderC N
  have e : potTailPhi N = -(fun w => potE w * annRemainderC N w) := by
    funext w; simp [potTailPhi, potE, mul_assoc]
  refine ⟨16 * CE * BR + 1, ?_⟩
  refine ⟨?_, by positivity, fun w hw => ?_, fun i hi w hw => ?_⟩
  · rw [e]; exact (contDiff_potE.mul hR).neg
  · rcases hw with hw | hw
    · simp [potTailPhi, annRemainderC_eq_zero_of_nonpos N hw]
    · simp [potTailPhi, potCutoff_eq_zero hw]
  · rw [e]
    have hmul : ContDiff ℝ ∞ (fun w : ParabolicSpace => potE w * annRemainderC N w) :=
      contDiff_potE.mul hR
    rw [iteratedFDeriv_neg_apply, norm_neg]
    refine (_root_.norm_iteratedFDeriv_mul_le (N := i) (contDiff_potE.of_le
      (by exact_mod_cast le_top)) (hR.of_le (by exact_mod_cast le_top)) w
      (by exact_mod_cast le_refl i)).trans ?_
    have hrw := remWt_nonneg w.2
    by_cases hneg : w.1 < 0
    · have : ∀ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j potE w‖ *
          ‖iteratedFDeriv ℝ (i - j) (annRemainderC N) w‖ = 0 := by
        intro j _
        rw [iteratedFDeriv_annRemainderC_eq_zero_of_neg N _ hneg]; simp
      rw [Finset.sum_eq_zero this]
      positivity
    · push Not at hneg
      have hb : ∀ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j potE w‖ *
          ‖iteratedFDeriv ℝ (i - j) (annRemainderC N) w‖ ≤
          i.choose j * (CE * (BR * remWt w.2)) := by
        intro j hj
        have hj' : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left (mul_le_mul (hCE j (hj'.trans hi) w hneg hw)
          (hBR (i - j) (by omega) w hw) (norm_nonneg _) hCE0) (Nat.cast_nonneg _)
      refine (Finset.sum_le_sum hb).trans ?_
      rw [← Finset.sum_mul]
      have h2 : ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) = 2 ^ i := by
        exact_mod_cast Nat.sum_range_choose i
      rw [h2]
      have h3 : (2 : ℝ) ^ i ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hi
      have hp : 0 ≤ CE * (BR * remWt w.2) := by positivity
      nlinarith

end RegularityStructures.Potential

end
