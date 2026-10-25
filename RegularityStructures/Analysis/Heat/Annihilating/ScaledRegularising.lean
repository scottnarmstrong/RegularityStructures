/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Annihilating.Scaled
public import RegularityStructures.Analysis.Heat.Annihilating.ScaledDeriv
public import RegularityStructures.Analysis.Heat.Decomposition.MomentDegree

/-!
# Dyadic rescalings of a bump satisfy Assumption 5.1 with `β = 2`

For `h` smooth and supported in the unit parabolic ball, the kernels `K_n(x, y) = scaledShell h n (x - y)`
form a regularising decomposition (`isRegularisingDecomposition_scaledShell`), by the same
argument as for the heat shells: exact scaling plus integration by parts [Hai14, (5.3)–(5.5)].

Source: Hairer, arXiv:1303.5113v4, proof of Lemma 5.5.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

/-- Exact scaling of the moments of the rescalings. -/
theorem integral_monoFn_mul_lineIter_scaledShell (h : ParabolicSpace → ℝ) (h0 : ContDiff ℝ ∞ h)
    (k l : Fin 4 →₀ ℕ) (n : ℕ) :
    ∫ z, monoFn l z * lineIter ((Finsupp.toMultiset k).toList.map coordDir) (scaledShell h n) z =
      ((2 : ℝ) ^ n) ^ (3 + multiDeg k) * (((2 : ℝ) ^ n) ^ multiDeg l)⁻¹ * (((2 : ℝ) ^ n) ^ 5)⁻¹ *
        ∫ z, monoFn l z * lineIter ((Finsupp.toMultiset k).toList.map coordDir) h z := by
  have hd : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hpt : ∀ z, monoFn l z *
      lineIter ((Finsupp.toMultiset k).toList.map coordDir) (scaledShell h n) z =
      (((2 : ℝ) ^ n) ^ (3 + multiDeg k) * (((2 : ℝ) ^ n) ^ multiDeg l)⁻¹) *
        ((fun w => monoFn l w *
          lineIter ((Finsupp.toMultiset k).toList.map coordDir) h w)
          (parabolicDilate (2 ^ n) z)) := by
    intro z
    rw [lineIter_coordDir_scaledShell h0 n]
    simp only [indexWeight_toList, monoFn_parabolicDilate]
    field_simp
  simp_rw [hpt]
  rw [integral_const_mul,
    integral_comp_parabolicDilate (fun w => monoFn l w *
      lineIter ((Finsupp.toMultiset k).toList.map coordDir) h w) hd]
  ring

theorem integral_monoFn_mul_lineIter_scaledShell_eq_zero {h : ParabolicSpace → ℝ}
    (h0 : ContDiff ℝ ∞ h) (hs : ∀ z, 1 < parabolicNorm z → h z = 0) (k l : Fin 4 →₀ ℕ)
    (hkl : ¬ k ≤ l) (n : ℕ) :
    ∫ z, monoFn l z * lineIter ((Finsupp.toMultiset k).toList.map coordDir) (scaledShell h n) z =
      0 := by
  obtain ⟨i, hi⟩ : ∃ i, l i < k i := by
    by_contra hcon
    exact hkl (Finsupp.le_def.2 fun i => by by_contra h; exact hcon ⟨i, not_le.1 h⟩)
  exact integral_monoFn_mul_lineIter_eq_zero (contDiff_scaledShell h0 n)
    (hasCompactSupport_scaledShell hs n) _ _ ⟨i, by rw [count_toList]; exact hi⟩

/-- The moment bound `(5.5)` for the rescalings, in terms of the monomial `monoFn l`. -/
theorem exists_abs_integral_monoFn_mul_lineIter_scaledShell_le {h : ParabolicSpace → ℝ}
    (h0 : ContDiff ℝ ∞ h) (hs : ∀ z, 1 < parabolicNorm z → h z = 0) (k l : Fin 4 →₀ ℕ) :
    ∃ C : ℝ, ∀ n : ℕ,
      |∫ z, monoFn l z * lineIter ((Finsupp.toMultiset k).toList.map coordDir) (scaledShell h n) z| ≤
        C * (2 : ℝ) ^ (-(2 : ℝ) * (n : ℝ)) := by
  by_cases hkl : k ≤ l
  · refine ⟨|∫ z, monoFn l z *
      lineIter ((Finsupp.toMultiset k).toList.map coordDir) h z|, fun n => ?_⟩
    have hd : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have hd0 : (0 : ℝ) < 2 ^ n := by linarith
    rw [integral_monoFn_mul_lineIter_scaledShell h h0, abs_mul, rpow_neg_two_mul_nat, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_of_nonneg (by positivity)]
    have hle : multiDeg k ≤ multiDeg l := multiDeg_le_of_le hkl
    set a : ℝ := 2 ^ n with ha
    have h1 : a ^ (3 + multiDeg k) * a ^ 2 ≤ a ^ multiDeg l * a ^ 5 := by
      rw [← pow_add, ← pow_add]
      exact pow_le_pow_right₀ hd (by omega)
    have e : a ^ (3 + multiDeg k) * (a ^ multiDeg l)⁻¹ * (a ^ 5)⁻¹ =
        ((a ^ (3 + multiDeg k) * a ^ 2) / (a ^ multiDeg l * a ^ 5)) * (a ^ 2)⁻¹ := by
      field_simp
    rw [e]
    exact mul_le_of_le_one_left (by positivity) ((div_le_one (by positivity)).2 h1)
  · refine ⟨0, fun n => ?_⟩
    rw [integral_monoFn_mul_lineIter_scaledShell_eq_zero h0 hs k l hkl n]
    simp

theorem contDiff_uncurry_scaledShell_sub {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h) (n : ℕ) :
    ContDiff ℝ ∞ (Function.uncurry fun x y : ParabolicSpace => scaledShell h n (x - y)) := by
  have : (Function.uncurry fun x y : ParabolicSpace => scaledShell h n (x - y)) =
      scaledShell h n ∘ (ContinuousLinearMap.fst ℝ ParabolicSpace ParabolicSpace -
        ContinuousLinearMap.snd ℝ ParabolicSpace ParabolicSpace) := by
    funext p; simp [Function.uncurry]
  rw [this]
  exact (contDiff_scaledShell h0 n).comp (ContinuousLinearMap.contDiff _)

/-- The dyadic rescalings of a smooth bump supported in the unit parabolic ball satisfy
Hairer's Assumption 5.1 with `β = 2` [Hai14, (5.3)–(5.5)]. -/
theorem isRegularisingDecomposition_scaledShell {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h)
    (hs : ∀ z, 1 < parabolicNorm z → h z = 0) :
    IsRegularisingDecomposition (fun n x y => scaledShell h n (x - y)) 2 where
  smooth := contDiff_uncurry_scaledShell_sub h0
  support := fun n x y hxy => scaledShell_eq_zero hs hxy
  deriv_le := fun k l => exists_abs_kernelDeriv_scaledShell_le h0 hs k l
  moment_fst_le := by
    intro k l
    obtain ⟨C, hC⟩ := exists_abs_integral_monoFn_mul_lineIter_scaledShell_le h0 hs k l
    refine ⟨C, fun n y => ?_⟩
    have hpt : ∀ x, evalParabolic (MvPolynomial.monomial l 1) (x - y) *
        kernelDeriv 0 k (fun x y => scaledShell h n (x - y)) x y =
        (-1 : ℝ) ^ (multiDirs k).length *
          ((fun z => monoFn l z *
            lineIter ((Finsupp.toMultiset k).toList.map coordDir) (scaledShell h n) z) (x - y)) := by
      intro x
      rw [kernelDeriv_sub (contDiff_scaledShell h0 n), multiDirs_zero, evalParabolic_monomial_eq]
      simp only [List.nil_append, multiDirs_eq_map]
      ring
    simp_rw [hpt]
    rw [integral_const_mul, Measure.volume_eq_prod, integral_sub_right_eq_self
      (fun z => monoFn l z *
        lineIter ((Finsupp.toMultiset k).toList.map coordDir) (scaledShell h n) z) y,
      ← Measure.volume_eq_prod, abs_mul,
      abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact hC n
  moment_snd_le := by
    intro k l
    obtain ⟨C, hC⟩ := exists_abs_integral_monoFn_mul_lineIter_scaledShell_le h0 hs k l
    refine ⟨C, fun n x => ?_⟩
    have hpt : ∀ y, evalParabolic (MvPolynomial.monomial l 1) (y - x) *
        kernelDeriv k 0 (fun x y => scaledShell h n (x - y)) x y =
        (-1 : ℝ) ^ (∑ i, (l : Fin 4 → ℕ) i) *
          ((fun z => monoFn l z *
            lineIter ((Finsupp.toMultiset k).toList.map coordDir) (scaledShell h n) z) (x - y)) := by
      intro y
      rw [kernelDeriv_sub (contDiff_scaledShell h0 n), multiDirs_zero, evalParabolic_monomial_eq,
        ← neg_sub, monoFn_neg]
      simp only [List.append_nil, List.length_nil, pow_zero, one_mul, multiDirs_eq_map]
      ring
    simp_rw [hpt]
    have : (volume : Measure ParabolicSpace).IsAddHaarMeasure :=
      (inferInstance : (volume.prod volume : Measure ParabolicSpace).IsAddHaarMeasure)
    rw [integral_const_mul, integral_sub_left_eq_self
      (fun z => monoFn l z *
        lineIter ((Finsupp.toMultiset k).toList.map coordDir) (scaledShell h n) z) volume x, abs_mul,
      abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact hC n

end RegularityStructures

end
