/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Ident.LatticeAvg

/-!
# Integrability of the dominating function against a compactly supported test function

For `-2 < min η 0` and a continuous compactly supported `ψ`, the function `|ψ| · identDom` is
integrable (`integrable_abs_mul_identDom`): on the support of `ψ` the time is bounded by `R²`, the
space variable lies in a box, `∑_j |g_{y,j}(y)|` is bounded, and `t ↦ (t/3)^{min(η,0)/2}` is
integrable on `(0, R²]` because `min(η, 0)/2 > -1`.
-/

public section

open MeasureTheory Set Filter

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

theorem integrableOn_sqrt_div_three_rpow {e : ℝ} (he : -2 < e) {b : ℝ} :
    IntegrableOn (fun t : ℝ => Real.sqrt (t / 3) ^ e) (Ioc 0 b) := by
  have h1 : IntegrableOn (fun t : ℝ => t ^ (e / 2)) (Ioc 0 b) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b) (by linarith)).1
  have h2 : IntegrableOn (fun t : ℝ => (3 : ℝ) ^ (-(e / 2)) * t ^ (e / 2)) (Ioc 0 b) :=
    h1.const_mul _
  refine IntegrableOn.congr_fun h2 (fun t ht => ?_) measurableSet_Ioc
  have ht0 : 0 < t := ht.1
  show (3 : ℝ) ^ (-(e / 2)) * t ^ (e / 2) = Real.sqrt (t / 3) ^ e
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (div_nonneg ht0.le (by norm_num)),
    Real.div_rpow ht0.le (by norm_num), Real.rpow_neg (by norm_num), inv_mul_eq_div, one_div]
  have hee : (2 : ℝ)⁻¹ * e = e / 2 := by ring
  rw [hee]

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {g : ParabolicSpace → ι → ParabolicSpace → ℝ}
  {γ η α Cf CPi CGam T : ℝ} {f : ParabolicSpace → ι → ℝ}

theorem identDom_nonneg' (hCf : 0 ≤ Cf) (y : ParabolicSpace) : 0 ≤ identDom 𝒯 g γ η Cf CGam y := by
  unfold identDom
  split_ifs
  · exact mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg hCf (by linarith [le_max_right CGam 0]))
        (identDomConst_nonneg 𝒯)) (Real.rpow_nonneg (Real.sqrt_nonneg _) _))
  · exact le_rfl

theorem measurable_identDom (hg : M.IsSmoothFunctionModelBelow g γ) :
    Measurable (identDom 𝒯 g γ η Cf CGam) := by
  unfold identDom
  refine Measurable.ite (measurableSet_lt measurable_const measurable_fst) ?_ measurable_const
  refine Measurable.mul ?_ ?_
  · exact Finset.measurable_sum _ fun j hj =>
      (hg.diag_continuous (Finset.mem_filter.1 hj).2).abs.measurable
  · exact measurable_const.mul ((measurable_fst.div_const 3).sqrt.pow_const _)

theorem integrable_abs_mul_identDom (hg : M.IsSmoothFunctionModelBelow g γ)
    (hη : -2 < min η 0) (hCf : 0 ≤ Cf) {ψ : ParabolicSpace → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) :
    Integrable (fun y => |ψ y| * identDom 𝒯 g γ η Cf CGam y) := by
  classical
  have hK := hψc.isCompact
  obtain ⟨R₀, hR₀⟩ := hK.exists_bound_of_continuousOn continuous_parabolicNorm.continuousOn
  obtain ⟨Bg, hBg⟩ := hK.exists_bound_of_continuousOn
    (f := fun y => ∑ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ), |g y j y|)
    (continuous_finsetSum _ fun j hj =>
      (hg.diag_continuous (Finset.mem_filter.1 hj).2).abs).continuousOn
  obtain ⟨Bψ, hBψ⟩ := hψ.bounded_above_of_compact_support hψc
  set R : ℝ := max R₀ 1 with hR
  have hR1 : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  set Kc : ℝ := Cf * (1 + max CGam 0) * identDomConst 𝒯 with hKc
  have hKc0 : 0 ≤ Kc :=
    mul_nonneg (mul_nonneg hCf (by linarith [le_max_right CGam 0])) (identDomConst_nonneg 𝒯)
  set Q : Set (Fin 3 → ℝ) := Set.pi univ (fun _ => Icc (-R) R) with hQ
  have hQc : IsCompact Q := isCompact_univ_pi fun _ => isCompact_Icc
  have hint : Integrable (fun y : ParabolicSpace =>
      (Ioc 0 (R ^ 2)).indicator (fun t : ℝ => Real.sqrt (t / 3) ^ min η 0) y.1 *
        Q.indicator (fun _ => (1 : ℝ)) y.2) := by
    have h1 : Integrable ((Ioc 0 (R ^ 2)).indicator
        (fun t : ℝ => Real.sqrt (t / 3) ^ min η 0)) :=
      (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_sqrt_div_three_rpow hη)
    have h2 : Integrable (Q.indicator (fun _ : Fin 3 → ℝ => (1 : ℝ))) :=
      (integrable_indicator_iff hQc.measurableSet).2
        (integrableOn_const hQc.measure_lt_top.ne)
    rw [Measure.volume_eq_prod]
    exact h1.mul_prod h2
  set Bg' : ℝ := max Bg 0 with hBg'
  refine (hint.const_mul (Bψ * Bg' * Kc)).mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact (hψ.abs.measurable.mul (measurable_identDom hg)).aestronglyMeasurable
  · have hBψ0 : 0 ≤ Bψ := (norm_nonneg _).trans (hBψ 0)
    have hBg0 : 0 ≤ Bg' := le_max_right _ _
    set v : ℝ := (Ioc 0 (R ^ 2)).indicator (fun t : ℝ => Real.sqrt (t / 3) ^ min η 0) y.1 *
        Q.indicator (fun _ => (1 : ℝ)) y.2 with hv
    have hv0 : 0 ≤ v := mul_nonneg
      (Set.indicator_nonneg (fun t _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _) _)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    have hrhs : 0 ≤ Bψ * Bg' * Kc * v := mul_nonneg (mul_nonneg (mul_nonneg hBψ0 hBg0) hKc0) hv0
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (identDom_nonneg' hCf y))]
    by_cases hy : ψ y = 0
    · rw [hy, abs_zero, zero_mul]; exact hrhs
    · have hyK : y ∈ tsupport ψ := subset_tsupport _ (by simpa using hy)
      have hpn : parabolicNorm y ≤ R := by
        have := hR₀ y hyK
        rw [Real.norm_eq_abs, abs_of_nonneg (parabolicNorm_nonneg _)] at this
        exact this.trans (le_max_left _ _)
      have hsq : Real.sqrt |y.1| ≤ R := by
        refine le_trans ?_ hpn
        unfold parabolicNorm
        linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (y.2 i))]
      have ht : |y.1| ≤ R ^ 2 := by
        calc |y.1| = Real.sqrt |y.1| ^ 2 := (Real.sq_sqrt (abs_nonneg _)).symm
          _ ≤ R ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2
      have hx : y.2 ∈ Q := by
        intro i _
        have h1 : |y.2 i| ≤ ∑ j, |y.2 j| :=
          Finset.single_le_sum (f := fun j => |y.2 j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
        have h2 : ∑ j, |y.2 j| ≤ parabolicNorm y := by
          unfold parabolicNorm
          linarith [Real.sqrt_nonneg |y.1|]
        exact abs_le.1 (h1.trans (h2.trans hpn))
      by_cases hy1 : 0 < y.1
      · have hmem : y.1 ∈ Ioc 0 (R ^ 2) := ⟨hy1, (le_abs_self _).trans ht⟩
        have hvv : v = Real.sqrt (y.1 / 3) ^ min η 0 := by
          rw [hv, Set.indicator_of_mem hmem, Set.indicator_of_mem hx]; ring
        have hgb : ∑ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ), |g y j y| ≤ Bg' := by
          have := hBg y hyK
          rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at this
          exact this.trans (le_max_left _ _)
        have hpsi : |ψ y| ≤ Bψ := by simpa using hBψ y
        have hw0 : 0 ≤ Real.sqrt (y.1 / 3) ^ min η 0 := Real.rpow_nonneg (Real.sqrt_nonneg _) _
        simp only [identDom, hy1, ↓reduceIte, hvv]
        calc |ψ y| * ((∑ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ), |g y j y|) *
              (Cf * (1 + max CGam 0) * identDomConst 𝒯 * Real.sqrt (y.1 / 3) ^ min η 0))
            ≤ Bψ * (Bg' * (Kc * Real.sqrt (y.1 / 3) ^ min η 0)) := by
              refine mul_le_mul hpsi (mul_le_mul hgb le_rfl (mul_nonneg hKc0 hw0) hBg0) ?_ hBψ0
              exact mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (mul_nonneg hKc0 hw0)
          _ = Bψ * Bg' * Kc * Real.sqrt (y.1 / 3) ^ min η 0 := by rw [hKc]; ring
      · have : identDom 𝒯 g γ η Cf CGam y = 0 := by
          simp [identDom, hy1]
        rw [this, mul_zero]; exact hrhs

end Model

end RegularityStructures
