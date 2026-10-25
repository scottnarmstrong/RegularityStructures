/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.IdentNear.RemIntegrable
public import RegularityStructures.Abstract.Singular.Ident.ShellSum

/-!
# Summability of the shell integrals `∑_n ∫ |R̃f K_n(x − ·)|`, near-pair `Γ`-bounds

For a point `x` with `x₀ > 0`, the pointwise reconstruction `R̃f` is bounded near `x`
(`exists_abs_pointwiseReconstruct_le_wnear`). For a shell profile `h`,
`∫ |K_n(x − y)| dy = (2^n)^{-2} ∫ |h|`, so the series `∑_n ∫ |R̃f(y) K_n(x − y)| dy` converges
(`summable_integral_norm_pointwiseReconstruct_mul_shell_wnear`).

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open MeasureTheory Set Filter Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

private theorem isNegInvariant_volume_parabolic :
    (volume : Measure ParabolicSpace).IsNegInvariant := by
  rw [Measure.volume_eq_prod]
  refine ⟨?_⟩
  have h := Measure.map_prod_map (volume : Measure ℝ) (volume : Measure (Fin 3 → ℝ))
    (measurable_neg (G := ℝ)) (measurable_neg (G := Fin 3 → ℝ))
  rw [Measure.map_neg_eq_self, Measure.map_neg_eq_self] at h
  exact h.symm

private theorem isAddLeftInvariant_volume_parabolic :
    (volume : Measure ParabolicSpace).IsAddLeftInvariant := by
  rw [Measure.volume_eq_prod]
  infer_instance

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {g : ParabolicSpace → ι → ParabolicSpace → ℝ}
  {γ η α Cf CPi CGam T : ℝ} {f : ParabolicSpace → ι → ℝ}

theorem exists_abs_pointwiseReconstruct_le_wnear (hg : M.IsSmoothFunctionModelBelow g γ)
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) {x : ParabolicSpace} (hx : 0 < x.1) :
    ∃ ρ B : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ y, parabolicNorm (y - x) ≤ ρ → |pointwiseReconstruct g f y| ≤ B := by
  set ρ : ℝ := min 1 (Real.sqrt x.1 / 2) with hρ
  have hsx : 0 < Real.sqrt x.1 := Real.sqrt_pos.2 hx
  have hρ0 : 0 < ρ := lt_min one_pos (by positivity)
  set K : Set ParabolicSpace := {y | parabolicNorm (y - x) ≤ ρ} with hKdef
  have hK : IsCompact K :=
    (Homeomorph.subRight x).isCompact_preimage.2 (isCompact_parabolicNorm_le ρ)
  have hpos : ∀ y ∈ K, 0 < y.1 := by
    intro y hy
    have hy' : parabolicNorm (y - x) ≤ ρ := hy
    have h1 : Real.sqrt |y.1 - x.1| ≤ ρ := by
      refine le_trans ?_ hy'
      unfold parabolicNorm
      simp only [Prod.fst_sub]
      linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg ((y - x).2 i))]
    have h2 : |y.1 - x.1| ≤ ρ ^ 2 := by
      calc |y.1 - x.1| = Real.sqrt |y.1 - x.1| ^ 2 := (Real.sq_sqrt (abs_nonneg _)).symm
        _ ≤ ρ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    have h3 : ρ ≤ Real.sqrt x.1 / 2 := min_le_right _ _
    have h4 : Real.sqrt x.1 ^ 2 = x.1 := Real.sq_sqrt hx.le
    have h5 : ρ ^ 2 ≤ x.1 / 4 := by nlinarith
    have := (abs_le.1 h2).1
    linarith
  set G : ParabolicSpace → ℝ := fun y =>
    (∑ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ), |g y j y|) *
      (Cf * (1 + max CGam 0) * identDomConst 𝒯 * Real.sqrt (y.1 / 3) ^ min η 0) with hG
  have hGc : ContinuousOn G K := by
    refine ContinuousOn.mul (continuous_finsetSum _ fun j hj =>
      (hg.diag_continuous (Finset.mem_filter.1 hj).2).abs).continuousOn ?_
    refine continuousOn_const.mul ?_
    refine ContinuousOn.rpow_const (Real.continuous_sqrt.comp
      (continuous_fst.div_const 3)).continuousOn fun y hy => Or.inl ?_
    have := hpos y hy
    exact (Real.sqrt_pos.2 (by positivity)).ne'
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hGc
  refine ⟨ρ, B, hρ0, min_le_left _ _, fun y hy => ?_⟩
  have hyK : y ∈ K := hy
  have h1 := abs_pointwiseReconstruct_le_identDom_wnear hg S y
  have h2 : identDom 𝒯 g γ η Cf CGam y = G y := by
    simp only [identDom, hpos y hyK, ↓reduceIte, hG]
  rw [h2] at h1
  exact h1.trans ((le_abs_self _).trans (by simpa using hB y hyK))

theorem summable_integral_norm_pointwiseReconstruct_mul_shell_wnear
    (hg : M.IsSmoothFunctionModelBelow g γ) (S : LayerSettingWNear M f γ η α Cf CPi CGam T)
    {h : ParabolicSpace → ℝ} {N : ℕ} (hh : ShellProfile h N) {x : ParabolicSpace} (hx : 0 < x.1) :
    Summable fun n : ℕ => ∫ y, ‖pointwiseReconstruct g f y * scaledShell h n (x - y)‖ := by
  classical
  obtain ⟨ρ, B, hρ0, -, hB⟩ := exists_abs_pointwiseReconstruct_le_wnear hg S hx
  set B' : ℝ := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  set Ih : ℝ := ∫ w, |h w| with hIh
  have hb : Summable fun n : ℕ => (((2 : ℝ) ^ n)⁻¹) ^ 2 := by
    have : (fun n : ℕ => (((2 : ℝ) ^ n)⁻¹) ^ 2) = fun n : ℕ => (1 / 4 : ℝ) ^ n := by
      funext n
      rw [← inv_pow, ← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [this]
    exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine Summable.of_norm_bounded_eventually_nat ((hb.mul_left Ih).mul_left B')
    ?_
  filter_upwards [eventually_inv_two_pow_lt hρ0] with n hn
  have hψc : HasCompactSupport (fun y => scaledShell h n (x - y)) :=
    (hasCompactSupport_scaledShell hh.eq_zero n).comp_homeomorph (Homeomorph.subLeft x)
  have hψ : Continuous (fun y => scaledShell h n (x - y)) :=
    (contDiff_scaledShell hh.contDiff n).continuous.comp (continuous_const.sub continuous_id)
  rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
  have hint : Integrable (fun y => B' * |scaledShell h n (x - y)|) :=
    (continuous_const.mul hψ.abs).integrable_of_hasCompactSupport
      (hψc.comp_left (g := fun t => B' * |t|) (by simp))
  calc ∫ y, ‖pointwiseReconstruct g f y * scaledShell h n (x - y)‖
      ≤ ∫ y, B' * |scaledShell h n (x - y)| := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _) hint
          (Eventually.of_forall fun y => ?_)
        beta_reduce
        by_cases hy : scaledShell h n (x - y) = 0
        · simp [hy]
        · have hn' : parabolicNorm (x - y) ≤ ((2 : ℝ)⁻¹) ^ n := by
            by_contra hlt
            exact hy (scaledShell_eq_zero hh.eq_zero (not_le.1 hlt))
          have hn'' : parabolicNorm (y - x) ≤ ρ := by
            rw [parabolicNorm_sub_comm]
            have : ((2 : ℝ)⁻¹) ^ n = ((2 : ℝ) ^ n)⁻¹ := by rw [inv_pow]
            exact hn'.trans (by rw [this]; exact hn.le)
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right ((hB y hn'').trans (le_max_left _ _)) (abs_nonneg _)
    _ = B' * (((2 : ℝ) ^ n)⁻¹ ^ 2 * Ih) := by
        rw [integral_const_mul]
        congr 1
        have := isNegInvariant_volume_parabolic
        have := isAddLeftInvariant_volume_parabolic
        rw [integral_sub_left_eq_self (fun w => |scaledShell h n w|) volume x,
          integral_abs_scaledShell]
    _ = B' * (Ih * (((2 : ℝ) ^ n)⁻¹ ^ 2)) := by ring

end Model

end RegularityStructures
