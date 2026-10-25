/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.IdentNear.Integrals
public import RegularityStructures.Abstract.Singular.Ident.RemElementary
public import RegularityStructures.Abstract.Singular.Remainder.RemKernelG

/-!
# Integrability of `R̃f` against remainder kernels, near-pair `Γ`-bounds

In the window layer setting `LayerSettingWNear`, for a remainder kernel `r`,
`|R̃f(y) r(x − y)| ≤ C (y₀/3)^{min(η, 0)/2} (1 + |y|)^{-4}` on the slab, and `y ↦ R̃f(y) r(x − y)`
is integrable, for models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Set Filter Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {g : ParabolicSpace → ι → ParabolicSpace → ℝ}
  {γ η α Cf CPi CGam T : ℝ} {f : ParabolicSpace → ι → ℝ}

theorem exists_abs_mul_rem_le_wnear (hg : M.IsSmoothFunctionModelBelow g γ)
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) {r : ParabolicSpace → ℝ} (hr : RemKernel r)
    (x : ParabolicSpace) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ y ∈ timeSlab T,
      |pointwiseReconstruct g f y * r (x - y)| ≤
        Cc * (Real.sqrt (y.1 / 3) ^ min η 0 * (1 + ‖y.2‖) ^ (-(4 : ℝ))) := by
  classical
  obtain ⟨Bd, nd, hBd⟩ := hg.diag_growth
  obtain ⟨C, hC0, hC⟩ := hr.decay [] (nd + 2) x.1
  set A : ℝ := 1 + ∑ i, |x.2 i| with hA
  have hA1 : 1 ≤ A := by
    have : 0 ≤ ∑ i, |x.2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  set Bd' : ℝ := max Bd 0 with hBd'
  have hBd0 : 0 ≤ Bd' := le_max_right _ _
  set Kc : ℝ := Cf * (1 + max CGam 0) * identDomConst 𝒯 with hKc
  have hKc0 : 0 ≤ Kc :=
    mul_nonneg (mul_nonneg S.hCf (by linarith [le_max_right CGam 0])) (identDomConst_nonneg 𝒯)
  set N : ℝ := Fintype.card ι * Bd' * 2 ^ nd with hN
  have hN0 : 0 ≤ N := by positivity
  refine ⟨N * Kc * C * 6 ^ (nd + 2) * A ^ (2 * (nd + 2)), by positivity, fun y hy => ?_⟩
  have hy0 : 0 < y.1 := hy.1
  have hy1 : y.1 ≤ 1 := hy.2.trans S.hT
  set P : ℝ := 1 + ∑ i, |y.2 i| with hP
  have hP1 : 1 ≤ P := by
    have : 0 ≤ ∑ i, |y.2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hP0 : 0 < P := by linarith
  set p : ℝ := P⁻¹ with hp
  have hp0 : 0 < p := inv_pos.2 (by linarith)
  have hp1 : p ≤ 1 := inv_le_one_of_one_le₀ hP1
  set V : ℝ := Real.sqrt (y.1 / 3) ^ min η 0 with hV
  have hV0 : 0 ≤ V := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  -- the bound on `Φ`
  have hΦ : |pointwiseReconstruct g f y| ≤
      (∑ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ), |g y j y|) * (Kc * V) := by
    have := abs_pointwiseReconstruct_le_identDom_wnear hg S y
    simpa only [identDom, hy0, ↓reduceIte, hKc, hV] using this
  have hSg : ∑ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ), |g y j y| ≤ N * P ^ nd := by
    have h1 : ∀ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ),
        |g y j y| ≤ Bd' * (2 * P) ^ nd := fun j hj => by
      refine (hBd y j (Finset.mem_filter.1 hj).2).trans ?_
      have hpn := parabolicNorm_nonneg y
      refine mul_le_mul (le_max_left _ _) ?_ (pow_nonneg (by linarith) _) hBd0
      exact pow_le_pow_left₀ (by linarith) (one_add_parabolicNorm_le_two_mul_of_slab hy0 hy1) nd
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : ((Finset.univ.filter (fun j => 𝒯.deg j < γ)).card : ℝ) ≤ Fintype.card ι := by
      exact_mod_cast Finset.card_le_univ _
    calc (Finset.univ.filter (fun j => 𝒯.deg j < γ)).card * (Bd' * (2 * P) ^ nd)
        ≤ Fintype.card ι * (Bd' * (2 * P) ^ nd) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = N * P ^ nd := by rw [hN, mul_pow]; ring
  -- the bound on `r`
  have hrem : |r (x - y)| ≤ C * 6 ^ (nd + 2) * (A * p) ^ (2 * (nd + 2)) := by
    have hz : (x - y).1 ≤ x.1 := by
      simp only [Prod.fst_sub]; linarith
    have h1 := hC (x - y) hz
    simp only [List.map_nil, lineIter_nil] at h1
    refine h1.trans ?_
    have h2 := inv_one_add_sqNorm3_pow_le (x - y).2 (nd + 2)
    have h3 : ((1 + ∑ i, |(x - y).2 i|)⁻¹) ≤ A * p := by
      have hs : 0 ≤ ∑ i, |(x - y).2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hle : P ≤ A * (1 + ∑ i, |(x - y).2 i|) := by
        have := one_add_sum_abs_le_mul x.2 y.2
        simpa [hP, hA] using this
      rw [hp, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    calc C * ((1 + sqNorm3 (x - y).2)⁻¹) ^ (nd + 2)
        ≤ C * (6 ^ (nd + 2) * ((1 + ∑ i, |(x - y).2 i|)⁻¹) ^ (2 * (nd + 2))) :=
          mul_le_mul_of_nonneg_left h2 hC0
      _ ≤ C * (6 ^ (nd + 2) * (A * p) ^ (2 * (nd + 2))) := by
          gcongr
      _ = _ := by ring
  have hpw : P ^ nd * p ^ (2 * (nd + 2)) = p ^ (nd + 4) := by
    have e : 2 * (nd + 2) = nd + (nd + 4) := by ring
    rw [e, pow_add, ← mul_assoc, ← mul_pow, hp, mul_inv_cancel₀ (by linarith), one_pow, one_mul]
  have hpp : p ^ (nd + 4) ≤ p ^ 4 := pow_le_pow_of_le_one hp0.le hp1 (by omega)
  have hnorm : p ^ 4 ≤ (1 + ‖y.2‖) ^ (-(4 : ℝ)) := by
    have h1 : 1 + ‖y.2‖ ≤ P := by
      have := norm_le_sum_abs y.2
      rw [hP]; linarith
    have h2 : (0 : ℝ) < 1 + ‖y.2‖ := by positivity
    rw [Real.rpow_neg h2.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hp,
      ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 (by linarith)) (inv_anti₀ h2 h1) 4
  rw [abs_mul]
  have hA0 : 0 ≤ A := by linarith
  calc |pointwiseReconstruct g f y| * |r (x - y)|
      ≤ ((N * P ^ nd) * (Kc * V)) * (C * 6 ^ (nd + 2) * (A * p) ^ (2 * (nd + 2))) := by
        refine mul_le_mul (hΦ.trans (mul_le_mul_of_nonneg_right hSg (mul_nonneg hKc0 hV0))) hrem
          (abs_nonneg _) (by positivity)
    _ = (N * Kc * C * 6 ^ (nd + 2) * A ^ (2 * (nd + 2))) * (V * (P ^ nd * p ^ (2 * (nd + 2)))) := by
        rw [mul_pow]; ring
    _ ≤ (N * Kc * C * 6 ^ (nd + 2) * A ^ (2 * (nd + 2))) * (V * (1 + ‖y.2‖) ^ (-(4 : ℝ))) := by
        rw [hpw]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hpp.trans hnorm) hV0) ?_
        positivity

theorem integrable_pointwiseReconstruct_mul_rem_wnear (hg : M.IsSmoothFunctionModelBelow g γ)
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) {r : ParabolicSpace → ℝ} (hr : RemKernel r)
    (x : ParabolicSpace) :
    Integrable (fun y => pointwiseReconstruct g f y * r (x - y)) := by
  classical
  have hη : -2 < min η 0 := lt_min (lt_of_lt_of_le S.hαη (min_le_right _ _)) (by norm_num)
  obtain ⟨Cc, hCc0, hCc⟩ := exists_abs_mul_rem_le_wnear hg S hr x
  have hcont : Continuous (fun y => r (x - y)) :=
    hr.contDiff.continuous.comp (continuous_const.sub continuous_id)
  have hint : Integrable (fun y : ParabolicSpace =>
      (Ioc 0 1).indicator (fun t : ℝ => Real.sqrt (t / 3) ^ min η 0) y.1 *
        (1 + ‖y.2‖) ^ (-(4 : ℝ))) := by
    have h1 : Integrable ((Ioc 0 1).indicator (fun t : ℝ => Real.sqrt (t / 3) ^ min η 0)) :=
      (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_sqrt_div_three_rpow hη)
    have h2 : Integrable (fun v : Fin 3 → ℝ => (1 + ‖v‖) ^ (-(4 : ℝ))) :=
      integrable_one_add_norm (by simp; norm_num)
    rw [Measure.volume_eq_prod]
    exact h1.mul_prod h2
  refine (hint.const_mul Cc).mono' (aestronglyMeasurable_pointwiseReconstruct_mul_wnear hg S hcont)
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  by_cases hy : y ∈ timeSlab T
  · have hmem : y.1 ∈ Ioc (0 : ℝ) 1 := ⟨hy.1, hy.2.trans S.hT⟩
    rw [Set.indicator_of_mem hmem]
    exact hCc y hy
  · rw [pointwiseReconstruct_eq_zero_of_not_mem_wnear S hy, zero_mul, abs_zero]
    refine mul_nonneg hCc0 (mul_nonneg ?_ (Real.rpow_nonneg (by positivity) _))
    exact Set.indicator_nonneg (fun t _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _) _

end Model

end RegularityStructures
