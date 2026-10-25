/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.SpatialDeriv
public import RegularityStructures.PDE.GaussDeriv
public import RegularityStructures.PDE.HeatTime
public import RegularityStructures.PDE.SmoothDense
public import RegularityStructures.PDE.Nonlin
public import RegularityStructures.PDE.Semigroup
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# `P_s` maps `C(T³)` into `C¹(T³)` with an `s^{-1/2}` bound

For `h ∈ C(T³)` and `s > 0`, `P_s h` has continuous partial derivatives `V` (`HasTorusDeriv`) with
`‖V‖ ≤ c₁ s^{-1/2} ‖h‖` (`exists_hasTorusDeriv_heatOp`).

For `h` with continuous partial derivatives `Dh`, the Gaussian integration by parts gives
`P_s (∂ᵢ h)(x) = -(2 √s)⁻¹ ∫ zᵢ γ₁(z) h(x - √s z) dz` (`abs_heatOp_deriv_le`). A general `h` is a
uniform limit of smooth functions, and `HasTorusDeriv` is stable under uniform limits
(`hasTorusDeriv_of_tendsto`).
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace RegularityStructures.Datum

open RegularityStructures.PDE

/-- The first Gaussian moment `∫ |z| γ₁(z) dz`. -/
def gaussMoment : ℝ := ∫ z : Fin 3 → ℝ, ‖z‖ * gaussKernel 1 z

/-- The constant `c₁ = (∫ |z| γ₁) / 2` in `‖∂ᵢ P_s h‖ ≤ c₁ s^{-1/2} ‖h‖`. -/
def derivConst : ℝ := gaussMoment / 2

end RegularityStructures.Datum

end

public section

open MeasureTheory Filter Topology Real
open scoped ContDiff

namespace RegularityStructures.Datum

open RegularityStructures.PDE

theorem gaussMoment_nonneg : 0 ≤ gaussMoment :=
  integral_nonneg fun z => mul_nonneg (norm_nonneg _) (gaussKernel_one_nonneg z)

theorem derivConst_nonneg : 0 ≤ derivConst := div_nonneg gaussMoment_nonneg (by norm_num)

/-- `HasTorusDeriv` is stable under uniform limits. -/
theorem hasTorusDeriv_of_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℕ → C(Torus3, E)} {D : ℕ → C(Torus3, Fin 3 → E)} {g₀ : C(Torus3, E)}
    {D₀ : C(Torus3, Fin 3 → E)} (hg : ∀ n, HasTorusDeriv (g n) (D n))
    (hgl : Tendsto g atTop (𝓝 g₀)) (hDl : Tendsto D atTop (𝓝 D₀)) : HasTorusDeriv g₀ D₀ := by
  intro y
  have hunif : TendstoUniformly (fun n (y' : Fin 3 → ℝ) => ofPartials (D n (torusProj y')))
      (fun y' => ofPartials (D₀ (torusProj y'))) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hP : 0 < ‖(ofPartials : (Fin 3 → E) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] E)‖ + 1 := by positivity
    have := (Metric.tendsto_nhds.1 hDl) (ε / (‖(ofPartials : (Fin 3 → E) →L[ℝ]
      (Fin 3 → ℝ) →L[ℝ] E)‖ + 1)) (by positivity)
    filter_upwards [this] with n hn y'
    have hn' : ‖D₀ - D n‖ < ε / (‖(ofPartials : (Fin 3 → E) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] E)‖ + 1) := by
      rw [norm_sub_rev, ← dist_eq_norm]
      exact hn
    have h1 : ‖D₀ (torusProj y') - D n (torusProj y')‖ ≤ ‖D₀ - D n‖ := by
      have := (D₀ - D n).norm_coe_le_norm (torusProj y')
      simpa using this
    rw [lt_div_iff₀ hP] at hn'
    calc dist (ofPartials (D₀ (torusProj y'))) (ofPartials (D n (torusProj y')))
        = ‖ofPartials (D₀ (torusProj y') - D n (torusProj y'))‖ := by
          rw [dist_eq_norm, map_sub]
      _ ≤ ‖(ofPartials : (Fin 3 → E) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] E)‖ *
          ‖D₀ (torusProj y') - D n (torusProj y')‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖(ofPartials : (Fin 3 → E) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] E)‖ * ‖D₀ - D n‖ := by
          gcongr
      _ ≤ (‖(ofPartials : (Fin 3 → E) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] E)‖ + 1) * ‖D₀ - D n‖ := by
          gcongr
          linarith
      _ < ε := by linarith
  refine hasFDerivAt_of_tendstoUniformly hunif (fun n y' => hg n y') (fun y' => ?_) y
  have := (ContinuousMap.evalCLM ℝ (torusProj y')).continuous.tendsto g₀ |>.comp hgl
  exact this

/-- **Gaussian integration by parts**: for `h` with continuous partial derivatives `Dh`,
`|P_s (∂ᵢ h)(x)| ≤ c₁ s^{-1/2} ‖h‖`. -/
theorem abs_heatOp_deriv_le {h : C(Torus3, ℝ)} {Dh : C(Torus3, Fin 3 → ℝ)}
    (hD : HasTorusDeriv h Dh) {s : ℝ} (hs : 0 < s) (x : Torus3) (i : Fin 3) :
    |heatOp s Dh x i| ≤ derivConst * (√s)⁻¹ * ‖h‖ := by
  have hst : 0 < √s := Real.sqrt_pos.2 hs
  obtain ⟨y, rfl⟩ := torusProj_surjective x
  have haff : ∀ z : Fin 3 → ℝ, HasFDerivAt (fun z : Fin 3 → ℝ => y - √s • z)
      (-(√s • ContinuousLinearMap.id ℝ (Fin 3 → ℝ))) z := fun z =>
    ((hasFDerivAt_id z).const_smul (√s)).const_sub y
  set φ : (Fin 3 → ℝ) → ℝ := fun z => h (torusProj (y - √s • z)) with hφ
  set φ' : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ := fun z =>
    (ofPartials (Dh (torusProj (y - √s • z))) : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
      (-(√s • ContinuousLinearMap.id ℝ (Fin 3 → ℝ))) with hφ'
  have hdiff : ∀ z, HasFDerivAt φ (φ' z) z := fun z =>
    HasFDerivAt.comp (g := fun y' => h (torusProj y')) z (hD (y - √s • z)) (haff z)
  have hφ'c : Continuous φ' := by
    have : Continuous fun z : Fin 3 → ℝ =>
        (ofPartials (Dh (torusProj (y - √s • z))) : (Fin 3 → ℝ) →L[ℝ] ℝ) :=
      (ofPartials (E := ℝ)).continuous.comp
        (Dh.continuous.comp (continuous_torusProj.comp (by fun_prop)))
    exact this.clm_comp continuous_const
  have hC : ∀ z, ‖φ z‖ ≤ ‖h‖ := fun z => h.norm_coe_le_norm _
  have hC' : ∀ z, ‖φ' z‖ ≤ ‖(ofPartials : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] ℝ)‖ * ‖Dh‖ * √s :=
    fun z => by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 : ‖(ofPartials (Dh (torusProj (y - √s • z))) : (Fin 3 → ℝ) →L[ℝ] ℝ)‖ ≤
        ‖(ofPartials : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] ℝ)‖ * ‖Dh‖ :=
      ((ofPartials (E := ℝ)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (Dh.norm_coe_le_norm _) (norm_nonneg _))
    have h2 : ‖-(√s • ContinuousLinearMap.id ℝ (Fin 3 → ℝ))‖ ≤ √s := by
      rw [norm_neg, norm_smul, Real.norm_of_nonneg hst.le]
      exact mul_le_of_le_one_right hst.le ContinuousLinearMap.norm_id_le
    exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  have hIBP := integral_coord_mul_gaussKernel_smul hdiff hφ'c hC hC' i
  -- identify the right-hand side with `-√s P_s (∂ᵢ h)(x)`
  have hrhs : ∫ z, gaussKernel 1 z • φ' z (Pi.single i 1) =
      -(√s) * heatOp s Dh (torusProj y) i := by
    have e1 : ∀ z, gaussKernel 1 z • φ' z (Pi.single i 1) =
        -(√s) * (gaussKernel 1 z • Dh (torusProj (y - √s • z)) i) := fun z => by
      simp only [hφ', ContinuousLinearMap.comp_apply, neg_apply, smul_apply,
        ContinuousLinearMap.id_apply, map_neg, map_smul, ofPartials_single, smul_eq_mul]
      ring
    simp_rw [e1]
    rw [integral_const_mul, heatOp_torusProj]
    congr 1
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).integral_comp_comm
      (μ := volume) (φ := fun z : Fin 3 → ℝ =>
        gaussKernel 1 z • Dh (torusProj (y - √s • z)))
      (by simpa [torusProj_sub] using integrable_heatOp_integrand Dh s (torusProj y))
    simpa using this
  rw [hrhs] at hIBP
  have hval : heatOp s Dh (torusProj y) i =
      -(2 * √s)⁻¹ * ∫ z, (z i * gaussKernel 1 z) • φ z := by
    rw [hIBP, smul_eq_mul]
    field_simp
  rw [hval, abs_mul, abs_neg, abs_of_pos (by positivity)]
  have hint : |∫ z, (z i * gaussKernel 1 z) • φ z| ≤ gaussMoment * ‖h‖ := by
    have hb : ∀ z, ‖(z i * gaussKernel 1 z) • φ z‖ ≤ (‖z‖ * gaussKernel 1 z) * ‖h‖ := fun z => by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussKernel_one_nonneg z)]
      have : |z i| ≤ ‖z‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm z i
      have h3 := gaussKernel_one_nonneg z
      have h4 : ‖φ z‖ ≤ ‖h‖ := hC z
      calc |z i| * gaussKernel 1 z * ‖φ z‖ ≤ ‖z‖ * gaussKernel 1 z * ‖h‖ :=
            mul_le_mul (mul_le_mul_of_nonneg_right this h3) h4 (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) h3)
        _ = _ := rfl
    have := norm_integral_le_of_norm_le (integrable_norm_mul_gaussKernel_one.mul_const ‖h‖)
      (Eventually.of_forall hb)
    rw [integral_mul_const] at this
    simpa [Real.norm_eq_abs, gaussMoment] using this
  calc (2 * √s)⁻¹ * |∫ z, (z i * gaussKernel 1 z) • φ z| ≤ (2 * √s)⁻¹ * (gaussMoment * ‖h‖) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = derivConst * (√s)⁻¹ * ‖h‖ := by
        rw [derivConst]
        field_simp

/-- **`P_s h` is `C¹` for continuous `h`**, with `‖∂ P_s h‖ ≤ c₁ s^{-1/2} ‖h‖`. -/
theorem exists_hasTorusDeriv_heatOp (h : C(Torus3, ℝ)) {s : ℝ} (hs : 0 < s) :
    ∃ V : C(Torus3, Fin 3 → ℝ), HasTorusDeriv (heatOp s h) V ∧
      ∀ (x : Torus3) (i : Fin 3), |V x i| ≤ derivConst * (√s)⁻¹ * ‖h‖ := by
  have hc : 0 ≤ derivConst * (√s)⁻¹ := mul_nonneg derivConst_nonneg (by positivity)
  choose hn hsm hnear using fun n : ℕ => exists_smooth_near h
    (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  set Dh : ℕ → C(Torus3, Fin 3 → ℝ) := fun n =>
    torusDerivOf (hn n) ((hsm n).of_le (by exact_mod_cast le_top)) with hDh
  have hDn : ∀ n, HasTorusDeriv (hn n) (Dh n) := fun n =>
    hasTorusDeriv_torusDerivOf _ _
  have hV : ∀ n, HasTorusDeriv (heatOp s (hn n)) (heatOp s (Dh n)) := fun n =>
    hasTorusDeriv_heatOp (hDn n) s
  -- the bound for each approximant
  have hbd : ∀ n (x : Torus3) (i : Fin 3), |heatOp s (Dh n) x i| ≤
      derivConst * (√s)⁻¹ * ‖hn n‖ := fun n x i => abs_heatOp_deriv_le (hDn n) hs x i
  -- Cauchy
  have hnorm : ∀ n m, ‖heatOp s (Dh n) - heatOp s (Dh m)‖ ≤
      derivConst * (√s)⁻¹ * ‖hn n - hn m‖ := by
    intro n m
    rw [← heatOp_sub]
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    exact abs_heatOp_deriv_le (HasTorusDeriv.sub (hDn n) (hDn m)) hs x i
  have hcauchy : CauchySeq fun n => heatOp s (Dh n) := by
    refine cauchySeq_of_le_tendsto_0 (fun N => derivConst * (√s)⁻¹ * (2 / ((N : ℝ) + 1)))
      (fun n m N hn' hm' => ?_) ?_
    · rw [dist_eq_norm]
      refine (hnorm n m).trans (mul_le_mul_of_nonneg_left ?_ hc)
      have h1 : ‖hn n - h‖ < 1 / ((n : ℝ) + 1) := by rw [norm_sub_rev]; exact hnear n
      have h2 : ‖hn m - h‖ < 1 / ((m : ℝ) + 1) := by rw [norm_sub_rev]; exact hnear m
      have h3 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn' 1)
      have h4 : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hm' 1)
      calc ‖hn n - hn m‖ = ‖(hn n - h) - (hn m - h)‖ := by congr 1; abel
        _ ≤ ‖hn n - h‖ + ‖hn m - h‖ := norm_sub_le _ _
        _ ≤ 2 / ((N : ℝ) + 1) := by
            have : 2 / ((N : ℝ) + 1) = 1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) := by ring
            rw [this]
            linarith
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (derivConst * (√s)⁻¹ * 2)
      rw [mul_zero] at this
      refine this.congr fun N => ?_
      ring
  obtain ⟨V, hVlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- the limits
  have hhn : Tendsto hn atTop (𝓝 h) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [norm_sub_rev]
    exact (hnear n).le
  have hgl : Tendsto (fun n => heatOp s (hn n)) atTop (𝓝 (heatOp s h)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (tendsto_iff_norm_sub_tendsto_zero.1 hhn)
    rw [← heatOp_sub]
    exact norm_heatOp_le _ _
  refine ⟨V, hasTorusDeriv_of_tendsto hV hgl hVlim, fun x i => ?_⟩
  have h1 : Tendsto (fun n => |heatOp s (Dh n) x i|) atTop (𝓝 |V x i|) :=
    ((continuous_abs.comp ((continuous_apply i).comp
      (ContinuousMap.evalCLM ℝ x).continuous)).tendsto V).comp hVlim
  have h2 : Tendsto (fun n => derivConst * (√s)⁻¹ * ‖hn n‖) atTop
      (𝓝 (derivConst * (√s)⁻¹ * ‖h‖)) :=
    (hhn.norm).const_mul _
  exact le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun n => hbd n x i)

end RegularityStructures.Datum

end
