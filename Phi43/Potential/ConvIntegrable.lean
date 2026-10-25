/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.KernelIdentity
public import Phi43.Potential.HeatIntegrable
public import Phi43.Potential.Convolution

/-!
# Integrability of the pieces of `K ∗ ζ`

`hairerKernel N` is integrable (it equals `G - R` on its support, the unit parabolic ball), the massive
Euclidean kernel `potMass = χ e^{-t} G` is integrable, and a continuous `ζ` bounded on the lag window of
the support gives integrable products `ζ(y) k(z - y)` (`integrable_conv_kernel`).
-/

public section

open MeasureTheory Set Filter

namespace RegularityStructures.Potential

private instance : (volume : Measure ParabolicSpace).IsAddLeftInvariant := by
  rw [Measure.volume_eq_prod]; infer_instance

private instance : (volume : Measure ParabolicSpace).IsNegInvariant := by
  refine ⟨?_⟩
  rw [Measure.volume_eq_prod]
  have h := Measure.map_prod_map (volume : Measure ℝ) (volume : Measure (Fin 3 → ℝ))
    (measurable_neg (G := ℝ)) (measurable_neg (G := Fin 3 → ℝ))
  rw [Measure.map_neg_eq_self, Measure.map_neg_eq_self] at h
  exact h.symm

private instance : NullSingletonClass (volume : Measure ParabolicSpace) := by
  rw [Measure.volume_eq_prod]; infer_instance

/-- The massive Euclidean heat kernel with the lag cutoff, `χ(t) e^{-t} G(t, x)`. -/
@[expose] noncomputable def potMass (w : ParabolicSpace) : ℝ :=
  potCutoff w.1 * Real.exp (-w.1) * heatKernelR4 w

theorem hairerKernel_eq_zero_of_nonpos (N : ℕ) {w : ParabolicSpace} (hw : w.1 ≤ 0) :
    Phi43.hairerKernel N w = 0 := by
  unfold Phi43.hairerKernel
  exact (tsum_congr fun n => annShellC_eq_zero_of_nonpos N n hw).trans tsum_zero

theorem potMass_eq_zero {w : ParabolicSpace} (h : w.1 ≤ 0 ∨ 1 / 4 ≤ w.1) : potMass w = 0 := by
  rcases h with h | h
  · simp [potMass, heatKernelR4_of_nonpos h]
  · simp [potMass, potCutoff_eq_zero h]

theorem integrable_potMass : Integrable potMass := by
  refine (integrable_heatKernelR4_lag 1).mono' ?_ (Eventually.of_forall fun w => ?_)
  · exact ((contDiff_potCutoff.continuous.comp continuous_fst).mul
      (Real.continuous_exp.comp continuous_fst.neg)).aestronglyMeasurable.mul
      measurable_heatKernelR4.aestronglyMeasurable
  · by_cases h : w.1 < 1
    · simp only [h, ite_true]
      by_cases h0 : 0 < w.1
      · rw [Real.norm_eq_abs, potMass, abs_mul, abs_mul, abs_of_nonneg (potCutoff_nonneg _),
          abs_of_pos (Real.exp_pos _), abs_of_nonneg (heatKernelR4_nonneg _)]
        have h1 : Real.exp (-w.1) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
        have h2 := potCutoff_le_one w.1
        have h3 := heatKernelR4_nonneg w
        have h4 := potCutoff_nonneg w.1
        calc potCutoff w.1 * Real.exp (-w.1) * heatKernelR4 w ≤ 1 * 1 * heatKernelR4 w := by
              gcongr
          _ = _ := by ring
      · rw [potMass_eq_zero (Or.inl (not_lt.1 h0))]
        simpa using heatKernelR4_nonneg w
    · rw [potMass_eq_zero (Or.inr (by linarith [not_lt.1 h]))]
      simp [h]

theorem integrable_hairerKernel (N : ℕ) : Integrable (Phi43.hairerKernel N) := by
  set S : Set ParabolicSpace := {w | parabolicNorm w ≤ 1} with hS
  have hSc : IsCompact S := isCompact_parabolicNorm_le 1
  have hSm : MeasurableSet S := hSc.isClosed.measurableSet
  have hvol : volume S < ⊤ := hSc.measure_lt_top
  have h1 : Integrable (S.indicator fun w : ParabolicSpace =>
      if w.1 < 2 then heatKernelR4 w else 0) :=
    (integrable_heatKernelR4_lag 2).indicator hSm
  have h2 : Integrable (S.indicator (annRemainderC N)) := by
    rw [integrable_indicator_iff hSm]
    exact (contDiff_annRemainderC N).continuous.continuousOn.integrableOn_compact hSc
  have hint := h1.sub h2
  refine hint.congr ?_
  have hae : ∀ᵐ w : ParabolicSpace ∂volume, w ≠ 0 :=
    compl_mem_ae_iff.2 (measure_singleton (0 : ParabolicSpace))
  filter_upwards [hae] with w hw
  by_cases hwS : w ∈ S
  · have hw1 : w.1 < 2 := by
      have := abs_time_sub_le_of_parabolicNorm_le (w := w) (r := 1) hwS
      have := (abs_le.1 this).2
      linarith
    simp only [Pi.sub_apply, indicator_of_mem hwS, hw1, ite_true]
    rw [Phi43.hairerKernel_eq_heat_sub_remainder hw]
  · simp only [Pi.sub_apply, indicator_of_notMem hwS]
    rw [hairerKernel_eq_zero_of_one_lt N (not_le.1 hwS)]
    simp

theorem integrable_conv_kernel {k : ParabolicSpace → ℝ} (hk : Integrable k) {a Bζ : ℝ}
    (hsupp : ∀ w, k w ≠ 0 → 0 ≤ w.1 ∧ w.1 ≤ a) {ζ : ParabolicSpace → ℝ} (hζ : Continuous ζ)
    (z : ParabolicSpace) (hb : ∀ y : ParabolicSpace, z.1 - a ≤ y.1 → y.1 ≤ z.1 → |ζ y| ≤ Bζ) :
    Integrable fun y => ζ y * k (z - y) := by
  have hk' := hk.comp_sub_left z
  refine (hk'.norm.const_mul Bζ).mono' (hζ.aestronglyMeasurable.mul hk'.aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  by_cases hy : k (z - y) = 0
  · simp [hy]
  · obtain ⟨h1, h2⟩ := hsupp _ hy
    simp only [Prod.fst_sub] at h1 h2
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hb y (by linarith) (by linarith)) (abs_nonneg _)

theorem potK1_eq_ae (z : ParabolicSpace) :
    ∀ᵐ y : ParabolicSpace ∂volume, z - y ≠ 0 := by
  have h : ∀ᵐ y : ParabolicSpace ∂volume, y ≠ z :=
    compl_mem_ae_iff.2 (measure_singleton z)
  filter_upwards [h] with y hy
  exact sub_ne_zero.2 (Ne.symm hy)

theorem hairerKernel_decomp (N : ℕ) {w : ParabolicSpace} (hw : w ≠ 0) :
    Phi43.hairerKernel N w = potTail N w + potK1 N w + potMass w := by
  rw [potK1_eq N hw]
  unfold potTail potMass
  ring

theorem hairerConvolution_decomp (N : ℕ) {ζ : ParabolicSpace → ℝ} (hζ : Continuous ζ)
    (z : ParabolicSpace) {Bζ : ℝ} (hb : ∀ y : ParabolicSpace, z.1 - 1 ≤ y.1 → y.1 ≤ z.1 →
      |ζ y| ≤ Bζ) :
    Phi43.hairerConvolution N ζ z =
      potConv ζ (potTail N) z + potConv ζ (potK1 N) z + potConv ζ potMass z := by
  have hK : Integrable fun y => ζ y * Phi43.hairerKernel N (z - y) :=
    integrable_conv_kernel (integrable_hairerKernel N) (a := 1)
      (fun w hw => by
        refine ⟨?_, ?_⟩
        · by_contra h
          exact hw (hairerKernel_eq_zero_of_nonpos N (not_le.1 h).le)
        · by_contra h
          have : 1 < parabolicNorm w := by
            have h1 : 1 < w.1 := not_le.1 h
            unfold parabolicNorm
            have := Finset.sum_nonneg fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
              abs_nonneg (w.2 i)
            have h2 : 1 < Real.sqrt |w.1| := by
              rw [show (1 : ℝ) = Real.sqrt 1 by simp]
              exact Real.sqrt_lt_sqrt zero_le_one (by rw [abs_of_pos (by linarith)]; exact h1)
            linarith
          exact hw (hairerKernel_eq_zero_of_one_lt N this))
      hζ z hb
  have hM : Integrable fun y => ζ y * potMass (z - y) :=
    integrable_conv_kernel integrable_potMass (a := 1 / 4)
      (fun w hw => by
        refine ⟨?_, ?_⟩
        · by_contra h; exact hw (potMass_eq_zero (Or.inl (not_le.1 h).le))
        · by_contra h; exact hw (potMass_eq_zero (Or.inr (by linarith [not_le.1 h]))))
      hζ z (fun y h1 h2 => hb y (by linarith) h2)
  have hTc : Continuous fun y => potTail N (z - y) :=
    (isUnitKernel_potTail N).smooth.continuous.comp (continuous_const.sub continuous_id)
  have hTs : HasCompactSupport fun y => potTail N (z - y) :=
    HasCompactSupport.intro (isCompact_closedBall z 1) fun y hy => by
      have hy' : z - y ∉ Metric.closedBall (0 : ParabolicSpace) 1 := by
        intro hmem
        apply hy
        rw [mem_closedBall_zero_iff, norm_sub_rev] at hmem
        rwa [mem_closedBall_iff_norm]
      exact (isUnitKernel_potTail N).supp _ (one_lt_parabolicNorm_of_not_mem_closedBall hy')
  have hT : Integrable fun y => ζ y * potTail N (z - y) :=
    (hζ.mul hTc).integrable_of_hasCompactSupport hTs.mul_left
  have hae := potK1_eq_ae z
  have hK1 : Integrable fun y => ζ y * potK1 N (z - y) := by
    refine ((hK.sub hT).sub hM).congr ?_
    filter_upwards [hae] with y hy
    simp only [Pi.sub_apply]
    rw [hairerKernel_decomp N hy]
    ring
  unfold potConv
  have hsum : ∀ᵐ y : ParabolicSpace ∂volume, ζ y * Phi43.hairerKernel N (z - y) =
      ζ y * potTail N (z - y) + ζ y * potK1 N (z - y) + ζ y * potMass (z - y) := by
    filter_upwards [hae] with y hy
    rw [hairerKernel_decomp N hy]
    ring
  unfold Phi43.hairerConvolution
  calc ∫ w, Phi43.hairerKernel N (z - w) * ζ w = ∫ y, ζ y * Phi43.hairerKernel N (z - y) :=
        integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
    _ = ∫ y, (ζ y * potTail N (z - y) + ζ y * potK1 N (z - y) + ζ y * potMass (z - y)) :=
        integral_congr_ae hsum
    _ = _ := by
        have h12 : Integrable fun y => ζ y * potTail N (z - y) + ζ y * potK1 N (z - y) :=
          hT.add hK1
        rw [integral_add h12 hM, integral_add hT hK1]

theorem integrable_hairerKernel_mul (N : ℕ) {ζ : ParabolicSpace → ℝ} (hζ : Continuous ζ)
    (z : ParabolicSpace) {Bζ : ℝ} (hb : ∀ y : ParabolicSpace, z.1 - 1 ≤ y.1 → y.1 ≤ z.1 →
      |ζ y| ≤ Bζ) : Integrable fun w => Phi43.hairerKernel N (z - w) * ζ w := by
  have : Integrable fun y => ζ y * Phi43.hairerKernel N (z - y) :=
    integrable_conv_kernel (integrable_hairerKernel N) (a := 1)
      (fun w hw => by
        refine ⟨?_, ?_⟩
        · by_contra h
          exact hw (hairerKernel_eq_zero_of_nonpos N (not_le.1 h).le)
        · by_contra h
          have : 1 < parabolicNorm w := by
            have h1 : 1 < w.1 := not_le.1 h
            unfold parabolicNorm
            have := Finset.sum_nonneg fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
              abs_nonneg (w.2 i)
            have h2 : 1 < Real.sqrt |w.1| := by
              rw [show (1 : ℝ) = Real.sqrt 1 by simp]
              exact Real.sqrt_lt_sqrt zero_le_one (by rw [abs_of_pos (by linarith)]; exact h1)
            linarith
          exact hw (hairerKernel_eq_zero_of_one_lt N this))
      hζ z hb
  exact this.congr (Eventually.of_forall fun y => mul_comm _ _)

theorem hairerConvolution_sub_smul (N : ℕ) {ζ₁ ζ₂ : ParabolicSpace → ℝ} (h₁ : Continuous ζ₁)
    (h₂ : Continuous ζ₂) (z : ParabolicSpace) {B₁ B₂ : ℝ}
    (hb₁ : ∀ y : ParabolicSpace, z.1 - 1 ≤ y.1 → y.1 ≤ z.1 → |ζ₁ y| ≤ B₁)
    (hb₂ : ∀ y : ParabolicSpace, z.1 - 1 ≤ y.1 → y.1 ≤ z.1 → |ζ₂ y| ≤ B₂) (c : ℝ) :
    Phi43.hairerConvolution N (fun w => c * (ζ₁ w - ζ₂ w)) z =
      c * (Phi43.hairerConvolution N ζ₁ z - Phi43.hairerConvolution N ζ₂ z) := by
  unfold Phi43.hairerConvolution
  have e : ∀ w : ParabolicSpace, Phi43.hairerKernel N (z - w) * (c * (ζ₁ w - ζ₂ w)) =
      c * (Phi43.hairerKernel N (z - w) * ζ₁ w - Phi43.hairerKernel N (z - w) * ζ₂ w) :=
    fun w => by ring
  simp only [e]
  rw [integral_const_mul, integral_sub (integrable_hairerKernel_mul N h₁ z hb₁)
    (integrable_hairerKernel_mul N h₂ z hb₂)]

end RegularityStructures.Potential

end
