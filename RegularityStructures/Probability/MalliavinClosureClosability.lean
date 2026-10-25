/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureSpectralGap

/-!
# Closability of the cylindrical Malliavin derivative

The graph closure in `MalliavinClosureCore` is a genuine operator graph: a sequence of
cylindrical pairs converging to `(0,G)` has `G = 0`.  The proof is a direct consequence of the
closed spectral-gap estimate and is the standard closability argument for `D^{1,2}`;
see [HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω]

theorem malliavinVariance_zero {P : Measure Ω} [IsProbabilityMeasure P] :
    malliavinVariance P (0 : Lp ℝ 2 P) = 0 := by
  simp [malliavinVariance, malliavinMean, malliavinLpPairing, malliavinOne]

theorem malliavinLpPairing_self_eq_norm_sq
    {μ : Measure Ω} {G : Lp ℝ 2 μ} :
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ 2 2 G G = ‖G‖ ^ 2 := by
  have hpair : (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ 2 2 G G =
      ∫ x, G x ^ 2 ∂μ := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [ContinuousLinearMap.mul_apply']
    simp [pow_two]
  rw [hpair]
  have hG : MemLp (fun x => G x) 2 μ := Lp.memLp G
  have hEq : hG.toLp (fun x => G x) = G := by
    apply Lp.ext
    exact hG.coeFn_toLp
  have hnonneg : 0 ≤ ∫ x, G x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  rw [← hEq, Lp.norm_toLp]
  rw [hG.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  rw [ENNReal.toReal_ofReal]
  · norm_num
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hnonneg]
  · positivity

theorem malliavin_zero_of_dense_duality
    {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Lp ℝ 2 (whiteNoiseDerivativeMeasure P)}
    {S : Set (Lp ℝ 2 (whiteNoiseDerivativeMeasure P))}
    (hS : Dense S)
    (hdual : ∀ V, V ∈ S →
      (ContinuousLinearMap.mul ℝ ℝ).lpPairing (whiteNoiseDerivativeMeasure P) 2 2 G V = 0) :
    G = 0 := by
  let ℓ : Lp ℝ 2 (whiteNoiseDerivativeMeasure P) →L[ℝ] ℝ :=
    ((ContinuousLinearMap.mul ℝ ℝ).lpPairing (whiteNoiseDerivativeMeasure P) 2 2) G
  have hclosed : IsClosed {V | ℓ V = 0} := by
    exact isClosed_eq ℓ.continuous continuous_const
  have hG : G ∈ closure S := by
    exact hS G
  have hsubset : S ⊆ {V | ℓ V = 0} := by
    intro V hV
    exact hdual V hV
  have hclsubset : closure S ⊆ {V | ℓ V = 0} := by
    calc
      closure S ⊆ closure {V | ℓ V = 0} := closure_mono hsubset
      _ = {V | ℓ V = 0} := hclosed.closure_eq
  have hzero : ℓ G = 0 := hclsubset hG
  have hnorm : ‖G‖ ^ 2 = 0 := by
    calc
      ‖G‖ ^ 2 = (ContinuousLinearMap.mul ℝ ℝ).lpPairing
          (whiteNoiseDerivativeMeasure P) 2 2 G G :=
        (malliavinLpPairing_self_eq_norm_sq).symm
      _ = 0 := hzero
  have : ‖G‖ = 0 := by
    exact (sq_eq_zero_iff).mp hnorm
  exact norm_eq_zero.mp this

theorem malliavin_derivative_closable_of_dense_duality
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ}
    {G : Lp ℝ 2 (whiteNoiseDerivativeMeasure P)}
    (q : ℕ → Lp ℝ 2 P × Lp ℝ 2 (whiteNoiseDerivativeMeasure P))
    (_hq : ∀ n, q n ∈ cylindricalMalliavinGraph P W)
    (hvalue : Tendsto (fun n => (q n).1) atTop (𝓝 0))
    (hderivative : Tendsto (fun n => (q n).2) atTop (𝓝 G))
    {S : Set (Lp ℝ 2 (whiteNoiseDerivativeMeasure P))}
    (hS : Dense S)
    (K : Lp ℝ 2 (whiteNoiseDerivativeMeasure P) → Lp ℝ 2 P)
    (hdual : ∀ n V, V ∈ S →
      (ContinuousLinearMap.mul ℝ ℝ).lpPairing (whiteNoiseDerivativeMeasure P) 2 2
          (q n).2 V =
        (ContinuousLinearMap.mul ℝ ℝ).lpPairing P 2 2 (q n).1 (K V)) :
    G = 0 := by
  apply malliavin_zero_of_dense_duality hS
  intro V hV
  have hleft : Tendsto
      (fun n => (ContinuousLinearMap.mul ℝ ℝ).lpPairing
        (whiteNoiseDerivativeMeasure P) 2 2 (q n).2 V) atTop
      (𝓝 ((ContinuousLinearMap.mul ℝ ℝ).lpPairing
        (whiteNoiseDerivativeMeasure P) 2 2 G V)) := by
    have hp := ((ContinuousLinearMap.mul ℝ ℝ).lpPairing
      (whiteNoiseDerivativeMeasure P) 2 2).continuous₂.comp₂ continuous_fst continuous_snd
    have hprod : Tendsto (fun n => ((q n).2, V)) atTop (𝓝 (G, V)) := by
      rw [nhds_prod_eq]
      exact hderivative.prodMk
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => V) atTop (𝓝 V))
    have ht := (hp.tendsto (G, V)).comp hprod
    change Tendsto (fun n => (ContinuousLinearMap.mul ℝ ℝ).lpPairing
      (whiteNoiseDerivativeMeasure P) 2 2 (q n).2 V) atTop
      (𝓝 ((ContinuousLinearMap.mul ℝ ℝ).lpPairing
        (whiteNoiseDerivativeMeasure P) 2 2 G V)) at ht
    exact ht
  have hright : Tendsto
      (fun n => (ContinuousLinearMap.mul ℝ ℝ).lpPairing P 2 2 (q n).1 (K V)) atTop
      (𝓝 0) := by
    have hp := ((ContinuousLinearMap.mul ℝ ℝ).lpPairing P 2 2).continuous₂.comp₂
      continuous_fst continuous_snd
    have hprod : Tendsto (fun n => ((q n).1, K V)) atTop (𝓝 (0, K V)) := by
      rw [nhds_prod_eq]
      exact hvalue.prodMk
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => K V) atTop (𝓝 (K V)))
    have ht := (hp.tendsto (0, K V)).comp hprod
    change Tendsto
      ((fun w : Lp ℝ 2 P × Lp ℝ 2 P =>
        (ContinuousLinearMap.mul ℝ ℝ).lpPairing P 2 2 w.1 w.2) ∘
        (fun n => ((q n).1, K V))) atTop
      (𝓝 ((ContinuousLinearMap.mul ℝ ℝ).lpPairing P 2 2 0 (K V))) at ht
    have hfun :
        ((fun w : Lp ℝ 2 P × Lp ℝ 2 P =>
          (ContinuousLinearMap.mul ℝ ℝ).lpPairing P 2 2 w.1 w.2) ∘
          (fun n => ((q n).1, K V))) =
        (fun n => (ContinuousLinearMap.mul ℝ ℝ).lpPairing P 2 2 (q n).1 (K V)) := by
      funext n
      rfl
    rw [hfun] at ht
    simpa using ht
  have hlim : Tendsto
      (fun n => (ContinuousLinearMap.mul ℝ ℝ).lpPairing
        (whiteNoiseDerivativeMeasure P) 2 2 (q n).2 V) atTop (𝓝 0) := by
    have heq : (fun n => (ContinuousLinearMap.mul ℝ ℝ).lpPairing
        (whiteNoiseDerivativeMeasure P) 2 2 (q n).2 V) =
        (fun n => (ContinuousLinearMap.mul ℝ ℝ).lpPairing P 2 2 (q n).1 (K V)) := by
      funext n
      exact hdual n V hV
    rw [heq]
    exact hright
  exact tendsto_nhds_unique hleft hlim

end RegularityStructures

end
