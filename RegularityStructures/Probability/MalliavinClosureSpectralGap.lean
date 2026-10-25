/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureCore
public import Mathlib.MeasureTheory.Function.Holder

/-!
# The spectral gap on the Malliavin closure

The `L²` pairing is continuous after Hölder's `2,2,1` multiplication.  Consequently the variance
minus derivative-energy sublevel set is closed in the product `L² × L²`; the cylindrical
white-noise spectral gap therefore extends to the closure of the cylindrical graph.  This is the
closed-graph form of the `D^{1,2}` spectral gap used for the infinite-coordinate functionals in
[HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The continuous `L²` scalar pairing, written as an iterated continuous linear map. -/
def malliavinLpPairing (P : Measure Ω) :
    Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing P 2 2

/-- The `L²` representative of the constant one. -/
def malliavinOne (P : Measure Ω) [IsFiniteMeasure P] : Lp ℝ 2 P :=
  Lp.const 2 P 1

/-- The mean of an `L²` class, defined by pairing with one. -/
def malliavinMean (P : Measure Ω) [IsFiniteMeasure P] (F : Lp ℝ 2 P) : ℝ :=
  malliavinLpPairing P F (malliavinOne P)

/-- The variance functional on `L²`, expressed through the centered representative. -/
def malliavinVariance (P : Measure Ω) [IsFiniteMeasure P] (F : Lp ℝ 2 P) : ℝ :=
  malliavinLpPairing P
    (F - malliavinMean P F • malliavinOne P)
    (F - malliavinMean P F • malliavinOne P)

/-- The closed variance-energy sublevel set in the product `L² × L²`. -/
def malliavinGapSet (P : Measure Ω) [IsFiniteMeasure P] :
    Set (Lp ℝ 2 P × Lp ℝ 2 (whiteNoiseDerivativeMeasure P)) :=
  {q | malliavinVariance P q.1 ≤ ‖q.2‖ ^ 2}

theorem continuous_malliavinMean (P : Measure Ω) [IsFiniteMeasure P] :
    Continuous (malliavinMean P) := by
  unfold malliavinMean
  exact (malliavinLpPairing P).continuous₂.comp₂ continuous_id continuous_const

theorem continuous_malliavinVariance (P : Measure Ω) [IsFiniteMeasure P] :
    Continuous (malliavinVariance P) := by
  let c : Lp ℝ 2 P → Lp ℝ 2 P :=
    fun F => F - malliavinMean P F • malliavinOne P
  have hc : Continuous c := by
    dsimp [c]
    exact continuous_id.sub ((continuous_malliavinMean P).smul continuous_const)
  unfold malliavinVariance
  exact (malliavinLpPairing P).continuous₂.comp₂ hc hc

theorem isClosed_malliavinGapSet (P : Measure Ω) [IsFiniteMeasure P] :
    IsClosed (malliavinGapSet P) := by
  unfold malliavinGapSet
  apply isClosed_le
  · exact (continuous_malliavinVariance P).comp continuous_fst
  · exact (continuous_norm.pow 2).comp continuous_snd

theorem malliavinMean_toLp {P : Measure Ω} [IsFiniteMeasure P]
    {F : Ω → ℝ} (hF : MemLp F 2 P) :
    malliavinMean P (hF.toLp F) = ∫ ω, F ω ∂P := by
  unfold malliavinMean malliavinLpPairing malliavinOne
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp, Lp.coeFn_const (2 : ENNReal) P (1 : ℝ)] with ω hω h₁
  rw [hω, h₁]
  change F ω * 1 = F ω
  simp

theorem malliavinVariance_toLp {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Ω → ℝ} (hF : MemLp F 2 P) :
    malliavinVariance P (hF.toLp F) = Var[F; P] := by
  rw [malliavinVariance]
  unfold malliavinLpPairing malliavinOne
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  rw [variance_eq_integral hF.aemeasurable]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp,
    Lp.coeFn_sub (hF.toLp F) (malliavinMean P (hF.toLp F) • malliavinOne P),
    Lp.coeFn_smul (malliavinMean P (hF.toLp F)) (malliavinOne P)] with ω hω hsub hsmul
  rw [ContinuousLinearMap.mul_apply']
  change
    (((hF.toLp F - malliavinMean P (hF.toLp F) • malliavinOne P : Lp ℝ 2 P) : Ω → ℝ) ω) *
        (((hF.toLp F - malliavinMean P (hF.toLp F) • malliavinOne P : Lp ℝ 2 P) : Ω → ℝ) ω) = _
  rw [hsub]
  change
    ((((hF.toLp F : Lp ℝ 2 P) : Ω → ℝ) ω) -
        (((malliavinMean P (hF.toLp F) • malliavinOne P : Lp ℝ 2 P) : Ω → ℝ) ω)) *
      ((((hF.toLp F : Lp ℝ 2 P) : Ω → ℝ) ω) -
        (((malliavinMean P (hF.toLp F) • malliavinOne P : Lp ℝ 2 P) : Ω → ℝ) ω)) = _
  rw [hω, hsmul]
  rw [malliavinMean_toLp hF]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hone : (((malliavinOne P : Lp ℝ 2 P) : Ω → ℝ) ω) = 1 := by
    simp [malliavinOne]
  rw [hone]
  simp only [mul_one]
  change (F ω - (∫ x, F x ∂P)) * (F ω - (∫ x, F x ∂P)) = _
  ring

theorem malliavinEnergy_toLp {P : Measure Ω} [IsFiniteMeasure P]
    {D : Ω × SpaceTime → ℝ}
    (hD : MemLp D 2 (whiteNoiseDerivativeMeasure P)) :
    ‖hD.toLp D‖ ^ 2 =
      ∫ p, D p ^ 2 ∂(whiteNoiseDerivativeMeasure P) := by
  have hnonneg : 0 ≤ ∫ p, D p ^ 2 ∂whiteNoiseDerivativeMeasure P :=
    integral_nonneg fun p => sq_nonneg _
  rw [Lp.norm_toLp]
  rw [hD.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  rw [ENNReal.toReal_ofReal]
  · norm_num
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hnonneg]
  · positivity

theorem cylindricalMalliavinGraph_subset_gapSet
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W) :
    cylindricalMalliavinGraph P W ⊆ malliavinGapSet P := by
  intro q hq
  rcases hq with ⟨n, h, f, hmem, hcont, hgrowth, hF, hD, rfl⟩
  have hgap := whiteNoise_cylindrical_spectral_gap hW hmem hcont hgrowth
  change malliavinVariance P (hF.toLp (cylindricalFunctional W h f)) ≤
    ‖hD.toLp (fun p : Ω × SpaceTime => cylindricalDerivative W h f p.1 p.2)‖ ^ 2
  rw [malliavinVariance_toLp hF]
  rw [malliavinEnergy_toLp hD]
  change Var[cylindricalFunctional W h f; P] ≤
    ∫ p, cylindricalDerivative W h f p.1 p.2 ^ 2 ∂(P.prod (volume : Measure SpaceTime))
  rw [integral_prod _ hD.integrable_sq]
  exact hgap

theorem malliavin_spectral_gap
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W)
    (u : MalliavinSobolev P W) :
    malliavinVariance P (malliavinValue u) ≤
      ‖malliavinDerivative u‖ ^ 2 := by
  have hsubset := cylindricalMalliavinGraph_subset_gapSet hW
  have hcl : closure (cylindricalMalliavinGraph P W) ⊆ malliavinGapSet P := by
    exact (isClosed_malliavinGapSet P).closure_subset_iff.mpr hsubset
  exact hcl u.2

end RegularityStructures

end
