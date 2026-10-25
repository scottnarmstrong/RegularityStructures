/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureAutomaticDuality
public import RegularityStructures.Probability.MalliavinClosureD1
public import RegularityStructures.Probability.MalliavinClosureRelativeClosability
public import RegularityStructures.Probability.MalliavinClosureCalculus
public import RegularityStructures.Probability.MalliavinClosureSpectralGap

/-!
# Closure-level Malliavin consequences

This module records the operator-theoretic passage from the cylindrical graph to its `L²`
closure.  The sequence closability theorem keeps the duality operator and its dense test set
explicit.  The chain and product theorems are continuous-closure transport statements: their
inputs are the concrete `L²` maps obtained from a bounded `C¹` scalar chain rule or a bounded
product rule, together with their cylindrical-core identities.  This is the closed-graph form of
[HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace RegularityStructures

theorem malliavin_cylindrical_derivative_representation_independent
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ}
    {n m : ℕ} {h : Fin n → SpaceTime → ℝ} {k : Fin m → SpaceTime → ℝ}
    {f : (Fin n → ℝ) → ℝ} {g : (Fin m → ℝ) → ℝ}
    (hW : IsWhiteNoise P W)
    (hmem_h : ∀ i, MemLp (h i) 2) (hmem_k : ∀ j, MemLp (k j) 2)
    (hcont_f : ContDiff ℝ 1 f) (hcont_g : ContDiff ℝ 1 g)
    (hgrowth_sub : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin (n + m) → ℝ,
        |f (malliavinConcatLeftCLM n m x) -
            g (malliavinConcatRightCLM n m x)| +
          ‖fderiv ℝ (fun y => f (malliavinConcatLeftCLM n m y) -
            g (malliavinConcatRightCLM n m y)) x‖ ≤ K * (1 + ‖x‖) ^ M)
    (hfg : cylindricalFunctional W h f =ᵐ[P] cylindricalFunctional W k g)
    (hDsub : MemLp (fun p : Ω × SpaceTime =>
      cylindricalDerivative W (malliavinConcatTest h k)
        (fun y => f (malliavinConcatLeftCLM n m y) -
          g (malliavinConcatRightCLM n m y)) p.1 p.2) 2
      (whiteNoiseDerivativeMeasure P)) :
    (fun p : Ω × SpaceTime => cylindricalDerivative W h f p.1 p.2) =ᵐ[
      whiteNoiseDerivativeMeasure P]
      (fun p => cylindricalDerivative W k g p.1 p.2) := by
  exact cylindricalDerivative_wellDefined hW hmem_h hmem_k hcont_f hcont_g
    hgrowth_sub hfg hDsub

theorem malliavin_derivative_closable_sequence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ}
    {G : Lp ℝ 2 (whiteNoiseDerivativeMeasure P)}
    (q : ℕ → Lp ℝ 2 P × Lp ℝ 2 (whiteNoiseDerivativeMeasure P))
    (hq : ∀ n, q n ∈ cylindricalMalliavinGraph P W)
    (hvalue : Tendsto (fun n => (q n).1) atTop (𝓝 0))
    (hderivative : Tendsto (fun n => (q n).2) atTop (𝓝 G))
    {S : Set (Lp ℝ 2 (whiteNoiseDerivativeMeasure P))}
    (hS : Dense S)
    (K : Lp ℝ 2 (whiteNoiseDerivativeMeasure P) → Lp ℝ 2 P)
    (hdual : ∀ n V, V ∈ S →
      (ContinuousLinearMap.mul ℝ ℝ).lpPairing
          (whiteNoiseDerivativeMeasure P) 2 2 (q n).2 V =
        (ContinuousLinearMap.mul ℝ ℝ).lpPairing P 2 2 (q n).1 (K V)) :
    G = 0 := by
  exact malliavin_derivative_closable_of_dense_duality q hq hvalue hderivative hS K hdual

theorem malliavin_sobolev_spectral_gap
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W) (u : MalliavinSobolev P W) :
    malliavinVariance P (malliavinValue u) ≤ ‖malliavinDerivative u‖ ^ 2 := by
  exact malliavin_spectral_gap hW u

theorem malliavin_chain_rule_closure_transport
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ}
    (T : (Lp ℝ 2 P × Lp ℝ 2 (whiteNoiseDerivativeMeasure P)) →
      (Lp ℝ 2 P × Lp ℝ 2 (whiteNoiseDerivativeMeasure P)))
    (hT : Continuous T)
    (hcore : ∀ q, q ∈ cylindricalMalliavinGraph P W →
      T q ∈ cylindricalMalliavinGraph P W)
    (u : MalliavinSobolev P W) :
    T u.1 ∈ MalliavinSobolev P W := by
  exact malliavin_closure_map T hT hcore u

theorem malliavin_product_rule_closure_transport
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ}
    (T : ((Lp ℝ 2 P × Lp ℝ 2 (whiteNoiseDerivativeMeasure P)) ×
      (Lp ℝ 2 P × Lp ℝ 2 (whiteNoiseDerivativeMeasure P))) →
      (Lp ℝ 2 P × Lp ℝ 2 (whiteNoiseDerivativeMeasure P)))
    (hT : Continuous T)
    (hcore : ∀ q₁ q₂,
      q₁ ∈ cylindricalMalliavinGraph P W → q₂ ∈ cylindricalMalliavinGraph P W →
      T (q₁, q₂) ∈ cylindricalMalliavinGraph P W)
    (u v : MalliavinSobolev P W) :
    T (u.1, v.1) ∈ MalliavinSobolev P W := by
  let S := cylindricalMalliavinGraph P W
  have huv : (u.1, v.1) ∈ closure (S ×ˢ S) := by
    rw [closure_prod_eq]
    exact ⟨u.2, v.2⟩
  have hclosed : IsClosed (T ⁻¹' closure S) := by
    exact isClosed_closure.preimage hT
  have hsubset : S ×ˢ S ⊆ T ⁻¹' closure S := by
    rintro ⟨q₁, q₂⟩ ⟨hq₁, hq₂⟩
    exact subset_closure (hcore q₁ q₂ hq₁ hq₂)
  exact hclosed.closure_subset_iff.mpr hsubset huv

end RegularityStructures

end
