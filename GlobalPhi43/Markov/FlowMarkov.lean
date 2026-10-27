module

public import GlobalPhi43.Markov.ConditionalMarkov
public import GlobalPhi43.Markov.NoiseWindows
public import GlobalPhi43.Markov.FlowKernel
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

public noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open RegularityStructures

namespace GlobalPhi43.Markov

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {η : NegExponent} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η}

/-- The conditional Markov property from deterministic-window hypotheses.
Restart, adaptedness and homogeneity are separate hypotheses. -/
theorem flowTransition_condExp_of_restart (hW : IsWhiteNoise P W) (s t : ℝ)
    (x : HolderBesov η)
    (hpast : Measurable[noiseWindowSigma P W 0 s] (u s 0 x))
    (hfuture : @Measurable (HolderBesov η × Ω) (HolderBesov η)
      ((inferInstance : MeasurableSpace (HolderBesov η)).prod (noiseWindowSigma P W s (s + t)))
      inferInstance (fun p => u (s + t) s p.1 p.2))
    (hlaw : ∀ y, P.map (u (s + t) s y) = flowLaw P u t y)
    (hrestart : u (s + t) 0 x =ᵐ[P] fun ω => u (s + t) s (u s 0 x ω) ω)
    {f : HolderBesov η → ℝ} (hf : Measurable f) {C : ℝ} (hb : ∀ y, |f y| ≤ C) :
    P[fun ω => f (u (s + t) 0 x ω) | noiseWindowSigma P W 0 s] =ᵐ[P]
      fun ω => flowTransition P u t f (u s 0 x ω) := by
  let F : HolderBesov η × Ω → HolderBesov η := fun p => u (s + t) s p.1 p.2
  have hId : @Measurable Ω Ω mΩ (noiseWindowSigma P W s (s + t)) id :=
    Measurable.of_comap_le (by
      simpa only [MeasurableSpace.comap_id] using noiseWindowSigma_le P hW s (s + t))
  have hambient : Measurable F := hfuture.comp
    (measurable_fst.prodMk (hId.comp measurable_snd))
  let κ := sampleKernel P F hambient
  have hk (y : HolderBesov η) : κ y = flowLaw P u t y := hlaw y
  have he := conditional_markov_from_restart P (noiseWindowSigma_le P hW 0 s)
    (noiseWindowSigma_le P hW s (s + t)) (indep_noiseWindowSigma P hW le_rfl)
    hpast hfuture κ (fun _ => rfl) hrestart hf hb
  exact he.trans (ae_of_all _ fun ω => by
    change (∫ y, f y ∂κ (u s 0 x ω)) = flowTransition P u t f (u s 0 x ω)
    rw [hk]
    rfl)

end GlobalPhi43.Markov
