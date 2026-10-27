module

public import GlobalPhi43.Flow.ReferenceMarkovInputs
public import GlobalPhi43.Markov.Semigroup

public noncomputable section

open MeasureTheory ProbabilityTheory Set RegularityStructures RegularityStructures.Phi43
open scoped NNReal ENNReal

namespace GlobalPhi43.Flow

section Reference

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
  (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
  (N : ℕ) (hN : 5 ≤ N) (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa)
  (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ)
  (η : NegExponent) (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
  (hκη : κ.1 < -(1 / 2 : ℝ) - η)
  (ξ : ℝ → Ω → SpaceTime → ℝ)
  (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))

include hW hN hκE hρ hη hκη

local notation "E" => referenceEvent N κ ρ mass η ξ (fun ε hε => And.left (hξ ε hε))
local notation "A" => (fun ω : E => dyadicLiftData N κ ρ mass η ξ
  (fun ε hε => And.left (hξ ε hε)) (Subtype.val ω) (Subtype.property ω))

/-- The actual sampled probability kernel; no new flow or measurable version. -/
@[expose] def referenceFlowKernel (u : EventFlow E η A) (t : ℝ≥0) : Kernel (HolderBesov η) (HolderBesov η) :=
  Markov.sampleKernel P (fun p : HolderBesov η × Ω => u.value p.2 t 0 p.1)
    (referenceFlow_state_noise_measurable P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u t t.property)

instance referenceFlowKernel_isMarkovKernel (u : EventFlow E η A) (t : ℝ≥0) :
    IsMarkovKernel (referenceFlowKernel P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u t) := by
  unfold referenceFlowKernel
  infer_instance

/-- Both kernel composition orders follow from the proved conditional
law, not from a supplied semigroup or Chapman--Kolmogorov hypothesis. -/
theorem referenceFlowKernel_semigroup (u : EventFlow E η A) (s t : ℝ≥0) :
    let K := referenceFlowKernel P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u
    K (s + t) = K t ∘ₖ K s ∧ K (s + t) = K s ∘ₖ K t := by
  apply Markov.kernel_semigroup_of_conditional P
    (referenceFlowKernel P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u)
    (fun t x ω => u.value ω (t : ℝ) 0 x) (fun s => noiseWindowSigma P W 0 s)
    (fun s => Markov.noiseWindowSigma_le P hW 0 s)
    (fun t x => referenceFlow_sample_measurable P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u t t.property x)
    (fun _ _ => rfl) ?_ s t
  intro a b x f hf hb
  obtain ⟨C, hC⟩ := hb
  have he := referenceFlow_condExp P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ
    u a b a.property b.property x hf hC
  change P[fun ω => f (u.value ω ((a : ℝ) + (b : ℝ)) 0 x) |
    noiseWindowSigma P W 0 a] =ᵐ[P]
    fun ω => flowTransition P (fun t s x ω => u.value ω t s x) b f (u.value ω a 0 x)
  exact he

/-- The Chapman–Kolmogorov identity in the order P_(t+s)(x,B) = integral P_s(y,B) P_t(x,dy).
Zero times are included. -/
theorem referenceFlow_chapmanKolmogorov (u : EventFlow E η A) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (x : HolderBesov η) (B : Set (HolderBesov η)) (hB : MeasurableSet B) :
    flowLaw P (fun t s x ω => u.value ω t s x) (t + s) x B =
      ∫⁻ y, flowLaw P (fun t s x ω => u.value ω t s x) s y B
        ∂flowLaw P (fun t s x ω => u.value ω t s x) t x := by
  have he := (referenceFlowKernel_semigroup P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ
    u (⟨t, ht⟩ : ℝ≥0) ⟨s, hs⟩).1
  have hv := congrArg (fun K : Kernel (HolderBesov η) (HolderBesov η) => K x B) he
  rw [Kernel.comp_apply' _ _ x hB] at hv
  change flowLaw P (fun t s x ω => u.value ω t s x) (t + s) x B =
    ∫⁻ y, flowLaw P (fun t s x ω => u.value ω t s x) s y B
      ∂flowLaw P (fun t s x ω => u.value ω t s x) t x at hv
  exact hv

end Reference
end GlobalPhi43.Flow
