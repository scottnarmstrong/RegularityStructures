module

public import GlobalPhi43.Flow.ReferenceTheoremAComparison
public import GlobalPhi43.Flow.FullRegularisedSolutions
public import GlobalPhi43.Flow.EventFlowLimitTransfer
public import GlobalPhi43.Flow.ReferenceFlowB1
public import Phi43.TheoremA

public noncomputable section

open MeasureTheory Set Filter Topology RegularityStructures RegularityStructures.Phi43
open scoped ENNReal

namespace GlobalPhi43.Flow

/-- For each fixed deterministic start, Theorem A and its mollifier uniqueness
identify every admissible regularisation with the SAME constructed global
path. Neither a comparison limit nor convergence is a caller premise. The
almost-sure identification is not intersected over starts or mollifiers. -/
theorem referenceFlow_limit_any_mollifier {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (N : ℕ) (hN : 5 ≤ N) (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ)
    (η : NegExponent) (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (hκη : κ.1 < -(1 / 2 : ℝ) - η)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
    (u : EventFlow (referenceEvent N κ ρ mass η ξ (fun ε hε => (hξ ε hε).1)) η
      (fun ω => dyadicLiftData N κ ρ mass η ξ (fun ε hε => (hξ ε hε).1) ω.val ω.property))
    (s : ℝ) (hs : 0 ≤ s)
    (ρ' : ParabolicSpace → ℝ) (hρ' : IsMollifier ρ')
    (ξ' : ℝ → Ω → SpaceTime → ℝ)
    (hξ' : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P (shiftWhiteNoise W s) ρ' ε (ξ' ε))
    (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x)
    (U' : ℝ → Ω → ℝ → C(Torus3, ℝ))
    (hU' : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsClassicalSolution
      (mass + 3 * wickConstant ρ' ε - 9 * sunsetConstant ρ' ε) (ξ' ε ω) x (U' ε ω)) :
    IsPhi43Limit P η x U' (fun _ => ⊤) (fun ω t => u.value ω (s + t) s (toHolderBesov η x)) := by
  let hsmooth := fun ε hε => (hξ ε hε).1
  let U := regularisedClassicalFamily ρ mass ξ hsmooth s x hx
  have hU := regularisedClassicalFamily_spec ρ mass ξ hsmooth s x hx
  have hWs := Attachment.whiteNoise_time_translate hW s
  have hξs := regularisedFamily_shifted_noise hξ s
  obtain ⟨τ, v, hv, huniq⟩ := RegularityStructures.Phi43.theoremA P (shiftWhiteNoise W s) hWs
    mass x hx η hη ρ hρ (fun ε ω => shiftForcing s (ξ ε ω)) hξs U hU
  have hid := reference_limit_global P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ
    u s hs x hx U hU τ v hv
  obtain ⟨τ', v', hv', _⟩ := RegularityStructures.Phi43.theoremA P (shiftWhiteNoise W s) hWs
    mass x hx η hη ρ' hρ' ξ' hξ' U' hU'
  obtain ⟨hτeq, hveq⟩ := huniq ρ' ξ' U' τ' v' hρ' hξ' hU' hv'
  have htop : ∀ᵐ ω ∂P, τ' ω = ⊤ := by
    filter_upwards [hτeq, hid.1] with ω hτeq htop
    exact hτeq.trans htop
  have heq : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → v' ω t = u.value ω (s + t) s (toHolderBesov η x) := by
    filter_upwards [hveq, hid.1, hid.2] with ω hveq htop heq t ht
    exact (hveq t ht (by simpa only [htop] using ENNReal.ofReal_lt_top (r := t))).trans (heq t ht)
  exact u.globalLimit_of_identification
    (referenceEventFlow_B1 P W hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u)
    s hs x U' τ' v' hv' htop heq

end GlobalPhi43.Flow
