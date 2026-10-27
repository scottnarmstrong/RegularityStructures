module

public import GlobalPhi43.Assembly.ReferenceFlowMoments
public import GlobalPhi43.Flow.ReferenceGlobalAssembly
public import GlobalPhi43.Proofs.GlobalDynamicsProfile

public noncomputable section

open MeasureTheory ProbabilityTheory Set RegularityStructures RegularityStructures.Phi43
open scoped ENNReal NNReal

namespace GlobalPhi43.Flow
open Attachment

universe u
section Reference
variable {Ω : Type u} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
  (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
  (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ)
  (a : ℝ) (η : NegExponent)
  (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
variable (ξ : ℝ → Ω → SpaceTime → ℝ)
  (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
include hW hρ
local notation "hs" => (fun ε hε => And.left (hξ ε hε))
local notation "κ" => selectedLoss η (And.right hη)
local notation "E" => referenceEvent 5 κ ρ a η ξ hs
local notation "A" => (fun ω : E => dyadicLiftData 5 κ ρ a η ξ hs
  (Subtype.val ω) (Subtype.property ω))

/-- The global flow properties for the specified reference flow follow from the
noise data. One law gives both averaged-law convergence and stationarity on the
product measure P.prod mu, without extra moment or invariant-law assumptions. -/
theorem referenceEventFlow_global (U : EventFlow E η A) :
    ∃ μ : ProbabilityMeasure (HolderBesov η),
      IsGlobalPhi43Flow (globalDynamicsProfile.{u} a η) P W a η E
        (fun t s x ω => U.value ω t s x) (μ : Measure _) ∧
      ∀ α, (η : ℝ) ≤ α → α < -(1 / 2 : ℝ) → ∀ p : ℝ, 1 ≤ p →
        ∫⁻ z, extNorm η α z ^ p ∂(μ : Measure _) ≤ globalDynamicsProfile.{u} a α p := by
  have hκ := selectedLoss_spec η hη.2
  obtain ⟨h4, hstrong⟩ := Assembly.reference_flow_B4_and_stronger P W hW
    ρ hρ a η hη ξ hξ U
  exact referenceEventFlow_global_of_moments P W hW 5 (by norm_num) κ hκ.1
    ρ hρ a η hη hκ.2 ξ hξ
    (globalDynamicsProfile.{u} a η) (globalDynamicsProfile.{u} a) U
    h4 hstrong

end Reference
end GlobalPhi43.Flow
