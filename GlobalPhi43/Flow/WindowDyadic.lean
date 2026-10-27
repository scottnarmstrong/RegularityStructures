module

public import GlobalPhi43.Flow.WindowMoments
public import Phi43.BPHZ.GModelsNoiseDist
public import RegularityStructures.BPHZ.ModelNormTriangle

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open scoped ENNReal

namespace GlobalPhi43.Flow

universe u

variable {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
  (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa) (N : ℕ) (hN : 5 ≤ N)
  (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (a : ℝ)
  (ξ : ℝ → Ω → SpaceTime → ℝ)
  (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
  (Z : ℝ → Ω → Model (phi43RegularityStructure κ) parabolicSemigroup)
  (ψ : ℝ → Ω → ℝ → C(Torus3, ℝ))
  (hlift : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
    Statements.IsModeratePhi43Lift N κ (ξ ε ω)
      (wickConstant ρ ε + a / 3, sunsetConstant ρ ε + 0) (Z ε ω) (ψ ε ω))

include W hW hκE N hN ρ hρ a ξ hξ hlift

/-- The same reference lift sequence is bounded and Cauchy on the literal compact S_k.
There is no supplied moment bound or shift-rate premise. -/
theorem ae_window_dyadic (η : NegExponent) (hη : (η : ℝ) < -(1 / 2 : ℝ))
    (k : ℝ) (hk : 18 ≤ k) :
    ∀ᵐ ω ∂P,
      (∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀,
        (Z ((2⁻¹ : ℝ) ^ n) ω).diffNormOn (Z ((2⁻¹ : ℝ) ^ m) ω) (gamma κ) (windowSet k) +
          Statements.phi43NoiseDist η k (ψ ((2⁻¹ : ℝ) ^ n) ω) (ψ ((2⁻¹ : ℝ) ^ m) ω) ≤
            ENNReal.ofReal δ) ∧
      ∃ B : ℝ, ∀ n : ℕ,
        (Z ((2⁻¹ : ℝ) ^ n) ω).normOn (gamma κ) (windowSet k) +
          Statements.phi43NoiseSize η k (ψ ((2⁻¹ : ℝ) ^ n) ω) ≤ ENNReal.ofReal B := by
  obtain ⟨θ, C, Cs, hθ, hC, -, hS, hD, -⟩ :=
    window_moments P W hW κ hκE N hN ρ hρ a ξ hξ Z ψ hlift η hη k hk
  apply ae_dyadic_of_momentBound hθ hC hD hS
  · exact ae_of_all _ fun ω n m => by rw [Model.diffNormOn_comm, phi43NoiseDist_comm]
  · exact ae_of_all _ fun ω n => by simp [Model.diffNormOn_self, phi43NoiseDist_self]
  · exact ae_of_all _ fun ω n l m =>
      (add_le_add Model.diffNormOn_triangle (phi43NoiseDist_triangle η k _ (ψ _ ω) _)).trans
        (le_of_eq (add_add_add_comm _ _ _ _))
  · exact ae_of_all _ fun ω n =>
      (add_le_add Model.normOn_le_add_diffNormOn (phi43NoiseSize_le_add_dist η k _ _)).trans
        (le_of_eq (add_add_add_comm _ _ _ _))

end GlobalPhi43.Flow
