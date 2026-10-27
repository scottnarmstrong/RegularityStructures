module

public import Phi43.Mollifier
public import Phi43.Constants
public import Phi43.ClassicalSolution
public import RegularityStructures.Torus.HolderBesov
public import RegularityStructures.Probability.WhiteNoise
import GlobalPhi43.Proofs.RegularisedKernelAssembly

/-! Uniform regularised-solution bounds from kernel estimates, deterministic
half-cylinder bounds, physical covers and moment estimates. -/

public noncomputable section
namespace GlobalPhi43
open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open scoped ENNReal NNReal

universe u

/-- Uniform regularised-solution bounds: one deterministic profile before the source space,
one measurable majorant family before all scales, data, times and moment orders,
and every supplied classical solution family at every outcome. -/
theorem regularisedBound :
    ∀ (a : ℝ) (η' : ℝ) (_hη' : η' ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
      (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (_hρ : IsMollifier ρ),
    ∃ C : ℝ → ℝ≥0,
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
      (W : (SpaceTime → ℝ) → Ω → ℝ) (_hW : IsWhiteNoise P W)
      (ξ : ℝ → Ω → SpaceTime → ℝ) (_hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
      (uε : ℝ → C(Torus3, ℝ) → Ω → ℝ → C(Torus3, ℝ))
      (_hu : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ x : C(Torus3, ℝ), IsSmoothOnTorus x → ∀ ω, IsClassicalSolution
        (a + 3 * wickConstant ρ ε - 9 * sunsetConstant ρ ε) (ξ ε ω) x (uε ε x ω)),
    ∃ M : ℝ → Ω → ℝ,
      (∀ ε ∈ Ioc (0 : ℝ) 1, Measurable (M ε) ∧ ∀ ω, 0 ≤ M ε ω) ∧
      (∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, ∀ x : C(Torus3, ℝ), IsSmoothOnTorus x → ∀ t ∈ Ioc (0 : ℝ) 1,
        ENNReal.ofReal (√t) * holderBesovENorm η' (uε ε x ω t) ≤ ENNReal.ofReal (M ε ω)) ∧
      ∀ p : ℝ, 1 ≤ p →
        ⨆ ε ∈ Ioc (0 : ℝ) 1, ∫⁻ ω, ENNReal.ofReal (M ε ω) ^ p ∂P ≤ C p := by
  intro a η hη ρ hρ
  refine ⟨regularisedProfile.{u} a η ρ hρ,?_⟩
  intro Ω _ P _ _ W hW ξ hξ uε hu
  exact regularisedBound_profile.{u} a η hη ρ hρ P W hW ξ hξ uε hu

end GlobalPhi43
