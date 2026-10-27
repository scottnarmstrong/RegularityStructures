module

public import GlobalPhi43.Attachment.IntegerModelMoments

/-! # Actual N=5 reference model/potential moment profiles before all noise spaces -/

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open scoped ENNReal NNReal

namespace GlobalPhi43.Attachment

universe u

/-- Full integer profiles are chosen from source constants before the space.
The reference models and potentials satisfy the required almost-everywhere bounds. -/
theorem reference_integer_profiles (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ) :
    ∃ CX CY : ℕ → ℝ≥0,
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : (SpaceTime → ℝ) → Ω → ℝ), IsWhiteNoise P W →
      ∀ (ξ : ℝ → Ω → SpaceTime → ℝ)
        (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε)),
      let Z := Flow.referenceAttachedModel 5 κ ρ mass ξ (fun ε hε => (hξ ε hε).1)
      let ψ := Flow.referencePotential ξ (fun ε hε => (hξ ε hε).1)
      ∀ p : ℕ, 1 ≤ p → ∀ ε ∈ Ioc (0 : ℝ) 1,
        AEMeasurable (fun ω => (Z ε ω).normOn (gamma κ) (Flow.majorantRegion 0)) P ∧
        (∫⁻ ω, (Z ε ω).normOn (gamma κ) (Flow.majorantRegion 0) ^ p ∂P ≤ CX p) ∧
        (∫⁻ ω, Flow.unitPotentialSize (Flow.lossExponent κ) 0 (ψ ε ω) ^ p ∂P ≤ CY p) := by
  classical
  have hx (p : {p : ℕ // 1 ≤ p}) := model_integer_moment.{u} 5 le_rfl κ hκE ρ hρ mass
    (Flow.majorantRegion 0) (isCompact_majorantRegion 0) p.val p.property
  have hy (p : {p : ℕ // 1 ≤ p}) := potential_integer_moment.{u}
    (Flow.lossExponent κ) (Flow.lossExponent_lt κ) ρ hρ p.val p.property
  choose CX hCX using hx
  choose CY hCY using hy
  refine ⟨(fun p => if hp : 1 ≤ p then CX ⟨p, hp⟩ else 0),
    (fun p => if hp : 1 ≤ p then CY ⟨p, hp⟩ else 0), ?_⟩
  intro Ω _ P _ W hW ξ hξ
  dsimp only
  intro p hp ε hε
  let hs := fun e he => (hξ e he).1
  let Z := Flow.referenceAttachedModel 5 κ ρ mass ξ hs
  let ψ := Flow.referencePotential ξ hs
  have hψ := fun e he => Flow.referencePotential_ae P W hW ρ hρ ξ hξ (ε := e) he
  have hlift := fun e he => Flow.referenceAttachedModel_lift_ae P W hW 5 κ ρ hρ mass ξ hξ ψ hψ (ε := e) he
  have hX := hCX ⟨p, hp⟩ P W hW ξ hξ Z ψ hlift ε hε
  have hY := hCY ⟨p, hp⟩ P W hW ξ hξ ψ hψ ε hε
  simpa only [dite_eq_left hp] using And.intro hX.1 (And.intro hX.2 hY)

end GlobalPhi43.Attachment
