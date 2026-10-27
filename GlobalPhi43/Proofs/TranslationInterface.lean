module

public import GlobalPhi43.Attachment.TranslateIdentification
public import GlobalPhi43.Attachment.NoiseGrowthTranslate

/-! Translation of model bounds and noise growth, without identifying representatives above the cutoff. -/

public section

namespace GlobalPhi43
open RegularityStructures RegularityStructures.Phi43

/-- The generic translation interface: bounds, predicate transport, norm choice-independence,
and noise growth. The predicate clause is independent of a noise space or growth premise. -/
theorem translationInterface :
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (𝒯 : RegularityStructure ι)
        (M M₂ : Model 𝒯 parabolicSemigroup) (a : ParabolicSpace) (γ C : ℝ) (S : Set ParabolicSpace),
      ((M.translate a).GammaBoundOn γ C S ↔ M.GammaBoundOn γ C ((· + a) '' S)) ∧
      ((M.translate a).GammaDiffBoundOn (M₂.translate a) γ C S ↔
        M.GammaDiffBoundOn M₂ γ C ((· + a) '' S)) ∧
      (M.translate a).normOn γ S = M.normOn γ ((· + a) '' S) ∧
      (M.translate a).diffNormOn (M₂.translate a) γ S = M.diffNormOn M₂ γ ((· + a) '' S)) ∧
    (∀ (N : ℕ) (κ : Kappa) (f : SpaceTime → ℝ) (C : RenormalisationConstants)
        (Z : Model (phi43RegularityStructure κ) parabolicSemigroup) (k : ℝ),
      Statements.IsModeratePhi43ModelOf N κ f C Z →
      Statements.IsModeratePhi43ModelOf N κ (fun z => f (z.1 + k, z.2)) C
        (Z.translate (k, 0))) ∧
    (∀ (N : ℕ) (κ : Kappa) (f : SpaceTime → ℝ) (C : RenormalisationConstants)
        (Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup),
      Statements.IsModeratePhi43ModelOf N κ f C Z →
      Statements.IsModeratePhi43ModelOf N κ f C Z' →
      ∀ S : Set ParabolicSpace, Z.normOn (gamma κ) S = Z'.normOn (gamma κ) S) ∧
    ∀ (f : SpaceTime → ℝ) (k : ℝ), Statements.HasPhi43NoiseGrowth f →
      Statements.HasPhi43NoiseGrowth (fun z => f (z.1 + k, z.2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ι _ _ 𝒯 M M₂ a γ C S
    exact ⟨Model.gammaBoundOn_translate_iff M a, Model.gammaDiffBoundOn_translate_iff M a M₂,
      Model.normOn_translate M a γ S, Model.diffNormOn_translate M a M₂ γ S⟩
  · intro N κ f C Z k hZ
    exact Attachment.moderatePhi43Model_translate hZ k
  · intro N κ f C Z Z' hZ hZ' S
    exact Model.normOn_eq_of_diffNormOn_eq_zero
      (Attachment.moderateModels_diffNormOn_eq_zero_generic hZ hZ' S)
  · intro f k hg
    exact Attachment.noiseGrowth_time_translate hg k

end GlobalPhi43
