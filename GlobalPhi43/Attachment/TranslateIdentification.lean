module

public import GlobalPhi43.Attachment.TranslatePredicate
public import GlobalPhi43.Attachment.TranslateNorm
public import Phi43.BPHZ.BphzCauchyTransfer
public import Phi43.Steps.RenormalisedCanonicalModel

/-! The zero-distance conclusion of the translation interface. -/

public section

namespace GlobalPhi43.Attachment

open RegularityStructures RegularityStructures.Phi43

/-- The weighted uniqueness proofs require only the moderate predicate. -/
theorem moderateModels_diffNormOn_eq_zero_generic {N : ℕ} {κ : Kappa}
    {f : SpaceTime → ℝ} {C : RenormalisationConstants}
    {Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hZ : Statements.IsModeratePhi43ModelOf N κ f C Z)
    (hZ' : Statements.IsModeratePhi43ModelOf N κ f C Z') (S : Set ParabolicSpace) :
    Z.diffNormOn Z' (gamma κ) S = 0 := by
  obtain ⟨noise, hn, hZ⟩ := hZ
  obtain ⟨noise', hn', hZ'⟩ := hZ'
  have he : noise' = noise := by
    cases noise with
    | mk f hf hp =>
      cases noise' with
      | mk f' hf' hp' =>
        have hfun : f' = f := (funext hn').trans (funext hn).symm
        subst hfun
        rfl
  subst he
  have hPi := renormalisedCanonicalModel_piDiffNormOn_eq_zero N κ noise' C Z Z' hZ hZ'
  have hGamma := renormalisedCanonicalModel_gammaDiffNormOn_eq_zero N κ noise' C Z Z' hZ hZ'
  have hzero : Z.diffNormOn Z' (gamma κ) Set.univ = 0 := by
    simp only [Model.diffNormOn, hPi, hGamma, add_zero]
  exact le_antisymm ((Model.diffNormOn_mono_set (Set.subset_univ S)).trans hzero.le) bot_le

end GlobalPhi43.Attachment
