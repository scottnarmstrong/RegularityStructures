module

public import GlobalPhi43.Attachment.TranslateNorm
public import GlobalPhi43.Attachment.TranslateRealisation
public import RegularityStructures.Abstract.Translate.Realising
public import Phi43.Restart.GrowthTranslate
public import Phi43Statements.Defs.IsModeratePhi43ModelOf

/-! Clause-by-clause translation of the generic moderate-model predicate.
The negative-realisation input is proved for arbitrary canonical noise in TranslateRealisation. -/

public section

namespace GlobalPhi43.Attachment

open RegularityStructures RegularityStructures.Phi43

/-- Translation of the generic canonical predicate, with unchanged constants. -/
theorem moderateRenormalisedModel_translate {N : ℕ} {κ : Kappa} {noise : CanonicalNoise}
    {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hZ : Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z) (a : ParabolicSpace) :
    Statements.IsModerateRenormalisedCanonicalModel N κ (translateNoise noise a) C
      (Z.translate a) := by
  obtain ⟨hadm, hreal, hnorm, ρ, p, B, hρ, hB, hbound⟩ := hZ
  refine ⟨Model.isRealisingP_translate Z a hadm, ?_, ?_,
    (fun z => ρ (z + a)), p, B, Model.isModerateWeight_translate hρ a, hB, ?_⟩
  · intro τ hτ x t ht z
    rw [Model.regPi_translate, hreal τ hτ (x + a) t ht (z + a)]
    rw [← parabolicSemigroup_apply_translate a]
    congr 1
    funext y
    exact (renormalisedPi_fMinus_translate N κ noise C a x y τ hτ).symm
  · intro S hS
    rw [Model.normOn_translate]
    exact hnorm _ (hS.image (continuous_id.add continuous_const))
  · intro i hi t ht x
    exact hbound i hi t ht (x + a)

/-- Translation covariance for arbitrary periodic smooth noise, any moderate model,
any real time shift. No growth or regularised-noise specialisation is assumed. -/
theorem moderatePhi43Model_translate {N : ℕ} {κ : Kappa} {f : SpaceTime → ℝ}
    {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hZ : Statements.IsModeratePhi43ModelOf N κ f C Z) (k : ℝ) :
    Statements.IsModeratePhi43ModelOf N κ (fun z => f (z.1 + k, z.2)) C
      (Z.translate (k, 0)) := by
  obtain ⟨noise, hn, hZ⟩ := hZ
  refine ⟨translateNoise noise (k, 0), ?_, moderateRenormalisedModel_translate hZ (k, 0)⟩
  intro z
  change noise.zeta (z + (k, 0)) = f (z.1 + k, torusProj z.2)
  rw [hn]
  congr 1
  apply Prod.ext
  · rfl
  · change torusProj (z.2 + 0) = torusProj z.2
    rw [add_zero]

end GlobalPhi43.Attachment
