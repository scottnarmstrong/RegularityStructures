module

public import GlobalPhi43.Attachment.TranslateNorm
public import Phi43.BPHZ.BphzCauchyTransfer
public import Phi43.Steps.RenormalisedCanonicalModel
public import Phi43.BPHZ.RandomCanonical

/-! The moderate model representative.
The choice is made from the proved moderate-model existence theorem. Outside the exact growth
event it is the model of zero noise, with the same renormalisation constants. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment

open RegularityStructures RegularityStructures.Phi43

/-- Smooth periodic noises of the stated growth have a moderate model. -/
theorem exists_moderateModel (N : ℕ) (κ : Kappa) (f : SpaceTime → ℝ)
    (C : RenormalisationConstants) (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) :
    ∃ Z : Model (phi43RegularityStructure κ) parabolicSemigroup,
      Statements.IsModeratePhi43ModelOf N κ f C Z := by
  let noise := canonicalNoiseOfSpaceTime f hf
  obtain ⟨Cg, q, hq⟩ := hg
  obtain ⟨Z, hZ⟩ := exists_isModerateRenormalisedCanonicalModel N κ noise Cg q hq C
  exact ⟨Z, noise, fun _ => rfl, hZ⟩

/-- A chosen representative; its norms are independent of the choice. -/
def moderateModel (N : ℕ) (κ : Kappa) (f : SpaceTime → ℝ)
    (C : RenormalisationConstants) (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) :
    Model (phi43RegularityStructure κ) parabolicSemigroup :=
  (exists_moderateModel N κ f C hf hg).choose

theorem moderateModel_spec (N : ℕ) (κ : Kappa) (f : SpaceTime → ℝ)
    (C : RenormalisationConstants) (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) :
    Statements.IsModeratePhi43ModelOf N κ f C (moderateModel N κ f C hf hg) :=
  (exists_moderateModel N κ f C hf hg).choose_spec

/-- The exact growth event, without replacing it by an arbitrary full-measure subset. -/
def growthEvent {Ω : Type*} (ξ : Ω → SpaceTime → ℝ) : Set Ω :=
  {ω | Statements.HasPhi43NoiseGrowth (ξ ω)}

/-- The model at a fixed regularisation scale, with zero-noise fallback. -/
def attachedModel {Ω : Type*} (N : ℕ) (κ : Kappa) (ξ : Ω → SpaceTime → ℝ)
    (C : RenormalisationConstants) (hξ : ∀ ω, IsSmoothOnSpaceTime (ξ ω))
    (ω : Ω) : Model (phi43RegularityStructure κ) parabolicSemigroup := by
  classical
  exact if hg : ω ∈ growthEvent ξ then moderateModel N κ (ξ ω) C (hξ ω) hg
    else moderateModel N κ (fun _ => 0) C contDiff_const hasPhi43NoiseGrowth_zero

theorem attachedModel_spec {Ω : Type*} (N : ℕ) (κ : Kappa) (ξ : Ω → SpaceTime → ℝ)
    (C : RenormalisationConstants) (hξ : ∀ ω, IsSmoothOnSpaceTime (ξ ω))
    (ω : Ω) (hω : ω ∈ growthEvent ξ) :
    Statements.IsModeratePhi43ModelOf N κ (ξ ω) C (attachedModel N κ ξ C hξ ω) := by
  classical
  simp only [attachedModel, dite_eq_left hω]
  exact moderateModel_spec N κ (ξ ω) C (hξ ω) hω
end GlobalPhi43.Attachment
