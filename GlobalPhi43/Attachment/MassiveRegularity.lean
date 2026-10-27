module

public import GlobalPhi43.Attachment.PotentialObservable
public import GlobalPhi43.Attachment.DefectPDE
public import Phi43.Potential.NoiseBounds

/-! Regularity of a massive potential of a smooth noise with polynomial growth. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open RegularityStructures RegularityStructures.Phi43 RegularityStructures.Potential

/-- The defining absolutely convergent integral determines the potential everywhere. -/
theorem massivePotential_unique {f : SpaceTime → ℝ} {ψ ψ' : ℝ → C(Torus3, ℝ)}
    (hψ : IsMassivePotential f ψ) (hψ' : IsMassivePotential f ψ') : ψ = ψ' := by
  funext t
  ext x
  exact (hψ.2 t x).trans (hψ'.2 t x).symm

/-- Growth and smoothness give a time-polynomial bound on the forcing. -/
theorem attachment_potForcing {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) : PotForcing f :=
  RegularityStructures.Phi43.Potential.potForcing_of_growth (noise := canonicalNoiseOfSpaceTime f hf) (fun _ => rfl) hg

/-- Every supplied massive potential is smooth and continuous, not only a chosen representative. -/
theorem massivePotential_regular {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f) {ψ : ℝ → C(Torus3, ℝ)}
    (hψ : IsMassivePotential f ψ) :
    IsSmoothOnSpaceTime (fun z : SpaceTime => ψ z.1 z.2) ∧ Continuous ψ := by
  obtain ⟨ψ', hψ', hs, hc⟩ := massivePotential_exists_smooth_of_polynomialLift_growth f hf hg
  have he := massivePotential_unique hψ hψ'
  rw [he]
  exact ⟨hs, hc⟩

end GlobalPhi43.Attachment
