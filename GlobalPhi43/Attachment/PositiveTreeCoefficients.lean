module

public import GlobalPhi43.Attachment.Realisation
public import Phi43.BPHZ.PositiveMomentGammaV

/-! The positive-tree Gamma columns for the actual trees and arbitrary constants. -/

public section

namespace GlobalPhi43.Attachment
open RegularityStructures RegularityStructures.Phi43

variable {N : ℕ} {κ : Kappa} {f : SpaceTime → ℝ} {C : RenormalisationConstants}
  {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}

/-- The unit entry of the integrated square is exactly the increment of Y. -/
theorem gamma_treeY_coefficient (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f)
    (hZ : Statements.IsModeratePhi43ModelOf N κ f C Z) (y x : ParabolicSpace) :
    Z.gammaMap y x (Pi.single .iPsiSq 1) .one =
      treeY N f (C₁ C) (spaceTimeProj y) - treeY N f (C₁ C) (spaceTimeProj x) := by
  obtain ⟨noise, hn, hRC, _⟩ := regPi_fMinus hZ
  obtain ⟨Cg, q, hgr⟩ := hg
  have hz : noise.zeta = fun w : ParabolicSpace => f (w.1, torusProj w.2) := funext hn
  have hg' : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q := by
    rw [hz]; exact hgr
  rw [gammaMap_iPsiSq_one_eq_pairing (ξ := fun _ : Unit => f) (ω := ())
    Cg q hg' (noise_zeta_eq hn) hf hRC y x]
  exact pairing_treeJ_sq hf (C₁ C) _ _

/-- The unit entry of the integrated cube is exactly the increment of Z. -/
theorem gamma_treeZ_coefficient (hf : IsSmoothOnSpaceTime f)
    (hg : Statements.HasPhi43NoiseGrowth f)
    (hZ : Statements.IsModeratePhi43ModelOf N κ f C Z) (y x : ParabolicSpace) :
    Z.gammaMap y x (Pi.single .iPsiCube 1) .one =
      treeZ N f (C₁ C) (spaceTimeProj y) - treeZ N f (C₁ C) (spaceTimeProj x) := by
  obtain ⟨noise, hn, hRC, _⟩ := regPi_fMinus hZ
  obtain ⟨Cg, q, hgr⟩ := hg
  have hz : noise.zeta = fun w : ParabolicSpace => f (w.1, torusProj w.2) := funext hn
  have hg' : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q := by
    rw [hz]; exact hgr
  rw [gammaMap_iPsiCube_one_eq_pairing (ξ := fun _ : Unit => f) (ω := ())
    Cg q hg' (noise_zeta_eq hn) hf hRC y x]
  exact pairing_treeW hf (C₁ C) _ _

end GlobalPhi43.Attachment
