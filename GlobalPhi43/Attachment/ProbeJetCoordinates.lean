module

public import RegularityStructures.Analysis.Parabolic.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basis
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Finite coordinate evaluations control the full Frechet jet. The comparison
constant depends only on the derivative order and the fixed spacetime carrier. -/

@[expose] public noncomputable section

open RegularityStructures

namespace GlobalPhi43.Attachment

abbrev ProbeJet (k : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin k => ParabolicSpace) ℝ
abbrev ProbeDirection := Fin (Module.finrank ℝ ParabolicSpace)

def probeDirectionBasis := Module.finBasis ℝ ParabolicSpace

def probeJetCoordinates (k : ℕ) : ProbeJet k →ₗ[ℝ] ((Fin k → ProbeDirection) → ℝ) where
  toFun M p := M (fun i => probeDirectionBasis (p i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem probeJetCoordinates_injective (k : ℕ) : Function.Injective (probeJetCoordinates k) := by
  intro M N h
  have he : M.toMultilinearMap = N.toMultilinearMap :=
    Module.Basis.ext_multilinear (fun _ => probeDirectionBasis) (fun p => congrFun h p)
  ext v
  exact congrArg (fun F => F v) he

/-- A fixed finite comparison, with no Gaussian derivative bound as an input. -/
theorem probeJet_coordinate_bound (k : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (M : ProbeJet k) (B : ℝ), 0 ≤ B →
      (∀ p : Fin k → ProbeDirection, |M (fun i => probeDirectionBasis (p i))| ≤ B) →
      ‖M‖ ≤ D * B := by
  let : FiniteDimensional ℝ (ProbeJet k) :=
    FiniteDimensional.of_injective (probeJetCoordinates k) (probeJetCoordinates_injective k)
  obtain ⟨D, hD, hd⟩ := (probeJetCoordinates k).injective_iff_antilipschitz.mp
    (probeJetCoordinates_injective k)
  refine ⟨D, hD, ?_⟩
  intro M B hB hb
  have hc : ‖probeJetCoordinates k M‖ ≤ B := by
    apply (pi_norm_le_iff_of_nonneg hB).mpr
    intro p
    exact hb p
  have hh := hd.le_mul_dist M 0
  simp only [dist_zero_right, map_zero] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hc hD.le)

end GlobalPhi43.Attachment
