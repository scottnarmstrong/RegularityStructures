/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaEntryFormulas
public import Phi43.Structure.Abstract
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Structure-group entries of an arbitrary Phi43 model below the cutoff `γ'`

For *any* `Model (phi43RegularityStructure κ) parabolicSemigroup` `Z` the map `Γ_{yx}` lies in the
structure group, hence equals `phi43StructureGroupElement g` for some `g : G`.  Consequently every
entry `Γ_{yx} e_i (j)`, `deg j < deg i`, for the symbols `i` of `F₋` and the unit is a *named
parameter* of `g`, and the parameters are shared between symbols:

* `Ψ`-type symbols `Ξ, Ψ, Ψ², Ψ³, 1` are fixed by `Γ`;
* `Ψ²Xᵢ ↦ Ψ²Xᵢ + shiftᵢ Ψ²` (the entry equals the entry of `Xᵢ` on `1`: deterministic);
* `I(Ψ²)Ψ² ↦ I(Ψ²)Ψ² + cΨ² Ψ²`, the entry equals the entry of `I(Ψ²)` on `1`;
* `I(Ψ³)Ψ ↦ I(Ψ³)Ψ + cΨ³ Ψ` and `I(Ψ³)Ψ² ↦ I(Ψ³)Ψ² + cΨ³ Ψ²`, the entries equal the entry of
  `I(Ψ³)` on `1`.

No other entry of these symbols is nonzero.  These are exactly the `Γ`-entries that the Kolmogorov
bound for the model norms requires below a cutoff `γ' < 1/2 - 3κ`.
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

variable {κ : Kappa} (Z : Model (phi43RegularityStructure κ) parabolicSemigroup)

/-- `Γ_{yx}` of any model is a concrete structure-group element. -/
theorem phi43_exists_gammaMap_eq_structureGroupElement (y x : ParabolicSpace) :
    ∃ g : G, Z.gammaMap y x =
      (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ)) := by
  obtain ⟨g, hg⟩ := (Z.gamma y x).2
  exact ⟨g, by rw [Model.gammaMap, ← hg]⟩

private theorem gammaMap_single_eq (y x : ParabolicSpace) (g : G)
    (hg : Z.gammaMap y x =
      (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))) (τ : Symbol) :
    Z.gammaMap y x (Pi.single τ (1 : ℝ)) = phi43CoordinateEquiv (structureGroupMap g (basis τ)) := by
  rw [hg, phi43StructureGroupElement_apply_single]

/-- `Γ_{yx} I(Ψ³) = I(Ψ³) + c 1`, where `c` is the `1`-entry. -/
theorem gammaMap_single_iPsiCube (y x : ParabolicSpace) :
    Z.gammaMap y x (Pi.single Symbol.iPsiCube (1 : ℝ)) = Pi.single Symbol.iPsiCube (1 : ℝ) +
      Z.gammaMap y x (Pi.single Symbol.iPsiCube (1 : ℝ)) Symbol.one • (Pi.single Symbol.one (1 : ℝ) : Symbol → ℝ) := by
  obtain ⟨g, hg⟩ := phi43_exists_gammaMap_eq_structureGroupElement Z y x
  rw [gammaMap_single_eq Z y x g hg, structureGroupMap_basis_iPsiCube_eq]
  simp only [map_add, map_smul, phi43CoordinateEquiv_basis, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  simp

/-- `Γ_{yx} I(Ψ²) = I(Ψ²) + c 1`, where `c` is the `1`-entry. -/
theorem gammaMap_single_iPsiSq (y x : ParabolicSpace) :
    Z.gammaMap y x (Pi.single Symbol.iPsiSq (1 : ℝ)) = Pi.single Symbol.iPsiSq (1 : ℝ) +
      Z.gammaMap y x (Pi.single Symbol.iPsiSq (1 : ℝ)) Symbol.one • (Pi.single Symbol.one (1 : ℝ) : Symbol → ℝ) := by
  obtain ⟨g, hg⟩ := phi43_exists_gammaMap_eq_structureGroupElement Z y x
  rw [gammaMap_single_eq Z y x g hg, structureGroupMap_basis_iPsiSq_eq]
  simp only [map_add, map_smul, phi43CoordinateEquiv_basis, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  simp

end RegularityStructures.Phi43

end
