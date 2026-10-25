/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.ModelSpace
public import RegularityStructures.Abstract.RegularityStructure
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# The Φ⁴₃ sector as an abstract graded regularity structure

The abstract interface uses the coordinate space `Symbol → ℝ`, whereas the
concrete finite algebra uses `Symbol →₀ ℝ`.  The finite-coordinate linear
equivalence transports the concrete structure-group maps without changing
their basis action or triangularity.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The coordinate realization of the concrete finite model space. -/
def phi43CoordinateEquiv : T ≃ₗ[ℝ] (Symbol → ℝ) :=
  Finsupp.linearEquivFunOnFinite ℝ ℝ Symbol

theorem phi43CoordinateEquiv_basis (τ : Symbol) :
    phi43CoordinateEquiv (basis τ) = Pi.single τ 1 := by
  simp [phi43CoordinateEquiv, basis]

/-- The inverse of a concrete structure-group map, as a linear equivalence. -/
def structureGroupLinearEquiv (g : G) : T ≃ₗ[ℝ] T where
  toFun := structureGroupMap g
  invFun := structureGroupMap (structureGroupInv g)
  map_add' := (structureGroupMap g).map_add
  map_smul' := (structureGroupMap g).map_smul
  left_inv := by
    intro v
    simpa [LinearMap.comp_apply] using
      LinearMap.congr_fun (structureGroupMap_inverse g) v
  right_inv := by
    intro v
    have hright : g * structureGroupInv g = 0 := by
      cases g with
      | mk shift cPsi cPsiGrad cPsiSq cPsiCube =>
          change
            (⟨shift + -shift,
              cPsi + (-cPsi + ∑ i : Fin 3, shift i.succ * cPsiGrad i) +
                ∑ i : Fin 3, shift i.succ * (-cPsiGrad) i,
              cPsiGrad + -cPsiGrad,
              cPsiSq + -cPsiSq, cPsiCube + -cPsiCube⟩ : G) = (0 : G)
          congr
          · funext i
            simp
          · simp
          · simp
          · simp
          · simp
    change ((structureGroupMap g).comp
      (structureGroupMap (structureGroupInv g))) v = v
    rw [structureGroupMap_comp, hright, structureGroupMap_zero]
    rfl

theorem structureGroupLinearEquiv_apply (g : G) (v : T) :
    structureGroupLinearEquiv g v = structureGroupMap g v := rfl

/-- The conjugated linear equivalence on coefficient functions. -/
def phi43StructureGroupEquiv (g : G) : (Symbol → ℝ) ≃ₗ[ℝ] (Symbol → ℝ) :=
  phi43CoordinateEquiv.symm.trans
    ((structureGroupLinearEquiv g).trans phi43CoordinateEquiv)

/-- A concrete group element transported to the abstract coordinate space. -/
def phi43StructureGroupElement (g : G) :
    LinearMap.GeneralLinearGroup ℝ (Symbol → ℝ) :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv (phi43StructureGroupEquiv g)

theorem phi43StructureGroupElement_apply_single (g : G) (τ : Symbol) :
    (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
        (Pi.single τ 1) = phi43CoordinateEquiv (structureGroupMap g (basis τ)) := by
  have hτ : phi43CoordinateEquiv.symm (Pi.single τ 1) = basis τ := by
    apply phi43CoordinateEquiv.injective
    simp [phi43CoordinateEquiv_basis]
  simp [phi43StructureGroupElement, phi43StructureGroupEquiv, hτ,
    structureGroupLinearEquiv_apply]

theorem phi43StructureGroupElement_mul (g h : G) :
    phi43StructureGroupElement g * phi43StructureGroupElement h =
      phi43StructureGroupElement (g * h) := by
  apply Units.ext
  apply LinearMap.ext
  intro v
  rw [Units.val_mul]
  change (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
      ((phi43StructureGroupElement h : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ)) v) =
    (phi43StructureGroupElement (g * h) : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ)) v
  simp only [phi43StructureGroupElement, LinearMap.GeneralLinearGroup.coe_ofLinearEquiv,
    phi43StructureGroupEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    structureGroupLinearEquiv_apply]
  change phi43CoordinateEquiv (structureGroupMap g
      (structureGroupMap h (phi43CoordinateEquiv.symm v))) =
    phi43CoordinateEquiv (structureGroupMap (g * h) (phi43CoordinateEquiv.symm v))
  change phi43CoordinateEquiv (((structureGroupMap g).comp
      (structureGroupMap h)) (phi43CoordinateEquiv.symm v)) =
    phi43CoordinateEquiv (structureGroupMap (g * h) (phi43CoordinateEquiv.symm v))
  rw [structureGroupMap_comp]

theorem phi43StructureGroupElement_inv (g : G) :
    (phi43StructureGroupElement g)⁻¹ = phi43StructureGroupElement (structureGroupInv g) := by
  apply Units.ext
  apply LinearMap.ext
  intro v
  change phi43CoordinateEquiv (structureGroupMap (structureGroupInv g)
      (phi43CoordinateEquiv.symm v)) =
    phi43CoordinateEquiv (structureGroupMap (structureGroupInv g)
      (phi43CoordinateEquiv.symm v))
  rfl

private theorem phi43_lower_of_concrete (κ : Kappa) (g : G) (τ : Symbol) (σ : Symbol)
    (hσ : (phi43CoordinateEquiv (structureGroupMap g (basis τ) - basis τ)) σ ≠ 0) :
    homogeneity κ σ < homogeneity κ τ := by
  have h := structureGroup_triangular_basis κ g τ
  apply h σ
  exact hσ

/-- The abstract Φ⁴₃ regularity structure at parameter `κ`. -/
def phi43RegularityStructure (κ : Kappa) :
    RegularityStructure Symbol where
  deg := homogeneity κ
  group :=
    { carrier := Set.range phi43StructureGroupElement
      one_mem' := by
        refine ⟨0, ?_⟩
        apply Units.ext
        apply LinearMap.ext
        intro v
        change phi43CoordinateEquiv (structureGroupMap 0
          (phi43CoordinateEquiv.symm v)) = v
        rw [structureGroupMap_zero]
        exact phi43CoordinateEquiv.apply_symm_apply v
      mul_mem' := by
        rintro a b ⟨g, rfl⟩ ⟨h, rfl⟩
        refine ⟨g * h, ?_⟩
        exact (phi43StructureGroupElement_mul g h).symm
      inv_mem' := by
        rintro a ⟨g, rfl⟩
        refine ⟨structureGroupInv g, ?_⟩
        exact (phi43StructureGroupElement_inv g).symm }
  isGradedUnipotent := by
    rintro g ⟨p, rfl⟩
    intro τ σ hdeg
    by_contra hσ
    have hσ' : (phi43CoordinateEquiv
        (structureGroupMap p (basis τ) - basis τ)) σ ≠ 0 := by
      rw [map_sub, phi43CoordinateEquiv_basis,
        ← phi43StructureGroupElement_apply_single p τ]
      exact hσ
    exact (not_lt_of_ge hdeg) (phi43_lower_of_concrete κ p τ σ hσ')

theorem phi43RegularityStructure_deg (κ : Kappa) :
    (phi43RegularityStructure κ).deg = homogeneity κ := rfl

theorem phi43RegularityStructure_group_mem (κ : Kappa) (g : G) :
    phi43StructureGroupElement g ∈ (phi43RegularityStructure κ).group :=
  ⟨g, rfl⟩

end RegularityStructures.Phi43

end
