/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Identification.CubeBasic
public import Phi43.Identification.BaseFunctions
import Mathlib.Tactic.Module

/-!
# The cube of the Φ⁴₃ ansatz in the enlarged structure

This is a step of the identification of the renormalised equation ([Hai14, p. 147]).

For the generic element of `V_γ`
`u = a Ψ + φ 1 + c₃ I(Ψ³) + c₂ I(Ψ²) + ∑ᵢ φᵢ Xᵢ + r`
(`phi43AnsatzF a φ c₃ c₂ ψ + r`, with `r` any vector supported in degrees `≥ γ = 1 + 3κ`, which
cannot contribute below `κ`: `γ + 2 (-1/2 - κ) = κ`), the truncation below `κ` of the cube
`u ⋆ (u ⋆ u)` for the product `phi43ProductF κ` is
`phi43CubeLowF a φ c₃ c₂ ψ` (`lowerProj_cube_ansatz`).  The specialisation `a = 1`, `c₃ = -1`,
`c₂ = -3φ` is Hairer's display (`neg_lowerProj_cube_eq_oldEmb`):
`Ξ - u³ - Ξ = -Ψ³ - 3φΨ² + 3Ψ²I(Ψ³) - 3φ²Ψ + 6φΨI(Ψ³) + 9φΨ²I(Ψ²) - 3φᵢΨ²Xᵢ - φ³·1`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The ansatz `a Ψ + φ 1 + c₃ I(Ψ³) + c₂ I(Ψ²) + ∑ᵢ ψᵢ Xᵢ` in the enlarged coordinate space. -/
def phi43AnsatzF (a φ c₃ c₂ : ℝ) (ψ : Fin 3 → ℝ) : SymbolF → ℝ :=
  a • phi43EF .psi + φ • phi43EF .one + c₃ • phi43EF .iPsiCube + c₂ • phi43EF .iPsiSq +
    ∑ i, ψ i • phi43EF (.x i)

/-- The retained part of the square of the ansatz (without the `X Xⱼ` terms). -/
def phi43SqMainF (a φ c₃ c₂ : ℝ) (ψ : Fin 3 → ℝ) : SymbolF → ℝ :=
  (a ^ 2) • phi43EF .psiSq + (2 * a * φ) • phi43EF .psi + (2 * a * c₃) • phi43EF .iPsiCubePsi +
    (2 * a * c₂) • phi43EF .iPsiSqPsi + (∑ i, (2 * a * ψ i) • phi43EF (.psiX i)) +
    (φ ^ 2) • phi43EF .one + (2 * φ * c₃) • phi43EF .iPsiCube + (2 * φ * c₂) • phi43EF .iPsiSq +
    (∑ i, (2 * φ * ψ i) • phi43EF (.x i)) + (c₃ ^ 2) • phi43EF .iPsiCubeSq

/-- The `Xᵢ Xⱼ` terms of the square of the ansatz (degree `2`). -/
def phi43SqXF (ψ : Fin 3 → ℝ) : SymbolF → ℝ :=
  ∑ i, ∑ j, (ψ i * ψ j) • phi43EF (.xMul s(i, j))

/-- The truncation below `κ` of the cube of the ansatz. -/
def phi43CubeLowF (a φ c₃ c₂ : ℝ) (ψ : Fin 3 → ℝ) : SymbolF → ℝ :=
  (a ^ 3) • phi43EF .psiCube + (3 * a ^ 2 * φ) • phi43EF .psiSq + (3 * a * φ ^ 2) • phi43EF .psi +
    (φ ^ 3) • phi43EF .one + (3 * a ^ 2 * c₃) • phi43EF .iPsiCubePsiSq +
    (3 * a ^ 2 * c₂) • phi43EF .iPsiSqPsiSq + (6 * a * φ * c₃) • phi43EF .iPsiCubePsi +
    ∑ i, (3 * a ^ 2 * ψ i) • phi43EF (.psiSqX i)

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

theorem phi43ProductF_mul (κ : Kappa) : (phi43ProductF κ).mul = phi43ProductLinearF := rfl

theorem phi43SqF_eq (a φ c₃ c₂ : ℝ) (ψ : Fin 3 → ℝ) :
    phi43ProductLinearF (phi43AnsatzF a φ c₃ c₂ ψ) (phi43AnsatzF a φ c₃ c₂ ψ) =
      phi43SqMainF a φ c₃ c₂ ψ + phi43SqXF ψ := by
  simp only [phi43AnsatzF, phi43SqMainF, phi43SqXF, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, Fin.sum_univ_three, phi43ProductLinearF_eF]
  simp [productSymbol]
  module

theorem lowerProj_phi43EF (κ : Kappa) (τ : Symbol) :
    RegularityStructures.lowerProj (phi43RegularityStructureF κ).deg κ.1 (phi43EF τ) =
      if homogeneity κ τ < κ.1 then phi43EF τ else 0 := by
  funext υ
  rw [RegularityStructures.lowerProj_apply]
  by_cases h : υ = .old τ
  · subst h
    by_cases hc : homogeneity κ τ < κ.1 <;> simp [phi43EF, phi43RegularityStructureF_old_deg, hc]
  · have : phi43EF τ υ = 0 := by simp [phi43EF, h]
    split_ifs <;> simp [this]

theorem lowerProj_mul_ansatz_sqMain (κ : Kappa) (a φ c₃ c₂ : ℝ) (ψ : Fin 3 → ℝ) :
    RegularityStructures.lowerProj (phi43RegularityStructureF κ).deg κ.1
      (phi43ProductLinearF (phi43AnsatzF a φ c₃ c₂ ψ) (phi43SqMainF a φ c₃ c₂ ψ)) =
      phi43CubeLowF a φ c₃ c₂ ψ := by
  simp only [phi43AnsatzF, phi43SqMainF, phi43CubeLowF, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, Fin.sum_univ_three, phi43ProductLinearF_eF]
  simp [productSymbol, lowerProj_phi43EF, homogeneity_lt_kappa_iff, mem_fMinus_iff_isFMinus,
    isFMinus]
  module

end RegularityStructures.Phi43

end
