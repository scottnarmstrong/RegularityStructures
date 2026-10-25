/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedSymbolsF
public import RegularityStructures.Abstract.RegularityStructure

/-!
# Integration in the finite planted completion

Hairer [Hai14, Definition 5.7, Theorem 5.14]. The old coordinate
space embeds literally. Each old Psi-containing product has a retained
integral; integration vanishes on planted symbols and on polynomials.
This file proves the linear algebra, not yet group commutation.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- Literal inclusion of the old finite coordinate space. -/
def phi43OldEmbF : (Symbol → ℝ) →ₗ[ℝ] (SymbolF → ℝ) where
  toFun a τ := match τ with | .old τ => a τ | .planted _ => 0
  map_add' a b := by funext τ; cases τ <;> simp
  map_smul' c a := by funext τ; cases τ <;> simp

/-- Restriction to the original symbols. -/
def phi43OldRestrictF : (SymbolF → ℝ) →ₗ[ℝ] (Symbol → ℝ) where
  toFun a τ := a (.old τ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Integration on the enlarged space, with no missing old product sources. -/
def phi43IntegrationF : (SymbolF → ℝ) →ₗ[ℝ] (SymbolF → ℝ) where
  toFun a σ := match σ with
    | .old .psi => a (.old .noise)
    | .old .iPsi => a (.old .psi)
    | .old .iPsiSq => a (.old .psiSq)
    | .old .iPsiCube => a (.old .psiCube)
    | .planted τ => a (.old τ.symbol)
    | _ => 0
  map_add' a b := by
    funext σ
    cases σ with
    | old τ => cases τ <;> simp
    | planted τ => rfl
  map_smul' c a := by
    funext σ
    cases σ with
    | old τ => cases τ <;> simp
    | planted τ => rfl

/-- All basis vectors except the raw noise belong to the integration block. -/
def phi43XiFreeF : Finset SymbolF := Finset.univ.erase (.old .noise)

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

theorem phi43OldEmbF_single (τ : Symbol) :
    phi43OldEmbF (Pi.single τ 1) = Pi.single (.old τ) 1 := by
  funext σ
  cases σ <;> simp [phi43OldEmbF, Pi.single_apply]

theorem phi43IntegrationF_planted (τ : Phi43PlantSource) :
    phi43IntegrationF (Pi.single (.planted τ) 1) = 0 := by
  funext σ
  cases σ with
  | old σ => cases σ <;> simp [phi43IntegrationF]
  | planted σ => simp [phi43IntegrationF]

theorem phi43IntegrationF_single (τ : SymbolF) :
    phi43IntegrationF (Pi.single τ 1) =
      match phi43IntegrationSymbolF τ with
      | none => 0
      | some σ => Pi.single σ 1 := by
  cases τ with
  | planted τ => exact phi43IntegrationF_planted τ
  | old τ =>
    cases τ <;> funext σ
    all_goals cases σ with
      | old σ => cases σ <;> simp [phi43IntegrationF, phi43IntegrationSymbolF]
      | planted σ => cases σ <;>
          simp [phi43IntegrationF, phi43IntegrationSymbolF, Phi43PlantSource.symbol,
            Pi.single_apply]

theorem phi43IntegrationF_old_source (τ : Phi43PlantSource) :
    phi43IntegrationF (Pi.single (.old τ.symbol) 1) = Pi.single (.planted τ) 1 := by
  rw [phi43IntegrationF_single, phi43IntegrationSymbolF_planted_source]

end RegularityStructures.Phi43

end
