/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.Symbols
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The finite planted completion for the Phi4 fixed point

Hairer [Hai14, Definition 5.7, Theorem 5.14, (8.3)–(8.4), Section 9.4].
All old symbols are retained. The additional symbols integrate the old
Psi-containing products on which the old integration vanished. This is a
finite integration completion, not the complete degree-four tree algebra.
Its group and integration properties are proved in subsequent modules.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- Products requiring a new planted symbol in the integration completion. -/
inductive Phi43PlantSource where
  | psiX (i : Fin 3)
  | psiSqX (i : Fin 3)
  | iPsiPsi
  | iPsiPsiSq
  | iPsiSqPsi
  | iPsiSqPsiSq
  | iPsiCubePsi
  | iPsiCubePsiSq
  deriving DecidableEq, Fintype

/-- Underlying old product of a new planted symbol. -/
def Phi43PlantSource.symbol : Phi43PlantSource → Symbol
  | .psiX i => .psiX i
  | .psiSqX i => .psiSqX i
  | .iPsiPsi => .iPsiPsi
  | .iPsiPsiSq => .iPsiPsiSq
  | .iPsiSqPsi => .iPsiSqPsi
  | .iPsiSqPsiSq => .iPsiSqPsiSq
  | .iPsiCubePsi => .iPsiCubePsi
  | .iPsiCubePsiSq => .iPsiCubePsiSq

/-- Old finite symbols together with the twelve new planted integrals. -/
inductive SymbolF where
  | old (τ : Symbol)
  | planted (τ : Phi43PlantSource)
  deriving DecidableEq, Fintype

/-- Old degrees are unchanged; every new plant has its source degree plus two. -/
def phi43DegreeF (κ : Kappa) : SymbolF → ℝ
  | .old τ => homogeneity κ τ
  | .planted τ => homogeneity κ τ.symbol + 2

/-- The literal basis-level integration, including the old noise source. -/
def phi43IntegrationSymbolF : SymbolF → Option SymbolF
  | .old .noise => some (.old .psi)
  | .old .psi => some (.old .iPsi)
  | .old .psiSq => some (.old .iPsiSq)
  | .old .psiCube => some (.old .iPsiCube)
  | .old (.psiX i) => some (.planted (.psiX i))
  | .old (.psiSqX i) => some (.planted (.psiSqX i))
  | .old .iPsiPsi => some (.planted .iPsiPsi)
  | .old .iPsiPsiSq => some (.planted .iPsiPsiSq)
  | .old .iPsiSqPsi => some (.planted .iPsiSqPsi)
  | .old .iPsiSqPsiSq => some (.planted .iPsiSqPsiSq)
  | .old .iPsiCubePsi => some (.planted .iPsiCubePsi)
  | .old .iPsiCubePsiSq => some (.planted .iPsiCubePsiSq)
  | _ => none

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

theorem phi43IntegrationSymbolF_planted_source (τ : Phi43PlantSource) :
    phi43IntegrationSymbolF (.old τ.symbol) = some (.planted τ) := by
  cases τ <;> rfl

theorem phi43IntegrationSymbolF_degree (κ : Kappa) {τ σ : SymbolF}
    (h : phi43IntegrationSymbolF τ = some σ) :
    phi43DegreeF κ σ = phi43DegreeF κ τ + 2 := by
  cases τ with
  | old τ =>
    cases τ <;> simp only [phi43IntegrationSymbolF, Option.some.injEq,
      reduceCtorEq] at h
    all_goals subst σ
    all_goals simp only [phi43DegreeF, Phi43PlantSource.symbol, homogeneity]
    all_goals ring
  | planted τ => simp [phi43IntegrationSymbolF] at h

end RegularityStructures.Phi43

end
