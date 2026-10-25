/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.Abstract
import Mathlib.Tactic

/-!
# Reading the structure-group parameters off the group action

A structure-group element `g : G` of the Φ⁴₃ structure has parameters `shift`, `cPsi`, `cPsiGrad`,
`cPsiSq`, `cPsiCube`.  They are recovered from the coordinates of `Γ e_τ` for
`τ ∈ {X_i, I(Ψ), I(Ψ²), I(Ψ³)}`, and the action on every basis symbol other than the time
coordinate `X₀` depends only on these.  (The component `shift 0` only enters `Γ X₀`; `X₀` has
degree `2`, above the cutoff.)
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The parameters of `g` and `g'` agree, except possibly the time shift `shift 0`. -/
structure SameParametersExceptTime (g g' : G) : Prop where
  shift : ∀ i : Fin 3, g.shift i.succ = g'.shift i.succ
  cPsi : g.cPsi = g'.cPsi
  cPsiGrad : g.cPsiGrad = g'.cPsiGrad
  cPsiSq : g.cPsiSq = g'.cPsiSq
  cPsiCube : g.cPsiCube = g'.cPsiCube

theorem primitiveAction_congr {g g' : G} (h : SameParametersExceptTime g g') {σ : Symbol}
    (hσ : σ ≠ .x0) : primitiveAction g σ = primitiveAction g' σ := by
  cases σ <;> simp_all [primitiveAction, h.shift, h.cPsi, h.cPsiGrad, h.cPsiSq, h.cPsiCube]

theorem integratedPsiProductAction_congr {g g' : G} (h : SameParametersExceptTime g g')
    (b : Bool) : integratedPsiProductAction g b = integratedPsiProductAction g' b := by
  cases b <;> simp [integratedPsiProductAction, h.cPsi, h.cPsiGrad]

theorem xMulAction_congr {g g' : G} (h : SameParametersExceptTime g g') (p : Sym2 (Fin 3)) :
    xMulAction g p = xMulAction g' p := by
  induction p using Sym2.inductionOn with
  | _ i j =>
    rw [xMulAction_mk, xMulAction_mk, primitiveAction_congr h (by simp),
      primitiveAction_congr h (σ := .x j) (by simp)]

/-- The action on every basis symbol except `X₀` depends only on the parameters other than
`shift 0`. -/
theorem structureBasisAction_congr {g g' : G} (h : SameParametersExceptTime g g') {τ : Symbol}
    (hτ : τ ≠ .x0) : structureBasisAction g τ = structureBasisAction g' τ := by
  have hp : ∀ σ : Symbol, σ ≠ .x0 → primitiveAction g σ = primitiveAction g' σ :=
    fun σ hσ => primitiveAction_congr h hσ
  cases τ <;> simp_all [structureBasisAction, integratedPsiProductAction_congr h,
    xMulAction_congr h]

theorem structureBasisAction_x_one (g : G) (i : Fin 3) :
    structureBasisAction g (.x i) .one = g.shift i.succ := by
  simp [structureBasisAction, primitiveAction, basis]

theorem structureBasisAction_iPsi_one (g : G) :
    structureBasisAction g .iPsi .one = g.cPsi := by
  simp [structureBasisAction, primitiveAction, basis]

theorem structureBasisAction_iPsi_x (g : G) (i : Fin 3) :
    structureBasisAction g .iPsi (.x i) = g.cPsiGrad i := by
  simp [structureBasisAction, primitiveAction, basis, Finsupp.single_apply]

theorem structureBasisAction_iPsiSq_one (g : G) :
    structureBasisAction g .iPsiSq .one = g.cPsiSq := by
  simp [structureBasisAction, primitiveAction, basis]

theorem structureBasisAction_iPsiCube_one (g : G) :
    structureBasisAction g .iPsiCube .one = g.cPsiCube := by
  simp [structureBasisAction, primitiveAction, basis]

/-- If two structure-group elements agree on `X_i`, `I(Ψ)`, `I(Ψ²)`, `I(Ψ³)`, then their
parameters agree except possibly for the time shift. -/
theorem sameParametersExceptTime_of_basisAction {g g' : G}
    (hx : ∀ i : Fin 3, structureBasisAction g (.x i) = structureBasisAction g' (.x i))
    (h1 : structureBasisAction g .iPsi = structureBasisAction g' .iPsi)
    (h2 : structureBasisAction g .iPsiSq = structureBasisAction g' .iPsiSq)
    (h3 : structureBasisAction g .iPsiCube = structureBasisAction g' .iPsiCube) :
    SameParametersExceptTime g g' where
  shift i := by
    rw [← structureBasisAction_x_one, ← structureBasisAction_x_one, hx i]
  cPsi := by rw [← structureBasisAction_iPsi_one, ← structureBasisAction_iPsi_one, h1]
  cPsiGrad := by
    funext i
    rw [← structureBasisAction_iPsi_x, ← structureBasisAction_iPsi_x, h1]
  cPsiSq := by rw [← structureBasisAction_iPsiSq_one, ← structureBasisAction_iPsiSq_one, h2]
  cPsiCube := by
    rw [← structureBasisAction_iPsiCube_one, ← structureBasisAction_iPsiCube_one, h3]

end RegularityStructures.Phi43

end
