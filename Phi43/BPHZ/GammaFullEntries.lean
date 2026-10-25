/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaEntryFormulas
import Mathlib.Tactic
public import Phi43.Structure.ModelSpace

/-!
# The off-diagonal entries of `structureGroupMap g` below the cutoff `γ = 1 + 3κ`

For `g : G` with the parameters `shift`, `cPsi`, `cPsiGrad`, `cPsiSq`, `cPsiCube`, and
`e = structureGroupMap g (basis i) j` with `j ≠ i`:

Symbols `i` with `deg i < γ` and shift-only (polynomial) entries, the deterministic set
`gammaFullDeterministic`: `1, Ξ, Ψ, Ψ², Ψ³` (all entries `0`), and
* `Xₖ`: `e = shift (k+1)` for `j = 1`, else `0`;
* `ΨXₖ`: `e = shift (k+1)` for `j = Ψ`, else `0`;
* `Ψ²Xₖ`: `e = shift (k+1)` for `j = Ψ²`, else `0`.

Random symbols (nine of them, `IsGammaFullRandom`), where `c₂ = cPsiSq`, `c₃ = cPsiCube`,
`c₁ = cPsi`, `gₖ = cPsiGrad k`:

| `i`          | nonzero entries                                        |
|--------------|--------------------------------------------------------|
| `I(Ψ²)`      | `j = 1`: `c₂`                                          |
| `I(Ψ³)`      | `j = 1`: `c₃`                                          |
| `I(Ψ)Ψ`      | `j = Ψ`: `c₁`; `j = ΨXₖ`: `gₖ`                         |
| `I(Ψ)Ψ²`     | `j = Ψ²`: `c₁`; `j = Ψ²Xₖ`: `gₖ`                       |
| `I(Ψ²)Ψ`     | `j = Ψ`: `c₂`                                          |
| `I(Ψ²)Ψ²`    | `j = Ψ²`: `c₂`                                         |
| `I(Ψ³)Ψ`     | `j = Ψ`: `c₃`                                          |
| `I(Ψ³)Ψ²`    | `j = Ψ²`: `c₃`                                         |
| `I(Ψ³)²`     | `j = I(Ψ³)`: `2 c₃`; `j = 1`: `c₃²`                    |

The symbols `X₀`, `XᵢXⱼ`, `I(Ψ)` have degree `≥ γ`.
-/

@[expose] public section

namespace RegularityStructures.Phi43

/-- The extended deterministic set `D_Γ^full` of the pairs `(i, j)` whose `Γ`-entry is a polynomial
in the shift: `i ∈ {1, Ξ, Ψ, Ψ², Ψ³, Xₖ, ΨXₖ, Ψ²Xₖ}`. -/
def gammaFullDeterministic : Set (Symbol × Symbol) :=
  {p | p.1 = Symbol.one ∨ p.1 = Symbol.noise ∨ p.1 = Symbol.psi ∨ p.1 = Symbol.psiSq ∨
    p.1 = Symbol.psiCube ∨ (∃ k : Fin 3, p.1 = Symbol.x k) ∨ (∃ k : Fin 3, p.1 = Symbol.psiX k) ∨
    ∃ k : Fin 3, p.1 = Symbol.psiSqX k}

/-- The nine random symbols below the cutoff `γ`. -/
def IsGammaFullRandom (i : Symbol) : Prop :=
  i = Symbol.iPsiSq ∨ i = Symbol.iPsiCube ∨ i = Symbol.iPsiPsi ∨ i = Symbol.iPsiPsiSq ∨
    i = Symbol.iPsiSqPsi ∨ i = Symbol.iPsiSqPsiSq ∨ i = Symbol.iPsiCubePsi ∨
    i = Symbol.iPsiCubePsiSq ∨ i = Symbol.iPsiCubeSq

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

open RegularityStructures

/-! ### Deterministic entries -/

theorem gammaFull_entry_fixed (g : G) {i j : Symbol}
    (hi : i = Symbol.one ∨ i = Symbol.noise ∨ i = Symbol.psi ∨ i = Symbol.psiSq ∨
      i = Symbol.psiCube) (hj : j ≠ i) : structureGroupMap g (basis i) j = 0 := by
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · rw [structureGroup_one]; simp [basis, hj]
  · rw [structureGroupMap_basis_noise_eq]; simp [basis, hj]
  · rw [structureGroupMap_basis_psi_eq]; simp [basis, hj]
  · rw [structureGroupMap_basis_psiSq_eq]; simp [basis, hj]
  · rw [structureGroupMap_basis_psiCube_eq]; simp [basis, hj]

theorem gammaFull_entry_x (g : G) (k : Fin 3) (j : Symbol) (hj : j ≠ Symbol.x k) :
    (j = Symbol.one → structureGroupMap g (basis (Symbol.x k)) j = g.shift k.succ) ∧
      (j ≠ Symbol.one → structureGroupMap g (basis (Symbol.x k)) j = 0) := by
  rw [structureGroupMap_basis_x_eq]
  refine ⟨?_, ?_⟩
  · rintro rfl
    simp [basis]
  · intro h
    simp [basis, hj, h]

theorem gammaFull_entry_psiX (g : G) (k : Fin 3) (j : Symbol) (hj : j ≠ Symbol.psiX k) :
    (j = Symbol.psi → structureGroupMap g (basis (Symbol.psiX k)) j = g.shift k.succ) ∧
      (j ≠ Symbol.psi → structureGroupMap g (basis (Symbol.psiX k)) j = 0) := by
  rw [structureGroupMap_basis_psiX_eq]
  refine ⟨?_, ?_⟩
  · rintro rfl
    simp [basis]
  · intro h
    simp [basis, hj, h]

theorem gammaFull_entry_psiSqX (g : G) (k : Fin 3) (j : Symbol) (hj : j ≠ Symbol.psiSqX k) :
    (j = Symbol.psiSq → structureGroupMap g (basis (Symbol.psiSqX k)) j = g.shift k.succ) ∧
      (j ≠ Symbol.psiSq → structureGroupMap g (basis (Symbol.psiSqX k)) j = 0) := by
  rw [structureGroupMap_basis_psiSqX_eq]
  refine ⟨?_, ?_⟩
  · rintro rfl
    simp [basis]
  · intro h
    simp [basis, hj, h]

/-! ### Random entries -/

theorem gammaFull_entry_iPsiSq (g : G) (j : Symbol) (hj : j ≠ Symbol.iPsiSq) :
    (j = Symbol.one → structureGroupMap g (basis Symbol.iPsiSq) j = g.cPsiSq) ∧
      (j ≠ Symbol.one → structureGroupMap g (basis Symbol.iPsiSq) j = 0) := by
  rw [structureGroupMap_basis_iPsiSq_eq]
  refine ⟨?_, ?_⟩
  · rintro rfl
    simp [basis]
  · intro h
    simp [basis, hj, h]

theorem gammaFull_entry_iPsiCube (g : G) (j : Symbol) (hj : j ≠ Symbol.iPsiCube) :
    (j = Symbol.one → structureGroupMap g (basis Symbol.iPsiCube) j = g.cPsiCube) ∧
      (j ≠ Symbol.one → structureGroupMap g (basis Symbol.iPsiCube) j = 0) := by
  rw [structureGroupMap_basis_iPsiCube_eq]
  refine ⟨?_, ?_⟩
  · rintro rfl
    simp [basis]
  · intro h
    simp [basis, hj, h]

theorem gammaFull_entry_iPsiSqPsi (g : G) (j : Symbol) (hj : j ≠ Symbol.iPsiSqPsi) :
    (j = Symbol.psi → structureGroupMap g (basis Symbol.iPsiSqPsi) j = g.cPsiSq) ∧
      (j ≠ Symbol.psi → structureGroupMap g (basis Symbol.iPsiSqPsi) j = 0) := by
  rw [structureGroupMap_basis_iPsiSqPsi_eq]
  refine ⟨?_, ?_⟩
  · rintro rfl
    simp [basis]
  · intro h
    simp [basis, hj, h]

theorem gammaFull_entry_iPsiSqPsiSq (g : G) (j : Symbol) (hj : j ≠ Symbol.iPsiSqPsiSq) :
    (j = Symbol.psiSq → structureGroupMap g (basis Symbol.iPsiSqPsiSq) j = g.cPsiSq) ∧
      (j ≠ Symbol.psiSq → structureGroupMap g (basis Symbol.iPsiSqPsiSq) j = 0) := by
  rw [structureGroupMap_basis_iPsiSqPsiSq_eq]
  refine ⟨?_, ?_⟩
  · rintro rfl
    simp [basis]
  · intro h
    simp [basis, hj, h]

theorem gammaFull_entry_iPsiCubePsi (g : G) (j : Symbol) (hj : j ≠ Symbol.iPsiCubePsi) :
    (j = Symbol.psi → structureGroupMap g (basis Symbol.iPsiCubePsi) j = g.cPsiCube) ∧
      (j ≠ Symbol.psi → structureGroupMap g (basis Symbol.iPsiCubePsi) j = 0) := by
  rw [structureGroupMap_basis_iPsiCubePsi_eq]
  refine ⟨?_, ?_⟩
  · rintro rfl
    simp [basis]
  · intro h
    simp [basis, hj, h]

theorem gammaFull_entry_iPsiCubePsiSq (g : G) (j : Symbol) (hj : j ≠ Symbol.iPsiCubePsiSq) :
    (j = Symbol.psiSq → structureGroupMap g (basis Symbol.iPsiCubePsiSq) j = g.cPsiCube) ∧
      (j ≠ Symbol.psiSq → structureGroupMap g (basis Symbol.iPsiCubePsiSq) j = 0) := by
  rw [structureGroupMap_basis_iPsiCubePsiSq_eq]
  refine ⟨?_, ?_⟩
  · rintro rfl
    simp [basis]
  · intro h
    simp [basis, hj, h]

theorem gammaFull_entry_iPsiPsi (g : G) (j : Symbol) (hj : j ≠ Symbol.iPsiPsi) :
    (j = Symbol.psi → structureGroupMap g (basis Symbol.iPsiPsi) j = g.cPsi) ∧
    (∀ k, j = Symbol.psiX k → structureGroupMap g (basis Symbol.iPsiPsi) j = g.cPsiGrad k) ∧
    ((j ≠ Symbol.psi ∧ ∀ k, j ≠ Symbol.psiX k) →
      structureGroupMap g (basis Symbol.iPsiPsi) j = 0) := by
  rw [structureGroupMap_basis_iPsiPsi_eq]
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    simp [basis]
  · rintro k rfl
    simp [basis, Finsupp.single_apply]
  · rintro ⟨h1, h2⟩
    cases j <;> simp_all [basis]

theorem gammaFull_entry_iPsiPsiSq (g : G) (j : Symbol) (hj : j ≠ Symbol.iPsiPsiSq) :
    (j = Symbol.psiSq → structureGroupMap g (basis Symbol.iPsiPsiSq) j = g.cPsi) ∧
    (∀ k, j = Symbol.psiSqX k → structureGroupMap g (basis Symbol.iPsiPsiSq) j = g.cPsiGrad k) ∧
    ((j ≠ Symbol.psiSq ∧ ∀ k, j ≠ Symbol.psiSqX k) →
      structureGroupMap g (basis Symbol.iPsiPsiSq) j = 0) := by
  rw [structureGroupMap_basis_iPsiPsiSq_eq]
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    simp [basis]
  · rintro k rfl
    simp [basis, Finsupp.single_apply]
  · rintro ⟨h1, h2⟩
    cases j <;> simp_all [basis]

theorem gammaFull_entry_iPsiCubeSq (g : G) (j : Symbol) (hj : j ≠ Symbol.iPsiCubeSq) :
    (j = Symbol.iPsiCube → structureGroupMap g (basis Symbol.iPsiCubeSq) j = 2 * g.cPsiCube) ∧
    (j = Symbol.one → structureGroupMap g (basis Symbol.iPsiCubeSq) j = g.cPsiCube * g.cPsiCube) ∧
    ((j ≠ Symbol.iPsiCube ∧ j ≠ Symbol.one) →
      structureGroupMap g (basis Symbol.iPsiCubeSq) j = 0) := by
  rw [structureGroupMap_basis_iPsiCubeSq_eq]
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    simp [basis]
  · rintro rfl
    simp [basis]
  · rintro ⟨h1, h2⟩
    cases j <;> simp_all [basis]

end RegularityStructures.Phi43

end
