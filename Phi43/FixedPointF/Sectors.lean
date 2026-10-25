/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.FixedPointF.GroupAction
public import RegularityStructures.Abstract.Singular.Phi4FixedPointBlock
public import RegularityStructures.Abstract.Singular.Slab.OperatorSlab

/-!
# The coordinate sectors `V ⊂ W` of the `Φ⁴₃` fixed point on the enlarged structure

[Hai14, Section 9.4, Proposition 9.8]. `V` is spanned by `1`, `X₀`, `Xᵢ`, `XᵢXⱼ`, `Ψ`, `I(Ψ)`,
`I(Ψ²)`, `I(Ψ³)` and all twelve planted integrals; `W ⊇ V ⋆ V` adds `Ψ²`, `XᵢΨ`, `I(Ψ)Ψ`,
`I(Ψ²)Ψ`, `I(Ψ³)Ψ`, `I(Ψ³)²`.  Both are coordinate subspaces `blockSpan` of explicit symbol
sets (Boolean predicates `phi43VBool`, `phi43WBool`).
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The symbols spanning the solution sector `V`. -/
def phi43VBool : SymbolF → Bool
  | .old .one => true
  | .old .x0 => true
  | .old (.x _) => true
  | .old (.xMul _) => true
  | .old .psi => true
  | .old .iPsi => true
  | .old .iPsiSq => true
  | .old .iPsiCube => true
  | .planted _ => true
  | _ => false

/-- The symbols spanning the product sector `W ⊇ V ⋆ V`. -/
def phi43WBool : SymbolF → Bool
  | .old .psiSq => true
  | .old .iPsiPsi => true
  | .old .iPsiSqPsi => true
  | .old .iPsiCubePsi => true
  | .old (.psiX _) => true
  | .old .iPsiCubeSq => true
  | τ => phi43VBool τ

/-- The finite set of symbols of `V`. -/
def phi43VSyms : Finset SymbolF := Finset.univ.filter fun j => phi43VBool j = true

/-- The finite set of symbols of `W`. -/
def phi43WSyms : Finset SymbolF := Finset.univ.filter fun j => phi43WBool j = true

/-- The solution sector `V`. -/
def phi43SectorV : Submodule ℝ (SymbolF → ℝ) := blockSpan phi43VSyms

/-- The product sector `W`. -/
def phi43SectorW : Submodule ℝ (SymbolF → ℝ) := blockSpan phi43WSyms

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

theorem phi43VBool_of_phi43WBool_false {j : SymbolF} (h : phi43WBool j = false) :
    phi43VBool j = false := by
  cases j with
  | old τ => cases τ <;> simp_all [phi43WBool, phi43VBool]
  | planted τ => simp [phi43WBool, phi43VBool] at h

theorem mem_phi43SectorV {a : SymbolF → ℝ} :
    a ∈ phi43SectorV ↔ ∀ j, phi43VBool j = false → a j = 0 := by
  constructor
  · intro ha j hj
    exact eq_zero_of_notMem_of_mem_blockSpan ha (by simp [phi43VSyms, hj])
  · intro h
    exact mem_blockSpan_of_forall fun j hj => h j (by simpa [phi43VSyms] using hj)

theorem mem_phi43SectorW {a : SymbolF → ℝ} :
    a ∈ phi43SectorW ↔ ∀ j, phi43WBool j = false → a j = 0 := by
  constructor
  · intro ha j hj
    exact eq_zero_of_notMem_of_mem_blockSpan ha (by simp [phi43WSyms, hj])
  · intro h
    exact mem_blockSpan_of_forall fun j hj => h j (by simpa [phi43WSyms] using hj)

theorem single_mem_phi43SectorV {j : SymbolF} (hj : phi43VBool j = true) :
    (Pi.single j 1 : SymbolF → ℝ) ∈ phi43SectorV :=
  Submodule.subset_span ⟨j, by simpa [phi43VSyms] using hj, rfl⟩

theorem single_mem_phi43SectorW {j : SymbolF} (hj : phi43WBool j = true) :
    (Pi.single j 1 : SymbolF → ℝ) ∈ phi43SectorW :=
  Submodule.subset_span ⟨j, by simpa [phi43WSyms] using hj, rfl⟩

theorem isCoordClosed_phi43SectorV : IsCoordClosed phi43SectorV :=
  isCoordClosed_blockSpan _

theorem isCoordClosed_phi43SectorW : IsCoordClosed phi43SectorW :=
  isCoordClosed_blockSpan _

/-- A coordinate subspace is a sector as soon as the group maps its basis vectors into it. -/
theorem isSector_blockSpan_of_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    {𝒯 : RegularityStructure ι} {S : Finset ι}
    (h : ∀ g ∈ 𝒯.group, ∀ i ∈ S, ∀ j, j ∉ S →
      ((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (Pi.single i 1) j = 0) :
    𝒯.IsSector (blockSpan S) where
  graded α a ha := by
    refine mem_blockSpan_of_forall fun i hi => ?_
    rw [homogeneousProj_apply]
    split_ifs with hdeg
    · exact eq_zero_of_notMem_of_mem_blockSpan ha hi
    · rfl
  invariant g hg a ha := by
    refine mem_blockSpan_of_forall fun j hj => ?_
    conv_lhs => rw [eq_sum_single a]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ S
    · rw [h g hg i hi j hj, mul_zero]
    · rw [eq_zero_of_notMem_of_mem_blockSpan ha hi, zero_mul]

end RegularityStructures.Phi43

end
