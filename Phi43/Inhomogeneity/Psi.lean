/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Inhomogeneity.SlabConst
public import Phi43.FixedPointF.Sectors
public import Phi43.FixedPointF.GroupAction
public import Phi43.FixedPointF.Hypotheses
public import RegularityStructures.Abstract.Model

/-!
# The inhomogeneity `Ψ · 1_{slab}` of the `Φ⁴₃` fixed point

[Hai14, Section 9.4]. In the enlarged structure the symbol `Ψ` has degree `-1/2 - κ`, lies in the
solution sector `V`, and is fixed by every element of the structure group
(`phi43ExtensionGroupF_psi_fixed`), hence by every `Γ_{yx}` of every model.  By
`Phi43.Inhomogeneity.SlabConst` the function `Ψ · 1_{(0,T] × ℝ³}` is therefore an element of
`SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T)` of norm at most `1`, for every
`η` and every model (`norm_phi43PsiSlab_le`); the comparison of two such elements vanishes.
(No inequality between `η` and the degree of `Ψ` is needed: the weight exponent
`min (η - deg Ψ) 0` is nonpositive.)
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The basis vector `e_Ψ` of the enlarged structure. -/
def phi43PsiVec : SymbolF → ℝ := Pi.single (.old .psi) 1

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

theorem phi43ExtensionGroupF_psi_fixed (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (SymbolF → ℝ))
    (hg : g ∈ (phi43RegularityStructureF κ).group) :
    g.val phi43PsiVec = phi43PsiVec := by
  obtain ⟨p, hp⟩ := phi43ExtensionGroupF_old_params κ g hg
  rw [phi43PsiVec, hp .psi]
  simp only [structureBasisAction, primitiveAction, phi43CoordinateEquiv_basis,
    phi43OldEmbF_single]

theorem gammaMap_phi43PsiVec (κ : Kappa) {E : Type*} [MeasurableSpace E]
    {μ : MeasureTheory.Measure E} {K : RegularisingSemigroup E μ}
    (M : Model (phi43RegularityStructureF κ) K) (x y : E) :
    M.gammaMap y x phi43PsiVec = phi43PsiVec :=
  phi43ExtensionGroupF_psi_fixed κ _ (M.gamma y x).2

theorem phi43PsiVec_mem (κ : Kappa) :
    phi43PsiVec ∈ phi43SectorV ⊓ lowerSubspace (phi43RegularityStructureF κ).deg (gamma κ) := by
  have h0 := κ.2.1
  have h1 := κ.2.2
  refine ⟨single_mem_phi43SectorV (j := SymbolF.old .psi) rfl,
    single_mem_lowerSubspace (i := SymbolF.old .psi) ?_ 1⟩
  simp only [phi43RegularityStructureF_old_deg, homogeneity, gamma]
  linarith

end RegularityStructures.Phi43

end

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- **`Ψ · 1_{(0,T]×ℝ³}` as an element of the slab space** of the fixed point
(any model, any exponent `η`). -/
def phi43PsiSlab (κ : Kappa) (η T : ℝ) (M : Model (phi43RegularityStructureF κ) parabolicSemigroup) :
    M.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T) :=
  Inhomogeneity.slabConstElem M T phi43PsiVec (phi43PsiVec_mem κ) (gammaMap_phi43PsiVec κ M)

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

theorem abs_phi43PsiVec_le (i : SymbolF) : |phi43PsiVec i| ≤ 1 := by
  by_cases h : i = .old .psi <;> simp [phi43PsiVec, h]

/-- **The norm of `Ψ · 1_{slab}` is at most `1`.** -/
theorem norm_phi43PsiSlab_le (κ : Kappa) (η T : ℝ)
    (M : Model (phi43RegularityStructureF κ) parabolicSemigroup) :
    ‖phi43PsiSlab κ η T M‖ ≤ 1 :=
  Inhomogeneity.norm_slabConstElem_le M T phi43PsiVec (phi43PsiVec_mem κ)
    (gammaMap_phi43PsiVec κ M) zero_le_one abs_phi43PsiVec_le

/-- **Two models:** the comparison norm of `Ψ · 1_{slab}` for two models vanishes. -/
theorem singularDiffBoundOn_phi43PsiSlab (κ : Kappa) (η T : ℝ)
    (M₁ M₂ : Model (phi43RegularityStructureF κ) parabolicSemigroup) :
    M₁.SingularDiffBoundOn M₂ timeZeroDist (gamma κ) η 0 (timeSlab T)
      (phi43PsiSlab κ η T M₁).val (phi43PsiSlab κ η T M₂).val :=
  Inhomogeneity.singularDiffBoundOn_slabConst_self (gammaMap_phi43PsiVec κ M₁)
    (gammaMap_phi43PsiVec κ M₂)

end RegularityStructures.Phi43

end
