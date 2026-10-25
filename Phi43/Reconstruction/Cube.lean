/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Identification.Evaluate
public import Phi43.Reconstruction.Expansion
public import RegularityStructures.Abstract.QFamilyContinuousModel

/-!
# Pointwise reconstruction of the cube

The expansion of the nonlinearity and its pointwise evaluation, in the identification of the
reconstructed solution with the classical one.  For `u = Ψ + φ·1 - I(Ψ³) - 3φ I(Ψ²) +
φᵢ Xᵢ` the block projection of the truncated cube is `-(F(u) - Ξ)`
(`blockProj_lowerProj_cube_ansatz`), and for a family `g` of functions with
`g_{y, old τ}(y) = Π^M_{y + a} τ (y + a)` (the diagonal of the translated renormalised canonical
model) its pointwise reconstruction is
`R̃(u³)(y) = w³ - (3C₁ - 9C₂) w`, `w = (K ∗ ζ)(y + a) + φ` (`pointwiseReconstruct_cube_ansatz`).
-/

public section

namespace RegularityStructures.Phi43

theorem blockProj_lowerProj_cube_ansatz (κ : Kappa) (φ : ℝ) (ψ : Fin 3 → ℝ) :
    RegularityStructures.blockProj phi43XiFreeF
      (RegularityStructures.lowerProj (phi43RegularityStructureF κ).deg κ.1
        ((phi43ProductF κ).mul (phi43AnsatzF 1 φ (-1) (-3 * φ) ψ)
          ((phi43ProductF κ).mul (phi43AnsatzF 1 φ (-1) (-3 * φ) ψ)
            (phi43AnsatzF 1 φ (-1) (-3 * φ) ψ)))) = -phi43OldEmbF (phi43FDisplayOld φ ψ) := by
  have h := neg_lowerProj_cube_eq_oldEmb κ φ ψ 0 (phi43SuppGe_zero κ _)
  simp only [add_zero] at h
  rw [← neg_neg (RegularityStructures.lowerProj _ _ _), h]
  funext i
  rw [RegularityStructures.blockProj_apply]
  split_ifs with hi
  · rfl
  · cases i with
    | planted p => simp [phi43OldEmbF]
    | old τ =>
        have : τ = .noise := by
          by_contra hn
          exact hi (by simpa [phi43XiFreeF] using hn)
        subst this
        simp [phi43OldEmbF, phi43FDisplayOld, Pi.single_apply]

/-- The sum over `SymbolF` of a family vanishing on the planted symbols is the sum over `Symbol`. -/
theorem sum_symbolF_of_planted_zero (F : SymbolF → ℝ) (h : ∀ p, F (.planted p) = 0) :
    ∑ i, F i = ∑ τ : Symbol, F (.old τ) := by
  classical
  have hinj : Function.Injective (SymbolF.old) := fun a b hab => by simpa using hab
  rw [← Finset.sum_image (f := F) (g := SymbolF.old) (s := Finset.univ) (fun a _ b _ hab => hinj hab)]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
  cases i with
  | planted p => exact h p
  | old τ => exact absurd (Finset.mem_image.2 ⟨τ, Finset.mem_univ _, rfl⟩) hi

theorem pointwiseReconstruct_cube_ansatz (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants) (a : ParabolicSpace)
    (gF : ParabolicSpace → SymbolF → ParabolicSpace → ℝ)
    (hgF : ∀ y τ, gF y (.old τ) y = phi43BaseFunctions N κ noise C (y + a) τ (y + a))
    (f : ParabolicSpace → SymbolF → ℝ) (y : ParabolicSpace) (φ : ℝ) (ψ : Fin 3 → ℝ)
    (hf : f y = -phi43OldEmbF (phi43FDisplayOld φ ψ)) :
    RegularityStructures.pointwiseReconstruct gF f y =
      (phi43PsiAt N κ noise C (y + a) + φ) ^ 3 -
        (3 * C₁ C - 9 * C₂ C) * (phi43PsiAt N κ noise C (y + a) + φ) := by
  unfold RegularityStructures.pointwiseReconstruct
  rw [sum_symbolF_of_planted_zero]
  · have h := phi43_evaluate_at_base N κ noise C (y + a) φ ψ
    simp only [hf, hgF, Pi.neg_apply, phi43OldEmbF, LinearMap.coe_mk, AddHom.coe_mk, neg_mul,
      Finset.sum_neg_distrib]
    rw [h]
    ring
  · intro p
    simp [hf, phi43OldEmbF]

end RegularityStructures.Phi43

end
