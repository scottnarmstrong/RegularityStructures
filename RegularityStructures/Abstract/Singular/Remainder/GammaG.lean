/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.Emb
public import RegularityStructures.Abstract.Singular.Remainder.Gamma
public import RegularityStructures.Abstract.Singular.Remainder.RemKernelG
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# The `X^k`-components of `R_γ f(x)` for a generic remainder kernel

`remVecG` analogues of `remVec_mem_subspace`, `remVec_apply_emb`, `remVec_sub_gammaMap_apply_emb`
and `remVec_mem_lowerSubspace` (`RegularityStructures.Abstract.Singular.Remainder.Gamma`).
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

theorem remVecG_mem_subspace (M : Model 𝒯 parabolicSemigroup) (r : ParabolicSpace → ℝ) (P : PolynomialSector 𝒯 N')
    (γ : ℝ) (f : ParabolicSpace → ι → ℝ) (x : ParabolicSpace) :
    M.remVecG r P γ f x ∈ P.subspace := by
  classical
  unfold remVecG
  refine Submodule.sum_mem _ fun k _ => ?_
  split_ifs
  · exact Submodule.smul_mem _ _ (single_emb_mem_subspace P k)
  · exact Submodule.zero_mem _

theorem remVecG_apply_emb (M : Model 𝒯 parabolicSemigroup) (r : ParabolicSpace → ℝ) (P : PolynomialSector 𝒯 N')
    (γ : ℝ) (f : ParabolicSpace → ι → ℝ) (y : ParabolicSpace) (k : PolyIndex N') :
    M.remVecG r P γ f y (P.emb k) = if polyDeg N' k < γ + 2 then
      M.remPairing f (fun w => lineIter (multiDirs k.1) r (y - w)) /
        multiFactorial k.1 else 0 := by
  classical
  simp only [remVecG, Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · by_cases hp : polyDeg N' k < γ + 2 <;> simp [hp]
  · intro c _ hc
    by_cases hp : polyDeg N' c < γ + 2 <;> simp [hp, single_emb_apply, hc]
  · simp

/-- The `X^k`-component of `R_γ f(y) − Γ_{yx} R_γ f(x)` is the pairing of `R f` with the Taylor
remainder kernel (before applying linearity). -/
theorem remVecG_sub_gammaMap_apply_emb {M : Model 𝒯 parabolicSemigroup} {P : PolynomialSector 𝒯 N'}
    (hM : M.IsPolyCompatible P) (r : ParabolicSpace → ℝ) (γ : ℝ) (f : ParabolicSpace → ι → ℝ)
    (x y : ParabolicSpace) (k : PolyIndex N') (hk : polyDeg N' k < γ + 2)
    (hNγ : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) < γ + 2 → multiDeg l < N') :
    (M.remVecG r P γ f y - M.gammaMap y x (M.remVecG r P γ f x)) (P.emb k) * multiFactorial k.1 =
      M.remPairing f (fun w => lineIter (multiDirs k.1) r (y - w)) -
        ∑ l ∈ taylorIdx (γ + 2 - multiDeg k.1), coeffT (parabolicCoords (y - x)) l *
          M.remPairing f (fun w => lineIter (multiDirs (k.1 + l)) r (x - w)) := by
  have h := gammaMap_polyVec_apply_emb hM γ
    (fun k' => M.remPairing f (fun w => lineIter (multiDirs k') r (x - w)))
    x y k hNγ
  have h' : M.gammaMap y x (M.remVecG r P γ f x) (P.emb k) * multiFactorial k.1 = _ := h
  have hne : (multiFactorial k.1 : ℝ) ≠ 0 := by exact_mod_cast (multiFactorial_pos k.1).ne'
  rw [Pi.sub_apply, sub_mul, h', remVecG_apply_emb]
  simp only [hk, ↓reduceIte]
  rw [div_mul_cancel₀ _ hne]

theorem remVecG_mem_lowerSubspace (M : Model 𝒯 parabolicSemigroup) (r : ParabolicSpace → ℝ)
    (P : PolynomialSector 𝒯 N') (γ : ℝ) (f : ParabolicSpace → ι → ℝ) (x : ParabolicSpace) :
    M.remVecG r P γ f x ∈ lowerSubspace 𝒯.deg (γ + 2) := by
  refine (mem_lowerSubspace).2 fun i hi => ?_
  by_cases hr : i ∈ Set.range P.emb
  · obtain ⟨k, rfl⟩ := hr
    rw [P.deg_emb] at hi
    simp [remVecG_apply_emb, not_lt.2 hi]
  · exact M.remVecG_mem_subspace r P γ f x i hr

end Model

end RegularityStructures

end
