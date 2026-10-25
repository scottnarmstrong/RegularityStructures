/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.JMapLinear
public import RegularityStructures.Abstract.Integration.JMapCoeff
public import RegularityStructures.Abstract.Integration
public import RegularityStructures.Abstract.RegularityStructureDegrees
public import RegularityStructures.Abstract.Polynomial

/-!
# Hairer's map `J(x)`

`jVec` and `jMap`: `J(x) e_i = ∑_{|k|_𝔰 < deg i + 2} jCoeff / k! · X^k`, extended linearly; `J(x)`
takes values in the abstract polynomials (`jMap_mem_subspace`).

Source: [Hai14, (5.11)].
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

open Classical in
/-- `J(x) e_i = ∑_{|k|_𝔰 < deg i + 2} jCoeff / k! · X^k`, as a vector of `T`. -/
def jVec (M : Model 𝒯 parabolicSemigroup) (N : ℕ) {N' : ℕ} (P : PolynomialSector 𝒯 N')
    (x : ParabolicSpace) (i : ι) : ι → ℝ :=
  ∑ k : PolyIndex N', if polyDeg N' k < 𝒯.deg i + 2 then
    (jCoeff M N x i k.1 / multiFactorial k.1) • (Pi.single (P.emb k) 1 : ι → ℝ) else 0

/-- Hairer's `J(x)` [Hai14, (5.11)], extended linearly from the basis. -/
def jMap (M : Model 𝒯 parabolicSemigroup) (N : ℕ) {N' : ℕ} (P : PolynomialSector 𝒯 N')
    (x : ParabolicSpace) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun τ := ∑ i, τ i • jVec M N P x i
  map_add' τ σ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c τ := by simp [Finset.smul_sum, smul_smul]

end RegularityStructures

end

public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

theorem jMap_single (M : Model 𝒯 parabolicSemigroup) (N : ℕ) {N' : ℕ}
    (P : PolynomialSector 𝒯 N') (x : ParabolicSpace) (i : ι) :
    jMap M N P x (Pi.single i 1) = jVec M N P x i := by
  simp only [jMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem jVec_mem_subspace (M : Model 𝒯 parabolicSemigroup) (N : ℕ) {N' : ℕ}
    (P : PolynomialSector 𝒯 N') (x : ParabolicSpace) (i : ι) : jVec M N P x i ∈ P.subspace := by
  classical
  unfold jVec
  refine Submodule.sum_mem _ fun k _ => ?_
  split_ifs
  · exact Submodule.smul_mem _ _ (single_emb_mem_subspace P k)
  · exact Submodule.zero_mem _

/-- `J(x)` takes values in the abstract polynomials `T̄`. -/
theorem jMap_mem_subspace (M : Model 𝒯 parabolicSemigroup) (N : ℕ) {N' : ℕ}
    (P : PolynomialSector 𝒯 N') (x : ParabolicSpace) (τ : ι → ℝ) :
    jMap M N P x τ ∈ P.subspace :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (jVec_mem_subspace M N P x i)

end RegularityStructures

end
