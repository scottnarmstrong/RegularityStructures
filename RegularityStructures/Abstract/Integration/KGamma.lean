/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.NMap
public import RegularityStructures.Abstract.Integration.JMapLinear
public import RegularityStructures.Abstract.Integration.JMapDef

/-!
# The operator `𝒦_γ` on modelled distributions

[Hai14, (5.15)]: `(𝒦_γ f)(x) = I f(x) + J(x) f(x) + (N_γ f)(x)`, where `I` is an abstract
integration map, `J(x)` is (5.11) (`jMap`) and

  `(N_γ f)(x) = ∑_{|k|_𝔰 < γ + β} X^k / k! · nCoeff M N f x k`

is (5.16) (`nVec`), with β = 2 and the heat-kernel decomposition `K_n = annShell N n`. The
multilevel Schauder estimate [Hai14, Theorem 5.12] states that `𝒦_γ` maps `D^γ` into `D^{γ+β}`
and `R 𝒦_γ f = K ∗ Rf`; this file only records the definition and the fact that the
polynomial corrections take values in `T̄`.

Source: [Hai14, (5.15)–(5.17)].
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

open Classical in
/-- `(N_γ f)(x) = ∑_{|k|_𝔰 < γ + 2} nCoeff / k! · X^k` [Hai14, (5.16)]. -/
def nVec (M : Model 𝒯 parabolicSemigroup) (N : ℕ) {N' : ℕ} (P : PolynomialSector 𝒯 N')
    (γ : ℝ) (f : ParabolicSpace → ι → ℝ) (x : ParabolicSpace) : ι → ℝ :=
  ∑ k : PolyIndex N', if polyDeg N' k < γ + 2 then
    (nCoeff M N f x k.1 / multiFactorial k.1) • (Pi.single (P.emb k) 1 : ι → ℝ) else 0

/-- `(𝒦_γ f)(x) = I f(x) + J(x) f(x) + (N_γ f)(x)` [Hai14, (5.15)]. -/
def kGamma (M : Model 𝒯 parabolicSemigroup) (N : ℕ) {N' : ℕ} (P : PolynomialSector 𝒯 N')
    (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (γ : ℝ) (f : ParabolicSpace → ι → ℝ) (x : ParabolicSpace) :
    ι → ℝ :=
  I (f x) + jMap M N P x (f x) + nVec M N P γ f x

end RegularityStructures

end

public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

theorem nVec_mem_subspace (M : Model 𝒯 parabolicSemigroup) (N : ℕ) {N' : ℕ}
    (P : PolynomialSector 𝒯 N') (γ : ℝ) (f : ParabolicSpace → ι → ℝ) (x : ParabolicSpace) :
    nVec M N P γ f x ∈ P.subspace := by
  classical
  unfold nVec
  refine Submodule.sum_mem _ fun k _ => ?_
  split_ifs
  · exact Submodule.smul_mem _ _ (single_emb_mem_subspace P k)
  · exact Submodule.zero_mem _

/-- The polynomial corrections `J(x) f(x) + N_γ f(x)` lie in `T̄`. -/
theorem kGamma_sub_mem_subspace (M : Model 𝒯 parabolicSemigroup) (N : ℕ) {N' : ℕ}
    (P : PolynomialSector 𝒯 N') (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (γ : ℝ)
    (f : ParabolicSpace → ι → ℝ) (x : ParabolicSpace) :
    kGamma M N P I γ f x - I (f x) ∈ P.subspace := by
  have h : kGamma M N P I γ f x - I (f x) = jMap M N P x (f x) + nVec M N P γ f x := by
    unfold kGamma; abel
  rw [h]
  exact Submodule.add_mem _ (jMap_mem_subspace M N P x (f x)) (nVec_mem_subspace M N P γ f x)

end RegularityStructures

end
