/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Profile.Basic
public import RegularityStructures.Abstract.Integration.JMapLinear
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Heat.Annihilating.Scaled
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# Hairer's map `J(x)` for a general shell profile

Profile-generic versions of the coefficients of `J(x)` and of
`RegularityStructures.Abstract.Integration.JMapLinear`: for a kernel profile `h`
(`ShellProfile h N`) with shells `K_n = scaledShell h n`,
`jCoeffP M h x i k = ∑_n ⟨Π_x e_i, D^k K_n(x - ·)⟩`, with the absolute convergence and the bound
`|jCoeffP M h x i k| ≤ c C_Π max(C_Γ, 1)` for `|k|_𝔰 < deg i + 2`
(`summable_jCoeff_termsP`, `abs_jCoeff_leP`), and the linear map `jMapP` [Hai14, (5.11)].
For `h = annKernel0 N` these are `jCoeff` and `jMap`.

Source: [Hai14] = arXiv:1303.5113v4, (5.11).
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- `jCoeffP M h x i k = ∑ₙ ⟨Π_x e_i, D^k (scaledShell h n)(x - ·)⟩`. -/
def jCoeffP (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (i : ι) (k : Fin 4 →₀ ℕ) : ℝ :=
  ∑' n : ℕ, parabolicSemigroup.pairing (fun t y => M.regPi x (Pi.single i 1) t y)
    (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y))

open Classical in
/-- `J(x) e_i = ∑_{|k|_𝔰 < deg i + 2} jCoeffP / k! · X^k`, as a vector of `T`. -/
def jVecP (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) {N' : ℕ}
    (P : PolynomialSector 𝒯 N') (x : ParabolicSpace) (i : ι) : ι → ℝ :=
  ∑ k : PolyIndex N', if polyDeg N' k < 𝒯.deg i + 2 then
    (jCoeffP M h x i k.1 / multiFactorial k.1) • (Pi.single (P.emb k) 1 : ι → ℝ) else 0

/-- Hairer's `J(x)` [Hai14, (5.11)] for the profile `h`, extended linearly from the basis. -/
def jMapP (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) {N' : ℕ}
    (P : PolynomialSector 𝒯 N') (x : ParabolicSpace) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun τ := ∑ i, τ i • jVecP M h P x i
  map_add' τ σ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c τ := by simp [Finset.smul_sum, smul_smul]

end RegularityStructures

end

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

theorem jMapP_single (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) {N' : ℕ}
    (P : PolynomialSector 𝒯 N') (x : ParabolicSpace) (i : ι) :
    jMapP M h P x (Pi.single i 1) = jVecP M h P x i := by
  simp only [jMapP, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem jVecP_mem_subspace (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) {N' : ℕ}
    (P : PolynomialSector 𝒯 N') (x : ParabolicSpace) (i : ι) :
    jVecP M h P x i ∈ P.subspace := by
  classical
  unfold jVecP
  refine Submodule.sum_mem _ fun k _ => ?_
  split_ifs
  · exact Submodule.smul_mem _ _ (single_emb_mem_subspace P k)
  · exact Submodule.zero_mem _

/-- `J(x)` takes values in the abstract polynomials `T̄`. -/
theorem jMapP_mem_subspace (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) {N' : ℕ}
    (P : PolynomialSector 𝒯 N') (x : ParabolicSpace) (τ : ι → ℝ) :
    jMapP M h P x τ ∈ P.subspace :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (jVecP_mem_subspace M h P x i)

end RegularityStructures

end
