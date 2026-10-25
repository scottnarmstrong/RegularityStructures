/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.SchauderComp
public import RegularityStructures.Abstract.Integration.SchauderCompEmb

/-!
# Multilevel Schauder: decomposition of `𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x)`

`kGamma_sub_gamma_eq`: `𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x) = I τ + J(y) τ + N_γ f(y) − Γ_{yx} N_γ f(x)`,
`τ = f(y) − Γ_{yx} f(x)`, from Lemma 5.16 (`Model.gammaMap_integral_add_jMap_of_mem`).  Its component
along `X^k` (`kGamma_sub_gamma_apply_emb`) is the starting point of the polynomial part of
[Hai14, Theorem 5.12].
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {N : ℕ} {γ CPi CGam : ℝ} {P : PolynomialSector 𝒯 N'}
  {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)}

theorem kGamma_sub_gamma_eq
    (hreal : M.IsRealising N γ P I V) (hI : IsAbstractIntegration P V I 2)
    (hV : 𝒯.IsSector V) (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (hPi : M.PiBoundOn γ CPi univ) (hGam : M.GammaBoundOn γ CGam univ) (hCPi : 0 ≤ CPi)
    (hN' : ∀ j, 𝒯.deg j < γ → ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 →
      multiDeg k < N')
    {f : ParabolicSpace → ι → ℝ} (hf : f ∈ M.modelledDistributions γ) (hfV : ∀ x, f x ∈ V)
    (x y : ParabolicSpace) :
    kGamma M N P I γ f y - M.gammaMap y x (kGamma M N P I γ f x) =
      I (f y - M.gammaMap y x (f x)) + jMap M N P y (f y - M.gammaMap y x (f x)) +
        nVec M N P γ f y - M.gammaMap y x (nVec M N P γ f x) := by
  have h516 := gammaMap_integral_add_jMap_of_mem hreal hI hV hVb hdeg hPi hGam hCPi hN'
    (hfV x) (hf.2.1 x) y x
  have e1 : kGamma M N P I γ f y = (I (f y) + jMap M N P y (f y)) + nVec M N P γ f y := rfl
  have e2 : M.gammaMap y x (kGamma M N P I γ f x) =
      M.gammaMap y x (I (f x) + jMap M N P x (f x)) + M.gammaMap y x (nVec M N P γ f x) := by
    simp only [kGamma, map_add]
  rw [e1, e2, h516, map_sub, map_sub]
  abel

theorem kGamma_sub_gamma_apply_emb
    (hreal : M.IsRealising N γ P I V) (hI : IsAbstractIntegration P V I 2)
    (hV : 𝒯.IsSector V) (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (hPi : M.PiBoundOn γ CPi univ) (hGam : M.GammaBoundOn γ CGam univ) (hCPi : 0 ≤ CPi)
    (hN' : ∀ j, 𝒯.deg j < γ → ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 →
      multiDeg k < N')
    (hIpoly : ∀ a ∈ V, ∀ k : PolyIndex N', I a (P.emb k) = 0)
    {f : ParabolicSpace → ι → ℝ} (hf : f ∈ M.modelledDistributions γ) (hfV : ∀ x, f x ∈ V)
    (x y : ParabolicSpace) (k : PolyIndex N') :
    (kGamma M N P I γ f y - M.gammaMap y x (kGamma M N P I γ f x)) (P.emb k) =
      (∑ i, (f y - M.gammaMap y x (f x)) i * (if polyDeg N' k < 𝒯.deg i + 2 then
        jCoeff M N y i k.1 / multiFactorial k.1 else 0)) +
      (if polyDeg N' k < γ + 2 then nCoeff M N f y k.1 / multiFactorial k.1 else 0) -
      M.gammaMap y x (nVec M N P γ f x) (P.emb k) := by
  have hτV : f y - M.gammaMap y x (f x) ∈ V :=
    Submodule.sub_mem _ (hfV y) (hV.invariant _ (M.gamma y x).2 _ (hfV x))
  rw [kGamma_sub_gamma_eq hreal hI hV hVb hdeg hPi hGam hCPi hN' hf hfV x y]
  simp only [Pi.add_apply, Pi.sub_apply, hIpoly _ hτV k, jMap_apply_emb, nVec_apply_emb]
  ring

end Model

end RegularityStructures

end
