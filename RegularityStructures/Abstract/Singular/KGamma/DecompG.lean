/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.Emb
public import RegularityStructures.Abstract.Profile.Growth.Commute
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Analysis.Parabolic.SingularKernel

/-!
# Singular `𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x)`: decomposition, weighted models

Weighted (`_growth`) version of the decomposition: Lemma 5.16 for `J` is taken from
`RegularityStructures.Abstract.Profile.Growth.Commute`
(`gammaMap_integral_add_jMap_of_mem_inP_growth`); the model enters only through a
`Model.GrowthModel`.

Singular analogue of the decomposition of `𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x)` in the proof of
[Hai14, Theorem 5.12], for `kGammaS` (`RegularityStructures.Abstract.Singular.KGamma.Defs`) and a
shell profile `h`: with `τ = f(y) − Γ_{yx} f(x)`,

* `𝒦f(y) − Γ_{yx} 𝒦f(x) = I τ + J(y) τ + N f(y) − Γ_{yx} N f(x)` (Lemma 5.16 of [Hai14] for `J`);
* its `X^k`-component is `∑_i τ_i J_{i,k} + N_k(y) − (Γ_{yx} N f(x))_k`;
* its components outside `T̄` equal `(I τ)_j`, with the bound of [Hai14, Thm 5.12].

Here `f` only needs values in `V ∩ T_{<γ}`; no analytic bound on `R f` is used.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {h : ParabolicSpace → ℝ} {N : ℕ} {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}
  {P : PolynomialSector 𝒯 N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)}

theorem kGammaS_sub_gamma_eq_growth
    (hh : ShellProfile h N) (hreal : M.IsRealisingP h γ P I V) (hI : IsAbstractIntegration P V I 2)
    (hV : 𝒯.IsSector V) (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (hN' : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 →
      multiDeg k < N')
    {f : ParabolicSpace → ι → ℝ} (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ) (hfV : ∀ x, f x ∈ V)
    (x y : ParabolicSpace) :
    kGammaS M h P I γ f y - M.gammaMap y x (kGammaS M h P I γ f x) =
      I (f y - M.gammaMap y x (f x)) + jMapP M h P y (f y - M.gammaMap y x (f x)) +
        nVecS M h P γ f y - M.gammaMap y x (nVecS M h P γ f x) := by
  have h516 := gammaMap_integral_add_jMap_of_mem_inP_growth hh hreal hI hV hVb hdeg G hN'
    (hfV x) (hf x) y x
  have e1 : kGammaS M h P I γ f y = (I (f y) + jMapP M h P y (f y)) + nVecS M h P γ f y := rfl
  have e2 : M.gammaMap y x (kGammaS M h P I γ f x) =
      M.gammaMap y x (I (f x) + jMapP M h P x (f x)) + M.gammaMap y x (nVecS M h P γ f x) := by
    simp only [kGammaS, map_add]
  rw [e1, e2, h516, map_sub, map_sub]
  abel

theorem kGammaS_sub_gamma_apply_emb_growth
    (hh : ShellProfile h N) (hreal : M.IsRealisingP h γ P I V) (hI : IsAbstractIntegration P V I 2)
    (hV : 𝒯.IsSector V) (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (hN' : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 →
      multiDeg k < N')
    (hIpoly : ∀ a ∈ V, ∀ k : PolyIndex N', I a (P.emb k) = 0)
    {f : ParabolicSpace → ι → ℝ} (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ) (hfV : ∀ x, f x ∈ V)
    (x y : ParabolicSpace) (k : PolyIndex N') :
    (kGammaS M h P I γ f y - M.gammaMap y x (kGammaS M h P I γ f x)) (P.emb k) =
      (∑ i, (f y - M.gammaMap y x (f x)) i * (if polyDeg N' k < 𝒯.deg i + 2 then
        jCoeffP M h y i k.1 / multiFactorial k.1 else 0)) +
      (if polyDeg N' k < γ + 2 then nCoeffS M h f y k.1 / multiFactorial k.1 else 0) -
      M.gammaMap y x (nVecS M h P γ f x) (P.emb k) := by
  have hτV : f y - M.gammaMap y x (f x) ∈ V :=
    Submodule.sub_mem _ (hfV y) (hV.invariant _ (M.gamma y x).2 _ (hfV x))
  rw [kGammaS_sub_gamma_eq_growth hh hreal hI hV hVb hdeg G hN' hf hfV x y]
  simp only [Pi.add_apply, Pi.sub_apply, hIpoly _ hτV k, jMapP_apply_emb, nVecS_apply_emb]
  ring

end Model

end RegularityStructures

end
