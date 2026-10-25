/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Schauder
public import RegularityStructures.Abstract.Integration.SchauderPolyBound

/-!
# The standing hypotheses of the multilevel Schauder estimate

`SchauderSetting M N γ P I V CPi CGam CI` bundles the hypotheses shared by the two increment
theorems `Model.abs_kGamma_sub_gamma_nonpoly_le` and `Model.exists_abs_kGamma_sub_gamma_poly_le`
and the sup bounds of [Hai14, Theorem 5.12]: a realising model `M` for the abstract integration map
`I` on the sector `V`, the model bounds, the degree conditions, and `I` having no `T̄` component.
The non-integrality conditions on `γ` are the model-free `SchauderNonIntegral`; the kernel
annihilation order `N` must satisfy `N' ≤ N` (a hypothesis of the theorems, not of the setting).

Restrictions relative to [Hai14]: every homogeneity of `𝒯` below
`γ` (not only those occurring in `V`) must exceed `−2`, which excludes the Φ⁴₃ noise symbol of
degree `−5/2 − κ`; the model and `D^γ` bounds are global (`univ`); `I` has no `T̄` component; the
non-integrality conditions are stronger than `γ + β ∉ ℕ`. Only the first half of Theorem 5.12 is
formalised (the bound and (5.17)); the local Lipschitz estimate in the model is not.

Source: [Hai14, Theorem 5.12, Definitions 5.7 and 5.9].
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

/-- The standing hypotheses of [Hai14, Theorem 5.12]. -/
structure SchauderSetting (M : Model 𝒯 parabolicSemigroup) (N : ℕ) (γ : ℝ)
    (P : PolynomialSector 𝒯 N') (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (V : Submodule ℝ (ι → ℝ))
    (CPi CGam CI : ℝ) : Prop where
  pos : 0 < γ
  realising : M.IsRealising N γ P I V
  integration : IsAbstractIntegration P V I 2
  sector : 𝒯.IsSector V
  basis_mem : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V
  deg_gt : ∀ j, 𝒯.deg j < γ → -2 < 𝒯.deg j
  piBound : M.PiBoundOn γ CPi univ
  gammaBound : M.GammaBoundOn γ CGam univ
  piBound_nonneg : 0 ≤ CPi
  poly_large : ∀ j, 𝒯.deg j < γ → ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 →
    multiDeg k < N'
  poly_large' : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) < γ + 2 → multiDeg l < N'
  integration_poly : ∀ a ∈ V, ∀ k : PolyIndex N', I a (P.emb k) = 0
  entry_bound : ∀ i j, |I (Pi.single i 1) j| ≤ CI

/-- The non-integrality conditions on `γ` of [Hai14, Theorem 5.12] (they involve no model):
`γ + 2 − |k|_𝔰 ∉ ℕ[𝔰]` and `|k|_𝔰 ≠ deg i + 2` for the **non-polynomial** components
`i ∉ range P.emb` with `|k|_𝔰 < γ + 2`. For a polynomial component `X^l` the pairing
`⟨Π_y X^l, D^k K_n(y − ·)⟩` vanishes outright when `|l|_𝔰 < N` (`PolyPairing.Main`), so no
condition is needed there; requiring it would be contradictory, since `X^0` has degree `0 < γ` and
`k = e₀` has `|k|_𝔰 = 2 = 0 + 2`. -/
structure SchauderNonIntegral (𝒯 : RegularityStructure ι) (γ : ℝ) (N' : ℕ)
    (P : PolynomialSector 𝒯 N') : Prop where
  nonint₁ : ∀ k : PolyIndex N', polyDeg N' k < γ + 2 →
    ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) ≠ γ + 2 - multiDeg k.1
  nonint₂ : ∀ k : PolyIndex N', polyDeg N' k < γ + 2 →
    ∀ i, i ∉ Set.range P.emb → 𝒯.deg i < γ → (multiDeg k.1 : ℝ) ≠ 𝒯.deg i + 2

end RegularityStructures

end
