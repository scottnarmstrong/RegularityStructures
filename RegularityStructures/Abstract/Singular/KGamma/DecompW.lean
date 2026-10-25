/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.DecompG
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Analysis.Parabolic.SingularKernel

/-!
# Singular `𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x)`: decomposition, window models

Window (`_win`) versions of `RegularityStructures.Abstract.Singular.KGamma.DecompG`. These are
identities (and a bound whose constant does not involve the model): the qualitative growth model of
`LayerSettingW.hgrowth` is passed to the weighted lemma, so no quantitative window data enters.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {h : ParabolicSpace → ℝ} {N : ℕ} {γ : ℝ}
  {P : PolynomialSector 𝒯 N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)}

theorem kGammaS_sub_gamma_eq_win
    (hh : ShellProfile h N) (hreal : M.IsRealisingP h γ P I V) (hI : IsAbstractIntegration P V I 2)
    (hV : 𝒯.IsSector V) (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (hgrowth : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M.GrowthModel γ C' C'' ρP ρG p q) (hN' : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 →
      multiDeg k < N')
    {f : ParabolicSpace → ι → ℝ} (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ) (hfV : ∀ x, f x ∈ V)
    (x y : ParabolicSpace) :
    kGammaS M h P I γ f y - M.gammaMap y x (kGammaS M h P I γ f x) =
      I (f y - M.gammaMap y x (f x)) + jMapP M h P y (f y - M.gammaMap y x (f x)) +
        nVecS M h P γ f y - M.gammaMap y x (nVecS M h P γ f x) := by
  obtain ⟨_, _, _, _, _, _, G⟩ := hgrowth
  apply kGammaS_sub_gamma_eq_growth (G := G) <;> assumption

end Model

end RegularityStructures

end
