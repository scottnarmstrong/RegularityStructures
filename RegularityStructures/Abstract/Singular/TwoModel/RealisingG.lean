/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TwoModel.CoeffLinearG
public import RegularityStructures.Abstract.Singular.TwoModel.Realising
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Profile.Realising

/-!
# The difference model realises the kernel, under weighted bounds

Weighted version of the realising property of the difference model: for a kernel profile `h`
(`ShellProfile h N`), if `M₁, M₂` realise the kernel for `I` on `V` and satisfy the weighted bounds
`Model.GrowthModel`, then `M⊕` realises it for `I⊕` on `V⊕` with `P⊕`. The non-integrality
hypothesis `hnat` is not needed (the germs are controlled through the `J`-coefficients and the
weighted `K ∗ Λ`, `RegularityStructures.Abstract.Profile.Growth`).
-/

public section

open MeasureTheory Set Filter

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup}
  {h : ParabolicSpace → ℝ} {N : ℕ} {V : Submodule ℝ (ι → ℝ)} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
  {γ CPi₁ CGam₁ CPi₂ CGam₂ p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}

/-- **The difference model realises the kernel** for `I⊕` on `V⊕`, under weighted bounds. -/
theorem isRealisingP_modelSum_growth (hh : ShellProfile h N) (h₁ : M₁.IsPolyCompatible P)
    (h₂ : M₂.IsPolyCompatible P) (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (G₁ : M₁.GrowthModel γ CPi₁ CGam₁ ρP ρG p qG) (G₂ : M₂.GrowthModel γ CPi₂ CGam₂ ρP ρG p qG)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (hreal₁ : M₁.IsRealisingP h γ P I V) (hreal₂ : M₂.IsRealisingP h γ P I V) :
    (modelSum (lam := lam) h₁ h₂).IsRealisingP h γ (polySectorSum P) (intSum P I)
      (sectorSum P V) where
  poly := isPolyCompatible_modelSum h₁ h₂
  realises x s hs hsV t ht z := by
    rcases s with j | j
    · have hj : 𝒯.deg j.1 < γ := hs
      have hVj : (Pi.single j.1 1 : ι → ℝ) ∈ V := (single_mem_sectorSum_iff P _).1 hsV
      have hg₁ := M₁.polyBounded_realGermP_growth hh G₁ hV hVb hdeg hVj hj x
      have hg₂ := M₂.polyBounded_realGermP_growth hh G₂ hV hVb hdeg hVj hj x
      have hge : realGermP (modelSum (lam := lam) h₁ h₂) h x (Sum.inl j) =
          fun y => lam⁻¹ * (realGermP M₁ h x j.1 y - realGermP M₂ h x j.1 y) :=
        funext fun y => realGermP_modelSum_inl_growth hh h₁ h₂ hV hVb G₁ G₂ hdeg j hVj hj x y
      rw [regPi_modelSum_intSum_inl, realRegP_of_pos _ _ _ _ ht, hge,
        apply_const_mul_sub hg₁ hg₂ _ ht, hreal₁.realises x j.1 hj hVj t ht z,
        hreal₂.realises x j.1 hj hVj t ht z, realRegP_of_pos _ _ _ _ ht,
        realRegP_of_pos _ _ _ _ ht]
    · have hj : 𝒯.deg j < γ := hs
      have hVj : (Pi.single j 1 : ι → ℝ) ∈ V := (single_mem_sectorSum_iff P _).1 hsV
      rw [regPi_modelSum_intSum_inr, hreal₂.realises x j hj hVj t ht z, realRegP_of_pos _ _ _ _ ht,
        realRegP_of_pos _ _ _ _ ht, show realGermP (modelSum (lam := lam) h₁ h₂) h x (Sum.inr j) =
          realGermP M₂ h x j from funext (realGermP_modelSum_inr h₁ h₂ j x)]

end TwoModel

end RegularityStructures

end
