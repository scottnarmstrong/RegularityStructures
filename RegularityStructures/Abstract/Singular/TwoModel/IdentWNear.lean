/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.TwoModel.LatticeSumWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Singular.TwoModel.GrowthCommonW
public import RegularityStructures.Abstract.Singular.TwoModel.IdentG

/-!
# Identification of `𝒦⊕ f⊕` for a kernel pair, near-pair `Γ`-bounds

For a kernel pair `(h, r)`, layer settings of `(M₁, f₁)`, `(M₂, f₂)`, and the lift
`f⊕ = liftSum P λ f₁ f₂` on the time slab:

* `kGammaRemG_modelSum_parts_win_near`: the left part of `M⊕.kGammaRemG h r P⊕ I⊕ γ f⊕ x` is
  `λ • Q (I (f₁ x))` and its right part is
  `M₁.kGammaRemG h r P I γ f₁ x - M₂.kGammaRemG h r P I γ f₂ x`;
* `rightPart_sub_gammaSum_kGammaRemG_win_near`: the increment identity
  `rightPart (F⊕ y - Γ⊕_{yx} F⊕ x) = (F₁ y - Γ¹_{yx} F₁ x) - (F₂ y - Γ²_{yx} F₂ x)`.

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

namespace RegularityStructures

namespace TwoModel

open Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {P : PolynomialSector 𝒯 N'} {lam : ℝ} {M₁ M₂ : Model 𝒯 parabolicSemigroup}
  {V : Submodule ℝ (ι → ℝ)} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
  {f₁ f₂ : ParabolicSpace → ι → ℝ} {γ η α C₁ C₂ CPi₁ CPi₂ CGam₁ CGam₂ T : ℝ}
  {h r : ParabolicSpace → ℝ} {N : ℕ}

theorem kGammaRemG_modelSum_parts_win_near (K : KernelPair h r N) (hlam : lam ≠ 0)
    (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P) (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hI : IsAbstractIntegration P V I 2)
    (S₁ : LayerSettingWNear M₁ f₁ γ η α C₁ CPi₁ CGam₁ T)
    (S₂ : LayerSettingWNear M₂ f₂ γ η α C₂ CPi₂ CGam₂ T) 
    (hN : N' ≤ N)
    (hni : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ + 2 →
      ∀ i, i ∉ Set.range P.emb → α ≤ 𝒯.deg i → 𝒯.deg i < γ → (multiDeg k : ℝ) ≠ 𝒯.deg i + 2)
    (hf₁V : ∀ z, f₁ z ∈ V) {x : ParabolicSpace} (hx : x ∈ timeSlab T) :
    leftPart P ((modelSum (lam := lam) h₁ h₂).kGammaRemG h r (polySectorSum P) (intSum P I) γ
        (liftSum P lam f₁ f₂) x) = lam • restrictNP P (I (f₁ x)) ∧
      rightPart P ((modelSum (lam := lam) h₁ h₂).kGammaRemG h r (polySectorSum P) (intSum P I) γ
        (liftSum P lam f₁ f₂) x) =
        M₁.kGammaRemG h r P I γ f₁ x - M₂.kGammaRemG h r P I γ f₂ x := by
  obtain ⟨_, _, _, _, _, _, _, _, G₁, G₂⟩ := exists_common_growthModel S₁.hgrowth S₂.hgrowth
  have hN := nVecS_modelSum_parts_win_near (h := h) h₁ h₂ hlam K.shell K.causal S₁ S₂ hN hni hx
  have hR := remVecG_modelSum_parts_win_near h₁ h₂ hlam S₁ S₂ K.rem hx.2
  have hJ : leftPart P (jMapP (modelSum (lam := lam) h₁ h₂) h (polySectorSum P) x
        (liftSum P lam f₁ f₂ x)) = 0 ∧
      rightPart P (jMapP (modelSum (lam := lam) h₁ h₂) h (polySectorSum P) x
        (liftSum P lam f₁ f₂ x)) = jMapP M₁ h P x (f₁ x) - jMapP M₂ h P x (f₂ x) :=
    jMapP_modelSum_liftVec_growth (h := h) K.shell hlam h₁ h₂ hV hVb G₁ G₂
      (fun j _ hj => S₁.hdeg j hj) x (hf₁V x) (S₁.hfT x)
  have hQ : restrictNP P (I (extendNP P (restrictNP P (f₁ x)))) = restrictNP P (I (f₁ x)) := by
    rw [map_extendNP_restrictNP P hVb hI (hf₁V x)]
  unfold Model.kGammaRemG Model.kGammaS
  refine ⟨?_, ?_⟩
  · simp only [map_add]
    rw [hN.1, hR.1, hJ.1]
    change restrictNP P (I (extendNP P (lam • restrictNP P (f₁ x)))) + 0 + 0 + 0 = _
    rw [map_smul, map_smul, map_smul, hQ]
    simp
  · simp only [map_add]
    rw [hN.2, hR.2, hJ.2]
    have e : rightPart P (intSum P I (liftSum P lam f₁ f₂ x)) = I (f₁ x - f₂ x) :=
      rightPart_intSum P I _
    rw [e, map_sub]
    abel

theorem rightPart_sub_gammaSum_kGammaRemG_win_near (K : KernelPair h r N) (hlam : lam ≠ 0)
    (h₁ : M₁.IsPolyCompatible P) (h₂ : M₂.IsPolyCompatible P) (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hI : IsAbstractIntegration P V I 2)
    (S₁ : LayerSettingWNear M₁ f₁ γ η α C₁ CPi₁ CGam₁ T)
    (S₂ : LayerSettingWNear M₂ f₂ γ η α C₂ CPi₂ CGam₂ T) 
    (hN : N' ≤ N)
    (hni : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ + 2 →
      ∀ i, i ∉ Set.range P.emb → α ≤ 𝒯.deg i → 𝒯.deg i < γ → (multiDeg k : ℝ) ≠ 𝒯.deg i + 2)
    (hf₁V : ∀ z, f₁ z ∈ V) {x y : ParabolicSpace} (hx : x ∈ timeSlab T) (hy : y ∈ timeSlab T) :
    rightPart P ((modelSum (lam := lam) h₁ h₂).kGammaRemG h r (polySectorSum P) (intSum P I) γ
          (liftSum P lam f₁ f₂) y -
        (modelSum (lam := lam) h₁ h₂).gammaMap y x
          ((modelSum (lam := lam) h₁ h₂).kGammaRemG h r (polySectorSum P) (intSum P I) γ
            (liftSum P lam f₁ f₂) x)) =
      (M₁.kGammaRemG h r P I γ f₁ y - M₁.gammaMap y x (M₁.kGammaRemG h r P I γ f₁ x)) -
        (M₂.kGammaRemG h r P I γ f₂ y - M₂.gammaMap y x (M₂.kGammaRemG h r P I γ f₂ x)) := by
  have px := kGammaRemG_modelSum_parts_win_near K hlam h₁ h₂ hV hVb hI S₁ S₂ hN hni hf₁V hx
  have py := kGammaRemG_modelSum_parts_win_near K hlam h₁ h₂ hV hVb hI S₁ S₂ hN hni hf₁V hy
  set Fx := (modelSum (lam := lam) h₁ h₂).kGammaRemG h r (polySectorSum P) (intSum P I) γ
    (liftSum P lam f₁ f₂) x with hFx
  have hFx' : Fx = pairVec P (lam • restrictNP P (I (f₁ x)))
      (M₁.kGammaRemG h r P I γ f₁ x - M₂.kGammaRemG h r P I γ f₂ x) := by
    rw [← px.1, ← px.2, pairVec_leftPart_rightPart]
  rw [map_sub, gammaMap_modelSum, hFx', gammaSum_pairVec, py.2]
  have hD := gammaMap_eq_of_mem_subspace h₁ h₂ y x
    (p := M₁.kGammaRemG h r P I γ f₁ x - I (f₁ x)) (kGammaRemG_sub_mem_subspace M₁ h r f₁ x)
  have hsub := gammaMap_sub_extendNP_restrictNP h₁ h₂ y x (I (f₁ x))
  rw [map_sub, map_sub] at hD
  have hE : M₁.gammaMap y x (extendNP P (lam • restrictNP P (I (f₁ x)))) -
      M₂.gammaMap y x (extendNP P (lam • restrictNP P (I (f₁ x)))) =
      lam • (M₁.gammaMap y x (I (f₁ x)) - M₂.gammaMap y x (I (f₁ x))) := by
    rw [map_smul, map_smul, map_smul, ← smul_sub, hsub]
  have hE' : lam⁻¹ • (M₁.gammaMap y x (extendNP P (lam • restrictNP P (I (f₁ x)))) -
      M₂.gammaMap y x (extendNP P (lam • restrictNP P (I (f₁ x))))) =
      M₁.gammaMap y x (I (f₁ x)) - M₂.gammaMap y x (I (f₁ x)) := by
    rw [hE, smul_smul, inv_mul_cancel₀ hlam, one_smul]
  have : rightPart P (pairVec P (restrictNP P (M₁.gammaMap y x
        (extendNP P (lam • restrictNP P (I (f₁ x))))))
      (lam⁻¹ • (M₁.gammaMap y x (extendNP P (lam • restrictNP P (I (f₁ x)))) -
        M₂.gammaMap y x (extendNP P (lam • restrictNP P (I (f₁ x))))) +
        M₂.gammaMap y x (M₁.kGammaRemG h r P I γ f₁ x - M₂.kGammaRemG h r P I γ f₂ x))) =
      (M₁.gammaMap y x (I (f₁ x)) - M₂.gammaMap y x (I (f₁ x))) +
        M₂.gammaMap y x (M₁.kGammaRemG h r P I γ f₁ x - M₂.kGammaRemG h r P I γ f₂ x) := by
    rw [rightPart_pairVec, hE']
  rw [this, map_sub (M₂.gammaMap y x)]
  linear_combination (norm := module) hD

end TwoModel

end RegularityStructures

end
