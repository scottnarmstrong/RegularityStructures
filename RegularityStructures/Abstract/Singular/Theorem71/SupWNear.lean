/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.FarPolyWNear
public import RegularityStructures.Abstract.Singular.KGamma.SupMainWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.Remainder.SupWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.Singular.Remainder.GammaG
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG

/-!
# Sup bounds for `𝒦_γ f + R_γ f`, near-pair `Γ`-bounds

Sup bounds on the polynomial and non-polynomial components of `𝒦_γ f + R_γ f` for a kernel pair
`(h, r)` on the time slab, for models whose `Γ`-bounds hold only for near pairs:
`GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

/-- Sup bound for the polynomial components of `𝒦_γ f + R_γ f` (kernel pair `(h, r)`). -/
theorem exists_abs_kGammaRemG_apply_emb_le_win_near (𝒯 : RegularityStructure ι)
    (γ η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) {N : ℕ} {h r : ParabolicSpace → ℝ} (hp : KernelPair h r N)
    (P : PolynomialSector 𝒯 N') (hN : N' ≤ N) (kk : PolyIndex N')
    (hk : polyDeg N' kk < γ + 2)
    (hni : ∀ i, i ∉ Set.range P.emb → α ≤ 𝒯.deg i → 𝒯.deg i < γ →
      (multiDeg kk.1 : ℝ) ≠ 𝒯.deg i + 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ),
      LayerSettingWNear M f γ η α Cf CPi CGam T →
      M.IsPolyCompatible P → ∀ (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (V : Submodule ℝ (ι → ℝ)),
        (∀ z, f z ∈ V) → (∀ a ∈ V, ∀ k : PolyIndex N', I a (P.emb k) = 0) →
      ∀ {x : ParabolicSpace}, x ∈ timeSlab T →
      |(M.kGammaRemG h r P I γ f x) (P.emb kk)| ≤
        C * (max 1 CGam * CPi) * Cf *
          singularWeight timeZeroDist x ^ (min α η + 2 - polyDeg N' kk) := by
  have hk' : (multiDeg kk.1 : ℝ) < γ + 2 := hk
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_abs_kGammaS_apply_emb_le_win_near 𝒯 γ η α hdeg hγ hαγ hαη
    hp.shell hp.causal kk.1 hk' P hN hni
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_abs_remPairing_le_weight_win_near 𝒯 γ η α hdeg hγ hαγ hαη
    hp.rem kk.1
  refine ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0,
    fun M f T Cf CPi CGam S hM I V hfV hIp x hx => ?_⟩
  have h1 := hC₁ M f T Cf CPi CGam S hM I V hfV hIp hx kk rfl
  have h2 := hC₂ M f T Cf CPi CGam S x hx
  have hf1 : (1 : ℝ) ≤ multiFactorial kk.1 := by exact_mod_cast multiFactorial_pos kk.1
  have h3 : |M.remVecG r P γ f x (P.emb kk)| ≤
      C₂ * (max 1 CGam * CPi) * Cf *
        singularWeight timeZeroDist x ^ (min α η + 2 - (multiDeg kk.1 : ℝ)) := by
    rw [remVecG_apply_emb]
    simp only [hk, ↓reduceIte]
    rw [abs_div, abs_of_pos (lt_of_lt_of_le one_pos hf1)]
    exact (div_le_self (abs_nonneg _) hf1).trans h2
  unfold kGammaRemG
  rw [Pi.add_apply]
  refine (abs_add_le _ _).trans ?_
  have e : (C₁ + C₂) * (max 1 CGam * CPi) * Cf *
      singularWeight timeZeroDist x ^ (min α η + 2 - polyDeg N' kk) =
      C₁ * (max 1 CGam * CPi) * Cf * singularWeight timeZeroDist x ^
        (min α η + 2 - (multiDeg kk.1 : ℝ)) +
      C₂ * (max 1 CGam * CPi) * Cf * singularWeight timeZeroDist x ^
        (min α η + 2 - (multiDeg kk.1 : ℝ)) := by
    have hpd : polyDeg N' kk = (multiDeg kk.1 : ℝ) := rfl
    rw [hpd]; ring
  rw [e]
  exact add_le_add h1 h3

/-- Sup bound for the non-polynomial components of `𝒦_γ f + R_γ f`. -/
theorem abs_kGammaRemG_apply_le_of_notMem_range_win_near {γ η α Cf CPi CGam T CI : ℝ}
    {M : Model 𝒯 parabolicSemigroup} {f : ParabolicSpace → ι → ℝ}
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) (h r : ParabolicSpace → ℝ)
    (P : PolynomialSector 𝒯 N') (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (V : Submodule ℝ (ι → ℝ))
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hInt : IsAbstractIntegration P V I 2) (hfV : ∀ z, f z ∈ V)
    (hCI : ∀ i j, |I (Pi.single i 1) j| ≤ CI) {x : ParabolicSpace} (hx : x ∈ timeSlab T)
    {j : ι} (hj : j ∉ Set.range P.emb) :
    |M.kGammaRemG h r P I γ f x j| ≤
      Fintype.card ι * CI * Cf * singularWeight timeZeroDist x ^ (min α η + 2 - 𝒯.deg j) := by
  have hR : M.remVecG r P γ f x j = 0 := M.remVecG_mem_subspace r P γ f x j hj
  unfold kGammaRemG
  rw [Pi.add_apply, hR, add_zero]
  exact abs_kGammaS_apply_le_of_notMem_range_win_near S h P I V hVb hInt hfV hCI hx hj

end Model

end RegularityStructures

end
