/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.SchauderPoly
public import RegularityStructures.Abstract.Integration.SchauderSeries
public import RegularityStructures.Abstract.Integration.PolyPairing.Main

/-!
# Theorem 5.12: the polynomial components of the increment

`Model.exists_abs_kGamma_sub_gamma_poly_le`: the polynomial components of
`𝒦_γ f(x) - Γ_{xy} 𝒦_γ f(y)` satisfy the `D^{γ+2}` bound.

Source: [Hai14, proof of Theorem 5.12].
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

theorem exists_abs_kGamma_sub_gamma_poly_le {γ : ℝ} (hγ : 0 < γ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -2 < 𝒯.deg j) (N : ℕ) {N' : ℕ} (P : PolynomialSector 𝒯 N')
    (hNN : N' ≤ N) (k : PolyIndex N') (hk : polyDeg N' k < γ + 2)
    (hnat1 : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) ≠ γ + 2 - multiDeg k.1)
    (hnat2 : ∀ i, i ∉ Set.range P.emb → 𝒯.deg i < γ → (multiDeg k.1 : ℝ) ≠ 𝒯.deg i + 2) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (M : Model 𝒯 parabolicSemigroup) {CPi CGam Cf : ℝ}
      (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (V : Submodule ℝ (ι → ℝ)),
      M.IsRealising N γ P I V → IsAbstractIntegration P V I 2 → 𝒯.IsSector V →
      (∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V) →
      M.PiBoundOn γ CPi univ → M.GammaBoundOn γ CGam univ → 0 ≤ CPi →
      (∀ j, 𝒯.deg j < γ → ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 → multiDeg k < N') →
      (∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) < γ + 2 → multiDeg l < N') →
      (∀ a ∈ V, ∀ k : PolyIndex N', I a (P.emb k) = 0) → M.IsPolyCompatible P →
      ∀ {f : ParabolicSpace → ι → ℝ}, f ∈ M.modelledDistributions γ →
      M.ModelledBoundOn γ Cf univ f → 0 ≤ Cf → (∀ x, f x ∈ V) → ∀ x y : ParabolicSpace,
      |(kGamma M N P I γ f y - M.gammaMap y x (kGamma M N P I γ f x)) (P.emb k)| ≤
        c * CPi * Cf * max CGam 1 * parabolicNorm (y - x) ^ (γ + 2 - multiDeg k.1) := by
  have hk' : (multiDeg k.1 : ℝ) < γ + 2 := hk
  obtain ⟨c, hc0, hmain⟩ := exists_abs_tsum_polyU_le hγ hdeg N k.1 hk' (Finset.univ.image P.emb) hnat1
    (fun i hi => hnat2 i fun h => hi (Finset.mem_image.2
      (by obtain ⟨l, hl⟩ := h; exact ⟨l, Finset.mem_univ _, hl⟩)))
  refine ⟨c, hc0, ?_⟩
  intro M CPi CGam Cf I V hreal hI hV hVb hPi hGam hCPi hN' hNγ hIpoly hM f hf hfb hCf hfV x y
  have hσ : 0 < γ + 2 - (multiDeg k.1 : ℝ) := by linarith
  have hkf : (1 : ℝ) ≤ multiFactorial k.1 := by exact_mod_cast multiFactorial_pos k.1
  by_cases hd : parabolicNorm (y - x) = 0
  · have hyx : y = x := sub_eq_zero.1 (eq_zero_of_parabolicNorm_eq_zero hd)
    subst hyx
    rw [M.gammaMap_self]
    simp only [LinearMap.id_apply, sub_self, Pi.zero_apply, abs_zero]
    rw [parabolicNorm_zero, Real.zero_rpow hσ.ne']
    simp
  · have hdpos : 0 < parabolicNorm (y - x) := lt_of_le_of_ne (parabolicNorm_nonneg _) (Ne.symm hd)
    obtain ⟨hsum, hbr⟩ := poly_bracket hreal hI hV hVb hγ hdeg hPi hGam hCPi hN' hNγ hIpoly hM hf
      hfb hCf hfV x y k hk
    have hS0 : ∀ i ∈ Finset.univ.image P.emb, ∀ (y : ParabolicSpace) (n : ℕ),
        derivShellPairing (fun t z => M.regPi y (Pi.single i 1) t z) (annKernel0 N) k.1 y n = 0 :=
      fun i hi y n => by
        obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hi
        exact Model.derivShellPairing_regPi_emb_eq_zero hreal.poly hNN y ⟨l, rfl⟩ k.1 n
    have h1 := hmain M hS0 hPi hGam hCPi hf hfb hCf x y hdpos hsum
    rw [← hbr, abs_mul, abs_of_pos (lt_of_lt_of_le one_pos hkf)] at h1
    have h0 : 0 ≤ c * CPi * Cf * max CGam 1 * parabolicNorm (y - x) ^ (γ + 2 - multiDeg k.1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc0 hCPi) hCf)
        (le_trans zero_le_one (le_max_right _ _))) (Real.rpow_nonneg hdpos.le _)
    have h2 : |(kGamma M N P I γ f y - M.gammaMap y x (kGamma M N P I γ f x)) (P.emb k)| ≤
        |(kGamma M N P I γ f y - M.gammaMap y x (kGamma M N P I γ f x)) (P.emb k)| *
          multiFactorial k.1 := le_mul_of_one_le_right (abs_nonneg _) hkf
    linarith

end Model

end RegularityStructures

end
