/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Ext514W.SettingNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Ext514.Large
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Profile.Growth.Commute
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Singular.KGamma.Emb
public import RegularityStructures.Abstract.Singular.KGamma.LargeG
public import RegularityStructures.Analysis.Heat.Schauder.Derivative
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# The polynomial components of `Γ_{yx} I e_i`, near-pair `Γ`-bounds

Under `ExtSettingWNear`: the polynomial components of `Γ_{yx} I e_i` [Hai14, (5.24), Lemma 5.21],
the large-scale form of the terms `extU n`, and the series representation [Hai14, (5.38)] of these
components as `∑ₙ extU n`, for models whose `Γ`-bounds hold only for near pairs:
`GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set Filter MeasureTheory

open scoped Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {h : ParabolicSpace → ℝ} {N : ℕ} {V : Submodule ℝ (ι → ℝ)}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {γ CPi CGam : ℝ} {P : PolynomialSector 𝒯 N'}
  {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}

/-- **The polynomial components of `Γ_{yx} I e_i`**, window models [Hai14, (5.24), Lemma 5.21]. -/
theorem ExtSettingWNear.gammaMap_integral_apply_emb (S : ExtSettingWNear M h N γ P I V CPi CGam) {i : ι}
    (hi : 𝒯.deg i < γ) (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) (x y : ParabolicSpace)
    (k : PolyIndex N') :
    M.gammaMap y x (I (Pi.single i 1)) (P.emb k) * multiFactorial k.1 =
      (∑ j, M.gammaMap y x (Pi.single i 1) j * (if polyDeg N' k < 𝒯.deg j + 2 then
        jCoeffP M h y j k.1 else 0)) -
      ∑ l ∈ taylorIdx (𝒯.deg i + 2 - multiDeg k.1), coeffT (parabolicCoords (y - x)) l *
        jCoeffP M h x i (k.1 + l) := by
  obtain ⟨_, _, _, _, _, _, G⟩ := S.growth
  have hkf : (multiFactorial k.1 : ℝ) ≠ 0 := by exact_mod_cast (multiFactorial_pos k.1).ne'
  set τ := M.gammaMap y x (Pi.single i 1) with hτ
  have hτV : τ ∈ V := S.sector.invariant _ (M.gamma y x).2 _ hVi
  have h516 := M.gammaMap_integral_add_jMap_inP_growth S.profile S.realising S.integration
    S.sector S.basis_mem S.deg_gtV G S.poly_largeV hi hVi y x
  have hcomp : M.gammaMap y x (I (Pi.single i 1)) =
      I τ + jMapP M h P y τ - M.gammaMap y x (jMapP M h P x (Pi.single i 1)) := by
    rw [map_add] at h516
    rw [← hτ] at h516
    rw [← h516]; abel
  have hJ := gammaMap_jVecP_apply_emb S.realising.poly h i x y k (S.poly_largeV i hVi hi)
  rw [hcomp, Pi.sub_apply, Pi.add_apply, S.integration_poly τ hτV k, jMapP_apply_emb, zero_add,
    jMapP_single, sub_mul, Finset.sum_mul, hJ]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · field_simp
  · simp

/-- **Large-scale form of the series**, window models:
`extU n = ⟨Π_x e_i, K^{k,σ}_{n;xy}⟩ − extR n`. -/
theorem ExtSettingWNear.extU_eq_large (S : ExtSettingWNear M h N γ P I V CPi CGam) {i : ι}
    (hi : 𝒯.deg i < γ) (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) (x y : ParabolicSpace)
    (k : Fin 4 →₀ ℕ) (n : ℕ) :
    extU M h x y i k n = parabolicSemigroup.pairing (fun t z => M.regPi x (Pi.single i 1) t z)
      (dTaylorKernel h k n (𝒯.deg i + 2 - multiDeg k) x y) - extR M h x y i k n := by
  classical
  obtain ⟨_, _, _, _, _, _, G⟩ := S.growth
  have hdeg := S.deg_gt4
  set τ := M.gammaMap y x (Pi.single i 1) with hτ
  obtain ⟨-, hτl⟩ := S.gammaMap_single_mem hi hVi x y
  obtain ⟨C, -, hC⟩ := exists_isScaledTest_lineIter_multiDirs_scaledShell S.profile k
  set φ : ParabolicSpace → ℝ := fun w => lineIter (multiDirs k) (scaledShell h n) (y - w)
    with hφ
  have hA : IsScaledTest φ y (((2 : ℝ) ^ n)⁻¹) _ := hC n y
  have hreg : M.regPi y τ = M.regPi x (Pi.single i 1) := by
    funext t w; exact M.regPi_gammaMap y x (Pi.single i 1) t w
  have hsum := M.pairing_regPi_eq_sum_single_of_scaled_growth G hdeg hτl hA
  rw [hreg] at hsum
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset ι)
    (fun j => (multiDeg k : ℝ) < 𝒯.deg j + 2)
    (fun j => τ j * parabolicSemigroup.pairing (M.regPi y (Pi.single j 1)) φ)
  rw [M.pairing_regPi_dTaylorKernel_growth S.profile G hdeg (single_mem_lowerSubspace hi 1) x y k
    n]
  unfold extU extR derivShellPairing
  change _ = parabolicSemigroup.pairing (M.regPi x (Pi.single i 1)) φ - _ - _
  rw [hsum, ← hsplit]
  ring

theorem ExtSettingWNear.summable_extU_terms (S : ExtSettingWNear M h N γ P I V CPi CGam) {i : ι}
    (hi : 𝒯.deg i < γ) (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) (x y : ParabolicSpace)
    (k : Fin 4 →₀ ℕ) (j : ι) (hk : (multiDeg k : ℝ) < 𝒯.deg j + 2) :
    Summable fun n => M.gammaMap y x (Pi.single i 1) j *
      derivShellPairing (fun t z => M.regPi y (Pi.single j 1) t z) h k y n := by
  obtain ⟨_, _, _, _, _, _, G⟩ := S.growth
  by_cases hτ : M.gammaMap y x (Pi.single i 1) j = 0
  · simp [hτ]
  · obtain ⟨hVj, hlt, -⟩ := S.gammaMap_single_support hi hVi x y hτ
    exact (summable_jCoeff_terms_growthP M S.profile G y j k S.sector S.basis_mem hVj hlt
      (fun j _ hl => S.deg_gt4 j hl) hk).mul_left _

/-- **The series for the polynomial components of `Γ_{yx} I e_i`**, window models
[Hai14, (5.38)]. -/
theorem ExtSettingWNear.poly_bracket_ext (S : ExtSettingWNear M h N γ P I V CPi CGam) {i : ι}
    (hi : 𝒯.deg i < γ) (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) (x y : ParabolicSpace)
    (k : PolyIndex N') (hk : polyDeg N' k < 𝒯.deg i + 2) :
    Summable (extU M h x y i k.1) ∧
      M.gammaMap y x (I (Pi.single i 1)) (P.emb k) * multiFactorial k.1 =
        ∑' n, extU M h x y i k.1 n := by
  classical
  obtain ⟨_, _, _, _, _, _, G⟩ := S.growth
  have hk' : (multiDeg k.1 : ℝ) < 𝒯.deg i + 2 := hk
  have hSa := S.summable_extU_terms hi hVi x y k.1
  have hSe : ∀ l ∈ taylorIdx (𝒯.deg i + 2 - multiDeg k.1), Summable fun n =>
      coeffT (parabolicCoords (y - x)) l *
        derivShellPairing (fun t z => M.regPi x (Pi.single i 1) t z) h (k.1 + l) x n := by
    intro l hl
    have hl' := (mem_taylorIdx_iff _).1 hl
    have hadd : multiDeg (k.1 + l) = multiDeg k.1 + multiDeg l := map_add _ _ _
    refine (summable_jCoeff_terms_growthP M S.profile G x i (k.1 + l) S.sector S.basis_mem hVi hi
      (fun j _ hl => S.deg_gt4 j hl) ?_).mul_left _
    rw [hadd]; push_cast; linarith
  have hSA : Summable fun n => ∑ j ∈ Finset.univ.filter
      (fun j => (multiDeg k.1 : ℝ) < 𝒯.deg j + 2), M.gammaMap y x (Pi.single i 1) j *
        derivShellPairing (fun t z => M.regPi y (Pi.single j 1) t z) h k.1 y n :=
    summable_sum fun j hj => hSa j (Finset.mem_filter.1 hj).2
  have hSE : Summable fun n => ∑ l ∈ taylorIdx (𝒯.deg i + 2 - multiDeg k.1),
      coeffT (parabolicCoords (y - x)) l *
        derivShellPairing (fun t z => M.regPi x (Pi.single i 1) t z) h (k.1 + l) x n :=
    summable_sum hSe
  refine ⟨hSA.sub hSE, ?_⟩
  rw [S.gammaMap_integral_apply_emb hi hVi x y k]
  have e1 : ∑' n, extU M h x y i k.1 n =
      (∑' n, ∑ j ∈ Finset.univ.filter (fun j => (multiDeg k.1 : ℝ) < 𝒯.deg j + 2),
        M.gammaMap y x (Pi.single i 1) j *
          derivShellPairing (fun t z => M.regPi y (Pi.single j 1) t z) h k.1 y n) -
      ∑' n, ∑ l ∈ taylorIdx (𝒯.deg i + 2 - multiDeg k.1),
        coeffT (parabolicCoords (y - x)) l *
          derivShellPairing (fun t z => M.regPi x (Pi.single i 1) t z) h (k.1 + l) x n := by
    unfold extU
    exact Summable.tsum_sub hSA hSE
  rw [e1, Summable.tsum_finsetSum fun j hj => hSa j (Finset.mem_filter.1 hj).2,
    Summable.tsum_finsetSum hSe]
  congr 1
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : polyDeg N' k < 𝒯.deg j + 2
    · have hc' : (multiDeg k.1 : ℝ) < 𝒯.deg j + 2 := hc
      simp only [hc, hc', ite_true]
      rw [tsum_mul_left]
      rfl
    · have hc' : ¬ (multiDeg k.1 : ℝ) < 𝒯.deg j + 2 := hc
      simp [hc, hc']
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [tsum_mul_left]
    rfl

end Model

end RegularityStructures

end
