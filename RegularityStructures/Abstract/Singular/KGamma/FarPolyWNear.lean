/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.Singular.KGamma.Defs
public import RegularityStructures.Abstract.Singular.KGamma.SupMain
public import RegularityStructures.Abstract.Singular.KGamma.SupPieces
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Sup bounds for the components of `𝒦_γ f` of degree below `γ + 2`, near-pair `Γ`-bounds

For `j ∉ range P.emb`, `|(𝒦_γ f(x))_j| ≤ |ι| C_I C_f ‖x‖_P^{α∧η + 2 − deg j}`
(`abs_kGammaS_apply_le_of_notMem_range_win_near`); this uses no model bound, only the singular bound
on `f`. Together with a uniform bound `C₀` on the polynomial components it gives the sup bound of
`𝒦_γ f(x)` in every component of degree `< γ + 2` (`abs_kGammaS_apply_le_of_lt_win_near`).

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

/-- **Sup bound for the non-polynomial components of `𝒦_γ f`**: for `j ∉ range P.emb`,
`|(𝒦_γ f(x))_j| ≤ |ι| C_I C_f ‖x‖_P^{α∧η + 2 − deg j}`. -/
theorem abs_kGammaS_apply_le_of_notMem_range_win_near {γ η α Cf CPi CGam T CI : ℝ}
    {M : Model 𝒯 parabolicSemigroup} {f : ParabolicSpace → ι → ℝ}
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) (h : ParabolicSpace → ℝ)
    (P : PolynomialSector 𝒯 N') (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (V : Submodule ℝ (ι → ℝ))
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hInt : IsAbstractIntegration P V I 2) (hfV : ∀ z, f z ∈ V)
    (hCI : ∀ i j, |I (Pi.single i 1) j| ≤ CI) {x : ParabolicSpace} (hx : x ∈ timeSlab T)
    {j : ι} (hj : j ∉ Set.range P.emb) :
    |M.kGammaS h P I γ f x j| ≤
      Fintype.card ι * CI * Cf * singularWeight timeZeroDist x ^ (min α η + 2 - 𝒯.deg j) := by
  rw [kGammaS_apply_of_notMem_range M h P I γ f x hj, linearMap_apply_eq_sum]
  have hw := KGammaSup.weight_pos hx
  have hw1 := singularWeight_le_one timeZeroDist x
  have hCf := S.hCf
  have hterm : ∀ i, |f x i * I (Pi.single i 1) j| ≤
      CI * Cf * singularWeight timeZeroDist x ^ (min α η + 2 - 𝒯.deg j) := by
    intro i
    have hCI0 : 0 ≤ CI := (abs_nonneg _).trans (hCI i j)
    have hW0 : 0 ≤ singularWeight timeZeroDist x ^ (min α η + 2 - 𝒯.deg j) :=
      Real.rpow_nonneg hw.le _
    by_cases hfi : f x i = 0
    · rw [hfi, zero_mul, abs_zero]; positivity
    · by_cases hIij : I (Pi.single i 1) j = 0
      · rw [hIij, mul_zero, abs_zero]; positivity
      · have hi : 𝒯.deg i < γ := by
          by_contra hge
          exact hfi ((mem_lowerSubspace).1 (S.hfT x) i (not_lt.1 hge))
        have hαi : α ≤ 𝒯.deg i := S.hα x i hfi
        have hIi : I (Pi.single i 1) ∈ homogeneousSubspace 𝒯.deg (𝒯.deg i + 2) :=
          hInt.map_homogeneous _ _ (hVb _ (hfV x) i hfi) (single_mem_homogeneousSubspace i 1)
        have hdj : 𝒯.deg j = 𝒯.deg i + 2 := by
          by_contra hne
          exact hIij (hIi j hne)
        have hf1 := S.hf.1 x hx (timeZeroDist_pos_of_mem_timeSlab hx) i hi
        have hs : min α η + 2 - 𝒯.deg j ≤ min (η - 𝒯.deg i) 0 := by
          rw [hdj]
          refine le_min ?_ ?_
          · linarith [min_le_right α η]
          · linarith [min_le_left α η]
        have hwp : singularWeight timeZeroDist x ^ min (η - 𝒯.deg i) 0 ≤
            singularWeight timeZeroDist x ^ (min α η + 2 - 𝒯.deg j) :=
          Real.rpow_le_rpow_of_exponent_ge hw hw1 hs
        rw [abs_mul, mul_comm]
        calc |I (Pi.single i 1) j| * |f x i| ≤ CI * (Cf * singularWeight timeZeroDist x ^
              min (η - 𝒯.deg i) 0) :=
              mul_le_mul (hCI i j) hf1 (abs_nonneg _) hCI0
          _ ≤ CI * (Cf * singularWeight timeZeroDist x ^ (min α η + 2 - 𝒯.deg j)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwp hCf) hCI0
          _ = _ := by ring
  calc |∑ i, f x i * I (Pi.single i 1) j|
      ≤ ∑ _i : ι, CI * Cf * singularWeight timeZeroDist x ^ (min α η + 2 - 𝒯.deg j) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hterm i)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- The sup bound of `𝒦_γ f(x)` in every component of degree `< γ + 2`, from the uniform
polynomial bound `C₀` and the non-polynomial bound. -/
theorem abs_kGammaS_apply_le_of_lt_win_near {γ η α Cf CPi CGam T CI C0 : ℝ}
    {M : Model 𝒯 parabolicSemigroup} {f : ParabolicSpace → ι → ℝ}
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) (h : ParabolicSpace → ℝ)
    (P : PolynomialSector 𝒯 N') (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (V : Submodule ℝ (ι → ℝ))
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hInt : IsAbstractIntegration P V I 2) (hfV : ∀ z, f z ∈ V)
    (hCI : ∀ i j, |I (Pi.single i 1) j| ≤ CI) (hC0 : 0 ≤ C0)
    {x : ParabolicSpace} (hx : x ∈ timeSlab T)
    (hpoly : ∀ kk : PolyIndex N', polyDeg N' kk < γ + 2 →
      |M.kGammaS h P I γ f x (P.emb kk)| ≤
        C0 * (max 1 CGam * CPi) * Cf * singularWeight timeZeroDist x ^
          (min α η + 2 - polyDeg N' kk))
    {l : ι} (hl : 𝒯.deg l < γ + 2) :
    |M.kGammaS h P I γ f x l| ≤
      (C0 * (max 1 CGam * CPi) + Fintype.card ι * CI) * Cf *
        singularWeight timeZeroDist x ^ (min α η + 2 - 𝒯.deg l) := by
  have hCI0 : 0 ≤ CI := (abs_nonneg _).trans (hCI l l)
  have hK : 0 ≤ max 1 CGam * CPi := S.hK0
  have hwp : 0 ≤ singularWeight timeZeroDist x ^ (min α η + 2 - 𝒯.deg l) :=
    Real.rpow_nonneg (KGammaSup.weight_pos hx).le _
  have hcard : (0 : ℝ) ≤ Fintype.card ι * CI := mul_nonneg (Nat.cast_nonneg _) hCI0
  by_cases hjr : l ∈ Set.range P.emb
  · obtain ⟨kk, rfl⟩ := hjr
    have hd : polyDeg N' kk = 𝒯.deg (P.emb kk) := (P.deg_emb kk).symm
    have hk : polyDeg N' kk < γ + 2 := by rw [hd]; exact hl
    refine (hpoly kk hk).trans ?_
    rw [hd]
    have : 0 ≤ Cf * singularWeight timeZeroDist x ^ (min α η + 2 - 𝒯.deg (P.emb kk)) :=
      mul_nonneg S.hCf hwp
    nlinarith [mul_nonneg hcard this]
  · have := abs_kGammaS_apply_le_of_notMem_range_win_near S h P I V hVb hInt hfV hCI hx hjr
    refine this.trans ?_
    have h2 : 0 ≤ Cf * singularWeight timeZeroDist x ^ (min α η + 2 - 𝒯.deg l) :=
      mul_nonneg S.hCf hwp
    nlinarith [mul_nonneg (mul_nonneg hC0 hK) h2]

end Model

end RegularityStructures

end
