/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Ext514W.IdentityNear
public import RegularityStructures.Abstract.Ext514W.SettingNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Ext514.Bounds
public import RegularityStructures.Analysis.Heat.Schauder.Derivative
public import RegularityStructures.Analysis.Heat.Schauder.TaylorRegime

/-!
# Term bounds for the series of `Γ_{yx} I e_i`, near-pair `Γ`-bounds

Under `ExtSettingWNear`, for `x, y` in the window with `d(y, x) ≤ gammaNearRadius`: bounds on a
single term `τ_j ⟨Π_y e_j, D^k K_n(y − ·)⟩`, on `extR` and on the small-scale terms `extU`, for
models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {h : ParabolicSpace → ℝ} {N : ℕ} {V : Submodule ℝ (ι → ℝ)}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {γ CPi CGam : ℝ} {P : PolynomialSector 𝒯 N'}
  {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}

/-- The bound for a single term `τ_j ⟨Π_y e_j, D^k K_n(y − ·)⟩`. -/
theorem ExtSettingWNear.abs_extTerm_le (S : ExtSettingWNear M h N γ P I V CPi CGam) {i : ι}
    (hi : 𝒯.deg i < γ) (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) {x y : ParabolicSpace}
    (hx : x ∈ hairerTimeWindow) (hy : y ∈ hairerTimeWindow)
    (hxy : parabolicNorm (y - x) ≤ gammaNearRadius) (k : Fin 4 →₀ ℕ) (n : ℕ) {j : ι}
    {Cs : ℝ}
    (hP : |derivShellPairing (fun t z => M.regPi y (Pi.single j 1) t z) h k y n| ≤
      Cs * (max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg j)) :
    |M.gammaMap y x (Pi.single i 1) j *
        derivShellPairing (fun t z => M.regPi y (Pi.single j 1) t z) h k y n| ≤
      max CGam 1 * parabolicNorm (y - x) ^ (𝒯.deg i - 𝒯.deg j) *
        (Cs * (max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg j)) := by
  have hCw : 0 ≤ Cs * (max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg j) :=
    (abs_nonneg _).trans hP
  have hd0 : 0 ≤ parabolicNorm (y - x) := parabolicNorm_nonneg _
  by_cases hτ : M.gammaMap y x (Pi.single i 1) j = 0
  · rw [hτ, zero_mul, abs_zero]
    have : 0 ≤ max CGam 1 := le_trans zero_le_one (le_max_right _ _)
    positivity
  · rw [abs_mul]
    have h1 := S.abs_gammaMap_single_le hi hVi hx hy hxy hτ
    exact mul_le_mul h1 hP (abs_nonneg _)
      (mul_nonneg (le_trans zero_le_one (le_max_right _ _)) (Real.rpow_nonneg hd0 _))

theorem ExtSettingWNear.abs_extR_le (S : ExtSettingWNear M h N γ P I V CPi CGam) {i : ι}
    (hi : 𝒯.deg i < γ) (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) {x y : ParabolicSpace}
    (hx : x ∈ hairerTimeWindow) (hy : y ∈ hairerTimeWindow)
    (hxy : parabolicNorm (y - x) ≤ gammaNearRadius) (k : Fin 4 →₀ ℕ) (n : ℕ)
    (Sx : Finset ι)
    (hS0 : ∀ j ∈ Sx, ∀ (y : ParabolicSpace) (n : ℕ),
      derivShellPairing (fun t z => M.regPi y (Pi.single j 1) t z) h k y n = 0)
    {Cs : ℝ}
    (hPy : ∀ j, 𝒯.deg j < γ →
      |derivShellPairing (fun t z => M.regPi y (Pi.single j 1) t z) h k y n| ≤
        Cs * (max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg j)) :
    |extR M h x y i k n| ≤ ∑ j ∈ extF₂ 𝒯 V k i Sx,
      max CGam 1 * parabolicNorm (y - x) ^ (𝒯.deg i - 𝒯.deg j) *
        (Cs * (max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg j)) := by
  classical
  unfold extR
  have hsub : extF₂ 𝒯 V k i Sx ⊆
      Finset.univ.filter (fun j => ¬ (multiDeg k : ℝ) < 𝒯.deg j + 2) := fun j hj => by
    simp only [extF₂, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢; exact hj.1
  have hzero : ∀ j ∈ Finset.univ.filter (fun j => ¬ (multiDeg k : ℝ) < 𝒯.deg j + 2),
      j ∉ extF₂ 𝒯 V k i Sx →
      M.gammaMap y x (Pi.single i 1) j *
        derivShellPairing (fun t z => M.regPi y (Pi.single j 1) t z) h k y n = 0 := by
    intro j hj hnj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    by_cases hτ : M.gammaMap y x (Pi.single i 1) j = 0
    · rw [hτ, zero_mul]
    · obtain ⟨hVj, -, hji⟩ := S.gammaMap_single_support hi hVi x y hτ
      have hjS : j ∈ Sx := by
        by_contra hjS
        exact hnj (by simp only [extF₂, Finset.mem_filter, Finset.mem_univ, true_and]
                      exact ⟨hj, hVj, hji, hjS⟩)
      rw [hS0 j hjS y n, mul_zero]
  rw [← Finset.sum_subset hsub hzero]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  have hj' := Finset.mem_filter.1 hj
  exact S.abs_extTerm_le hi hVi hx hy hxy k n
    (hPy j (lt_of_le_of_lt hj'.2.2.2.1 hi))

theorem ExtSettingWNear.abs_extU_le_small (S : ExtSettingWNear M h N γ P I V CPi CGam) {i : ι}
    (hi : 𝒯.deg i < γ) (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) {x y : ParabolicSpace}
    (hx : x ∈ hairerTimeWindow) (hy : y ∈ hairerTimeWindow)
    (hxy : parabolicNorm (y - x) ≤ gammaNearRadius) (k : Fin 4 →₀ ℕ) (n : ℕ)
    {Cs : ℝ}
    (hPy : ∀ j, 𝒯.deg j < γ →
      |derivShellPairing (fun t z => M.regPi y (Pi.single j 1) t z) h k y n| ≤
        Cs * (max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg j))
    (hPx : ∀ l ∈ taylorIdx (𝒯.deg i + 2 - multiDeg k),
      |derivShellPairing (fun t z => M.regPi x (Pi.single i 1) t z) h (k + l) x n| ≤
        Cs * (max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg (k + l) : ℝ) - 2 - 𝒯.deg i)) :
    |extU M h x y i k n| ≤
      (∑ j ∈ extF₁ 𝒯 V k i,
        max CGam 1 * parabolicNorm (y - x) ^ (𝒯.deg i - 𝒯.deg j) *
          (Cs * (max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg k : ℝ) - 2 - 𝒯.deg j))) +
      ∑ l ∈ taylorIdx (𝒯.deg i + 2 - multiDeg k), parabolicNorm (y - x) ^ multiDeg l *
        (Cs * (max 1 CGam * CPi) * ((2 : ℝ) ^ n) ^ ((multiDeg (k + l) : ℝ) - 2 - 𝒯.deg i)) := by
  classical
  have hd0 : 0 ≤ parabolicNorm (y - x) := parabolicNorm_nonneg _
  unfold extU
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · have hsub : extF₁ 𝒯 V k i ⊆
        Finset.univ.filter (fun j => (multiDeg k : ℝ) < 𝒯.deg j + 2) := fun j hj => by
      simp only [extF₁, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢; exact hj.1
    have hzero : ∀ j ∈ Finset.univ.filter (fun j => (multiDeg k : ℝ) < 𝒯.deg j + 2),
        j ∉ extF₁ 𝒯 V k i →
        M.gammaMap y x (Pi.single i 1) j *
          derivShellPairing (fun t z => M.regPi y (Pi.single j 1) t z) h k y n = 0 := by
      intro j hj hnj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      by_cases hτ : M.gammaMap y x (Pi.single i 1) j = 0
      · rw [hτ, zero_mul]
      · obtain ⟨hVj, -, hji⟩ := S.gammaMap_single_support hi hVi x y hτ
        exact absurd (by simp only [extF₁, Finset.mem_filter, Finset.mem_univ, true_and]
                         exact ⟨hj, hVj, hji⟩) hnj
    rw [← Finset.sum_subset hsub hzero]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    have hj' := Finset.mem_filter.1 hj
    exact S.abs_extTerm_le hi hVi hx hy hxy k n (hPy j (lt_of_le_of_lt hj'.2.2.2 hi))
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l hl => ?_)
    rw [abs_mul]
    have hz : ∀ j, |parabolicCoords (y - x) j| ≤ parabolicNorm (y - x) ^ parabolicWeight j :=
      fun j => abs_parabolicCoords_le j
    exact mul_le_mul (abs_coeffT_le hz l) (hPx l hl) (abs_nonneg _) (pow_nonneg hd0 _)

end Model

end RegularityStructures

end
