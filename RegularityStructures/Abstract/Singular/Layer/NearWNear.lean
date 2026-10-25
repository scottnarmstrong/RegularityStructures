/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.Layer.SupBoundWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.LatticeApprox.Pieces
public import RegularityStructures.Abstract.Singular.Layer.Rescale
public import RegularityStructures.Abstract.Singular.ModelPairingGrowth.Increment
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Increment bound for a near pair of lattice points, near-pair `Γ`-bounds

For `z' = z_{n+1,k}`, `z = z_{n,l}`, and `g` scaled at `z'` with radius `8 · 2^{-(n+1)}` and
constant `A` and vanishing outside the cell `χ_{n,l}`,
`|⟨Π_{z'} (f(z') - Γ_{z'z} f(z)), g⟩| ≤ C K₀ Cf A (2^{-n})^{5 + α ∧ η}` with `K₀ = max 1 CGam * CPi`
(`exists_abs_pairing_near_le_win_near`): the two pairings `⟨Π_{z'} f(z'), g⟩` and `⟨Π_z f(z), g⟩`
are bounded separately by the sup bound.

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open MeasureTheory Filter Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_abs_pairing_near_le_win_near (𝒯 : RegularityStructure ι) (γ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {M : Model 𝒯 parabolicSemigroup} {f : ParabolicSpace → ι → ℝ}
      {η α Cf CPi CGam T : ℝ}, LayerSettingWNear M f γ η α Cf CPi CGam T → ∀ {n : ℕ}, 3 ≤ n →
      ∀ {k l : LatticeIndex} {g : ParabolicSpace → ℝ} {A : ℝ},
      IsScaledTest g (latticePoint (n + 1) k) (8 * ((2 : ℝ) ^ (n + 1))⁻¹) A →
      (∀ w, g w ≠ 0 → latticeCell n l w ≠ 0) →
      |parabolicSemigroup.pairing (M.regPi (latticePoint (n + 1) k)
        (f (latticePoint (n + 1) k) - M.gammaMap (latticePoint (n + 1) k) (latticePoint n l)
          (f (latticePoint n l)))) g| ≤
        C * (max 1 CGam * CPi) * Cf * A * (((2 : ℝ) ^ n)⁻¹) ^ (5 + min α η) := by
  obtain ⟨C₀, hC₀, hsup⟩ := exists_abs_pairing_regPi_lattice_le_win_near 𝒯 γ
  refine ⟨257 * C₀, by positivity, ?_⟩
  intro M f η α Cf CPi CGam T S n hn3 k l g A hg hsuppl
  set r : ℝ := ((2 : ℝ) ^ n)⁻¹ with hr_def
  have hr : 0 < r := by positivity
  have hr8 : 8 * r ≤ 1 := by
    have := eight_mul_two_pow_inv_le_one hn3
    rwa [← hr_def] at this
  have e : 8 * ((2 : ℝ) ^ (n + 1))⁻¹ = 4 * r := by rw [hr_def, pow_succ, mul_inv]; ring
  have hΓ : M.gammaMap (latticePoint (n + 1) k) (latticePoint n l) (f (latticePoint n l)) ∈
      lowerSubspace 𝒯.deg γ :=
    (M.isGradedUnipotent_gammaMap _ _).map_lowerSubspace (S.hfT _)
  obtain ⟨_, _, _, _, _, _, G⟩ := S.hgrowth
  have hsub := M.pairing_regPi_sub_of_scaled_growth G S.hdeg
    (S.hfT (latticePoint (n + 1) k)) hΓ hg
  have htr := M.pairing_regPi_eq_gammaMap (latticePoint n l) (latticePoint (n + 1) k)
    (f (latticePoint n l)) g
  rw [hsub, ← htr]
  refine (abs_sub _ _).trans ?_
  have hP1 := hsup S (q := n + 1) (by omega) hg
  have hR2 : 2 * (8 * ((2 : ℝ) ^ (n + 1))⁻¹) = 8 * r := by rw [e]; ring
  have hsupp : ∀ w', 2 * (8 * ((2 : ℝ) ^ (n + 1))⁻¹) <
      parabolicNorm (w' - latticePoint n l) → g w' = 0 := by
    intro w' hw'
    by_contra hne
    have := parabolicNorm_sub_latticePoint_le (hsuppl w' hne)
    rw [hR2] at hw'
    exact absurd this (not_le.2 hw')
  have hg' : IsScaledTest g (latticePoint n l) (8 * r) (256 * A) := by
    have := hg.double (z := latticePoint n l) (by rw [hR2]; exact hr8) hsupp
    rwa [hR2] at this
  have hP2 := hsup S (q := n) hn3 hg'
  have hm : 0 ≤ 5 + min α η := by linarith [S.hαη]
  have hρ : (((2 : ℝ) ^ (n + 1))⁻¹) ^ (5 + min α η) ≤ r ^ (5 + min α η) := by
    refine Real.rpow_le_rpow (by positivity) ?_ hm
    rw [hr_def]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n))
  have hA := hg.const_pos
  have hK0 : 0 ≤ max 1 CGam * CPi := S.hK0
  have hQ : 0 ≤ C₀ * (max 1 CGam * CPi) * Cf * A :=
    mul_nonneg (mul_nonneg (mul_nonneg hC₀ hK0) S.hCf) hA.le
  have h1 := mul_le_mul_of_nonneg_left hρ hQ
  have e2 : C₀ * (max 1 CGam * CPi) * Cf * (256 * A) * r ^ (5 + min α η) =
      256 * (C₀ * (max 1 CGam * CPi) * Cf * A * r ^ (5 + min α η)) := by ring
  have e3 : 257 * C₀ * (max 1 CGam * CPi) * Cf * A * r ^ (5 + min α η) =
      257 * (C₀ * (max 1 CGam * CPi) * Cf * A * r ^ (5 + min α η)) := by ring
  rw [e3]
  linarith [hP1, hP2, h1, e2]

end RegularityStructures

end
