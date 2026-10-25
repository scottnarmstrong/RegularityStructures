/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.DerivHyp
public import RegularityStructures.Abstract.Singular.WindowAt.ScaledNear
public import RegularityStructures.Abstract.Integration.PolyPairing.Limit
public import RegularityStructures.Abstract.Singular.Local.Const
public import Phi43.Inhomogeneity.DuhamelBounds
public import Phi43.Potential.TestFunction
public import RegularityStructures.Abstract.Singular.WindowAt.Basic

/-!
# Near-pair `Γ` version of `Phi43.Potential.PairingBound` and `DerivHyp`

The `Γ`-hypothesis is `GammaNearOn` (near pairs of radius `gammaNearRadius`).
-/

public section

open MeasureTheory Filter Topology Set

namespace RegularityStructures.Potential

open RegularityStructures.Inhomogeneity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup) {γ CPi CGam : ℝ}

/-- **Pointwise derivative bound of `Q ∗ ξ` from the window model bounds.** -/
theorem abs_ddA_potConv_le_near (hPi : M.PiBoundOn γ CPi hairerTimeWindow) (hCPi : 0 ≤ CPi)
    (hGam : M.GammaNearOn γ CGam hairerTimeWindow) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    {o : ι} (ho : 𝒯.deg o < γ) {ξ : ParabolicSpace → ℝ} (hξ : Continuous ξ) {B : ℝ} {n : ℕ}
    (hB : ∀ u, |ξ u| ≤ B * (1 + parabolicNorm u) ^ n)
    (hreg : ∀ (x : ParabolicSpace) (t : ℝ), 0 < t → ∀ y,
      M.regPi x (Pi.single o 1) t y = parabolicSemigroup.apply t ξ y)
    (hgrowth : ∀ z : ParabolicSpace, 0 ≤ z.1 → z.1 ≤ 1 → M.HasQualitativeGrowthAt γ z)
    (N : ℕ) (l : List (Fin 4)) {z : ParabolicSpace} (hz0 : 0 ≤ z.1) (hz1 : z.1 ≤ 1) :
    |ddA l (potConv ξ (potQ N)) z| ≤
      r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * potTestConst N l := by
  have hball : ∀ y, parabolicNorm (y - z) ≤ 1 → y ∈ hairerTimeWindow := fun y hy =>
    ball_subset_hairerTimeWindow hz0 hz1 hy
  have hg := isScaledTest_ddA_potQ N l z
  have hmain := (M.tendsto_abs_pairing_regPi_single_of_scaled_onWindowAt_near hPi hCPi hGam
    (hgrowth z hz0 hz1) hdeg ho hball hg).2
  have hcont : Continuous (fun y => ddA l (potQ N) (z - y)) := hg.contDiff.continuous
  have hcs : HasCompactSupport (fun y => ddA l (potQ N) (z - y)) :=
    HasCompactSupport.intro (isCompact_closedBall z 1) fun y hy => by
      have hy' : z - y ∉ Metric.closedBall (0 : ParabolicSpace) 1 := by
        intro h
        apply hy
        rw [mem_closedBall_zero_iff, norm_sub_rev] at h
        rwa [mem_closedBall_iff_norm]
      exact ddA_potQ_eq_zero_of_one_lt N l (one_lt_parabolicNorm_of_not_mem_closedBall hy')
  have hpair := pairing_eq_integral_of_bound hξ hB hcont hcs
    (Λ := M.regPi z (Pi.single o 1)) (fun s hs => funext fun y => hreg z s hs y)
  rw [ddA_potConv hξ (contDiff_potQ N) (hasCompactSupport_ddA_potQ N) l z]
  show |∫ y, ξ y * ddA l (potQ N) (z - y)| ≤ _
  rw [← hpair]
  simpa using hmain

/-- `DerivHyp` form, near-pair `Γ`. -/
theorem derivHyp_potConv_near (hPi : M.PiBoundOn γ CPi hairerTimeWindow) (hCPi : 0 ≤ CPi)
    (hGam : M.GammaNearOn γ CGam hairerTimeWindow) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    {o : ι} (ho : 𝒯.deg o < γ) {ξ : ParabolicSpace → ℝ} (hξ : Continuous ξ) {B : ℝ} {n : ℕ}
    (hB : ∀ u, |ξ u| ≤ B * (1 + parabolicNorm u) ^ n)
    (hreg : ∀ (x : ParabolicSpace) (t : ℝ), 0 < t → ∀ y,
      M.regPi x (Pi.single o 1) t y = parabolicSemigroup.apply t ξ y)
    (hgrowth : ∀ z : ParabolicSpace, 0 ≤ z.1 → z.1 ≤ 1 → M.HasQualitativeGrowthAt γ z) (N : ℕ)
    (L : ℕ) : DerivHyp (potConv ξ (potQ N)) (potGc N 𝒯 γ L * (max 1 CGam * CPi)) L := by
  intro l hl s hs y
  have h := abs_ddA_potConv_le_near M hPi hCPi hGam hdeg ho hξ hB hreg hgrowth N l
    (z := (s, y)) hs.1 hs.2
  refine h.trans ?_
  have h1 : 0 ≤ max 1 CGam * CPi :=
    mul_nonneg (zero_le_one.trans (le_max_left _ _)) hCPi
  unfold potGc
  have h2 := r4ModelConst_nonneg 𝒯 hdeg
  have h3 := potTestConst_le_potWordConst N hl
  calc r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * potTestConst N l
      ≤ r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * potWordConst N L := by gcongr
    _ = _ := by ring

end RegularityStructures.Potential

end
