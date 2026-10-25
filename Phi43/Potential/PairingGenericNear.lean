/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.PairingGeneric
public import Phi43.Potential.NearPairing
public import Phi43.Potential.Convolution
public import RegularityStructures.Abstract.Singular.WindowAt.Basic

/-!
# Near-pair `Γ` version of `abs_potConv_le`
-/

public section

open MeasureTheory Filter Topology Set

namespace RegularityStructures.Potential

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup) {γ CPi CGam : ℝ}

/-- **Pairing bound for a smooth kernel of lag and range at most `1`.** -/
theorem abs_potConv_le_near (hPi : M.PiBoundOn γ CPi hairerTimeWindow) (hCPi : 0 ≤ CPi)
    (hGam : M.GammaNearOn γ CGam hairerTimeWindow) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    {o : ι} (ho : 𝒯.deg o < γ) {ξ : ParabolicSpace → ℝ} (hξ : Continuous ξ) {B : ℝ} {n : ℕ}
    (hB : ∀ u, |ξ u| ≤ B * (1 + parabolicNorm u) ^ n)
    (hreg : ∀ (x : ParabolicSpace) (t : ℝ), 0 < t → ∀ y,
      M.regPi x (Pi.single o 1) t y = parabolicSemigroup.apply t ξ y)
    (hgrowth : ∀ z : ParabolicSpace, 0 ≤ z.1 → z.1 ≤ 1 → M.HasQualitativeGrowthAt γ z)
    {h : ParabolicSpace → ℝ} (hh : IsUnitKernel h) {z : ParabolicSpace} (hz0 : 0 ≤ z.1)
    (hz1 : z.1 ≤ 1) :
    |potConv ξ h z| ≤ r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * potKernelConst h := by
  have hball : ∀ y, parabolicNorm (y - z) ≤ 1 → y ∈ hairerTimeWindow := fun y hy =>
    ball_subset_hairerTimeWindow hz0 hz1 hy
  have hg := isScaledTest_kernel hh z
  have hmain := (M.tendsto_abs_pairing_regPi_single_of_scaled_onWindowAt_near hPi hCPi hGam
    (hgrowth z hz0 hz1) hdeg ho hball hg).2
  have hcont : Continuous (fun y => h (z - y)) := hg.contDiff.continuous
  have hcs : HasCompactSupport (fun y => h (z - y)) :=
    HasCompactSupport.intro (isCompact_closedBall z 1) fun y hy => by
      have hy' : z - y ∉ Metric.closedBall (0 : ParabolicSpace) 1 := by
        intro hmem
        apply hy
        rw [mem_closedBall_zero_iff, norm_sub_rev] at hmem
        rwa [mem_closedBall_iff_norm]
      exact hh.supp _ (one_lt_parabolicNorm_of_not_mem_closedBall hy')
  have hpair := pairing_eq_integral_of_bound hξ hB hcont hcs
    (Λ := M.regPi z (Pi.single o 1)) (fun s hs => funext fun y => hreg z s hs y)
  show |∫ y, ξ y * h (z - y)| ≤ _
  rw [← hpair]
  simpa using hmain

end RegularityStructures.Potential

end
