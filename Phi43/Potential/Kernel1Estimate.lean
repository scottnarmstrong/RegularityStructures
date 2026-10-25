/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.Kernel1Bound
public import Phi43.Potential.Convolution
public import Phi43.Potential.TailTheta
public import RegularityStructures.Abstract.Singular.WindowAt.Basic

/-!
# `|(ξ ⋆ potK1 N)(z)| ≤ r4ModelConst · max(1, C_Γ) C_Π · potK1Const N (deg o)`

The union of the singular, unit and tail families is a family of scaled test functions summing to
`potK1 N (z - ·)`; apply `abs_integral_testFamily_le` and add the three tail sums.
-/

public section

open MeasureTheory Filter Topology Set

namespace RegularityStructures.Potential

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup) {γ CPi CGam : ℝ}

theorem abs_potConv_potK1_le (hPi : M.PiBoundOn γ CPi hairerTimeWindow) (hCPi : 0 ≤ CPi)
    (hGam : M.GammaNearOn γ CGam hairerTimeWindow) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    {o : ι} (ho : 𝒯.deg o < γ) {ξ : ParabolicSpace → ℝ} (hξ : Continuous ξ) {B' : ℝ} {n : ℕ}
    (hB' : ∀ u, |ξ u| ≤ B' * (1 + parabolicNorm u) ^ n)
    (hreg : ∀ (x : ParabolicSpace) (t : ℝ), 0 < t → ∀ y,
      M.regPi x (Pi.single o 1) t y = parabolicSemigroup.apply t ξ y)
    (hgrowth : ∀ z : ParabolicSpace, 0 ≤ z.1 → z.1 ≤ 1 → M.HasQualitativeGrowthAt γ z)
    {Bξ : ℝ} (hξb : ∀ y : ParabolicSpace, -1 ≤ y.1 → y.1 ≤ 2 → |ξ y| ≤ Bξ) (N : ℕ)
    {z : ParabolicSpace} (hz0 : 0 ≤ z.1) (hz1 : z.1 ≤ 1) :
    |potConv ξ (potK1 N) z| ≤
      r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * potK1Const N (𝒯.deg o) := by
  have hz : 0 ≤ z.1 ∧ z.1 ≤ 1 := ⟨hz0, hz1⟩
  have hd : -4 < 𝒯.deg o := hdeg o ho
  set K0 : ℝ := r4ModelConst 𝒯 γ * (max 1 CGam * CPi) with hK0
  have hK0nn : 0 ≤ K0 :=
    mul_nonneg (r4ModelConst_nonneg 𝒯 hdeg) (mul_nonneg (zero_le_one.trans (le_max_left _ _)) hCPi)
  set Fs := singFamily z hz
  set Fu := unitFamily N z hz
  set Ft := tailFamily N z hz
  have hKs : ∀ y, HasSum (fun j => Fs.g j y) (potSing 2 (z - y)) := fun y =>
    hasSum_potShellKernel 2 (z - y)
  have hKu : ∀ y, HasSum (fun j => Fu.g j y)
      (potUnit 0 (z - y) + potUnit 1 (z - y) + potUnitBump N (z - y)) := fun y => by
    have := hasSum_fintype (fun i => potUnitK N i (z - y))
    rwa [sum_potUnitK] at this
  have hKt : ∀ y, HasSum (fun j => Ft.g j y) (potTailPhi N (z - y)) := fun y => by
    have := (hasSum_bump3 (fun i => 8 * y.2 i)).mul_left (potTailPhi N (z - y))
    rw [mul_one] at this
    exact this
  have hKsu := fun y => Fs.hasSum_add Fu hKs hKu y
  have hK : ∀ y, HasSum (fun j => ((Fs.add Fu).add Ft).g j y) (potK1 N (z - y)) := fun y => by
    have := (Fs.add Fu).hasSum_add Ft (fun y => hKsu y) hKt y
    simpa [potK1] using this
  have h1 : Summable fun j => ((Fs.add Fu).add Ft).A j * ((Fs.add Fu).add Ft).R j ^ 5 :=
    Summable.sum _ (Summable.sum _ (summable_singFamily_A z hz) (summable_unitFamily_A N z hz))
      (summable_tailFamily_A N z hz)
  have hS : Summable (Fs.term K0 (𝒯.deg o)) := summable_singFamily_term hd z hz K0
  have hU : Summable (Fu.term K0 (𝒯.deg o)) := summable_unitFamily_term N z hz K0 _
  have hT : Summable (Ft.term K0 (𝒯.deg o)) := summable_tailFamily_term N z hz K0 _
  have h2 : Summable (((Fs.add Fu).add Ft).term K0 (𝒯.deg o)) :=
    (Fs.add Fu).summable_add Ft (Fs.summable_add Fu hS hU) hT
  have h := abs_integral_testFamily_le M hPi hCPi hGam hdeg ho hξ hB' hreg hgrowth hξb
    ((Fs.add Fu).add Ft) (fun y => potK1 N (z - y)) hK h1 h2
  refine h.trans ?_
  rw [(Fs.add Fu).tsum_add Ft (Fs.summable_add Fu hS hU) hT, Fs.tsum_add Fu hS hU,
    tsum_singFamily_term, tsum_unitFamily_term]
  have := tsum_tailFamily_term_le N z hz hK0nn (𝒯.deg o)
  unfold potK1Const
  nlinarith [this]

end RegularityStructures.Potential

end
