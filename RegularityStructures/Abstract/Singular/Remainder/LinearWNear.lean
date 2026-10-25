/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Singular.Kernel.LinearW
public import RegularityStructures.Abstract.Singular.Remainder.Linear

/-!
# Linearity of `⟨R f, ·⟩`, near-pair `Γ`-bounds

In the window layer setting `LayerSettingWNear`: `f` vanishes for `t ≤ 0`; the lattice
reconstruction is linear on finite weighted sums of smooth compactly supported test functions and
unchanged by adding a test function that vanishes for `t ≥ 0`; `ψ ↦ ⟨R f, ψ⟩` is linear on
admissible test functions, and test functions that agree for `t ≥ 0` have the same pairing, for
models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Filter Topology Set

open scoped ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  {M : Model 𝒯 parabolicSemigroup} {f : ParabolicSpace → ι → ℝ} {γ η α Cf CPi CGam T : ℝ}

theorem LayerSettingWNear.hf0' (S : LayerSettingWNear M f γ η α Cf CPi CGam T) :
    ∀ z : ParabolicSpace, z.1 ≤ 0 → f z = 0 := fun z hz =>
  S.hf0 z (fun h => absurd h.1 (not_lt.2 hz))

theorem latticeRecon_sum_smul_win_near (S : LayerSettingWNear M f γ η α Cf CPi CGam T) {κ : Type*}
    (s : Finset κ) (c : κ → ℝ) (g : κ → ParabolicSpace → ℝ) (z : κ → ParabolicSpace)
    (hg : ∀ a ∈ s, ContDiff ℝ ∞ (g a))
    (hgs : ∀ a ∈ s, ∀ w, 1 < parabolicNorm (w - z a) → g a w = 0) (L : κ → ℝ)
    (hL : ∀ a ∈ s, Tendsto (M.latticeApprox f (g a)) atTop (𝓝 (L a))) :
    Tendsto (M.latticeApprox f (fun w => ∑ a ∈ s, c a * g a w)) atTop
        (𝓝 (∑ a ∈ s, c a * L a)) ∧
      M.latticeRecon f (fun w => ∑ a ∈ s, c a * g a w) = ∑ a ∈ s, c a * L a := by
  have hψ : ∀ a ∈ s, ContDiff ℝ ∞ (c a • g a) := fun a ha => contDiff_const.smul (hg a ha)
  have hs : ∀ a ∈ s, ∀ w, 1 < parabolicNorm (w - z a) → (c a • g a) w = 0 := fun a ha w hw => by
    simp [hgs a ha w hw]
  have ht : ∀ a ∈ s, Tendsto (M.latticeApprox f (c a • g a)) atTop (𝓝 (c a * L a)) :=
    fun a ha => M.tendsto_latticeApprox_smul_win S.hfT S.hgrowth S.hdeg (hg a ha)
      (hgs a ha) (c a) (hL a ha)
  have h := M.tendsto_latticeApprox_finset_sum_win S.hfT S.hgrowth S.hdeg s
    (fun a => c a • g a) z (fun _ => 1) hψ hs (fun a => c a * L a) ht
  have e : (fun w => ∑ a ∈ s, c a * g a w) = ∑ a ∈ s, c a • g a := by
    funext w; simp [Finset.sum_apply]
  rw [e]
  exact ⟨h, h.limUnder_eq⟩

theorem latticeRecon_add_of_causal_win_near (S : LayerSettingWNear M f γ η α Cf CPi CGam T)
    {g h : ParabolicSpace → ℝ} {z₁ z₂ : ParabolicSpace} (hg : ContDiff ℝ ∞ g)
    (hgs : ∀ w, 1 < parabolicNorm (w - z₁) → g w = 0) (hh : ContDiff ℝ ∞ h)
    (hhs : ∀ w, 1 < parabolicNorm (w - z₂) → h w = 0) {L : ℝ}
    (hL : Tendsto (M.latticeApprox f g) atTop (𝓝 L))
    (hh0 : ∀ w : ParabolicSpace, 0 ≤ w.1 → h w = 0) :
    Tendsto (M.latticeApprox f (g + h)) atTop (𝓝 L) ∧ M.latticeRecon f (g + h) = L := by
  have hz : M.latticeApprox f h = fun _ => 0 :=
    funext (M.latticeApprox_eq_zero_of_causal hh0 S.hf0')
  have ht : Tendsto (M.latticeApprox f h) atTop (𝓝 0) := by rw [hz]; exact tendsto_const_nhds
  have h2 := M.tendsto_latticeApprox_add_win S.hfT S.hgrowth S.hdeg hg hh hgs hhs hL ht
  rw [add_zero] at h2
  exact ⟨h2, h2.limUnder_eq⟩

end RegularityStructures

end

public section

open Filter Topology

open scoped ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  {M : Model 𝒯 parabolicSemigroup} {f : ParabolicSpace → ι → ℝ} {γ η α Cf CPi CGam T : ℝ}

/-- Linearity of `ψ ↦ ⟨R f, ψ⟩` on admissible test functions (finite weighted sums). -/
theorem remPairing_sum_smul_win_near (S : LayerSettingWNear M f γ η α Cf CPi CGam T) {κ : Type*}
    (s : Finset κ) (c : κ → ℝ) (ψ : κ → ParabolicSpace → ℝ)
    (h : ∀ a ∈ s, M.RemSumm f (ψ a)) :
    M.RemSumm f (fun y => ∑ a ∈ s, c a * ψ a y) ∧
      M.remPairing f (fun y => ∑ a ∈ s, c a * ψ a y) = ∑ a ∈ s, c a * M.remPairing f (ψ a) := by
  have hpiece : ∀ j : LatticeIndex,
      (fun y => (∑ a ∈ s, c a * ψ a y) * latticeCell 3 j y) =
        fun y => ∑ a ∈ s, c a * (ψ a y * latticeCell 3 j y) := fun j => by
    funext y; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun a _ => by ring
  have hsm : ∀ a ∈ s, ∀ j : LatticeIndex, ContDiff ℝ ∞ (fun y => ψ a y * latticeCell 3 j y) :=
    fun a ha j => (h a ha).contDiff.mul (contDiff_latticeCell 3 j)
  have hsupp : ∀ a ∈ s, ∀ j : LatticeIndex, ∀ w, 1 < parabolicNorm (w - latticePoint 3 j) →
      ψ a w * latticeCell 3 j w = 0 := fun a _ j w hw => by
    rw [latticeCell_eq_zero_of_one_lt hw, mul_zero]
  have key : ∀ j : LatticeIndex,
      Tendsto (M.latticeApprox f (fun y => (∑ a ∈ s, c a * ψ a y) * latticeCell 3 j y))
        atTop (𝓝 (∑ a ∈ s, c a * M.latticeRecon f (fun y => ψ a y * latticeCell 3 j y))) ∧
      M.latticeRecon f (fun y => (∑ a ∈ s, c a * ψ a y) * latticeCell 3 j y) =
        ∑ a ∈ s, c a * M.latticeRecon f (fun y => ψ a y * latticeCell 3 j y) := fun j => by
    rw [hpiece j]
    exact latticeRecon_sum_smul_win_near S s c (fun a y => ψ a y * latticeCell 3 j y)
      (fun _ => latticePoint 3 j) (fun a ha => hsm a ha j) (fun a ha => hsupp a ha j)
      (fun a => M.latticeRecon f (fun y => ψ a y * latticeCell 3 j y))
      (fun a ha => (h a ha).tendsto j)
  have hsum : Summable (fun j : LatticeIndex => ∑ a ∈ s,
      c a * M.latticeRecon f (fun y => ψ a y * latticeCell 3 j y)) :=
    summable_sum fun a ha => ((h a ha).summable).mul_left (c a)
  refine ⟨⟨ContDiff.sum fun a ha => contDiff_const.mul (h a ha).contDiff,
    fun j => ?_, ?_⟩, ?_⟩
  · rw [(key j).2]; exact (key j).1
  · simp only [(key _).2]; exact hsum
  · unfold Model.remPairing
    simp only [(key _).2]
    rw [Summable.tsum_finsetSum fun a ha => ((h a ha).summable).mul_left (c a)]
    exact Finset.sum_congr rfl fun a ha => ((h a ha).summable).tsum_mul_left (c a)

/-- Test functions that agree for `t ≥ 0` have the same `⟨R f, ·⟩` (`f` vanishes for `t ≤ 0`). -/
theorem remSumm_remPairing_eq_of_eq_of_nonneg_win_near (S : LayerSettingWNear M f γ η α Cf CPi CGam T)
    {ψ Φ : ParabolicSpace → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hΦ : M.RemSumm f Φ)
    (he : ∀ y : ParabolicSpace, 0 ≤ y.1 → ψ y = Φ y) :
    M.RemSumm f ψ ∧ M.remPairing f ψ = M.remPairing f Φ := by
  have hj : ∀ j : LatticeIndex,
      Tendsto (M.latticeApprox f (fun y => ψ y * latticeCell 3 j y)) atTop
        (𝓝 (M.latticeRecon f (fun y => Φ y * latticeCell 3 j y))) ∧
      M.latticeRecon f (fun y => ψ y * latticeCell 3 j y) =
        M.latticeRecon f (fun y => Φ y * latticeCell 3 j y) := fun j => by
    have e : (fun y => ψ y * latticeCell 3 j y) = (fun y => Φ y * latticeCell 3 j y) +
        (fun y => (ψ y - Φ y) * latticeCell 3 j y) := by
      funext y; simp only [Pi.add_apply]; ring
    rw [e]
    exact latticeRecon_add_of_causal_win_near S (hΦ.contDiff.mul (contDiff_latticeCell 3 j))
      (fun w hw => by rw [latticeCell_eq_zero_of_one_lt hw, mul_zero])
      ((hψ.sub hΦ.contDiff).mul (contDiff_latticeCell 3 j))
      (fun w hw => by rw [latticeCell_eq_zero_of_one_lt hw, mul_zero]) (hΦ.tendsto j)
      (fun w hw => by simp [he w hw])
  have hfun : (fun j : LatticeIndex => M.latticeRecon f (fun y => ψ y * latticeCell 3 j y)) =
      fun j => M.latticeRecon f (fun y => Φ y * latticeCell 3 j y) := funext fun j => (hj j).2
  refine ⟨⟨hψ, fun j => by rw [(hj j).2]; exact (hj j).1, by rw [hfun]; exact hΦ.summable⟩, ?_⟩
  unfold Model.remPairing
  rw [hfun]

end RegularityStructures

end
