/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.Remainder.LinearWNear
public import RegularityStructures.Abstract.Singular.Remainder.PairingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Singular.Remainder.Linear
public import RegularityStructures.Abstract.Singular.Remainder.RemKernelG
public import RegularityStructures.Abstract.Singular.Remainder.Sup

/-!
# Weighted sup bound for remainder pairings, near-pair `Γ`-bounds

In the window layer setting `LayerSettingWNear`, for a remainder kernel `r` and `x` in the slab,
`|⟨R f, D^k r(x − ·)⟩| ≤ C K₀ C_f w_x^{α∧η+2−|k|}`, for models whose `Γ`-bounds hold only for near
pairs: `GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open scoped ContDiff

open Filter Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_abs_remPairing_le_weight_win_near (𝒯 : RegularityStructure ι) (γ η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) {r : ParabolicSpace → ℝ} (hr : RemKernel r) (k : Fin 4 →₀ ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ x ∈ timeSlab T,
      |M.remPairing f (fun y => lineIter (multiDirs k) r (x - y))| ≤
        C * (max 1 CGam * CPi) * Cf *
          singularWeight timeZeroDist x ^ (min α η + 2 - (multiDeg k : ℝ)) := by
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_remSumm_abs_remPairing_le_win_near 𝒯 γ η α hdeg hγ hαγ hαη
  set e : ℝ := min α η + 2 - (multiDeg k : ℝ) with he
  set m : ℕ := ⌈max 0 (e / 2)⌉₊ with hm
  have hem : e ≤ 2 * m := by
    have h1 : e / 2 ≤ m := (le_max_right 0 (e / 2)).trans (Nat.le_ceil _)
    linarith
  obtain ⟨n, c, hc0, hK⟩ := exists_isRemKernel_timeTaylorRem m
  obtain ⟨BG, hBG0, hBG⟩ := hr.exists_remDecay_lineIter k n 7
  refine ⟨C₂ * (c * BG), by positivity, fun M f T Cf CPi CGam S x hx => ?_⟩
  obtain ⟨hx0, hxT⟩ := hx
  set G : ParabolicSpace → ℝ := lineIter (multiDirs k) r with hG
  have hGs : ContDiff ℝ ∞ G := contDiff_lineIter hr.contDiff _
  have hΦ := hK hGs hBG0 hBG x.1 hx0.le (hxT.trans S.hT)
  -- the subtracted terms vanish
  have hsub : ∀ (l : ℕ) (w : ParabolicSpace), w.1 ≤ 0 → (dirDeriv timeDir)^[l] G w = 0 := by
    intro l w hw
    rw [← lineIter_replicate, hG, ← lineIter_append]
    exact hr.lineIter_eq_zero _ hw
  have hrem : ∀ y : ParabolicSpace,
      timeTaylorRem x.1 m G (x - y - x.1 • timeDir) = G (x - y) -
        ∑ l ∈ Finset.range m, (x.1 ^ l / (Nat.factorial l : ℝ)) *
          (dirDeriv timeDir)^[l] G (x - y - x.1 • timeDir) := fun y => by
    unfold timeTaylorRem
    rw [sub_add_cancel]
  have hvan : ∀ y : ParabolicSpace, T < y.1 → timeTaylorRem x.1 m G (x - y - x.1 • timeDir) = 0 := by
    intro y hy
    rw [hrem, hG, hr.lineIter_sub_eq_zero _ (by linarith), zero_sub, neg_eq_zero]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [hsub l _ (by simp [timeDir]; linarith), mul_zero]
  have he0 : ∀ y : ParabolicSpace, 0 ≤ y.1 →
      G (x - y) = timeTaylorRem x.1 m G (x - y - x.1 • timeDir) := by
    intro y hy
    rw [hrem]
    have : ∑ l ∈ Finset.range m, (x.1 ^ l / (Nat.factorial l : ℝ)) *
        (dirDeriv timeDir)^[l] G (x - y - x.1 • timeDir) = 0 :=
      Finset.sum_eq_zero fun l _ => by
        rw [hsub l _ (by simp [timeDir]; linarith), mul_zero]
    rw [this, sub_zero]
  obtain ⟨hs, hb⟩ := hC₂ M f T Cf CPi CGam S hΦ hxT (fun y hy => by
    simpa using hvan y hy)
  have hE := remSumm_remPairing_eq_of_eq_of_nonneg_win_near S
    (ψ := fun y => G (x - y))
    (Φ := fun y => (fun u => timeTaylorRem x.1 m G (u - x.1 • timeDir)) (x - y))
    (hGs.comp (contDiff_const.sub contDiff_id)) hs (fun y hy => he0 y hy)
  rw [hE.2]
  refine hb.trans ?_
  have hw := pow_le_singularWeight_rpow S.hT ⟨hx0, hxT⟩ e m hem
  have hK0 : 0 ≤ max 1 CGam * CPi := S.hK0
  have hpre : 0 ≤ C₂ * (max 1 CGam * CPi) * Cf * (c * BG) := by
    have := S.hCf; positivity
  calc C₂ * (max 1 CGam * CPi) * Cf * (c * BG * x.1 ^ m)
      = (C₂ * (max 1 CGam * CPi) * Cf * (c * BG)) * x.1 ^ m := by ring
    _ ≤ (C₂ * (max 1 CGam * CPi) * Cf * (c * BG)) * singularWeight timeZeroDist x ^ e :=
        mul_le_mul_of_nonneg_left hw hpre
    _ = _ := by ring

end RegularityStructures

end
