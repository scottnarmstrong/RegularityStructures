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
public import RegularityStructures.Abstract.Singular.Remainder.LipschitzG
public import RegularityStructures.Abstract.Singular.Remainder.RemKernelG

/-!
# Lipschitz bound for remainder pairings, near-pair `Γ`-bounds

In the window layer setting `LayerSettingWNear`, for a remainder kernel `r`,
`|⟨R f, D^k r(x − ·)⟩ − ⟨R f, D^k r(x' − ·)⟩| ≤ C K₀ C_f ‖x − x'‖` for `x₀, x'₀ ≤ T` and
`‖x − x'‖ ≤ 1`, for models whose `Γ`-bounds hold only for near pairs:
`GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open scoped ContDiff

open Filter Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_abs_remPairing_sub_le_win_near (𝒯 : RegularityStructure ι) (γ η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) {r : ParabolicSpace → ℝ} (hr : RemKernel r) (k : Fin 4 →₀ ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ x x' : ParabolicSpace, x.1 ≤ T → x'.1 ≤ T → ‖x - x'‖ ≤ 1 →
      |M.remPairing f (fun y => lineIter (multiDirs k) r (x - y)) -
        M.remPairing f (fun y => lineIter (multiDirs k) r (x' - y))| ≤
        C * (max 1 CGam * CPi) * Cf * ‖x - x'‖ := by
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_remSumm_abs_remPairing_le_win_near 𝒯 γ η α hdeg hγ hαγ hαη
  obtain ⟨c, hc0, hc⟩ := hr.exists_isRemKernel_sub_shift k
  refine ⟨C₂ * c, by positivity, fun M f T Cf CPi CGam S x x' hx hx' hd => ?_⟩
  have hΦ := hc (x - x') hd
  have hlin := remPairing_sum_smul_win_near S (Finset.univ : Finset Bool) (fun b => bif b then 1 else -1)
    (fun b => bif b then (fun y => lineIter (multiDirs k) r (x - y))
      else fun y => lineIter (multiDirs k) r (x' - y))
    (fun b _ => by cases b
                   · exact S.remSumm_lineIter_win hr k hx'
                   · exact S.remSumm_lineIter_win hr k hx)
  have hfun : (fun y => ∑ b : Bool, (bif b then (1 : ℝ) else -1) *
      (bif b then (fun y => lineIter (multiDirs k) r (x - y))
        else fun y => lineIter (multiDirs k) r (x' - y)) y) =
      fun y => (fun u => lineIter (multiDirs k) r (u + (x - x')) -
        lineIter (multiDirs k) r u) (x' - y) := by
    funext y
    simp only [Fintype.sum_bool, Bool.cond_true, Bool.cond_false]
    rw [show x' - y + (x - x') = x - y by abel]
    ring
  rw [hfun] at hlin
  obtain ⟨hs, hb⟩ := hC₂ M f T Cf CPi CGam S hΦ hx' (fun y hy => by
    rw [show x' - y + (x - x') = x - y by abel,
      hr.lineIter_sub_eq_zero _ (by linarith),
      hr.lineIter_sub_eq_zero _ (by linarith), sub_zero])
  have h2 := hlin.2
  simp only [Fintype.sum_bool, Bool.cond_true, Bool.cond_false] at h2
  have : M.remPairing f (fun y => lineIter (multiDirs k) r (x - y)) -
      M.remPairing f (fun y => lineIter (multiDirs k) r (x' - y)) =
      M.remPairing f (fun y => (fun u => lineIter (multiDirs k) r (u + (x - x')) -
        lineIter (multiDirs k) r u) (x' - y)) := by
    rw [h2]; ring
  rw [this]
  refine hb.trans (le_of_eq ?_)
  ring

end RegularityStructures

end
