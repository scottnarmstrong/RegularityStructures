/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.Remainder.LinearWNear
public import RegularityStructures.Abstract.Singular.Remainder.MasterWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Singular.Remainder.Linear
public import RegularityStructures.Abstract.Singular.Remainder.RemKernelG

/-!
# Admissibility of remainder kernels, near-pair `Γ`-bounds

A remainder kernel vanishing after time `T` is admissible for `⟨R f, ·⟩`, with
`|⟨R f, Φ(x − ·)⟩| ≤ C K₀ C_f B`; in particular every `D^k R(z − ·)` with `z₀ ≤ T ≤ 1` is
admissible, for models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open scoped ContDiff

open Filter Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A remainder kernel (vanishing after time `T`) is admissible, with `|⟨R f, Φ(x − ·)⟩| ≤ C K₀ Cf B`. -/
theorem exists_remSumm_abs_remPairing_le_win_near (𝒯 : RegularityStructure ι) (γ η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ {Φ : ParabolicSpace → ℝ} {B : ℝ} {x : ParabolicSpace}, IsRemKernel Φ B → x.1 ≤ T →
      (∀ y : ParabolicSpace, T < y.1 → Φ (x - y) = 0) →
      M.RemSumm f (fun y => Φ (x - y)) ∧
      |M.remPairing f (fun y => Φ (x - y))| ≤ C * (max 1 CGam * CPi) * Cf * B := by
  obtain ⟨C₁, -, hC₁⟩ := exists_remPiece_le_win_near 𝒯 γ η α hdeg hγ hαγ hαη
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_abs_remPairing_le_win_near 𝒯 γ η α hdeg hγ hαγ hαη
  refine ⟨C₂, hC₂0, fun M f T Cf CPi CGam S Φ B x hΦ hx hΦT => ?_⟩
  obtain ⟨hs, hb⟩ := hC₂ M f T Cf CPi CGam S hΦ hx hΦT
  exact ⟨⟨hΦ.contDiff.comp (contDiff_const.sub contDiff_id),
    fun j => (hC₁ M f T Cf CPi CGam S hΦ hx hΦT j).1, hs⟩, hb⟩

/-- Every `D^k R(z − ·)`, `z₀ ≤ T ≤ 1`, is admissible. -/
theorem LayerSettingWNear.remSumm_lineIter_win {𝒯 : RegularityStructure ι} {M : Model 𝒯 parabolicSemigroup}
    {f : ParabolicSpace → ι → ℝ} {γ η α Cf CPi CGam T : ℝ}
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) {r : ParabolicSpace → ℝ} (hr : RemKernel r) (k : Fin 4 →₀ ℕ)
    {z : ParabolicSpace} (hz : z.1 ≤ T) :
    M.RemSumm f (fun y => lineIter (multiDirs k) r (z - y)) := by
  obtain ⟨C, -, hC⟩ := exists_remSumm_abs_remPairing_le_win_near 𝒯 γ η α S.hdeg S.hγ S.hαγ S.hαη
  obtain ⟨B, hB⟩ := hr.isRemKernel_lineIter k
  exact (hC M f T Cf CPi CGam S hB hz (fun y hy =>
    hr.lineIter_sub_eq_zero _ (by linarith))).1

end RegularityStructures

end
