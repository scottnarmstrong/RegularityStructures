/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.Remainder.LayerWrapWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.Singular.Kernel.Vanish
public import RegularityStructures.Abstract.Singular.Remainder.Master

/-!
# The reconstruction of the pieces of a remainder kernel, near-pair `Γ`-bounds

For a remainder kernel `Φ` with constant `B`, `x₀ ≤ T ≤ 1`, and `Φ(x − y) = 0` for `y₀ > T`, the
lattice approximations of every piece `Φ(x − ·) χ_{3,j}` converge, and
`|⟨R f, Φ(x − ·) χ_{3,j}⟩| ≤ C K₀ Cf B remCellWt x j` (`exists_remPiece_le_win_near`). Summing over
`j` gives summability and `|remPairing f Φ(x − ·)| ≤ C K₀ Cf B`
(`exists_abs_remPairing_le_win_near`).

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open scoped ContDiff

open Filter Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_remPiece_le_win_near (𝒯 : RegularityStructure ι) (γ η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ {Φ : ParabolicSpace → ℝ} {B : ℝ} {x : ParabolicSpace}, IsRemKernel Φ B → x.1 ≤ T →
      (∀ y : ParabolicSpace, T < y.1 → Φ (x - y) = 0) → ∀ j : LatticeIndex,
      Tendsto (M.latticeApprox f (fun y => Φ (x - y) * latticeCell 3 j y)) atTop
        (𝓝 (M.latticeRecon f (fun y => Φ (x - y) * latticeCell 3 j y))) ∧
      |M.latticeRecon f (fun y => Φ (x - y) * latticeCell 3 j y)| ≤
        C * (max 1 CGam * CPi) * Cf * B * remCellWt x j := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_abs_latticeRecon_le_of_unit_ball_win_near 𝒯 γ η α hdeg hγ hαγ hαη
  obtain ⟨Cc, hCc0, hCc⟩ := exists_cell_mul_scaled_bound
  refine ⟨C₁ * Cc * (2 + 6 * (1 : ℝ) ^ 2) ^ 3, by positivity,
    fun M f T Cf CPi CGam S Φ B x hΦ hx hΦT j => ?_⟩
  have hK0 : 0 ≤ max 1 CGam * CPi := S.hK0
  by_cases hj : j.1 ∈ Finset.Icc (-1 : ℤ) 63
  · have hj1 : (-1 : ℤ) ≤ j.1 := (Finset.mem_Icc.1 hj).1
    have hb := scaled_bound_remPiece hΦ S.hT hx hj1
    have hB' : 0 ≤ (2 + 6 * (1 : ℝ) ^ 2) ^ 3 * B * remWt (x.2 - (latticePoint 3 j).2) :=
      mul_nonneg (mul_nonneg (by positivity) hΦ.nonneg) (remWt_nonneg _)
    obtain ⟨hsm, hsupp, hder⟩ := hCc j
      (hΦ.contDiff.comp (contDiff_const.sub contDiff_id)) hB' hb
    have h := hC₁ M f T Cf CPi CGam S hsm (by positivity) hsupp hder
      (fun w hw => by simp [hΦT w hw])
    refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
    simp only [remCellWt, hj, ite_true]
    ring
  · have hv := remPiece_vanish_of_not_mem_window S.hT hΦT hj
    have hf0 : ∀ z : ParabolicSpace, z.1 ≤ 0 → f z = 0 := fun z hz =>
      S.hf0 z (fun h => absurd h.1 (not_lt.2 hz))
    have hz : M.latticeApprox f (fun y => Φ (x - y) * latticeCell 3 j y) = fun _ => 0 :=
      funext (M.latticeApprox_eq_zero_of_causal hv hf0)
    have hr := M.latticeRecon_eq_zero_of_causal hv hf0
    have hw : remCellWt x j = 0 := by simp [remCellWt, hj]
    refine ⟨?_, ?_⟩
    · rw [hr, hz]; exact tendsto_const_nhds
    · rw [hr, hw]; simp

theorem exists_abs_remPairing_le_win_near (𝒯 : RegularityStructure ι) (γ η α : ℝ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (hγ : 0 < γ) (hαγ : α ≤ γ)
    (hαη : -2 < min α η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) (f : ParabolicSpace → ι → ℝ)
      (T Cf CPi CGam : ℝ), LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ {Φ : ParabolicSpace → ℝ} {B : ℝ} {x : ParabolicSpace}, IsRemKernel Φ B → x.1 ≤ T →
      (∀ y : ParabolicSpace, T < y.1 → Φ (x - y) = 0) →
      Summable (fun j => M.latticeRecon f (fun y => Φ (x - y) * latticeCell 3 j y)) ∧
      |M.remPairing f (fun y => Φ (x - y))| ≤ C * (max 1 CGam * CPi) * Cf * B := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_remPiece_le_win_near 𝒯 γ η α hdeg hγ hαγ hαη
  obtain ⟨W, hW0, hW⟩ := tsum_remCellWt_le
  refine ⟨C₁ * W, by positivity, fun M f T Cf CPi CGam S Φ B x hΦ hx hΦT => ?_⟩
  have hK0 : 0 ≤ max 1 CGam * CPi := S.hK0
  have hpc := fun j => (hC₁ M f T Cf CPi CGam S hΦ hx hΦT j).2
  set c : ℝ := C₁ * (max 1 CGam * CPi) * Cf * B with hc
  have hc0 : 0 ≤ c := by
    have := S.hCf; have := hΦ.nonneg; positivity
  have hsm : Summable (fun j => M.latticeRecon f (fun y => Φ (x - y) * latticeCell 3 j y)) := by
    refine Summable.of_norm_bounded ((summable_remCellWt x).mul_left c) fun j => ?_
    rw [Real.norm_eq_abs]
    refine (hpc j).trans (le_of_eq ?_)
    rw [hc]
  refine ⟨hsm, ?_⟩
  calc |M.remPairing f (fun y => Φ (x - y))|
      = ‖∑' j, M.latticeRecon f (fun y => Φ (x - y) * latticeCell 3 j y)‖ := by
        rw [Real.norm_eq_abs]; rfl
    _ ≤ ∑' j, ‖M.latticeRecon f (fun y => Φ (x - y) * latticeCell 3 j y)‖ :=
        norm_tsum_le_tsum_norm hsm.norm
    _ ≤ ∑' j, c * remCellWt x j := by
        refine Summable.tsum_le_tsum (fun j => ?_) hsm.norm ((summable_remCellWt x).mul_left c)
        rw [Real.norm_eq_abs]
        refine (hpc j).trans (le_of_eq ?_)
        rw [hc]
    _ = c * ∑' j, remCellWt x j := tsum_mul_left
    _ ≤ c * W := mul_le_mul_of_nonneg_left (hW x) hc0
    _ = C₁ * W * (max 1 CGam * CPi) * Cf * B := by rw [hc]; ring

end RegularityStructures

end
