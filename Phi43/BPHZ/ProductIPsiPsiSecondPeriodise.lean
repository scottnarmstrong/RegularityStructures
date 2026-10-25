/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestUnfold
public import Phi43.BPHZ.SemigroupTestPeriodise
import Mathlib.Tactic

/-!
# Periodisation of double integrals over `ℝ⁴ × ℝ⁴`

For a measurable `φ : ℝ⁴ → [0, ∞]` with periodisation `Φ(u) = ∑_k φ(lift_k u)` and a measurable
`Ψ : (ℝ × T³)² → [0, ∞]`,
`∫⁻_{ℝ⁴ × ℝ⁴} φ(y) φ(y') Ψ(proj y, proj y') = ∫⁻_{(ℝ × T³)²} Φ(u) Φ(v) Ψ(u, v)`
(`lintegral_prod_comp_proj_periodise`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

/-- The periodisation of `φ : ℝ⁴ → [0, ∞]`. -/
def periodiseENN (φ : ParabolicSpace → ℝ≥0∞) (u : SpaceTime) : ℝ≥0∞ :=
  ∑' k : Fin 3 → ℤ, φ (u.1, torusRep u.2 + fun i => (k i : ℝ))

end RegularityStructures

end

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

theorem measurable_periodiseENN {φ : ParabolicSpace → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable (periodiseENN φ) :=
  Measurable.tsum fun _ => hφ.comp
    (measurable_fst.prodMk ((measurable_torusRep.comp measurable_snd).add measurable_const))

/-- Single unfolding against a function of the projection. -/
theorem lintegral_mul_comp_proj_periodise {φ : ParabolicSpace → ℝ≥0∞} (hφ : Measurable φ)
    {ψ : SpaceTime → ℝ≥0∞} (hψ : Measurable ψ) :
    ∫⁻ y : ParabolicSpace, φ y * ψ (Phi43.spaceTimeProj y) =
      ∫⁻ u : SpaceTime, periodiseENN φ u * ψ u := by
  have hH : Measurable (fun y : ParabolicSpace => φ y * ψ (Phi43.spaceTimeProj y)) :=
    hφ.mul (hψ.comp Phi43.continuous_spaceTimeProj.measurable)
  rw [Phi43.lintegral_eq_lintegral_spaceTime_tsum hH]
  refine lintegral_congr fun q => ?_
  unfold periodiseENN
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun k => ?_
  simp only [spaceTimeProj_semigroup_lift]

/-- **Double unfolding.** -/
theorem lintegral_prod_comp_proj_periodise {φ : ParabolicSpace → ℝ≥0∞} (hφ : Measurable φ)
    {Ψ : SpaceTime → SpaceTime → ℝ≥0∞}
    (hΨ : Measurable (fun w : SpaceTime × SpaceTime => Ψ w.1 w.2)) :
    ∫⁻ q : ParabolicSpace × ParabolicSpace, φ q.1 * φ q.2 *
        Ψ (Phi43.spaceTimeProj q.1) (Phi43.spaceTimeProj q.2) =
      ∫⁻ w : SpaceTime × SpaceTime, periodiseENN φ w.1 * periodiseENN φ w.2 * Ψ w.1 w.2 := by
  have hΦ := measurable_periodiseENN hφ
  have hL : Measurable (fun q : ParabolicSpace × ParabolicSpace => φ q.1 * φ q.2 *
      Ψ (Phi43.spaceTimeProj q.1) (Phi43.spaceTimeProj q.2)) :=
    ((hφ.comp measurable_fst).mul (hφ.comp measurable_snd)).mul
      (hΨ.comp ((Phi43.continuous_spaceTimeProj.measurable.comp measurable_fst).prodMk
        (Phi43.continuous_spaceTimeProj.measurable.comp measurable_snd)))
  have hR : Measurable (fun w : SpaceTime × SpaceTime => periodiseENN φ w.1 * periodiseENN φ w.2 *
      Ψ w.1 w.2) :=
    ((hΦ.comp measurable_fst).mul (hΦ.comp measurable_snd)).mul hΨ
  rw [Measure.volume_eq_prod (α := ParabolicSpace) (β := ParabolicSpace),
    lintegral_prod _ hL.aemeasurable]
  rw [Measure.volume_eq_prod (α := SpaceTime) (β := SpaceTime), lintegral_prod _ hR.aemeasurable]
  have hinner : ∀ y : ParabolicSpace,
      ∫⁻ y' : ParabolicSpace, φ y * φ y' *
        Ψ (Phi43.spaceTimeProj y) (Phi43.spaceTimeProj y') =
      φ y * ∫⁻ v : SpaceTime, periodiseENN φ v * Ψ (Phi43.spaceTimeProj y) v := by
    intro y
    have hψ : Measurable (fun v : SpaceTime => Ψ (Phi43.spaceTimeProj y) v) :=
      hΨ.comp (measurable_const.prodMk measurable_id)
    have hm : Measurable (fun y' : ParabolicSpace =>
        φ y' * Ψ (Phi43.spaceTimeProj y) (Phi43.spaceTimeProj y')) :=
      hφ.mul (hψ.comp Phi43.continuous_spaceTimeProj.measurable)
    rw [← lintegral_mul_comp_proj_periodise hφ hψ, ← lintegral_const_mul _ hm]
    refine lintegral_congr fun y' => ?_
    simp only [mul_assoc]
  simp only [hinner]
  have hf : Measurable (fun w : SpaceTime × SpaceTime => periodiseENN φ w.2 * Ψ w.1 w.2) :=
    (hΦ.comp measurable_snd).mul hΨ
  have hΦ2 : Measurable (fun u : SpaceTime => ∫⁻ v : SpaceTime, periodiseENN φ v * Ψ u v) :=
    hf.lintegral_prod_right'
  have hm2 : Measurable (fun y : ParabolicSpace => φ y *
      ∫⁻ v : SpaceTime, periodiseENN φ v * Ψ (Phi43.spaceTimeProj y) v) :=
    hφ.mul (hΦ2.comp Phi43.continuous_spaceTimeProj.measurable)
  have := lintegral_mul_comp_proj_periodise hφ hΦ2
  rw [this]
  refine lintegral_congr fun u => ?_
  have hg : Measurable (fun v : SpaceTime => periodiseENN φ v * Ψ u v) :=
    hΦ.mul (hΨ.comp (measurable_const.prodMk measurable_id))
  rw [← lintegral_const_mul _ hg]
  refine lintegral_congr fun v => ?_
  simp only [mul_assoc]

end RegularityStructures

end
