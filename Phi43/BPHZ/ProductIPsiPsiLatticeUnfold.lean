/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestPeriodise
import Mathlib.Tactic

/-!
# Unfolding an integrable function on `ℝ⁴` onto `ℝ × T³`

`latticeLift u n = (u₀, torusRep u' + n)` is the `n`-th lift of `u ∈ ℝ × T³` to `ℝ⁴`.  For an
integrable `H` on `ℝ⁴`, `u ↦ ∑_n H (latticeLift u n)` is integrable on `ℝ × T³` and has the same
integral (`integrable_and_integral_tsum_latticeLift`).
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The `n`-th lift of `u ∈ ℝ × T³` to `ℝ⁴`. -/
def latticeLift (u : SpaceTime) (n : Fin 3 → ℤ) : ParabolicSpace :=
  (u.1, torusRep u.2 + fun i => (n i : ℝ))

end RegularityStructures.Phi43

end

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures.Phi43

open RegularityStructures

theorem measurable_latticeLift_left (n : Fin 3 → ℤ) :
    Measurable fun u : SpaceTime => latticeLift u n :=
  measurable_fst.prodMk ((measurable_torusRep.comp measurable_snd).add measurable_const)

theorem spaceTimeProj_latticeLift (u : SpaceTime) (n : Fin 3 → ℤ) :
    spaceTimeProj (latticeLift u n) = u := by
  have h := spaceTimeProj_semigroup_lift u.1 u.2 n
  simpa [latticeLift] using h

/-- **Unfolding onto `ℝ × T³`.** -/
theorem integrable_and_integral_tsum_latticeLift {H : ParabolicSpace → ℝ} (hm : Measurable H)
    (hint : Integrable H) :
    Integrable (fun u : SpaceTime => ∑' n : Fin 3 → ℤ, H (latticeLift u n)) ∧
      ∫ y, H y = ∫ u : SpaceTime, ∑' n : Fin 3 → ℤ, H (latticeLift u n) := by
  have hHt : Measurable (fun q : SpaceTime => ∑' k : Fin 3 → ℤ, H (latticeLift q k)) :=
    Measurable.tsum fun k => hm.comp (measurable_latticeLift_left k)
  have hfin : ∫⁻ q : SpaceTime, ‖∑' k : Fin 3 → ℤ, H (latticeLift q k)‖ₑ < ⊤ := by
    calc ∫⁻ q : SpaceTime, ‖∑' k : Fin 3 → ℤ, H (latticeLift q k)‖ₑ
        ≤ ∫⁻ q : SpaceTime, ∑' k : Fin 3 → ℤ, ‖H (latticeLift q k)‖ₑ :=
          lintegral_mono fun q => enorm_tsum_le_tsum_enorm
      _ = ∫⁻ y : ParabolicSpace, ‖H y‖ₑ :=
          (lintegral_eq_lintegral_spaceTime_tsum hm.enorm).symm
      _ < ⊤ := hint.2
  have hIntT : Integrable (fun u : SpaceTime => ∑' k : Fin 3 → ℤ, H (latticeLift u k)) :=
    ⟨hHt.aestronglyMeasurable, hfin⟩
  refine ⟨hIntT, ?_⟩
  have hint' : Integrable H (volume.prod volume : Measure (ℝ × (Fin 3 → ℝ))) := by
    rwa [← Measure.volume_eq_prod]
  have hIntT' : Integrable (fun q : SpaceTime => ∑' k : Fin 3 → ℤ, H (latticeLift q k))
      (volume.prod volume : Measure (ℝ × Torus3)) := by
    rwa [← Measure.volume_eq_prod]
  rw [show (∫ y : ParabolicSpace, H y) = ∫ t' : ℝ, ∫ z : Fin 3 → ℝ, H (t', z) by
      rw [Measure.volume_eq_prod]; exact integral_prod _ hint',
    show (∫ u : SpaceTime, ∑' k : Fin 3 → ℤ, H (latticeLift u k)) =
      ∫ t' : ℝ, ∫ u : Torus3, ∑' k : Fin 3 → ℤ, H (latticeLift (t', u) k) by
      rw [Measure.volume_eq_prod]; exact integral_prod _ hIntT']
  refine integral_congr_ae ?_
  filter_upwards [hint'.prod_right_ae] with t' ht'
  exact integral_eq_integral_torus_tsum (H := fun z => H (t', z)) ht'

end RegularityStructures.Phi43

end
