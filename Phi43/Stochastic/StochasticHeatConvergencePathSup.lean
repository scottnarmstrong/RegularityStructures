/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.KolmogorovChentsovSupNorm
public import Mathlib.Order.CompletePartialOrder

/-!
# A uniform maximal-moment bound for already continuous processes

The Kolmogorov modification and an already continuous version are indistinguishable,
by agreement on a countable dense set. The maximal bound thus applies to the original
continuous process. Its finite deterministic constant precedes all probability-space and
process binders. It is used in the pathwise construction of the stationary linear field.
-/

public noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures.Phi43

theorem continuous_process_sup_norm_moment_bound
    {p : ℕ} {q : ℝ} {M B : ℝ≥0∞} {r : ℝ≥0}
    (hp : 1 ≤ p) (hq : 0 ≤ q) (hr : 0 < r)
    (hpr : (p : ℝ) * (r : ℝ) < q - 1) (hM : M ≠ ∞) (hB : B ≠ ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
      [CompleteSpace E] [T3Space E] {P : Measure Ω} (Z : UnitInterval → Ω → E),
      (∀ ω, Continuous (Z · ω)) →
      (∀ s t, AEMeasurable (fun ω => edist (Z s ω) (Z t ω)) P) →
      (∀ s t, ∫⁻ ω, edist (Z s ω) (Z t ω) ^ p ∂P ≤ M * edist s t ^ q) →
      AEMeasurable (fun ω => ‖Z 0 ω‖ₑ) P →
      (∫⁻ ω, ‖Z 0 ω‖ₑ ^ p ∂P ≤ B) →
      (∫⁻ ω, (⨆ t, ‖Z t ω‖ₑ) ^ p ∂P) ≤ C := by
  let L : ℝ≥0∞ := (1 + 2 * dyadicTailCoeff r) * (2 : ℝ≥0∞) ^ (r : ℝ)
  let S : ℝ≥0∞ := ∑' n : ℕ, (dyadicBase n) ^ (q - (p : ℝ) * (r : ℝ) - 1)
  let C : ℝ≥0∞ := (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
    (B + L ^ p * ((10 : ℝ≥0∞) * M * (4 : ℝ≥0∞) ^ q * S))
  have hL : L ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.add_ne_top.mpr ⟨by simp,
        ENNReal.mul_ne_top (by simp) (dyadicTailCoeff_lt_top hr).ne⟩
    · exact (ENNReal.rpow_lt_top_of_nonneg (show 0 ≤ (r : ℝ) from r.2) (by simp)).ne
  have hS : S ≠ ∞ := dyadicBase_rpow_tsum_ne_top (by linarith only [hpr])
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have htwo : (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr hpR) (by simp)).ne
  have hfour : (4 : ℝ≥0∞) ^ q ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg hq (by simp)).ne
  have hC : C ≠ ∞ := ENNReal.mul_ne_top htwo (ENNReal.add_ne_top.mpr ⟨hB,
    ENNReal.mul_ne_top (ENNReal.pow_ne_top hL)
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hM) hfour) hS)⟩)
  refine ⟨C, hC, ?_⟩
  intro Ω E _ _ _ _ P Z hcont hmeas hpair h0meas hinit
  obtain ⟨Y, hmatch, hholder, hsup⟩ := exists_kolmogorov_chentsov_sup_norm_moment
    hp hq hr hpr hM hmeas hpair h0meas hinit
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense UnitInterval
  let _ : Countable D := hDcount.to_subtype
  have hD : ∀ᵐ ω ∂P, ∀ t : D, Z t ω = Y t ω :=
    ae_all_iff.mpr fun t => hmatch t
  have hall : ∀ᵐ ω ∂P, (fun t => Z t ω) = (fun t => Y t ω) := by
    filter_upwards [hD, hholder] with ω hω hω'
    exact hDdense.denseRange_val.equalizer (hcont ω) (hω'.continuous hr) (funext fun t => hω t)
  calc
    _ = ∫⁻ ω, (⨆ t, ‖Y t ω‖ₑ) ^ p ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hall] with ω hω
      simp_rw [congrFun hω]
    _ ≤ C := hsup

end RegularityStructures.Phi43

end
