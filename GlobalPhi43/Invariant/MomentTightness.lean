module

public import GlobalPhi43.Invariant.LateMoments
public import GlobalPhi43.Compactness.Compact
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.Tight

/-! # Extended moment tails and compact-sublevel tightness -/

public noncomputable section

open MeasureTheory Set RegularityStructures
open scoped ENNReal

namespace GlobalPhi43.Invariant

variable {E : Type*} [MeasurableSpace E]

/-- Extended Markov inequality, with no prior finiteness of the observable. -/
theorem measure_gt_le_moment_div (μ : Measure E) {N : E → ℝ≥0∞}
    (hN : Measurable N) {p : ℝ} (hp : 0 ≤ p) {C M : ℝ≥0∞}
    (hC : ∫⁻ z, N z ^ p ∂μ ≤ C) (hM : M ≠ 0) (hMt : M ≠ ⊤) :
    μ {z | M < N z} ≤ C / M ^ p := by
  have hm : Measurable (fun z => N z ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp hN
  exact (measure_mono (fun z hz => ENNReal.rpow_le_rpow hz.le hp)).trans
    ((meas_ge_le_lintegral_div hm.aemeasurable
      (ne_of_gt (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hM) hMt))
      (ENNReal.rpow_ne_top_of_nonneg hp hMt)).trans (ENNReal.div_le_div_right hC _))

variable [TopologicalSpace E]

/-- A uniform finite first moment of an observable with compact finite sublevels
gives genuine tightness, rather than taking tightness as an additional premise. -/
theorem isTightMeasureSet_of_moment (S : Set (Measure E)) {N : E → ℝ≥0∞}
    (hN : Measurable N) (hcompact : ∀ M : ℝ≥0∞, M ≠ ⊤ → IsCompact {z | N z ≤ M})
    {C : ℝ≥0∞} (hCt : C ≠ ⊤) (hC : ∀ μ ∈ S, ∫⁻ z, N z ∂μ ≤ C) :
    IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases hεt : ε = ⊤
  · exact ⟨∅, isCompact_empty, fun _ _ => by simp [hεt]⟩
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top hCt (ne_of_gt hε))
  let M : ℝ≥0∞ := n + 1
  have hM : M ≠ 0 := by simp [M]
  have hMt : M ≠ ⊤ := by simp [M]
  refine ⟨{z | N z ≤ M}, hcompact M hMt, fun μ hμ => ?_⟩
  have htail := measure_gt_le_moment_div μ hN (p := 1) zero_le_one
    (by simpa using hC μ hμ) hM hMt
  simp only [ENNReal.rpow_one] at htail
  have hratio : C / M ≤ ε := by
    apply (ENNReal.div_le_iff hM hMt).mpr
    have h := (ENNReal.div_le_iff (ne_of_gt hε) hεt).mp hn.le
    exact h.trans (by simpa [mul_comm] using
      mul_le_mul_right (le_add_right le_rfl : (n : ℝ≥0∞) ≤ M) ε)
  simpa only [compl_ofPred, not_le] using htail.trans hratio

/-- The stronger heat-probe norm has the compact sublevels needed above. -/
theorem holderBesov_isTightMeasureSet_of_moment (η γ : NegExponent)
    (hηγ : (η : ℝ) < γ) (S : Set (Measure (HolderBesov η)))
    {C : ℝ≥0∞} (hCt : C ≠ ⊤)
    (hC : ∀ μ ∈ S, ∫⁻ z, extNorm η γ z ∂μ ≤ C) : IsTightMeasureSet S :=
  isTightMeasureSet_of_moment S (measurable_extNorm η γ)
    (fun _ hM => isCompact_extNorm_sublevel η γ hηγ hM) hCt hC

end GlobalPhi43.Invariant
