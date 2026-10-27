module

public import GlobalPhi43.Invariant.StrongTransfer

/-! # Heat-probe late-moment transfer under restart -/

public noncomputable section

open MeasureTheory ProbabilityTheory RegularityStructures Filter Set Topology
open scoped ENNReal

namespace GlobalPhi43.Invariant

variable {X Ω : Type*} [TopologicalSpace X] [MeasurableSpace Ω]

/-- One-event one-step bounds and literal restart imply uniform late moments.
The random restarted datum is evaluated before integration; no datum-dependent null sets occur. -/
theorem holderBesov_late_moment_of_restart (η : NegExponent) (α : ℝ)
    (P : Measure Ω) (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (ρ : Kernel ℝ (HolderBesov η)) (z : HolderBesov η)
    (horbit : ∀ t, 1 < t → ρ t = P.map (u t 0 z))
    (hu : ∀ t, 1 < t → Measurable (u t 0 z))
    (B : ℝ → Ω → ℝ≥0∞) {p : ℝ} (hp : 0 ≤ p) {C : ℝ≥0∞}
    (hstep : ∀ t, 1 ≤ t → ∀ᵐ ω ∂P, ∀ v, extNorm η α (u t (t - 1) v ω) ≤ B t ω)
    (hrestart : ∀ t, 1 ≤ t → ∀ v ω,
      u t 0 v ω = u t (t - 1) (u (t - 1) 0 v ω) ω)
    (hB : ∀ t, 1 ≤ t → ∫⁻ ω, B t ω ^ p ∂P ≤ C)
    {T : ℝ} (hT : 1 < T) :
    ∫⁻ y, extNorm η α y ^ p ∂lateAverage ρ T ≤ C := by
  apply lintegral_lateAverage_le ρ
    (ENNReal.continuous_rpow_const.measurable.comp (measurable_extNorm η α)) _ hT
  intro t ht
  rw [horbit t ht]
  exact law_moment_of_restarted_bound P u (extNorm η α) (measurable_extNorm η α)
    B p hp C hstep hrestart hB ht.le z (hu t ht)

end GlobalPhi43.Invariant
