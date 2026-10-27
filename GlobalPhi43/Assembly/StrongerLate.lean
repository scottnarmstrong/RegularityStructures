module

public import GlobalPhi43.Assembly.StrongerMoments
public import GlobalPhi43.Invariant.RestartMomentTransfer
public import GlobalPhi43.Invariant.MomentTightness

/-! # Actual sampled orbit and late stronger moments of the same supplied flow -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory RegularityStructures Set Filter Topology
open scoped ENNReal NNReal

namespace GlobalPhi43.Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}

/-- Joint measurability of the actual orbit, clipped only at negative times. -/
theorem measurable_clippedOrbit {Ω₀ : Set Ω}
    {u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η}
    (hu : IsContinuousMeasurableFlow Ω₀ u) (z : HolderBesov η) :
    Measurable (fun q : ℝ × Ω => u (max 0 q.1) 0 z q.2) := by
  have ht : Measurable (fun q : ℝ × Ω =>
      (⟨(max 0 q.1, 0), le_rfl, le_max_left _ _⟩ :
        {r : ℝ × ℝ // 0 ≤ r.2 ∧ r.2 ≤ r.1})) :=
    ((measurable_const.max measurable_fst).prodMk measurable_const).subtype_mk
  exact hu.1.comp (ht.prodMk (measurable_const.prodMk measurable_snd))

/-- Sampled orbit law; no unrelated law kernel is an input. -/
def flowOrbitKernel (P : Measure Ω) [SFinite P] {Ω₀ : Set Ω}
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (hu : IsContinuousMeasurableFlow Ω₀ u) (z : HolderBesov η) :
    Kernel ℝ (HolderBesov η) :=
  Markov.sampleKernel P _ (measurable_clippedOrbit hu z)

instance flowOrbitKernel_isMarkovKernel (P : Measure Ω) [IsProbabilityMeasure P] {Ω₀ : Set Ω}
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (hu : IsContinuousMeasurableFlow Ω₀ u) (z : HolderBesov η) :
    IsMarkovKernel (flowOrbitKernel P u hu z) :=
  Markov.sampleKernel_isMarkovKernel P _ (measurable_clippedOrbit hu z)

theorem flowOrbitKernel_apply (P : Measure Ω) [SFinite P] {Ω₀ : Set Ω}
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (hu : IsContinuousMeasurableFlow Ω₀ u) (z : HolderBesov η) {t : ℝ} (ht : 0 ≤ t) :
    flowOrbitKernel P u hu z t = flowLaw P u t z := by
  change P.map (fun ω => u (max 0 t) 0 z ω) = P.map (fun ω => u t 0 z ω)
  rw [max_eq_right ht]

omit [MeasurableSpace Ω] in
/-- The actual supremum controls every datum pointwise, before any random substitution. -/
theorem extNorm_oneStep_le_strongWindowSup (α : ℝ)
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) (s : ℝ)
    (z : HolderBesov η) (ω : Ω) :
    extNorm η α (u (s + 1) s z ω) ≤ strongWindowSup α u s ω := by
  have h := le_iSup (fun p : HolderBesov η × Ioc (0 : ℝ) 1 =>
    strongerWindowProbe α u s ω p) (z, ⟨1, by norm_num⟩)
  simpa only [strongWindowSup, strongerWindowProbe, Real.sqrt_one, ENNReal.ofReal_one, one_mul] using h

/-- Exact T-1 late averaging for the actual flow orbit. The one-event one-step
bound is derived from the actual stronger supremum, not supplied as a premise. -/
theorem flowOrbit_late_moment (C : ℝ≥0∞) (P : Measure Ω) [SFinite P]
    (α : ℝ) {Ω₀ : Set Ω}
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (hu : IsContinuousMeasurableFlow Ω₀ u) (z : HolderBesov η)
    {p : ℝ} (hp : 1 ≤ p)
    (hstrong : ∀ r, 0 ≤ r → ∫⁻ ω, strongWindowSup α u r ω ^ p ∂P ≤ C)
    {T : ℝ} (hT : 1 < T) :
    ∫⁻ y, extNorm η α y ^ p ∂Invariant.lateAverage (flowOrbitKernel P u hu z) T ≤ C := by
  refine Invariant.holderBesov_late_moment_of_restart η α P u
    (flowOrbitKernel P u hu z) z ?_ ?_ (fun t => strongWindowSup α u (t - 1))
    (le_trans zero_le_one hp) ?_ ?_ ?_ hT
  · intro t ht
    exact flowOrbitKernel_apply P u hu z (by linarith)
  · intro t ht
    have hm := (measurable_clippedOrbit hu z).comp
      ((measurable_const (a := t)).prodMk measurable_id)
    change Measurable (fun ω => u (max 0 t) 0 z ω) at hm
    simpa only [max_eq_right (show 0 ≤ t by linarith)] using hm
  · intro t ht
    apply Eventually.of_forall
    intro ω v
    have hb := extNorm_oneStep_le_strongWindowSup α u (t - 1) v ω
    simpa only [sub_add_cancel] using hb
  · intro t ht v ω
    exact (hu.2.2.2.2 0 (t - 1) t le_rfl (by linarith) (by linarith) v ω).symm
  · intro t ht
    exact hstrong (t - 1) (by linarith)

/-- Consistency and time homogeneity transfer the profile to late moments,
with the profile still fixed before the probability space. -/
theorem flowOrbit_late_moments (C : ℝ → ℝ → ℝ≥0)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P] {η : NegExponent}
    {Ω₀ : Set Ω} (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (hu : IsContinuousMeasurableFlow Ω₀ u) (z : HolderBesov η)
    (hstrong : ∀ α, (η : ℝ) ≤ α → α < -(1 / 2 : ℝ) → ∀ p : ℝ, 1 ≤ p →
      (⨆ r ≥ (0 : ℝ), ∫⁻ ω, strongWindowSup α u r ω ^ p ∂P) ≤ C α p) :
    ∀ α, (η : ℝ) ≤ α → α < -(1 / 2 : ℝ) → ∀ p : ℝ, 1 ≤ p → ∀ T, 1 < T →
      ∫⁻ y, extNorm η α y ^ p ∂Invariant.lateAverage (flowOrbitKernel P u hu z) T ≤ C α p := by
  intro α hα hα' p hp T hT
  apply flowOrbit_late_moment (C α p) P α u hu z hp _ hT
  intro r hr
  exact (le_iSup₂_of_le r hr le_rfl).trans (hstrong α hα hα' p hp)

end GlobalPhi43.Assembly
