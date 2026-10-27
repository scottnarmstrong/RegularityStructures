module

public import GlobalPhi43.Flow.ClassicalStartContinuity
public import GlobalPhi43.Flow.ClassicalWindowMeasurable
public import GlobalPhi43.Markov.Measurability
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! Joint deterministic-start/noise measurability of the actual classical path.
Bounded relative-time charts avoid any continuity assumption on a rough flow. -/

public noncomputable section

open MeasureTheory Set Filter Topology RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

/-- Clip the elapsed time to a compact classical chart, retaining the initial face. -/
@[expose] def clippedElapsed (T : ℝ) (hT : 0 ≤ T) (t s : ℝ) : Icc (0 : ℝ) T :=
  ⟨min (max (t - s) 0) T, le_min (le_max_right _ _) hT, min_le_right _ _⟩

/-- Classical continuity jointly in external start and clipped observation time. -/
theorem continuous_clipped_classicalEndpoint (T b : ℝ) (hT : 0 ≤ T)
    (f : SpaceTime → ℝ) (hf : IsSmoothOnSpaceTime f) (x : SmoothDatum) :
    Continuous (fun p : ℝ × ℝ =>
      classicalCurve T b (shiftForcing p.2 f)
        (isSmoothOnSpaceTime_shiftForcing hf p.2) x (clippedElapsed T hT p.1 p.2)) := by
  have hc := (continuous_classicalCurve_shift T b hT f hf).comp
    (continuous_snd.prodMk continuous_const : Continuous (fun p : ℝ × ℝ => (p.2, x)))
  have hr : Continuous (fun p : ℝ × ℝ => clippedElapsed T hT p.1 p.2) := by
    apply Continuous.subtype_mk
    exact ((continuous_fst.sub continuous_snd).max continuous_const).min continuous_const
  exact continuous_eval.comp (hc.prodMk hr)

/-- The clipped actual endpoint is jointly measurable in both time coordinates
and the noise. Each approximant keeps its own linear coefficient. -/
theorem measurable_clipped_classicalEndpoint {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {ρ : ParabolicSpace → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {ξ : Ω → SpaceTime → ℝ} (hξ : IsRegularisedNoise P W ρ ε ξ)
    (T b : ℝ) (hT : 0 ≤ T) (x : SmoothDatum) :
    Measurable (fun p : (ℝ × ℝ) × Ω =>
      classicalCurve T b (shiftForcing p.1.2 (ξ p.2))
        (isSmoothOnSpaceTime_shiftForcing (hξ.1 p.2) p.1.2) x
        (clippedElapsed T hT p.1.1 p.1.2)) := by
  apply Markov.measurable_joint_of_sections (F := fun (p : ℝ × ℝ) (ω : Ω) =>
    classicalCurve T b (shiftForcing p.2 (ξ ω))
      (isSmoothOnSpaceTime_shiftForcing (hξ.1 ω) p.2) x
      (clippedElapsed T hT p.1 p.2))
  · intro ω
    exact continuous_clipped_classicalEndpoint T b hT (ξ ω) (hξ.1 ω) x
  · intro p
    let r := clippedElapsed T hT p.1 p.2
    let δ := ε ^ 2 * mollifierTimeRadius ρ hρ + 1
    have hm := smoothSolution_window_measurable P hW hρ hε hξ
      (s := p.2) (t := p.2 + r) (δ := δ)
      (le_add_of_nonneg_right r.property.1) (lt_add_one _) b x.val x.property
    have ha := hm.mono (enlargedNoiseWindowSigma_le P hW _ _ _) le_rfl
    change Measurable (fun ω => smoothSolution b (shiftForcing p.2 (ξ ω))
      (isSmoothOnSpaceTime_shiftForcing (hξ.1 ω) p.2) x.val x.property r.val)
    simpa only [add_sub_cancel_left] using ha

/-- Removing the compact chart gives the full classical endpoint, with observation
times before the start extended by the initial datum. No sample-space action is used. -/
theorem measurable_classicalEndpoint_extended {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {ρ : ParabolicSpace → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {ξ : Ω → SpaceTime → ℝ} (hξ : IsRegularisedNoise P W ρ ε ξ)
    (b : ℝ) (x : SmoothDatum) :
    Measurable (fun p : (ℝ × ℝ) × Ω =>
      smoothSolution b (shiftForcing p.1.2 (ξ p.2))
        (isSmoothOnSpaceTime_shiftForcing (hξ.1 p.2) p.1.2) x.val x.property
        (max (p.1.1 - p.1.2) 0)) := by
  apply measurable_of_tendsto_metrizable
    (fun n : ℕ => measurable_clipped_classicalEndpoint P hW hρ hε hξ
      (n : ℝ) b (Nat.cast_nonneg n) x)
  apply tendsto_pi_nhds.mpr
  intro p
  obtain ⟨N, hN⟩ := exists_nat_ge (max (p.1.1 - p.1.2) 0)
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop N] with n hn
  have hr : max (p.1.1 - p.1.2) 0 ≤ (n : ℝ) :=
    hN.trans (Nat.cast_le.mpr hn)
  simp only [classicalCurve, clippedElapsed, min_eq_left hr]
  rfl

/-- The same full parameter map in the negative-regularity state, with the actual
renormalised coefficient; no bound uniform over regularisation scales is used. -/
theorem measurable_renormalisedEndpoint_extended (η : NegExponent)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {ρ : ParabolicSpace → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {ξ : Ω → SpaceTime → ℝ} (hξ : IsRegularisedNoise P W ρ ε ξ)
    (a C₁ C₂ : ℝ) (x : SmoothDatum) :
    Measurable (fun p : (ℝ × ℝ) × Ω => toHolderBesov η
      (smoothSolution (a + 3 * C₁ - 9 * C₂) (shiftForcing p.1.2 (ξ p.2))
        (isSmoothOnSpaceTime_shiftForcing (hξ.1 p.2) p.1.2) x.val x.property
        (max (p.1.1 - p.1.2) 0))) :=
  (lipschitzWith_toHolderBesov η).continuous.measurable.comp
    (measurable_classicalEndpoint_extended P hW hρ hε hξ (a + 3 * C₁ - 9 * C₂) x)

end GlobalPhi43.Flow
