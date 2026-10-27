module

public import GlobalPhi43.Flow.NoiseWindowShift
public import Phi43.ClassicalSolution.MeasurableSupport
public import Phi43.Constants.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Supported mollifier tests and restriction measurability on an enlarged
completed noise window. Ambient measurability alone is not used as a local
measurability conclusion. -/

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open scoped symmDiff

namespace GlobalPhi43.Flow

/-- The enlarged window adjoins exactly the same ambient null sets as the
half-open window. Its tests have closed support in the enlarged time interval. -/
@[expose, instance_reducible] def enlargedNoiseWindowSigma {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : (SpaceTime → ℝ) → Ω → ℝ) (s t δ : ℝ) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom {A | MeasurableSet A ∧ P A = 0} ⊔
    ⨆ (h : SpaceTime → ℝ)
      (_ : MemLp h 2 ∧ Function.support h ⊆ Icc (s - δ) (t + δ) ×ˢ univ),
      MeasurableSpace.comap (W h) inferInstance

theorem enlargedNoiseWindowSigma_le {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W) (s t δ : ℝ) :
    enlargedNoiseWindowSigma P W s t δ ≤ mΩ := by
  apply sup_le
  · exact MeasurableSpace.generateFrom_le fun _ h => h.1
  · apply iSup_le
    intro h
    apply iSup_le
    intro hh
    exact (hW.1 h hh.1).comap_le

/-- Ambient-measurable versions remain measurable in a smaller information
field once that field contains all ambient measurable null sets. -/
theorem measurable_of_ae_eq_of_null_le {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace E] (P : Measure Ω) {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hn : MeasurableSpace.generateFrom {A | MeasurableSet[mΩ] A ∧ P A = 0} ≤ m)
    {f g : Ω → E} (hf : Measurable[mΩ] f) (hg : Measurable[m] g) (he : f =ᵐ[P] g) :
    Measurable[m] f := by
  intro V hV
  have hC : MeasurableSet[mΩ] (g ⁻¹' V) := hm _ (hg hV)
  have hD : MeasurableSet[mΩ] ((f ⁻¹' V) ∆ (g ⁻¹' V)) := (hf hV).symmDiff hC
  have hnull : P ((f ⁻¹' V) ∆ (g ⁻¹' V)) = 0 := by
    apply measure_symmDiff_eq_zero_iff.mpr
    exact he.mono fun ω h => congrArg (fun y => y ∈ V) h
  have hlocal : MeasurableSet[m] ((f ⁻¹' V) ∆ (g ⁻¹' V)) :=
    hn _ (MeasurableSpace.measurableSet_generateFrom ⟨hD, hnull⟩)
  simpa only [symmDiff_symmDiff_cancel_right] using hlocal.symmDiff (hg hV)

/-- A positive time-support radius is obtained from compact support alone. -/
theorem exists_mollifier_timeRadius (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ParabolicSpace, R < |z.1| → ρ z = 0 := by
  obtain ⟨B, hB⟩ := (hρ.hasCompactSupport.image continuous_fst.norm).bddAbove
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro z hz
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hb : |z.1| ≤ B := hB ⟨z, hmem, rfl⟩
  exact (not_lt_of_ge (hb.trans (le_max_right _ _))) hz

/-- An auxiliary radius depending solely on the fixed mollifier, selected
before the noise space, scale, start, window and data. -/
@[expose] def mollifierTimeRadius (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) : ℝ :=
  (exists_mollifier_timeRadius ρ hρ).choose

theorem mollifierTimeRadius_zero (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ)
    (z : ParabolicSpace) (hz : mollifierTimeRadius ρ hρ < |z.1|) : ρ z = 0 :=
  (exists_mollifier_timeRadius ρ hρ).choose_spec.2 z hz

/-- Spatial periodisation preserves the explicit parabolic time-support bound. -/
theorem periodise_eq_zero_of_timeRadius {ρ : ParabolicSpace → ℝ} (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) (z : SpaceTime)
    (hz : ε ^ 2 * mollifierTimeRadius ρ hρ < |z.1|) : periodise ρ ε z = 0 := by
  have hscale : ε ^ (-2 : ℤ) * ε ^ 2 = 1 := by simp [zpow_neg, hε.ne']
  have hpos : 0 < ε ^ (-2 : ℤ) := zpow_pos hε _
  have hscaled : mollifierTimeRadius ρ hρ < |ε ^ (-2 : ℤ) * z.1| := by
    rw [abs_mul, abs_of_pos hpos]
    calc mollifierTimeRadius ρ hρ = ε ^ (-2 : ℤ) * (ε ^ 2 * mollifierTimeRadius ρ hρ) := by
          rw [← mul_assoc, hscale, one_mul]
      _ < ε ^ (-2 : ℤ) * |z.1| := mul_lt_mul_of_pos_left hz hpos
  have hzero (k : Fin 3 → ℤ) :
      rescale ρ ε (z.1, torusRep z.2 + fun i => (k i : ℝ)) = 0 := by
    unfold rescale
    rw [mollifierTimeRadius_zero ρ hρ _ hscaled, mul_zero]
  simp only [periodise, hzero, tsum_zero]

/-- Every evaluation on the closed relative window uses a test supported in
the enlarged absolute window, with exactly the epsilon-squared threshold. -/
theorem mollifierAt_support_window {ρ : ParabolicSpace → ℝ} (hρ : IsMollifier ρ)
    {ε s t δ r : ℝ} (hε : 0 < ε) (hr : r ∈ Icc (0 : ℝ) (t - s))
    (hδ : ε ^ 2 * mollifierTimeRadius ρ hρ < δ) (x : Torus3) :
    Function.support (mollifierAt ρ ε (s + r, x)) ⊆ Icc (s - δ) (t + δ) ×ˢ univ := by
  intro w hw
  refine ⟨?_, trivial⟩
  by_contra h
  have hout : w.1 < s - δ ∨ t + δ < w.1 := by
    simpa only [mem_Icc, not_and_or, not_le] using h
  have habs : ε ^ 2 * mollifierTimeRadius ρ hρ < |((s + r, x) - w).1| := by
    change ε ^ 2 * mollifierTimeRadius ρ hρ < |s + r - w.1|
    rcases hout with hleft | hright
    · exact (by linarith [hr.1] : ε ^ 2 * mollifierTimeRadius ρ hρ < s + r - w.1).trans_le
        (le_abs_self _)
    · exact (by linarith [hr.2] : ε ^ 2 * mollifierTimeRadius ρ hρ < -(s + r - w.1)).trans_le
        (neg_le_abs _)
  exact hw (periodise_eq_zero_of_timeRadius hρ hε _ habs)

/-- Literal continuous restriction of a smooth noise version. -/
@[expose] def smoothNoiseRestriction {Ω : Type*} (ξ : Ω → SpaceTime → ℝ)
    (hξ : ∀ ω, IsSmoothOnSpaceTime (ξ ω)) (s T : ℝ) :
    Ω → C(Icc (0 : ℝ) T × Torus3, ℝ) := fun ω =>
  ⟨fun z => ξ ω (s + z.1.1, z.2),
    (Continuous.continuous_of_isSmoothOnSpaceTime (hξ ω)).comp
      ((continuous_const.add (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)⟩

/-- Restriction-window measurability, derived from the actual noise
predicates and the mollifier's radius. No local measurability is assumed. -/
theorem regularisedNoise_restriction_window_measurable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {ρ : ParabolicSpace → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {ξ : Ω → SpaceTime → ℝ} (hξ : IsRegularisedNoise P W ρ ε ξ)
    {s t δ : ℝ} (hδ : ε ^ 2 * mollifierTimeRadius ρ hρ < δ) :
    Measurable[enlargedNoiseWindowSigma P W s t δ]
      (smoothNoiseRestriction ξ hξ.1 s (t - s)) := by
  let m := enlargedNoiseWindowSigma P W s t δ
  have hm : m ≤ mΩ := @enlargedNoiseWindowSigma_le Ω mΩ P W hW s t δ
  have hn : MeasurableSpace.generateFrom {A | MeasurableSet[mΩ] A ∧ P A = 0} ≤ m := le_sup_left
  apply ContinuousMap.measurable_iff_eval.mpr
  intro z
  have htest : Measurable[m] (W (mollifierAt ρ ε (s + z.1.1, z.2))) := by
    apply Measurable.of_comap_le
    exact le_sup_of_le_right (le_iSup_of_le _ (le_iSup_of_le
      ⟨memLp_mollifierAt ρ hρ hε _, mollifierAt_support_window hρ hε z.1.2 hδ z.2⟩ le_rfl))
  exact measurable_of_ae_eq_of_null_le (mΩ := mΩ) P hm hn (hξ.2 _).1 htest (hξ.2 _).2

end GlobalPhi43.Flow
