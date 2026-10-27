/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Flow.NoiseWindowRestriction
public import Phi43.Stochastic.WhiteNoiseL2
public import Phi43.Stochastic.AnnealedNoiseTorus
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
public import Mathlib.MeasureTheory.Function.L2Space

/-! The actual white-noise family is an L2 isometry modulo null sets.
Completed supported information fields are consequently closed under L2 test
limits. No samplewise linearity on an uncountable family is assumed. -/

public noncomputable section

open MeasureTheory ProbabilityTheory Filter RegularityStructures
open scoped Topology

namespace GlobalPhi43.Probability

theorem realLp_norm_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (f : Lp ℝ 2 P) : ‖f‖ ^ 2 = ∫ ω, (f ω) ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- The L2 class of the actual supplied white-noise pairing. -/
@[expose] def whiteNoiseLp {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (h : SpaceTime → ℝ) (hh : MemLp h 2) : Lp ℝ 2 P :=
  (whiteNoise_pairing_hasGaussianLaw hW hh).memLp_two.toLp (W h)

theorem whiteNoiseLp_coe {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (h : SpaceTime → ℝ) (hh : MemLp h 2 volume) : whiteNoiseLp hW h hh =ᵐ[P] W h :=
  MemLp.coeFn_toLp _

theorem whiteNoiseLp_norm {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (h : SpaceTime → ℝ) (hh : MemLp h 2 volume) : ‖whiteNoiseLp hW h hh‖ = ‖hh.toLp h‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [realLp_norm_sq, realLp_norm_sq]
  calc (∫ ω, (whiteNoiseLp hW h hh ω) ^ 2 ∂P) = ∫ ω, (W h ω) ^ 2 ∂P :=
        integral_congr_ae ((whiteNoiseLp_coe hW h hh).mono fun _ he => congrArg (fun v => v ^ 2) he)
    _ = ∫ z, h z ^ 2 := whiteNoise_pairing_sq_integral hW hh
    _ = ∫ z, (hh.toLp h z) ^ 2 :=
      integral_congr_ae (hh.coeFn_toLp.symm.mono fun _ he => congrArg (fun v => v ^ 2) he)

theorem whiteNoiseLp_sub {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {h g : SpaceTime → ℝ} (hh : MemLp h 2 volume)
    (hg : MemLp g 2 volume) :
    whiteNoiseLp hW h hh - whiteNoiseLp hW g hg = whiteNoiseLp hW (h - g) (hh.sub hg) := by
  apply Lp.ext
  exact (Lp.coeFn_sub _ _).trans
    (((whiteNoiseLp_coe hW h hh).sub (whiteNoiseLp_coe hW g hg)).trans
      ((whiteNoise_pairing_sub_ae hW hh hg).trans
        (whiteNoiseLp_coe hW (h - g) (hh.sub hg)).symm))

theorem whiteNoiseLp_norm_sub {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {h g : SpaceTime → ℝ} (hh : MemLp h 2 (volume : Measure SpaceTime))
    (hg : MemLp g 2 (volume : Measure SpaceTime)) :
    ‖whiteNoiseLp hW h hh - whiteNoiseLp hW g hg‖ = ‖hh.toLp h - hg.toLp g‖ := by
  rw [whiteNoiseLp_sub, whiteNoiseLp_norm, MemLp.toLp_sub hh hg]

/-- L2 convergence of actual tests gives L2 convergence of their supplied
white-noise pairings. This is proved from the native Gaussian predicate. -/
theorem whiteNoiseLp_tendsto {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {f : ℕ → SpaceTime → ℝ} {h : SpaceTime → ℝ}
    (hf : ∀ n, MemLp (f n) 2 volume)
    (hh : MemLp h 2 volume)
    (hlim : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hh.toLp h))) :
    Tendsto (fun n => whiteNoiseLp hW (f n) (hf n)) atTop (𝓝 (whiteNoiseLp hW h hh)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hlim ⊢
  simpa only [whiteNoiseLp_norm_sub] using hlim

/-- Completed-field measurability is closed under L2 test approximation.
The approximation and isometry are proved inputs in the native germ application. -/
theorem measurable_whiteNoise_of_Lp_limit {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hn : MeasurableSpace.generateFrom {A | MeasurableSet[mΩ] A ∧ P A = 0} ≤ m)
    {f : ℕ → SpaceTime → ℝ} {h : SpaceTime → ℝ}
    (hf : ∀ n, MemLp (f n) 2 volume) (hh : MemLp h 2 volume)
    (hfm : ∀ n, Measurable[m] (W (f n)))
    (hlim : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hh.toLp h))) :
    Measurable[m] (W h) := by
  have hc : AEStronglyMeasurable[m] (whiteNoiseLp (mΩ := mΩ) hW h hh) P :=
    (isClosed_aestronglyMeasurable (m0 := mΩ) (μ := P) hm).mem_of_tendsto
      (whiteNoiseLp_tendsto (mΩ := mΩ) hW hf hh hlim)
      (Eventually.of_forall fun n => ⟨W (f n), (hfm n).stronglyMeasurable,
        whiteNoiseLp_coe (mΩ := mΩ) hW (f n) (hf n)⟩)
  have hraw := hc.congr (whiteNoiseLp_coe (mΩ := mΩ) hW h hh)
  exact Flow.measurable_of_ae_eq_of_null_le (mΩ := mΩ) P hm hn (hW.1 h hh)
    hraw.measurable_mk hraw.ae_eq_mk

end GlobalPhi43.Probability
