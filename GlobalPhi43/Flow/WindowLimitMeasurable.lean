module

public import GlobalPhi43.Flow.ClassicalApproximation
public import GlobalPhi43.Flow.NoiseWindowGerm
public import GlobalPhi43.Flow.DyadicLiftData
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

public noncomputable section

open MeasureTheory Set Filter Topology RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

/-- Internal version lemma: the common ambient null generator allows the
literal identity fallback on any given measurable full event. -/
theorem measurable_limit_on_full_event {Ω Y : Type*} [mΩ : MeasurableSpace Ω]
    [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (P : Measure Ω) {m : MeasurableSpace Ω}
    (hnull : MeasurableSpace.generateFrom {A | MeasurableSet[mΩ] A ∧ P A = 0} ≤ m)
    {E : Set Ω} (hE : MeasurableSet[mΩ] E) (hEc : P Eᶜ = 0)
    (f : ℕ → Ω → Y) (g : Ω → Y) (x : Y)
    (hf : ∀ᶠ n in atTop, Measurable[m] (f n))
    (hlim : ∀ ω ∈ E, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hoff : ∀ ω ∉ E, g ω = x) : Measurable[m] g := by
  classical
  have hec : MeasurableSet[m] Eᶜ :=
    hnull _ (MeasurableSpace.measurableSet_generateFrom ⟨hE.compl, hEc⟩)
  have he : MeasurableSet[m] E := by simpa only [compl_compl] using hec.compl
  obtain ⟨N, hN⟩ := eventually_atTop.mp hf
  apply measurable_of_tendsto_metrizable
    (f := fun n ω => if ω ∈ E then f (n + N) ω else x)
  · intro n
    exact (hN (n + N) (Nat.le_add_left _ _)).piecewise he measurable_const
  · apply tendsto_pi_nhds.mpr
    intro ω
    by_cases hω : ω ∈ E
    · simpa only [ite_eq_left hω, Function.comp_def] using (hlim ω hω).comp (tendsto_add_atTop_nat N)
    · simpa only [ite_eq_right hω, hoff ω hω] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))

/-- Actual source dyadic tail, including positivity at the first index. -/
theorem dyadicTailScale_mem (n : ℕ) : dyadicTailScale n ∈ Ioc (0 : ℝ) 1 := by
  constructor
  · exact pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) _
  · exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)

/-- Every positive forcing-window allowance eventually contains the dyadic
mollifier support. No random threshold or additional event is selected. -/
theorem eventually_dyadic_window (R : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, (dyadicTailScale n) ^ 2 * R < δ := by
  have hs : Tendsto dyadicTailScale atTop (𝓝 (0 : ℝ)) := by
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)).comp (tendsto_add_atTop_nat 1)
  have hh := (hs.pow 2).mul_const R
  simp only [zero_pow (by decide : 2 ≠ 0), zero_mul] at hh
  exact hh.eventually (gt_mem_nhds hδ)

section Reference

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
  {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
  (N : ℕ) (hN : 5 ≤ N) (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa)
  (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ)
  (η : NegExponent) (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
  (hκη : κ.1 < -(1 / 2 : ℝ) - η)
  (ξ : ℝ → Ω → SpaceTime → ℝ)
  (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))

include hW hN hκE hρ hη hκη

local notation "hsmooth" => (fun ε hε => And.left (hξ ε hε))
local notation "E" => referenceEvent N κ ρ mass η ξ hsmooth
local notation "A" => (fun ω : E => dyadicLiftData N κ ρ mass η ξ hsmooth (Subtype.val ω) (Subtype.property ω))

/-- Smooth-data causality of the supplied reference EventFlow on each enlarged
window. Measurability and convergence hold for the classical endpoints on the
same fixed event. -/
theorem referenceFlow_smooth_enlarged_measurable (u : EventFlow E η A)
    {s t δ : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hδ : 0 < δ)
    (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x) :
    Measurable[enlargedNoiseWindowSigma P W s t δ]
      (fun ω => u.value ω t s (toHolderBesov η x)) := by
  obtain ⟨he, hp⟩ := referenceEvent_measurable_measure_one P W hW N hN κ hκE
    ρ hρ mass η hη hκη ξ hξ
  have hec : P Eᶜ = 0 := by rw [measure_compl he (measure_ne_top P E), hp]; simp only [measure_univ, tsub_self]
  let b := fun n => 3 * (wickConstant ρ (dyadicTailScale n) + mass / 3) -
    9 * (sunsetConstant ρ (dyadicTailScale n) + 0)
  let f := fun n ω => toHolderBesov η
    (smoothSolution (b n) (shiftForcing s (ξ (dyadicTailScale n) ω))
      (isSmoothOnSpaceTime_shiftForcing ((hξ _ (dyadicTailScale_mem n)).1 ω) s) x hx (t-s))
  apply measurable_limit_on_full_event P le_sup_left he hec f _ (toHolderBesov η x)
  · filter_upwards [eventually_dyadic_window (mollifierTimeRadius ρ hρ) hδ] with n hn
    exact smoothSolution_holder_window_measurable η P hW hρ
      (dyadicTailScale_mem n).1 (hξ _ (dyadicTailScale_mem n)) hst hn (b n) x hx
  · intro ω hω
    have ht := (u.system ⟨ω, hω⟩).tendsto_smooth_value s (t-s) hs (sub_nonneg.mpr hst) x hx
    rw [u.value_on ⟨ω, hω⟩]
    exact ht
  · intro ω hω
    exact u.value_off hω t s _

/-- Exact completed-window causality on smooth data, by the germ.
The reference flow is fixed throughout the argument. -/
theorem referenceFlow_smooth_window_measurable (u : EventFlow E η A)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x) :
    Measurable[noiseWindowSigma P W s t] (fun ω => u.value ω t s (toHolderBesov η x)) := by
  rw [← noiseWindowSigma_germ P hW s t hst]
  intro B hB
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  exact referenceFlow_smooth_enlarged_measurable P hW N hN κ hκE ρ hρ mass η hη hκη
    ξ hξ u hs hst (by positivity : 0 < 1 / ((n : ℝ) + 1)) x hx hB

end Reference
end GlobalPhi43.Flow
