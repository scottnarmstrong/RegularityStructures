module

public import GlobalPhi43.Flow.NoiseWindowRestriction
public import GlobalPhi43.Flow.ClassicalTranslation
public import GlobalPhi43.Compactness.Embedding
public import Phi43.ClassicalSolution.MeasurableStability
import Mathlib.Tactic.Ring

/-! Classical endpoints are measurable in the same enlarged noise window as
their restricted forcing. The estimates use the existing chosen path;
no measurability of an endpoint factor or of the whole white noise on a smaller
sigma-algebra is assumed. -/

public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open scoped NNReal ENNReal

namespace GlobalPhi43.Flow

/-- Deterministic factorisation through the restricted forcing. Its Lipschitz
bound is derived from classical stability with the actual common coefficient. -/
theorem classicalEndpoint_measurable_of_restriction {Ω : Type*} [MeasurableSpace Ω]
    (ξ : Ω → SpaceTime → ℝ) (hξ : ∀ ω, IsSmoothOnSpaceTime (ξ ω))
    (b s T : ℝ) (hT : 0 ≤ T) (x : C(Torus3, ℝ))
    (u : Ω → ℝ → C(Torus3, ℝ))
    (hu : ∀ ω, IsClassicalSolution b (shiftForcing s (ξ ω)) x (u ω))
    {m : MeasurableSpace Ω} (hF : Measurable[m] (smoothNoiseRestriction ξ hξ s T)) :
    Measurable[m] (fun ω => u ω T) := by
  let F := smoothNoiseRestriction ξ hξ s T
  let L : ℝ≥0 := ⟨T * Real.exp (|b| * T), mul_nonneg hT (Real.exp_nonneg _)⟩
  apply measurable_of_lipschitz_range F (fun ω => u ω T) hF (K := L)
  intro ω ω'
  have hforce : ∀ q ∈ Icc (0 : ℝ) T, ∀ z : Torus3,
      |shiftForcing s (ξ ω) (q, z) - shiftForcing s (ξ ω') (q, z)| ≤ ‖F ω - F ω'‖ := by
    intro q hq z
    have hz := ContinuousMap.norm_coe_le_norm (F ω - F ω') (⟨q, hq⟩, z)
    change ‖ξ ω (s + q, z) - ξ ω' (s + q, z)‖ ≤ ‖F ω - F ω'‖ at hz
    simpa only [shiftForcing, add_comm q s, Real.norm_eq_abs] using hz
  have hstab := classicalSolution_sup_stability b (hu ω) (hu ω') hT
    ‖F ω - F ω'‖ (norm_nonneg _) hforce T ⟨hT, le_rfl⟩
  have hdist : dist (u ω T) (u ω' T) ≤ (L : ℝ) * dist (F ω) (F ω') := by
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖u ω T - u ω' T‖ ≤ ‖F ω - F ω'‖ * T * Real.exp (|b| * T) := hstab
      _ = (L : ℝ) * ‖F ω - F ω'‖ := by
        change ‖F ω - F ω'‖ * T * Real.exp (|b| * T) =
          (T * Real.exp (|b| * T)) * ‖F ω - F ω'‖
        ring
  rw [edist_dist, edist_dist, ENNReal.coe_nnreal_eq,
    ← ENNReal.ofReal_mul (show 0 ≤ (L : ℝ) from L.2)]
  exact ENNReal.ofReal_le_ofReal hdist

/-- The actual chosen classical endpoint is measurable on the enlarged window.
Only the source noise predicates, support threshold and smooth datum are inputs. -/
theorem smoothSolution_window_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {ρ : ParabolicSpace → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {ξ : Ω → SpaceTime → ℝ} (hξ : IsRegularisedNoise P W ρ ε ξ)
    {s t δ : ℝ} (hst : s ≤ t) (hδ : ε ^ 2 * mollifierTimeRadius ρ hρ < δ)
    (b : ℝ) (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x) :
    Measurable[enlargedNoiseWindowSigma P W s t δ]
      (fun ω => smoothSolution b (shiftForcing s (ξ ω))
        (isSmoothOnSpaceTime_shiftForcing (hξ.1 ω) s) x hx (t - s)) := by
  exact classicalEndpoint_measurable_of_restriction ξ hξ.1 b s (t - s)
    (sub_nonneg.mpr hst) x _
    (fun ω => smoothSolution_spec b _ _ x hx)
    (regularisedNoise_restriction_window_measurable P hW hρ hε hξ hδ)

/-- The same endpoint measurability in the negative-regularity state. -/
theorem smoothSolution_holder_window_measurable (η : NegExponent)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {ρ : ParabolicSpace → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {ξ : Ω → SpaceTime → ℝ} (hξ : IsRegularisedNoise P W ρ ε ξ)
    {s t δ : ℝ} (hst : s ≤ t) (hδ : ε ^ 2 * mollifierTimeRadius ρ hρ < δ)
    (b : ℝ) (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x) :
    Measurable[enlargedNoiseWindowSigma P W s t δ]
      (fun ω => toHolderBesov η (smoothSolution b (shiftForcing s (ξ ω))
        (isSmoothOnSpaceTime_shiftForcing (hξ.1 ω) s) x hx (t - s))) :=
  (lipschitzWith_toHolderBesov η).continuous.measurable.comp
    (smoothSolution_window_measurable P hW hρ hε hξ hst hδ b x hx)

end GlobalPhi43.Flow
