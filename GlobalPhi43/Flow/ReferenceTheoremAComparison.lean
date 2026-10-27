module

public import GlobalPhi43.Flow.ReferenceCompactLimit
public import GlobalPhi43.Flow.GlobalLifetime
public import GlobalPhi43.Flow.ClassicalTranslation

public noncomputable section

open MeasureTheory Set Metric Filter Topology RegularityStructures RegularityStructures.Phi43
open scoped ENNReal

namespace GlobalPhi43.Flow

/-- Identification with any Theorem-A limit of the reference regularisations
at a FIXED deterministic start. The comparison is almost sure for that start;
its null set is not added to the common reference event. All times are then
identified and A2 forces the Theorem-A lifetime to be infinite almost surely. -/
theorem reference_limit_global {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (N : ℕ) (hN : 5 ≤ N) (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ)
    (η : NegExponent) (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (hκη : κ.1 < -(1 / 2 : ℝ) - η)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
    (u : EventFlow (referenceEvent N κ ρ mass η ξ (fun ε hε => (hξ ε hε).1)) η
      (fun ω => dyadicLiftData N κ ρ mass η ξ (fun ε hε => (hξ ε hε).1) ω.val ω.property))
    (s : ℝ) (hs : 0 ≤ s) (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x)
    (U : ℝ → Ω → ℝ → C(Torus3, ℝ))
    (hU : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsClassicalSolution
      (mass + 3 * wickConstant ρ ε - 9 * sunsetConstant ρ ε)
      (shiftForcing s (ξ ε ω)) x (U ε ω))
    (τ : Ω → ℝ≥0∞) (v : Ω → ℝ → HolderBesov η) (hlim : IsPhi43Limit P η x U τ v) :
    (∀ᵐ ω ∂P, τ ω = ⊤) ∧
      ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → v ω t = u.value ω (s + t) s (toHolderBesov η x) := by
  apply ae_global_identification hlim
  · intro ω
    have hc : Continuous (fun t : ℝ => (s + t, toHolderBesov η x)) := by fun_prop
    exact (u.continuous_on ω s hs).comp hc.continuousOn
      (fun _ ht => ⟨le_add_of_nonneg_right ht, mem_univ _⟩)
  · intro T hT
    let hsmooth := fun ε hε => (hξ ε hε).1
    let E := referenceEvent N κ ρ mass η ξ hsmooth
    let F := fun n ω => referenceDyadicCurve ρ mass η ξ hsmooth s T x hx n ω
    let G := fun ω => u.elapsedPath ω s hs (toHolderBesov η x) T
    have hF (n : ℕ) (ω : Ω) (q : Icc (0 : ℝ) T) :
        F n ω q = toHolderBesov η (U (dyadicTailScale n) ω q.val) := by
      change toHolderBesov η (smoothSolution _ _ _ x hx q.val) = _
      exact congrArg (toHolderBesov η) (smoothSolution_eq_classical _ _ _ x hx
        (hU _ (dyadicTailScale_mem n) ω) q.property.1)
    have hevent := referenceEvent_measurable_measure_one P W hW N hN κ hκE
      ρ hρ mass η hη hκη ξ hξ
    have hfull : ∀ᵐ ω ∂P, ω ∈ E := (mem_ae_iff_prob_eq_one hevent.1).mpr hevent.2
    have hG : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (G ω)) := by
      filter_upwards [hfull] with ω hω
      exact referenceDyadicCurve_tendsto N κ ρ mass η ξ hsmooth u ⟨ω, hω⟩
        s T hs hT.le x hx
    have hid := ae_stoppedPath_eq hlim hT dyadicTailScale dyadicTailScale_tendsto_zero F hF G hG
    filter_upwards [hid] with ω hω hτ t ht
    exact hω hτ ⟨t, ht⟩

end GlobalPhi43.Flow
