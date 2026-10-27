module

public import GlobalPhi43.Flow.EventFlowRestart
public import GlobalPhi43.Flow.WindowLimitMeasurable

public noncomputable section

open MeasureTheory Set Metric Filter Topology RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

/-- The existing global path in elapsed-time coordinates on a closed interval. -/
@[expose] def EventFlow.elapsedPath {Ω : Type*} {N : ℕ} {κ : Kappa} {η : NegExponent}
    {E : Set Ω} {A : E → ℕ → LiftData N κ} (u : EventFlow E η A)
    (ω : Ω) (s : ℝ) (hs : 0 ≤ s) (x : HolderBesov η) (T : ℝ) :
    C(Icc (0 : ℝ) T, HolderBesov η) where
  toFun q := u.value ω (s + q.val) s x
  continuous_toFun := by
    have hc : Continuous (fun q : Icc (0 : ℝ) T => (s + q.val, x)) := by fun_prop
    exact (u.continuous_on ω s hs).comp_continuous hc
      (fun q => ⟨le_add_of_nonneg_right q.property.1, mem_univ _⟩)

/-- Actual classical dyadic curves, with the original mass/counterterm convention. -/
@[expose] def referenceDyadicCurve {Ω : Type*} (ρ : ParabolicSpace → ℝ) (mass : ℝ)
    (η : NegExponent) (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hsmooth : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
    (s T : ℝ) (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x) (n : ℕ) (ω : Ω) :
    C(Icc (0 : ℝ) T, HolderBesov η) :=
  smoothCurve η T (mass + 3 * wickConstant ρ (dyadicTailScale n) - 9 * sunsetConstant ρ (dyadicTailScale n))
    (shiftForcing s (ξ (dyadicTailScale n) ω))
    (isSmoothOnSpaceTime_shiftForcing (hsmooth _ (dyadicTailScale_mem n) ω) s) x hx

theorem dyadicTailScale_tendsto_zero : Tendsto dyadicTailScale atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num)).comp (tendsto_add_atTop_nat 1)
  · exact Eventually.of_forall (fun n => (dyadicTailScale_mem n).1)

/-- Path-space convergence of the actual reference classical curves to the
same constructed map. No new curve, event or probability limit is assumed. -/
theorem referenceDyadicCurve_tendsto {Ω : Type*} (N : ℕ) (κ : Kappa)
    (ρ : ParabolicSpace → ℝ) (mass : ℝ) (η : NegExponent)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hsmooth : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsSmoothOnSpaceTime (ξ ε ω))
    (u : EventFlow (referenceEvent N κ ρ mass η ξ hsmooth) η
      (fun ω => dyadicLiftData N κ ρ mass η ξ hsmooth ω.val ω.property))
    (ω : referenceEvent N κ ρ mass η ξ hsmooth)
    (s T : ℝ) (hs : 0 ≤ s) (_hT : 0 ≤ T) (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x) :
    Tendsto (fun n => referenceDyadicCurve ρ mass η ξ hsmooth s T x hx n ω.val)
      atTop (𝓝 (u.elapsedPath ω.val s hs (toHolderBesov η x) T)) := by
  let sys := u.system ω
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp
    (sys.uniform_on_box s T ‖toHolderBesov η x‖) δ hδ] with n hn
  apply (ContinuousMap.dist_lt_iff hδ).mpr
  intro q
  have hp := hn (s, q.val, toHolderBesov η x)
    (show (s, q.val, toHolderBesov η x) ∈ flowBox η s T ‖toHolderBesov η x‖ from
      ⟨⟨hs, le_rfl⟩, q.property, le_rfl⟩)
  have hf : referenceDyadicCurve ρ mass η ξ hsmooth s T x hx n ω.val q =
      sys.approximant n s q.val (toHolderBesov η x) := by
    rw [sys.approximant_smooth n s q.val hs q.property.1 x hx]
    have hb : 3 * (dyadicLiftData N κ ρ mass η ξ hsmooth ω.val ω.property n).constants.1 -
        9 * (dyadicLiftData N κ ρ mass η ξ hsmooth ω.val ω.property n).constants.2 =
        mass + 3 * wickConstant ρ (dyadicTailScale n) - 9 * sunsetConstant ρ (dyadicTailScale n) := by
      change 3 * (wickConstant ρ (dyadicTailScale n) + mass / 3) -
        9 * (sunsetConstant ρ (dyadicTailScale n) + 0) = _
      ring
    rw [hb]
    rfl
  change dist (referenceDyadicCurve ρ mass η ξ hsmooth s T x hx n ω.val q)
    (u.value ω.val (s + q.val) s (toHolderBesov η x)) < δ
  rw [hf, u.value_on ω, FiniteLimitSystem.evolution, add_sub_cancel_left, dist_comm]
  exact hp

end GlobalPhi43.Flow
