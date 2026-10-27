module

public import GlobalPhi43Statements.Defs.Characterisations
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

@[expose] public noncomputable section

open Set RegularityStructures TopologicalSpace
open scoped ENNReal

namespace GlobalPhi43

/-- Heat probes commute with the canonical exponent embedding. -/
theorem heatAt_holderBesovEmbed (η γ : NegExponent) (h : (η : ℝ) ≤ γ)
    (s : Ioc (0 : ℝ) 1) (x : Torus3) (z : HolderBesov γ) :
    heatAt η s x (holderBesovEmbed η γ h z) = heatAt γ s x z := by
  have heq := heatAt_unique γ s x
    (fun z => heatAt η s x (holderBesovEmbed η γ h z))
    ((continuous_heatAt η s x).comp (continuous_holderBesovEmbed η γ h))
    (fun f => by rw [holderBesovEmbed_toHolderBesov, heatAt_toHolderBesov])
  exact congrFun heq z

/-- Extended heat-probe norms are independent of the source completion. -/
theorem extNorm_holderBesovEmbed (η γ : NegExponent) (h : (η : ℝ) ≤ γ)
    (α : ℝ) (z : HolderBesov γ) :
    extNorm η α (holderBesovEmbed η γ h z) = extNorm γ α z := by
  simp only [extNorm, heatAt_holderBesovEmbed]

/-- Monotonicity of the extended norm in its probe exponent. -/
theorem extNorm_mono (η : NegExponent) {α β : ℝ} (h : α ≤ β) (z : HolderBesov η) :
    extNorm η α z ≤ extNorm η β z := by
  unfold extNorm
  refine iSup_mono fun s => mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  exact Real.rpow_le_rpow_of_exponent_ge s.2.1 s.2.2 (by linarith)

/-- Sublevels of the extended norm are closed in the target completion. -/
theorem isClosed_extNorm_sublevel (η : NegExponent) (α : ℝ) (M : ℝ≥0∞) :
    IsClosed {z : HolderBesov η | extNorm η α z ≤ M} :=
  (lowerSemicontinuous_extNorm η α).isClosed_preimage M

/-- The map from continuous functions to the little completion is a contraction. -/
theorem lipschitzWith_toHolderBesov (η : NegExponent) :
    LipschitzWith 1 (toHolderBesov η) := by
  refine LipschitzWith.of_dist_le_mul fun f g => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, ← toHolderBesov_sub, norm_toHolderBesov,
    dist_eq_norm]
  exact (ENNReal.toReal_mono (enorm_ne_top) (holderBesovENorm_le η.2.le (f - g))).trans_eq
    (by simp)

/-- The continuous functions have dense image in the little completion. -/
theorem denseRange_toHolderBesov (η : NegExponent) : DenseRange (toHolderBesov η) :=
  @UniformSpace.Completion.denseRange_coe (HolderBesovPre η) inferInstance

/-- Separability descends from the supremum-norm space of continuous functions. -/
instance holderBesov_separableSpace (η : NegExponent) : SeparableSpace (HolderBesov η) :=
  (denseRange_toHolderBesov η).separableSpace (lipschitzWith_toHolderBesov η).continuous

/-- The little completion is Polish with its existing norm topology. -/
instance holderBesov_polishSpace (η : NegExponent) : PolishSpace (HolderBesov η) := by
  infer_instance

end GlobalPhi43
