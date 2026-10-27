module

public import GlobalPhi43.Compactness.Norm
public import RegularityStructures.Abstract.Datum.HeatExtCont

@[expose] public noncomputable section

open Set RegularityStructures RegularityStructures.Datum RegularityStructures.PDE
open Filter Topology
open scoped ENNReal

namespace GlobalPhi43

/-- The continuous-function-valued extension realises the point probes. -/
theorem heatExt_apply_eq_heatAt (η : NegExponent) (s : Ioc (0 : ℝ) 1)
    (x : Torus3) (z : HolderBesov η) : heatExt η z s x = heatAt η s x z := by
  have he := heatAt_unique η s x (fun z => heatExt η z s x)
    ((continuous_eval_const x).comp (continuous_heatExt η s.2.1))
    (fun f => by rw [heatExt_toHolderBesov η f s.2.1, heatOp_eq_heatSemigroup s.2.1])
  exact congrFun he z

/-- The extended probes have the usual continuous-function supremum norm. -/
theorem iSup_enorm_heatAt (η : NegExponent) (s : Ioc (0 : ℝ) 1) (z : HolderBesov η) :
    (⨆ x, ‖heatAt η s x z‖ₑ) = ‖heatExt η z s‖ₑ := by
  rw [ContinuousMap.enorm_eq_iSup_enorm]
  exact iSup_congr fun x => congrArg (fun r : ℝ => ‖r‖ₑ)
    (heatExt_apply_eq_heatAt η s x z).symm

/-- Smoothing preserves every stronger extended-norm ball, with constant one. -/
theorem holderBesovENorm_heatExt_le_extNorm (η : NegExponent) (α : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (z : HolderBesov η) :
    holderBesovENorm α (heatExt η z δ) ≤ extNorm η α z := by
  refine iSup₂_le fun s hs => ?_
  refine le_iSup_of_le (⟨s, hs⟩ : Ioc (0 : ℝ) 1) ?_
  rw [iSup_enorm_heatSemigroup _ hs.1, iSup_enorm_heatAt]
  have he : heatOp s (heatExt η z δ) = heatOp δ (heatExt η z s) := by
    rw [heatOp_heatExt η z hs.1 hδ, heatOp_heatExt η z hδ hs.1, add_comm]
  rw [he]
  exact mul_le_mul_right (enorm_le_iff_norm_le.mpr (norm_heatOp_le _ _)) _

/-- Smoothing is a contraction on the source completion. -/
theorem norm_toHolderBesov_heatExt_le (η : NegExponent) {δ : ℝ} (hδ : 0 < δ)
    (z : HolderBesov η) : ‖toHolderBesov η (heatExt η z δ)‖ ≤ ‖z‖ := by
  rw [norm_toHolderBesov]
  have h := ENNReal.toReal_mono enorm_ne_top
    ((holderBesovENorm_heatExt_le_extNorm η η hδ z).trans (extNorm_self_le η z))
  simpa only [toReal_enorm] using h

/-- The source-completion heat operators are contractions for distance. -/
theorem dist_toHolderBesov_heatExt_le (η : NegExponent) {δ : ℝ} (hδ : 0 < δ)
    (z w : HolderBesov η) :
    dist (toHolderBesov η (heatExt η z δ)) (toHolderBesov η (heatExt η w δ)) ≤ dist z w := by
  rw [dist_eq_norm, ← toHolderBesov_sub, ← heatExt_sub, dist_eq_norm]
  exact norm_toHolderBesov_heatExt_le η hδ (z - w)

/-- Strong continuity of the heat operators on the little completion. -/
theorem tendsto_toHolderBesov_heatExt (η : NegExponent) (z : HolderBesov η) :
    Tendsto (fun δ : ℝ => toHolderBesov η (heatExt η z δ)) (𝓝[>] 0) (𝓝 z) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨f, hf⟩ := (denseRange_toHolderBesov η).exists_dist_lt z (by linarith : 0 < ε / 3)
  have hcont : Tendsto (fun δ : ℝ => toHolderBesov η (heatOp δ f)) (𝓝 0)
      (𝓝 (toHolderBesov η f)) := by
    have hc : Continuous (fun δ : ℝ => toHolderBesov η (heatOp δ f)) :=
      (lipschitzWith_toHolderBesov η).continuous.comp (continuous_heatOp_left f)
    have hh := hc.tendsto 0
    rw [heatOp_zero_left] at hh
    exact hh
  have hcont' : Tendsto (fun δ : ℝ => toHolderBesov η (heatOp δ f)) (𝓝[>] 0)
      (𝓝 (toHolderBesov η f)) := hcont.mono_left nhdsWithin_le_nhds
  have hevent := (Metric.tendsto_nhds.mp hcont') (ε / 3) (by linarith)
  filter_upwards [hevent, self_mem_nhdsWithin] with δ hδ hpos
  have hp : 0 < δ := hpos
  have hdist := dist_toHolderBesov_heatExt_le η hp z (toHolderBesov η f)
  rw [heatExt_toHolderBesov η f hp] at hdist
  calc
    dist (toHolderBesov η (heatExt η z δ)) z ≤
        dist (toHolderBesov η (heatExt η z δ)) (toHolderBesov η (heatOp δ f)) +
        dist (toHolderBesov η (heatOp δ f)) z := dist_triangle _ _ _
    _ ≤ dist z (toHolderBesov η f) +
        (dist (toHolderBesov η (heatOp δ f)) (toHolderBesov η f) + dist (toHolderBesov η f) z) :=
      add_le_add hdist (dist_triangle _ _ _)
    _ < ε := by
      have hf' := hf
      rw [dist_comm] at hf'
      linarith

end GlobalPhi43
