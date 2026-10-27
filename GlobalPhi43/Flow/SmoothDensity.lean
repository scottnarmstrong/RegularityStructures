module

public import GlobalPhi43.Compactness.Smoothing
public import RegularityStructures.Abstract.Datum.HeatLikeExt

public section

open Set Filter Topology
open RegularityStructures RegularityStructures.Datum
open RegularityStructures.PDE
open scoped ContDiff

namespace GlobalPhi43.Flow

/-- Continuous data have distinct images in the little Holder completion. -/
theorem toHolderBesov_injective (η : NegExponent) : Function.Injective (toHolderBesov η) := by
  intro f g h
  have hh : (fun t : ℝ => heatOp t f) =ᶠ[𝓝[>] 0] (fun t => heatOp t g) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have he := congrArg (fun z => heatExt η z t) h
    simpa only [heatExt_toHolderBesov η f ht, heatExt_toHolderBesov η g ht] using he
  have hf : Tendsto (fun t => heatOp t f) (𝓝[>] 0) (𝓝 (heatOp 0 f)) :=
    ((continuous_heatOp_left f).tendsto 0).mono_left nhdsWithin_le_nhds
  have hg : Tendsto (fun t => heatOp t g) (𝓝[>] 0) (𝓝 (heatOp 0 g)) :=
    ((continuous_heatOp_left g).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [heatOp_zero_left] at hf hg
  exact tendsto_nhds_unique (hf.congr' hh) hg

/-- Positive-time smoothing of a rough state is a smooth torus function. -/
theorem isSmoothOnTorus_heatExt (η : NegExponent) (z : HolderBesov η)
    {t : ℝ} (ht : 0 < t) : IsSmoothOnTorus (heatExt η z t) := by
  have hc : ContDiffOn ℝ ∞ (fun x : Fin 3 → ℝ => datumField η z (t, x)) univ :=
    (smoothPos_datumField η z).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ht)
  have he : (fun x : Fin 3 → ℝ => datumField η z (t, x)) =
      (fun x => heatExt η z t (torusProj x)) := by
    funext x
    exact datumField_of_pos η z ht
  rw [he] at hc
  exact contDiffOn_univ.mp hc

/-- Smooth data approximate every state without enlarging its closed eta-ball. -/
theorem exists_smooth_approx_ball (η : NegExponent) (z : HolderBesov η)
    {R ε : ℝ} (hz : ‖z‖ ≤ R) (hε : 0 < ε) :
    ∃ f : C(Torus3, ℝ), IsSmoothOnTorus f ∧ ‖toHolderBesov η f‖ ≤ R ∧
      dist (toHolderBesov η f) z < ε := by
  have hh := Metric.tendsto_nhds.mp (tendsto_toHolderBesov_heatExt η z) ε hε
  obtain ⟨t, hd, ht⟩ := (hh.and self_mem_nhdsWithin).exists
  exact ⟨heatExt η z t, isSmoothOnTorus_heatExt η z ht,
    (norm_toHolderBesov_heatExt_le η ht z).trans hz, hd⟩

end GlobalPhi43.Flow
