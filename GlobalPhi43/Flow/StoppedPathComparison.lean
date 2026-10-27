module

public import Phi43.Limit
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.ContinuousMap.Compact

public noncomputable section

open MeasureTheory Set Metric Filter Topology RegularityStructures RegularityStructures.Phi43
open scoped ENNReal

namespace GlobalPhi43.Flow

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {η : NegExponent}
  {x : C(Torus3, ℝ)} {U : ℝ → Ω → ℝ → C(Torus3, ℝ)}
  {τ : Ω → ℝ≥0∞} {v : Ω → ℝ → HolderBesov η}

/-- The Theorem-A path on a closed interval strictly before its lifetime,
and the zero path elsewhere. This selects no new exceptional event. -/
@[expose] def stoppedLimitPath (h : IsPhi43Limit P η x U τ v) (T : ℝ) (ω : Ω) :
    C(Icc (0 : ℝ) T, HolderBesov η) := by
  classical
  exact if hτ : ENNReal.ofReal T < τ ω then
    ⟨fun q => v ω q.val, (h.continuousOn ω).comp_continuous continuous_subtype_val
      (fun q => ⟨q.property.1, (ENNReal.ofReal_le_ofReal q.property.2).trans_lt hτ⟩)⟩
  else 0

@[expose] def stoppedApproxPath {T : ℝ} (τ : Ω → ℝ≥0∞)
    (F : ℕ → Ω → C(Icc (0 : ℝ) T, HolderBesov η)) (n : ℕ) (ω : Ω) :
    C(Icc (0 : ℝ) T, HolderBesov η) := by
  classical
  exact if ENNReal.ofReal T < τ ω then F n ω else 0

/-- A3 implies stopped path-space convergence in measure along every positive
scale sequence. No measurability of an additional selected path is assumed. -/
theorem stoppedPath_inMeasure (h : IsPhi43Limit P η x U τ v) {T : ℝ} (hT : 0 < T)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (F : ℕ → Ω → C(Icc (0 : ℝ) T, HolderBesov η))
    (hF : ∀ n ω q, F n ω q = toHolderBesov η (U (ε n) ω q.val)) :
    TendstoInMeasure P (stoppedApproxPath τ F) atTop (stoppedLimitPath h T) := by
  apply tendstoInMeasure_iff_dist.mpr
  intro δ hδ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ((h.converges T hT (δ / 2) (by positivity)).comp hε) (fun _ => bot_le) ?_
  intro n
  apply measure_mono
  intro ω hbad
  change δ ≤ dist (stoppedApproxPath τ F n ω) (stoppedLimitPath h T ω) at hbad
  by_cases hτ : ENNReal.ofReal T < τ ω
  · refine ⟨hτ, ?_⟩
    by_contra hn
    push Not at hn
    have hd : dist (F n ω) (stoppedLimitPath h T ω) ≤ δ / 2 := by
      apply (ContinuousMap.dist_le (by positivity)).mpr
      intro q
      rw [stoppedLimitPath, dite_eq_left hτ]
      change dist (F n ω q) (v ω q.val) ≤ δ / 2
      rw [hF n ω q, dist_eq_norm]
      exact hn q.val q.property
    have hb : δ ≤ dist (F n ω) (stoppedLimitPath h T ω) := by
      simpa only [stoppedApproxPath, ite_eq_left hτ] using hbad
    linarith
  · have hb : δ ≤ 0 := by
      simpa only [stoppedApproxPath, ite_eq_right hτ, stoppedLimitPath,
        dite_eq_right hτ, dist_self] using hbad
    exact ((not_le_of_gt hδ) hb).elim

/-- Identify the pathwise dyadic limit with Theorem A on each stopped compact
interval. Subsequence extraction in measure uses no supplied equality or new
start-indexed good event; all times in the interval agree on one null-set complement. -/
theorem ae_stoppedPath_eq (h : IsPhi43Limit P η x U τ v) {T : ℝ} (hT : 0 < T)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)))
    (F : ℕ → Ω → C(Icc (0 : ℝ) T, HolderBesov η))
    (hF : ∀ n ω q, F n ω q = toHolderBesov η (U (ε n) ω q.val))
    (G : Ω → C(Icc (0 : ℝ) T, HolderBesov η))
    (hG : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (G ω))) :
    ∀ᵐ ω ∂P, ENNReal.ofReal T < τ ω → ∀ q : Icc (0 : ℝ) T, v ω q.val = G ω q := by
  obtain ⟨ns, hns, hsub⟩ := (stoppedPath_inMeasure h hT ε hε F hF).exists_seq_tendsto_ae
  filter_upwards [hsub, hG] with ω hsub hG hτ q
  have hs : Tendsto (fun j => F (ns j) ω) atTop (𝓝 (stoppedLimitPath h T ω)) := by
    simpa only [stoppedApproxPath, ite_eq_left hτ] using hsub
  have he := tendsto_nhds_unique hs (hG.comp hns.tendsto_atTop)
  have hev := congrArg (fun f : C(Icc (0 : ℝ) T, HolderBesov η) => f q) he
  simpa only [stoppedLimitPath, dite_eq_left hτ, ContinuousMap.coe_mk] using hev

end GlobalPhi43.Flow
