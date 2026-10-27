module

public import GlobalPhi43.Flow.AllHorizonConvergence

public noncomputable section

open Set Metric Filter Topology RegularityStructures RegularityStructures.Phi43
open scoped ENNReal NNReal

namespace GlobalPhi43.Flow.FiniteLimitSystem

variable {N : ℕ} {κ : Kappa} {η : NegExponent} {a : ℕ → LiftData N κ}

theorem initial (sys : FiniteLimitSystem η a) (s : ℝ) (hs : 0 ≤ s) (x : HolderBesov η) :
    sys.value s 0 x = x := by
  let j := level s 0 x
  have hb := level_bounds s 0 x
  rw [sys.value_eq_chart (sys.chart j) s 0 x ⟨hs, hb.1⟩ ⟨le_rfl, hb.2.1⟩ hb.2.2]
  exact (sys.chart j).initial (by positivity) _ _

theorem tendsto_value (sys : FiniteLimitSystem η a) (s q : ℝ) (x : HolderBesov η)
    (hs : 0 ≤ s) (hq : 0 ≤ q) :
    Tendsto (fun n => sys.approximant n s q x) atTop (𝓝 (sys.value s q x)) := by
  exact (sys.uniform_on_box s q ‖x‖).tendsto_at
    (show (s, q, x) ∈ flowBox η s q ‖x‖ from ⟨⟨hs, le_rfl⟩, ⟨hq, le_rfl⟩, le_rfl⟩)

theorem continuous_on_chart (sys : FiniteLimitSystem η a) {S T L : ℝ}
    (c : FiniteLimitChart η a S T L) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) S) :
    ContinuousOn (fun p : ℝ × HolderBesov η => sys.value s p.1 p.2)
      (Icc (0 : ℝ) T ×ˢ closedBall (0 : HolderBesov η) L) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  let D := Icc (0 : ℝ) T ×ˢ closedBall (0 : HolderBesov η) L
  let f : D → Icc (0 : ℝ) T × StateBall η L := fun p =>
    (⟨p.val.1, p.property.1⟩, ⟨p.val.2, p.property.2⟩)
  have hf : Continuous f := by fun_prop
  have he : (fun p : D => sys.value s p.val.1 p.val.2) =
      fun p : D => c.limit (⟨s, hs⟩, (f p).2) (f p).1 := by
    funext p
    exact sys.value_eq_chart c _ _ _ hs p.property.1
      (by simpa only [mem_closedBall, dist_zero_right] using p.property.2)
  change Continuous (fun p : D => sys.value s p.val.1 p.val.2)
  rw [he]
  exact (c.joint ⟨s, hs⟩).comp hf

/-- Fixed-start joint continuity on the entire elapsed-time/data domain.
At a finite-chart boundary use a larger ball and horizon before taking neighborhoods. -/
theorem continuous_on (sys : FiniteLimitSystem η a) (s : ℝ) (hs : 0 ≤ s) :
    ContinuousOn (fun p : ℝ × HolderBesov η => sys.value s p.1 p.2)
      (Ici (0 : ℝ) ×ˢ univ) := by
  intro p hp
  obtain ⟨j, hj⟩ := exists_nat_gt (max s (max p.1 ‖p.2‖))
  have hs' : s ≤ (j : ℝ) + 1 := by linarith [le_max_left s (max p.1 ‖p.2‖)]
  have hq : p.1 < (j : ℝ) + 1 := by
    linarith [(le_max_left p.1 ‖p.2‖).trans (le_max_right s (max p.1 ‖p.2‖))]
  have hx : ‖p.2‖ < (j : ℝ) + 1 := by
    linarith [(le_max_right p.1 ‖p.2‖).trans (le_max_right s (max p.1 ‖p.2‖))]
  have hc := sys.continuous_on_chart (sys.chart j) s ⟨hs, hs'⟩ p
    ⟨⟨hp.1, hq.le⟩, by simpa only [mem_closedBall, dist_zero_right] using hx.le⟩
  apply hc.mono_of_mem_nhdsWithin
  have heq : ∀ᶠ z : ℝ × HolderBesov η in 𝓝 p, z.1 < (j : ℝ) + 1 :=
    continuous_fst.continuousAt.eventually (gt_mem_nhds hq)
  have hex : ∀ᶠ z : ℝ × HolderBesov η in 𝓝 p, ‖z.2‖ < (j : ℝ) + 1 :=
    (continuous_norm.comp continuous_snd).continuousAt.eventually (gt_mem_nhds hx)
  filter_upwards [heq.filter_mono nhdsWithin_le_nhds, hex.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hzq hzx hz
  exact ⟨⟨hz.1, hzq.le⟩, by simpa only [mem_closedBall, dist_zero_right] using hzx.le⟩

/-- Diagonal smooth-data/lift approximation converges in continuous path space
to the restriction of this very same all-horizon map. -/
theorem smooth_approx_on_chart (sys : FiniteLimitSystem η a) {S T L : ℝ}
    (c : FiniteLimitChart η a S T L) (s : Icc (0 : ℝ) S) (x : StateBall η L)
    (q : ℕ → smoothBall η L) (hq : Tendsto (fun n => (q n).val) atTop (𝓝 x)) :
    (∀ r : Icc (0 : ℝ) T, c.limit (s, x) r = sys.value s.val r.val x.val) ∧
    Tendsto (fun n => curveOnSmooth T (3 * (a n).constants.1 - 9 * (a n).constants.2)
      (shiftForcing s.val (a n).forcing) ((a n).shiftSmooth s.val) (q n))
      atTop (𝓝 (c.limit (s, x))) := by
  constructor
  · intro r
    exact (sys.value_eq_chart c _ _ _ s.property r.property
      (by simpa only [mem_closedBall, dist_zero_right] using x.property)).symm
  · exact localLimit_smooth_approx c.charts c.uniform c.lipschitz s x q hq

end GlobalPhi43.Flow.FiniteLimitSystem
