module

public import GlobalPhi43.Flow.AllHorizonLimit

public noncomputable section

open Set Metric Filter Topology RegularityStructures RegularityStructures.Phi43
open scoped ENNReal NNReal

namespace GlobalPhi43.Flow

/-- Rectangular start/elapsed-time/data domain; no compactness of the ball. -/
@[expose] def flowBox (η : NegExponent) (S T L : ℝ) : Set (ℝ × ℝ × HolderBesov η) :=
  {p | p.1 ∈ Icc (0 : ℝ) S ∧ p.2.1 ∈ Icc (0 : ℝ) T ∧ ‖p.2.2‖ ≤ L}

namespace FiniteLimitSystem

variable {N : ℕ} {κ : Kappa} {η : NegExponent} {a : ℕ → LiftData N κ}

/-- Uniform convergence of the one all-horizon approximant sequence on any
finite witness, including all start/data/time endpoints. -/
theorem uniform_on_chart (sys : FiniteLimitSystem η a) {S T L : ℝ}
    (c : FiniteLimitChart η a S T L) :
    TendstoUniformlyOn (fun n p => sys.approximant n p.1 p.2.1 p.2.2)
      (fun p => sys.value p.1 p.2.1 p.2.2) atTop (flowBox η S T L) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp c.uniform ε hε] with n hn p hp
  rcases hp with ⟨hs, hq, hx⟩
  rw [sys.value_eq_chart c _ _ _ hs hq hx, sys.approximant_eq_chart c n _ _ _ hs hq hx]
  let s : Icc (0 : ℝ) S := ⟨p.1, hs⟩
  let x : StateBall η L := ⟨p.2.2, by simpa only [mem_closedBall, dist_zero_right] using hx⟩
  exact (ContinuousMap.dist_apply_le_dist (f := c.limit (s, x))
    (g := (c.charts n s).path x) ⟨p.2.1, hq⟩).trans_lt (hn (s, x) (mem_univ _))

/-- Every bounded rectangle fits in a fixed member of the exhaustion. -/
theorem exists_cover (S T L : ℝ) : ∃ j : ℕ,
    S ≤ (j : ℝ) + 1 ∧ T ≤ (j : ℝ) + 1 ∧ L ≤ (j : ℝ) + 1 := by
  obtain ⟨j, hj⟩ := exists_nat_ge (max S (max T L))
  refine ⟨j, ?_, ?_, ?_⟩
  · linarith [le_max_left S (max T L)]
  · linarith [(le_max_left T L).trans (le_max_right S (max T L))]
  · linarith [(le_max_right T L).trans (le_max_right S (max T L))]

theorem uniform_on_box (sys : FiniteLimitSystem η a) (S T L : ℝ) :
    TendstoUniformlyOn (fun n p => sys.approximant n p.1 p.2.1 p.2.2)
      (fun p => sys.value p.1 p.2.1 p.2.2) atTop (flowBox η S T L) := by
  obtain ⟨j, hS, hT, hL⟩ := exists_cover S T L
  exact (sys.uniform_on_chart (sys.chart j)).mono (fun _ hp =>
    ⟨⟨hp.1.1, hp.1.2.trans hS⟩, ⟨hp.2.1.1, hp.2.1.2.trans hT⟩, hp.2.2.trans hL⟩)

end FiniteLimitSystem
end GlobalPhi43.Flow
