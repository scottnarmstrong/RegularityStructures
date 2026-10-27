module

public import GlobalPhi43.Flow.CompatibleFiniteLimits

public noncomputable section

open Set Metric RegularityStructures RegularityStructures.Phi43
open scoped ENNReal NNReal

namespace GlobalPhi43.Flow.FiniteLimitChart

/-- Evaluate the once-selected completed approximant on raw coordinates. -/
@[expose] def approximant {N : ℕ} {κ : Kappa} {η : NegExponent} {a : ℕ → LiftData N κ}
    {S T L : ℝ} (c : FiniteLimitChart η a S T L) (n : ℕ)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) S) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) T)
    (x : HolderBesov η) (hx : ‖x‖ ≤ L) : HolderBesov η :=
  (c.charts n ⟨s, hs⟩).path
    ⟨x, by simpa only [mem_closedBall, dist_zero_right] using hx⟩ ⟨q, hq⟩

/-- Independence of finite witnesses already holds before taking the lift limit. -/
theorem approximant_eq {N : ℕ} {κ : Kappa} {η : NegExponent} {a : ℕ → LiftData N κ}
    {S T L S' T' L' : ℝ} (c : FiniteLimitChart η a S T L) (d : FiniteLimitChart η a S' T' L')
    (n : ℕ) (s q : ℝ) (x : HolderBesov η)
    (hs : s ∈ Icc (0 : ℝ) S) (hs' : s ∈ Icc (0 : ℝ) S')
    (hq : q ∈ Icc (0 : ℝ) T) (hq' : q ∈ Icc (0 : ℝ) T') (hx : ‖x‖ ≤ L) (hx' : ‖x‖ ≤ L') :
    c.approximant n s hs q hq x hx = d.approximant n s hs' q hq' x hx' := by
  let z : StateBall η (min L L') := ⟨x, by
    simpa only [mem_closedBall, dist_zero_right] using (le_min hx hx')⟩
  let r : Icc (0 : ℝ) (min T T') := ⟨q, hq.1, le_min hq.2 hq'.2⟩
  exact LocalChart.overlap_eq (c.charts n ⟨s, hs⟩) (d.charts n ⟨s, hs'⟩)
    (min_le_left _ _) (min_le_right _ _) (min_le_left _ _) (min_le_right _ _) z r

end GlobalPhi43.Flow.FiniteLimitChart
