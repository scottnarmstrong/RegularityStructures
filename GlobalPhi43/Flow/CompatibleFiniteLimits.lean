module

public import GlobalPhi43.Flow.FiniteLimit

public noncomputable section

open Set Metric Filter Topology RegularityStructures RegularityStructures.Phi43
open scoped ENNReal NNReal

namespace GlobalPhi43.Flow

/-- The two analytic inputs, prior to any solution estimates. The later-state
bound holds for each admissible choice of persistence time. -/
structure FiniteAnalyticInputs {N : ℕ} {κ : Kappa} (η : NegExponent)
    (a : ℕ → LiftData N κ) : Prop where
  horizon : ∀ S T : ℝ, 0 ≤ S → 1 ≤ T → ∃ B : ℝ, 1 ≤ B ∧
    (∀ n, Statements.phi43Size κ η (T + S) (a n).model (a n).potential ≤ ENNReal.ofReal B) ∧
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀,
      Statements.phi43Dist κ η (T + S) (a n).model (a m).model
        (a n).potential (a m).potential ≤ ENNReal.ofReal ε
  later : ∀ S T L h₀ : ℝ, 0 ≤ S → 1 ≤ T → 1 ≤ L → 0 < h₀ → h₀ ≤ 1 →
    ∃ R : ℝ, 1 ≤ R ∧ ∀ n (s : Icc (0 : ℝ) S), LaterStateBound η L T h₀ R (a n) s.val

/-- A finite limit chart; its convergence and comparison fields are outputs of
`exists_finiteLimitChart`, not additional hypotheses on the lifts. -/
structure FiniteLimitChart {N : ℕ} {κ : Kappa} (η : NegExponent)
    (a : ℕ → LiftData N κ) (S T L : ℝ) where
  bound : ℝ≥0
  charts : ∀ n, ∀ s : Icc (0 : ℝ) S, LocalChart η L T bound (a n) s.val
  limit : Icc (0 : ℝ) S × StateBall η L → C(Icc (0 : ℝ) T, HolderBesov η)
  uniform : TendstoUniformlyOn (fun n p => (charts n p.1).path p.2) limit atTop univ
  lipschitz : ∀ s, LipschitzWith bound (fun x => limit (s, x))
  pair : ∀ n m (s : Icc (0 : ℝ) S) (x y : StateBall η L),
    edist ((charts n s).path x) ((charts m s).path y) ≤ bound *
      (edist x y + Statements.phi43Dist κ η (T + S)
        (a n).model (a m).model (a n).potential (a m).potential)
  initial : ∀ (hT : 0 ≤ T) s x, limit (s, x) ⟨0, le_rfl, hT⟩ = x.val
  joint : ∀ s, Continuous (fun p : Icc (0 : ℝ) T × StateBall η L => limit (s, p.2) p.1)

/-- Finite limit charts constructed from actual lifts and analytic inputs. -/
theorem exists_finiteLimitChart {κ : Kappa} (hκE : κ.1 ∉ Statements.excludedKappa)
    {N : ℕ} (hN : 5 ≤ N) {η : NegExponent}
    (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (hκη : κ.1 < -(1 / 2 : ℝ) - η) {a : ℕ → LiftData N κ}
    (inputs : FiniteAnalyticInputs η a) (S T L : ℝ)
    (hS : 0 ≤ S) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    Nonempty (FiniteLimitChart η a S T L) := by
  obtain ⟨B, hB, hsize, hD⟩ := inputs.horizon S T hS hT
  obtain ⟨h₀, hh₀, hh₀1, hrest⟩ :=
    exists_conditionalFiniteLimit hκE hN hη hκη T L B hT hL hB
  obtain ⟨R, hR, hlater⟩ := inputs.later S T L h₀ hS hT hL hh₀ hh₀1
  obtain ⟨_, _, K, _, mesh, hlimit⟩ := hrest R hR
  obtain ⟨U, F, hpair, hconv, hLip, hinit, hjoint⟩ :=
    hlimit S hS a (fun n s => ⟨hsize n, hlater n s⟩) hD
  exact ⟨⟨finiteRestartFactor K mesh.count, U, F, hconv, hLip, hpair,
    fun _ s x => hinit s x, hjoint⟩⟩

namespace FiniteLimitChart

@[expose] def value {N : ℕ} {κ : Kappa} {η : NegExponent} {a : ℕ → LiftData N κ}
    {S T L : ℝ} (c : FiniteLimitChart η a S T L) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) S)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) T) (x : HolderBesov η) (hx : ‖x‖ ≤ L) : HolderBesov η :=
  c.limit (⟨s, hs⟩, ⟨x, by simpa only [mem_closedBall, dist_zero_right] using hx⟩) ⟨q, hq⟩

/-- Arbitrary finite witnesses agree on overlaps, including different start
strips, size allowances, state radii, constants and mesh selections. -/
theorem value_eq {N : ℕ} {κ : Kappa} {η : NegExponent} {a : ℕ → LiftData N κ}
    {S T L S' T' L' : ℝ} (c : FiniteLimitChart η a S T L) (d : FiniteLimitChart η a S' T' L')
    (s q : ℝ) (x : HolderBesov η) (hs : s ∈ Icc (0 : ℝ) S) (hs' : s ∈ Icc (0 : ℝ) S')
    (hq : q ∈ Icc (0 : ℝ) T) (hq' : q ∈ Icc (0 : ℝ) T') (hx : ‖x‖ ≤ L) (hx' : ‖x‖ ≤ L') :
    c.value s hs q hq x hx = d.value s hs' q hq' x hx' := by
  let xc : StateBall η L := ⟨x, by simpa only [mem_closedBall, dist_zero_right] using hx⟩
  let xd : StateBall η L' := ⟨x, by simpa only [mem_closedBall, dist_zero_right] using hx'⟩
  have hc := ((continuous_eval_const (⟨q, hq⟩ : Icc (0 : ℝ) T)).tendsto
    (c.limit (⟨s, hs⟩, xc))).comp
      (c.uniform.tendsto_at (mem_univ ((⟨s, hs⟩ : Icc (0 : ℝ) S), xc)))
  have hd := ((continuous_eval_const (⟨q, hq'⟩ : Icc (0 : ℝ) T')).tendsto
    (d.limit (⟨s, hs'⟩, xd))).comp
      (d.uniform.tendsto_at (mem_univ ((⟨s, hs'⟩ : Icc (0 : ℝ) S'), xd)))
  have he (n : ℕ) : (c.charts n ⟨s, hs⟩).path xc ⟨q, hq⟩ =
      (d.charts n ⟨s, hs'⟩).path xd ⟨q, hq'⟩ := by
    let z : StateBall η (min L L') := ⟨x, by
      simpa only [mem_closedBall, dist_zero_right] using (le_min hx hx')⟩
    let r : Icc (0 : ℝ) (min T T') := ⟨q, hq.1, le_min hq.2 hq'.2⟩
    exact LocalChart.overlap_eq (c.charts n ⟨s, hs⟩) (d.charts n ⟨s, hs'⟩)
      (min_le_left _ _) (min_le_right _ _) (min_le_left _ _) (min_le_right _ _) z r
  exact tendsto_nhds_unique (hc.congr he) hd

end FiniteLimitChart
end GlobalPhi43.Flow
