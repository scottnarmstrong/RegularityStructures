module

public import GlobalPhi43.Flow.FiniteChartCompatibility

public noncomputable section

open Set Metric Filter Topology RegularityStructures RegularityStructures.Phi43
open scoped ENNReal NNReal

namespace GlobalPhi43.Flow

/-- A fixed countable cofinal family. Compatibility is proved, not a field. -/
structure FiniteLimitSystem {N : ℕ} {κ : Kappa} (η : NegExponent) (a : ℕ → LiftData N κ) where
  chart : ∀ j : ℕ, FiniteLimitChart η a (j + 1) (j + 1) (j + 1)

/-- The system is produced from the actual family and analytic inputs, with no
path estimate, path limit or inter-chart compatibility hypothesis. -/
theorem exists_finiteLimitSystem {κ : Kappa} (hκE : κ.1 ∉ Statements.excludedKappa)
    {N : ℕ} (hN : 5 ≤ N) {η : NegExponent}
    (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (hκη : κ.1 < -(1 / 2 : ℝ) - η) {a : ℕ → LiftData N κ}
    (inputs : FiniteAnalyticInputs η a) : Nonempty (FiniteLimitSystem η a) := by
  exact ⟨⟨fun j => Classical.choice (exists_finiteLimitChart hκE hN hη hκη inputs
    (j + 1) (j + 1) (j + 1) (by positivity)
    (by linarith [Nat.cast_nonneg (α := ℝ) j])
    (by linarith [Nat.cast_nonneg (α := ℝ) j]))⟩⟩

namespace FiniteLimitSystem

@[expose] def level {η : NegExponent} (s q : ℝ) (x : HolderBesov η) : ℕ :=
  Nat.ceil (max s (max q ‖x‖))

theorem level_bounds {η : NegExponent} (s q : ℝ) (x : HolderBesov η) :
    s ≤ (level s q x : ℝ) + 1 ∧ q ≤ (level s q x : ℝ) + 1 ∧
      ‖x‖ ≤ (level s q x : ℝ) + 1 := by
  have hm : max s (max q ‖x‖) ≤ (level s q x : ℝ) := Nat.le_ceil _
  constructor
  · linarith [le_max_left s (max q ‖x‖)]
  constructor
  · linarith [(le_max_left q ‖x‖).trans (le_max_right s (max q ‖x‖))]
  · linarith [(le_max_right q ‖x‖).trans (le_max_right s (max q ‖x‖))]

variable {N : ℕ} {κ : Kappa} {η : NegExponent} {a : ℕ → LiftData N κ}

/-- One elapsed-time map on all starts and data, using deterministic exhaustion. -/
@[expose] def value (sys : FiniteLimitSystem η a) (s q : ℝ) (x : HolderBesov η) : HolderBesov η :=
  if h : 0 ≤ s ∧ 0 ≤ q then
    (sys.chart (level s q x)).value s ⟨h.1, (level_bounds s q x).1⟩
      q ⟨h.2, (level_bounds s q x).2.1⟩ x (level_bounds s q x).2.2
  else x

@[expose] def approximant (sys : FiniteLimitSystem η a) (n : ℕ)
    (s q : ℝ) (x : HolderBesov η) : HolderBesov η :=
  if h : 0 ≤ s ∧ 0 ≤ q then
    (sys.chart (level s q x)).approximant n s ⟨h.1, (level_bounds s q x).1⟩
      q ⟨h.2, (level_bounds s q x).2.1⟩ x (level_bounds s q x).2.2
  else x

/-- Agreement with every finite witness, not just the selected exhaustion. -/
theorem value_eq_chart (sys : FiniteLimitSystem η a) {S T L : ℝ}
    (c : FiniteLimitChart η a S T L) (s q : ℝ) (x : HolderBesov η)
    (hs : s ∈ Icc (0 : ℝ) S) (hq : q ∈ Icc (0 : ℝ) T) (hx : ‖x‖ ≤ L) :
    sys.value s q x = c.value s hs q hq x hx := by
  rw [value, dite_eq_left ⟨hs.1, hq.1⟩]
  exact FiniteLimitChart.value_eq _ c s q x _ hs _ hq _ hx

theorem approximant_eq_chart (sys : FiniteLimitSystem η a) {S T L : ℝ}
    (c : FiniteLimitChart η a S T L) (n : ℕ) (s q : ℝ) (x : HolderBesov η)
    (hs : s ∈ Icc (0 : ℝ) S) (hq : q ∈ Icc (0 : ℝ) T) (hx : ‖x‖ ≤ L) :
    sys.approximant n s q x = c.approximant n s hs q hq x hx := by
  rw [approximant, dite_eq_left ⟨hs.1, hq.1⟩]
  exact FiniteLimitChart.approximant_eq _ c n s q x _ hs _ hq _ hx

/-- Absolute-time convention; no restart/cocycle assertion is implicit here. -/
@[expose] def evolution (sys : FiniteLimitSystem η a) (t s : ℝ) (x : HolderBesov η) :=
  sys.value s (t - s) x

end FiniteLimitSystem
end GlobalPhi43.Flow
