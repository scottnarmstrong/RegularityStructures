module

public import GlobalPhi43.Flow.EventFlow
public import GlobalPhi43.Flow.ClassicalWindowMeasurable
public import GlobalPhi43.Flow.ClassicalStartContinuity

public noncomputable section

open Set Metric Filter Topology RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow.FiniteLimitSystem

/-- The existing completed approximant agrees with the actual chosen classical
solution on every smooth datum. This does not choose a second approximant. -/
theorem approximant_smooth {N : ℕ} {κ : Kappa} {η : NegExponent}
    {a : ℕ → LiftData N κ} (sys : FiniteLimitSystem η a)
    (n : ℕ) (s q : ℝ) (hs : 0 ≤ s) (hq : 0 ≤ q)
    (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x) :
    sys.approximant n s q (toHolderBesov η x) =
      toHolderBesov η (smoothSolution (3 * (a n).constants.1 - 9 * (a n).constants.2)
        (shiftForcing s (a n).forcing) ((a n).shiftSmooth s) x hx q) := by
  let j := level s q (toHolderBesov η x)
  let c := sys.chart j
  have hb := level_bounds s q (toHolderBesov η x)
  let z : smoothBall η ((j : ℝ) + 1) :=
    ⟨⟨toHolderBesov η x, by simpa only [mem_closedBall, dist_zero_right] using hb.2.2⟩,
      ⟨x, hx, rfl⟩⟩
  rw [sys.approximant_eq_chart c n s q _ ⟨hs, hb.1⟩ ⟨hq, hb.2.1⟩ hb.2.2]
  change (c.charts n ⟨s, hs, hb.1⟩).path z.val ⟨q, hq, hb.2.1⟩ = _
  rw [(c.charts n ⟨s, hs, hb.1⟩).smooth_agreement z]
  have he : smoothRepresentative z = x :=
    toHolderBesov_injective η (smoothRepresentative_spec z).2
  change toHolderBesov η (smoothSolution _ _ _ (smoothRepresentative z)
    (smoothRepresentative_spec z).1 q) = _
  exact congrArg (fun y : SmoothDatum => toHolderBesov η
    (smoothSolution (3 * (a n).constants.1 - 9 * (a n).constants.2)
      (shiftForcing s (a n).forcing) ((a n).shiftSmooth s) y.val y.property q))
    (show (⟨smoothRepresentative z, (smoothRepresentative_spec z).1⟩ : SmoothDatum) =
      ⟨x, hx⟩ from Subtype.ext he)

/-- Smooth-data classical endpoints converge to the same all-horizon map. -/
theorem tendsto_smooth_value {N : ℕ} {κ : Kappa} {η : NegExponent}
    {a : ℕ → LiftData N κ} (sys : FiniteLimitSystem η a)
    (s q : ℝ) (hs : 0 ≤ s) (hq : 0 ≤ q)
    (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x) :
    Tendsto (fun n => toHolderBesov η
      (smoothSolution (3 * (a n).constants.1 - 9 * (a n).constants.2)
        (shiftForcing s (a n).forcing) ((a n).shiftSmooth s) x hx q))
      atTop (𝓝 (sys.value s q (toHolderBesov η x))) := by
  simpa only [sys.approximant_smooth _ s q hs hq x hx] using
    sys.tendsto_value s q (toHolderBesov η x) hs hq

end GlobalPhi43.Flow.FiniteLimitSystem
