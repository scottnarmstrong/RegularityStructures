module

public import GlobalPhi43.MW20.CubicTerminal

/-!
# MW20 Lemma 2.7: the cubic maximum principle

The estimate is independent of boundary values and holds at the terminal time.
The equation and bounded-forcing hypothesis are only required on the open
source cylinder. The explicit universal constant supplied here is 15.
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

/-- Negation commutes with the coordinate heat operator. -/
theorem sourceHeat_neg (u : ParabolicSpace → ℝ) (z : ParabolicSpace) :
    sourceHeat (fun y => -u y) z = -sourceHeat u z := by
  simp [sourceHeat, Finset.sum_neg_distrib]
  ring

/-- Signed cubic estimate with a cubed forcing bound. This is the direct
quantitative form of Lemma 2.7; the depth hypotheses allow any positive lower
bound on the parabolic distance from the initial and spatial boundary faces. -/
theorem source_cubic_abs_bound {u : ParabolicSpace → ℝ} (hu : SourceCubicRegularity u)
    {G : ℝ} (hG : 0 ≤ G)
    (hforce : ∀ z ∈ sourceCylinder 0, |sourceHeat u z + u z ^ 3| ≤ G ^ 3)
    (z : ParabolicSpace) {ρ : ℝ} (hρ : 0 < ρ) (ht : ρ ^ 2 ≤ z.1) (ht1 : z.1 ≤ 1)
    (hx : ∀ i, ρ ≤ 1 - z.2 i ∧ ρ ≤ 1 + z.2 i) :
    |u z| ≤ 15 * max (1 / ρ) G := by
  apply abs_le.mpr
  constructor
  · have hn : ∀ y ∈ sourceCylinder 0,
        sourceHeat (fun x => -u x) y + (-u y) ^ 3 ≤ G ^ 3 := by
      intro y hy
      rw [sourceHeat_neg]
      have hh := (abs_le.mp (hforce y hy)).1
      nlinarith
    have hb := source_cubic_upper_bound hu.neg hG hn z hρ ht ht1 hx
    linarith
  · exact source_cubic_upper_bound hu hG
      (fun y hy => (abs_le.mp (hforce y hy)).2) z hρ ht ht1 hx

/-- MW20 Lemma 2.7 for the actual source equation, with the bounded forcing
expressed by any nonnegative cubed bound `G³`. Smooth data satisfy the C²
premise; no derivative norm or boundary value occurs on the right. -/
theorem mw20_lemma_2_7_cubed {u g : ParabolicSpace → ℝ} (hu : SourceCubicRegularity u)
    {G : ℝ} (hG : 0 ≤ G)
    (hpde : ∀ z ∈ sourceCylinder 0, sourceHeat u z = -u z ^ 3 + g z)
    (hg : ∀ z ∈ sourceCylinder 0, |g z| ≤ G ^ 3)
    (z : ParabolicSpace) {ρ : ℝ} (hρ : 0 < ρ) (ht : ρ ^ 2 ≤ z.1) (ht1 : z.1 ≤ 1)
    (hx : ∀ i, ρ ≤ 1 - z.2 i ∧ ρ ≤ 1 + z.2 i) :
    |u z| ≤ 15 * max (1 / ρ) G := by
  apply source_cubic_abs_bound hu hG _ z hρ ht ht1 hx
  intro y hy
  have heq : sourceHeat u y + u y ^ 3 = g y := by rw [hpde y hy]; ring
  simpa only [heq] using hg y hy

end GlobalPhi43.MW20
