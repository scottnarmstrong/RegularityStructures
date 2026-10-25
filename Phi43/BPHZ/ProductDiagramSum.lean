/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiChain
public import Phi43.BPHZ.TreeI3PsiTwoLevel
public import Phi43.BPHZ.SemigroupTestTreesSlabAt

/-!
# Weighted sums of centred parabolic powers

For a list `ps` of pairs `(weight, centre)` and an exponent `a`, `spSum a ps w` is the weighted sum
`∑ weight * s(centre - w)^(-a)`.  These are the majorants of the product diagrams.  The product of a
sum with a further centred power is dominated by a sum of the same type with exponent `a + e`
(`spSum_mul_singularPow_le`), and the product of two sums of total order `< 5` has integral over a
time slab bounded by the product of the total weights times a constant independent of the centres
(`singularIntLe_slabAt_spSum_mul_spSum`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The weighted sum `∑ weight * s(centre - w)^(-a)` over a list of `(weight, centre)` pairs. -/
def spSum (a : ℝ) (ps : List (ℝ × SpaceTime)) (w : SpaceTime) : ℝ :=
  (ps.map fun p => p.1 * singularPow a p.2 w).sum

/-- The total weight of a list of `(weight, centre)` pairs. -/
def spWeight (ps : List (ℝ × SpaceTime)) : ℝ := (ps.map Prod.fst).sum

/-- All weights nonnegative. -/
def SpNonneg (ps : List (ℝ × SpaceTime)) : Prop := ∀ p ∈ ps, 0 ≤ p.1

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

@[simp] theorem spSum_nil (a : ℝ) (w : SpaceTime) : spSum a [] w = 0 := by
  simp [spSum]

@[simp] theorem spSum_cons (a : ℝ) (p : ℝ × SpaceTime) (ps : List (ℝ × SpaceTime)) (w : SpaceTime) :
    spSum a (p :: ps) w = p.1 * singularPow a p.2 w + spSum a ps w := by
  simp [spSum]

@[simp] theorem spWeight_nil : spWeight [] = 0 := by
  simp [spWeight]

@[simp] theorem spWeight_cons (p : ℝ × SpaceTime) (ps : List (ℝ × SpaceTime)) :
    spWeight (p :: ps) = p.1 + spWeight ps := by
  simp [spWeight]

theorem SpNonneg.tail {p : ℝ × SpaceTime} {ps : List (ℝ × SpaceTime)}
    (h : SpNonneg (p :: ps)) : SpNonneg ps := fun q hq => h q (List.mem_cons_of_mem _ hq)

theorem SpNonneg.head {p : ℝ × SpaceTime} {ps : List (ℝ × SpaceTime)}
    (h : SpNonneg (p :: ps)) : 0 ≤ p.1 := h p (List.mem_cons_self)

theorem spWeight_nonneg {ps : List (ℝ × SpaceTime)} (h : SpNonneg ps) : 0 ≤ spWeight ps := by
  induction ps with
  | nil => simp
  | cons p ps ih => simpa using add_nonneg h.head (ih h.tail)

theorem spSum_nonneg {a : ℝ} {ps : List (ℝ × SpaceTime)} (h : SpNonneg ps) (w : SpaceTime) :
    0 ≤ spSum a ps w := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    rw [spSum_cons]
    exact add_nonneg (mul_nonneg h.head (singularPow_nonneg _ _ _)) (ih h.tail)

theorem measurable_spSum (a : ℝ) (ps : List (ℝ × SpaceTime)) : Measurable (spSum a ps) := by
  induction ps with
  | nil =>
    have : spSum a [] = fun _ => 0 := funext fun w => spSum_nil a w
    rw [this]
    exact measurable_const
  | cons p ps ih =>
    have : spSum a (p :: ps) = fun w => p.1 * singularPow a p.2 w + spSum a ps w :=
      funext fun w => spSum_cons a p ps w
    rw [this]
    exact (measurable_const.mul (measurable_singularPow a p.2)).add ih

/-- A weighted sum times a centred power is dominated by a weighted sum of order `a + e`. -/
theorem spSum_mul_singularPow_le {a e : ℝ} (ha : 0 ≤ a) (he : 0 ≤ e)
    {ps : List (ℝ × SpaceTime)} (hps : SpNonneg ps) (c : SpaceTime) {w : SpaceTime}
    (hpos : ∀ p ∈ ps, 0 < torusParabolicSize (p.2 - w)) (hc : 0 < torusParabolicSize (c - w)) :
    spSum a ps w * singularPow e c w ≤
      spSum (a + e) ps w + spWeight ps * singularPow (a + e) c w := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have h1 := ih hps.tail (fun q hq => hpos q (List.mem_cons_of_mem _ hq))
    have h2 := singularPow_mul_le ha he (hpos p List.mem_cons_self) hc
    have hp0 := hps.head
    have e1 : spSum a (p :: ps) w * singularPow e c w =
        p.1 * (singularPow a p.2 w * singularPow e c w) + spSum a ps w * singularPow e c w := by
      rw [spSum_cons]; ring
    rw [e1, spSum_cons, spWeight_cons]
    have h3 := mul_le_mul_of_nonneg_left h2 hp0
    nlinarith [h1, h3]

/-- The product of two weighted sums of total order `< 5` on a time slab has integral at most
the product of the total weights times a constant independent of the centres. -/
theorem singularIntLe_slabAt_spSum_mul_spSum {a b T : ℝ} (τ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < 5) (hT : 0 ≤ T) {ps qs : List (ℝ × SpaceTime)} (hps : SpNonneg ps)
    (hqs : SpNonneg qs) :
    SingularIntLe (Set.indicator {w : SpaceTime | |w.1 - τ| ≤ T}
      (fun w => spSum a ps w * spSum b qs w))
      (spWeight ps * spWeight qs * (2 * (80 / (5 - (a + b)) + 2 * T))) := by
  -- first a single power against a weighted sum
  have inner : ∀ (p : SpaceTime) (qs : List (ℝ × SpaceTime)), SpNonneg qs →
      SingularIntLe (Set.indicator {w : SpaceTime | |w.1 - τ| ≤ T}
        (fun w => singularPow a p w * spSum b qs w))
        (spWeight qs * (2 * (80 / (5 - (a + b)) + 2 * T))) := by
    intro p qs hqs
    induction qs with
    | nil =>
      simpa using (singularIntLe_zero)
    | cons q qs ih =>
      have h1 := singularIntLe_slabAt_mul_two τ ha hb hab hT p q.2
      have h2 := (h1.const_mul hqs.head).add (ih hqs.tail)
      refine (h2.mono_right (le_of_eq (by rw [spWeight_cons]; ring))).congr_fun
        (fun w => ?_)
      by_cases hw : w ∈ {w : SpaceTime | |w.1 - τ| ≤ T}
      · simp only [Set.indicator_of_mem hw, spSum_cons]; ring
      · simp only [Set.indicator_of_notMem hw]; ring
  induction ps with
  | nil => simpa using (singularIntLe_zero)
  | cons p ps ih =>
    have h1 := (inner p.2 qs hqs).const_mul hps.head
    have h2 := h1.add (ih hps.tail)
    refine (h2.mono_right (le_of_eq (by rw [spWeight_cons]; ring))).congr_fun (fun w => ?_)
    by_cases hw : w ∈ {w : SpaceTime | |w.1 - τ| ≤ T}
    · simp only [Set.indicator_of_mem hw, spSum_cons]; ring
    · simp only [Set.indicator_of_notMem hw]; ring

end RegularityStructures

end
