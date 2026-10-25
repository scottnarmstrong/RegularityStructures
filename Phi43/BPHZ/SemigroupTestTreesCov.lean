/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesBound

/-!
# Local and global majorants of a covariance against a semigroup test profile

* `semigroupDoubleBound_of_majorants`: if `|Φ| ≤ Ml` on the pairs with
  `s(u - x), s(v - x) ≤ 1` and `|Φ| ≤ Mg` on the other pairs, and `Ml`, `Mg` have double bounds
  `Il`, `Ig`, then `|Φ|` has the double bound `Il + Ig`.
* `SemigroupTestProfile.doubleBound_global`: for `lam ≤ 1` the global majorant
  `(s(u - x)^n + s(v - x)^n) (s(u - v)^(-e) + s(u - x)^(-a) + s(v - x)^(-a) + 1)` (with
  `0 ≤ e < 5`, `a < 5` and `n ≥ max e a`) has a double bound independent of `lam`.
-/

public section

open MeasureTheory

namespace RegularityStructures


theorem semigroupDoubleBound_of_majorants {x : SpaceTime} {g : SpaceTime → ℝ}
    (hg : Measurable g)
    {Φ Ml Mg : SpaceTime → SpaceTime → ℝ} {Il Ig : ℝ}
    (hΦ : AEStronglyMeasurable (fun w : SpaceTime × SpaceTime => Φ w.1 w.2) volume)
    (hMl : SemigroupDoubleBound g Ml Il) (hMg : SemigroupDoubleBound g Mg Ig)
    (hl0 : ∀ u v, 0 ≤ Ml u v) (hg0 : ∀ u v, 0 ≤ Mg u v)
    (hloc : ∀ᵐ w : SpaceTime × SpaceTime ∂volume, torusParabolicSize (w.1 - x) ≤ 1 →
      torusParabolicSize (w.2 - x) ≤ 1 → |Φ w.1 w.2| ≤ Ml w.1 w.2)
    (hglob : ∀ᵐ w : SpaceTime × SpaceTime ∂volume,
      ¬(torusParabolicSize (w.1 - x) ≤ 1 ∧ torusParabolicSize (w.2 - x) ≤ 1) →
        |Φ w.1 w.2| ≤ Mg w.1 w.2) :
    SemigroupDoubleBound g (fun u v => |Φ u v|) (Il + Ig) := by
  refine SemigroupDoubleBound.of_abs_le hg (hMl.add hMg) hΦ ?_
  filter_upwards [hloc, hglob] with w h1 h2
  by_cases hb : torusParabolicSize (w.1 - x) ≤ 1 ∧ torusParabolicSize (w.2 - x) ≤ 1
  · have := h1 hb.1 hb.2
    linarith [hg0 w.1 w.2]
  · have := h2 hb
    linarith [hl0 w.1 w.2]

namespace SemigroupTestProfile

variable {x : SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ} {g : SpaceTime → ℝ}

theorem doubleBound_global (h : SemigroupTestProfile x lam B Mom g) (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) {n e a : ℝ} (he0 : 0 ≤ e) (he5 : e < 5) (ha5 : a < 5)
    (hen : e ≤ n) (han : a ≤ n) :
    SemigroupDoubleBound g (semigroupTestGlobalMajorant x n e a)
      (semigroupTestGlobalConst B Mom n e a) := by
  have hn0 : 0 ≤ n := he0.trans hen
  have t1 := h.doubleBound_fst (ζ := n) (e := -e) (by linarith) (by linarith) hlam
  have t2 := h.doubleBound_snd (ζ := n) (e := -e) (by linarith) (by linarith) hlam
  have t3 := h.doubleBound_fst (ζ := n - a) (e := 0) (by linarith) (by norm_num) hlam
  have t4 := h.doubleBound_snd (ζ := n - a) (e := 0) (by linarith) (by norm_num) hlam
  have t5 := h.doubleBound_mul (a := -a) (b := n) (by linarith) (by linarith) hlam
  have t6 := h.doubleBound_mul (a := n) (b := -a) (by linarith) (by linarith) hlam
  have t7 := h.doubleBound_fst (ζ := n) (e := 0) (by linarith) (by norm_num) hlam
  have t8 := h.doubleBound_snd (ζ := n) (e := 0) (by linarith) (by norm_num) hlam
  have c1 := h.semigroupTestDoubleConst_nonneg hlam (ζ := n) (e := -e) (by linarith)
    (by linarith) (by linarith)
  have c3 := h.semigroupTestDoubleConst_nonneg hlam (ζ := n - a) (e := 0) (by linarith)
    (by norm_num) (by linarith)
  have c7 := h.semigroupTestDoubleConst_nonneg hlam (ζ := n) (e := 0) (by linarith)
    (by norm_num) (by linarith)
  have c5 := h.semigroupTestMomConst_nonneg hlam (a := -a) (by linarith)
  have c6 := h.semigroupTestMomConst_nonneg hlam (a := n) (by linarith)
  have l1 : lam ^ (n + -e) ≤ 1 := Real.rpow_le_one hlam.le hlam1 (by linarith)
  have l3 : lam ^ (n - a + 0) ≤ 1 := Real.rpow_le_one hlam.le hlam1 (by linarith)
  have l5 : lam ^ (-a + n) ≤ 1 := Real.rpow_le_one hlam.le hlam1 (by linarith)
  have l6 : lam ^ (n + -a) ≤ 1 := Real.rpow_le_one hlam.le hlam1 (by linarith)
  have l7 : lam ^ (n + 0) ≤ 1 := Real.rpow_le_one hlam.le hlam1 (by linarith)
  have s := ((((((t1.add t2).add t3).add t4).add t5).add t6).add t7).add t8
  refine s.mono_right ?_
  unfold semigroupTestGlobalConst
  have m1 := mul_le_of_le_one_right c1 l1
  have m3 := mul_le_of_le_one_right c3 l3
  have m7 := mul_le_of_le_one_right c7 l7
  have m5 := mul_le_of_le_one_right (mul_nonneg c5 c6) l5
  have m6 := mul_le_of_le_one_right (mul_nonneg c6 c5) l6
  linarith

end SemigroupTestProfile

end RegularityStructures

end
