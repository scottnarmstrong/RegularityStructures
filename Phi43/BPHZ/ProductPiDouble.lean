/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesCov

/-!
# Double bounds for polynomially weighted covariance majorants

`productPolyMajorant x p e u v = (1 + s(u - x)²) (s(u - x)^p + s(v - x)^p) s(u - v)^(-e)`.
For a semigroup test profile of scale `lam ≤ 1` its double bound is
`(2 c(p, -e) + 3 c(p + 2, -e)) lam^(p - e)` for `p ≥ 0`, `0 ≤ e < 5`
(`SemigroupTestProfile.doubleBound_productPoly`): the polynomial growth is absorbed by the moments
of the profile.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- `(1 + s(u - x)²) (s(u - x)^p + s(v - x)^p) s(u - v)^(-e)`. -/
def productPolyMajorant (x : SpaceTime) (p e : ℝ) (u v : SpaceTime) : ℝ :=
  (1 + torusParabolicSize (u - x) ^ 2) *
    (torusParabolicSize (u - x) ^ p + torusParabolicSize (v - x) ^ p) *
      torusParabolicSize (u - v) ^ (-e)

/-- The constant of `SemigroupTestProfile.doubleBound_productPoly`. -/
def productPolyConst (B : ℝ) (Mom : ℝ → ℝ) (p e : ℝ) : ℝ :=
  2 * semigroupTestDoubleConst B Mom p (-e) + 3 * semigroupTestDoubleConst B Mom (p + 2) (-e)

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem productPolyMajorant_nonneg (x : SpaceTime) (p e : ℝ) (u v : SpaceTime) :
    0 ≤ productPolyMajorant x p e u v := by
  unfold productPolyMajorant
  have h1 := Real.rpow_nonneg (torusParabolicSize_nonneg (u - x)) p
  have h2 := Real.rpow_nonneg (torusParabolicSize_nonneg (v - x)) p
  have h3 := Real.rpow_nonneg (torusParabolicSize_nonneg (u - v)) (-e)
  have h4 := sq_nonneg (torusParabolicSize (u - x))
  positivity

theorem measurable_productPolyMajorant (x : SpaceTime) (p e : ℝ) :
    Measurable (fun w : SpaceTime × SpaceTime => productPolyMajorant x p e w.1 w.2) := by
  have hm := Phi43.measurable_torusParabolicSize
  unfold productPolyMajorant
  have a1 : Measurable fun w : SpaceTime × SpaceTime => torusParabolicSize (w.1 - x) :=
    hm.comp (measurable_fst.sub measurable_const)
  have a2 : Measurable fun w : SpaceTime × SpaceTime => torusParabolicSize (w.2 - x) :=
    hm.comp (measurable_snd.sub measurable_const)
  have a3 : Measurable fun w : SpaceTime × SpaceTime => torusParabolicSize (w.1 - w.2) :=
    hm.comp (measurable_fst.sub measurable_snd)
  exact ((measurable_const.add (a1.pow_const 2)).mul ((a1.pow_const p).add (a2.pow_const p))).mul
    (a3.pow_const _)

/-- `a² b^p ≤ a^(p+2) + b^(p+2)` for nonnegative `a, b`. -/
theorem sq_mul_rpow_le {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p) :
    a ^ 2 * b ^ p ≤ a ^ (p + 2) + b ^ (p + 2) := by
  have e1 : ∀ c : ℝ, 0 ≤ c → c ^ (p + 2) = c ^ p * c ^ 2 := by
    intro c hc
    rw [Real.rpow_add' hc (by linarith)]
    norm_num
  have n1 := Real.rpow_nonneg ha p
  have n2 := Real.rpow_nonneg hb p
  have s1 := sq_nonneg a
  have s2 := sq_nonneg b
  rcases le_total a b with h | h
  · have : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha h 2
    rw [e1 a ha, e1 b hb]
    nlinarith [mul_nonneg n1 s1, mul_le_mul_of_nonneg_left this n2]
  · have : b ^ p ≤ a ^ p := Real.rpow_le_rpow hb h hp
    rw [e1 a ha, e1 b hb]
    nlinarith [mul_nonneg n2 s2, mul_le_mul_of_nonneg_left this s1]

namespace SemigroupTestProfile

variable {x : SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ} {g : SpaceTime → ℝ}

/-- **Double bound of the polynomially weighted majorant.** -/
theorem doubleBound_productPoly (h : SemigroupTestProfile x lam B Mom g) (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) {p e : ℝ} (hp : 0 ≤ p) (he5 : e < 5) :
    SemigroupDoubleBound g (productPolyMajorant x p e)
      (productPolyConst B Mom p e * lam ^ (p - e)) := by
  have t1 := h.doubleBound_fst (ζ := p) (e := -e) (by linarith) (by linarith) hlam
  have t2 := h.doubleBound_snd (ζ := p) (e := -e) (by linarith) (by linarith) hlam
  have t3 := h.doubleBound_fst (ζ := p + 2) (e := -e) (by linarith) (by linarith) hlam
  have t4 := h.doubleBound_snd (ζ := p + 2) (e := -e) (by linarith) (by linarith) hlam
  have s := (((t1.add t2).add (t3.const_mul (c := 2) (by norm_num))).add t4)
  have c1 := h.semigroupTestDoubleConst_nonneg hlam (ζ := p) (e := -e) (by linarith)
    (by linarith) (by linarith)
  have c3 := h.semigroupTestDoubleConst_nonneg hlam (ζ := p + 2) (e := -e) (by linarith)
    (by linarith) (by linarith)
  have l3 : lam ^ (p + 2 + -e) ≤ lam ^ (p - e) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have l0 : 0 ≤ lam ^ (p + 2 + -e) := Real.rpow_nonneg hlam.le _
  have e1 : p + -e = p - e := by ring
  have m3 := mul_le_mul_of_nonneg_left l3 c3
  have hGdb : SemigroupDoubleBound g (fun u v =>
      (torusParabolicSize (u - x) ^ p * torusParabolicSize (u - v) ^ (-e) +
        torusParabolicSize (v - x) ^ p * torusParabolicSize (u - v) ^ (-e)) +
        2 * (torusParabolicSize (u - x) ^ (p + 2) * torusParabolicSize (u - v) ^ (-e)) +
        torusParabolicSize (v - x) ^ (p + 2) * torusParabolicSize (u - v) ^ (-e))
      (productPolyConst B Mom p e * lam ^ (p - e)) := by
    refine s.mono_right ?_
    rw [e1]
    unfold productPolyConst
    nlinarith [m3, mul_nonneg c1 (Real.rpow_nonneg hlam.le (p - e))]
  have key := SemigroupDoubleBound.of_abs_le h.measurable hGdb
    (F := fun u v => productPolyMajorant x p e u v)
    (measurable_productPolyMajorant x p e).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => by
      have hnn := productPolyMajorant_nonneg x p e w.1 w.2
      rw [abs_of_nonneg hnn]
      unfold productPolyMajorant
      set a := torusParabolicSize (w.1 - x) with ha
      set b := torusParabolicSize (w.2 - x) with hb
      set d := torusParabolicSize (w.1 - w.2) ^ (-e) with hd
      have ha0 : 0 ≤ a := torusParabolicSize_nonneg _
      have hb0 : 0 ≤ b := torusParabolicSize_nonneg _
      have hd0 : 0 ≤ d := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
      have ha2 : a ^ 2 * a ^ p = a ^ (p + 2) := by
        rw [Real.rpow_add' ha0 (by linarith), mul_comm]
        norm_num
      have hk := mul_le_mul_of_nonneg_right (sq_mul_rpow_le ha0 hb0 hp) hd0
      calc (1 + a ^ 2) * (a ^ p + b ^ p) * d
          = a ^ p * d + b ^ p * d + (a ^ 2 * a ^ p) * d + (a ^ 2 * b ^ p) * d := by ring
        _ ≤ _ := by rw [ha2]; nlinarith [hk])
  have e2 : (fun u v => |productPolyMajorant x p e u v|) = productPolyMajorant x p e :=
    funext fun u => funext fun v => abs_of_nonneg (productPolyMajorant_nonneg x p e u v)
  rw [e2] at key
  exact key

end SemigroupTestProfile

end RegularityStructures

end
