/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreePsiBallMass
public import RegularityStructures.Probability.SpaceTimeMeasure

/-!
# Profiles of semigroup test functions on space-time

A *semigroup test profile* at scale `lam` and base point `x` is a measurable function
`g : ℝ × T³ → ℝ` that is bounded by `B lam⁻⁵` and whose absolute moments
`∫ |g| s(· - x)^r` are integrable and at most `Mom r lam^r` for every `r ≥ 0`.  Here
`s = torusParabolicSize`.  This is the abstract shape of the periodised semigroup kernel
`q^♯_t(x, ·)`, `lam = t^(1/4)`, which has a rapidly decaying (non-compactly supported) tail.

The two pieces of information (sup bound and moments) suffice for all the weighted integral bounds
of the chaos reduction:

* `SemigroupTestProfile.integral_rpow_le`: `∫ |g| s(· - x)^a ≤ C lam^a` for every `a > -5`;
* `SemigroupTestProfile.integral_mul_rpow_sub_le`: `∫ |g v| s(u - v)^(-q) dv ≤ C lam^(-q)` for
  `0 < q < 5`, uniformly in `u`.

For negative exponents the singularity is integrated against the sup bound on the ball
`s ≤ lam`, and the exterior is controlled by `lam^(-p)` times the `L¹` norm.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures

/-- A semigroup test profile at scale `lam > 0` and base point `x`: measurable, bounded by
`B lam⁻⁵`, with integrable absolute moments `∫ |g| s(· - x)^r ≤ Mom r lam^r`, `r ≥ 0`. -/
structure SemigroupTestProfile (x : SpaceTime) (lam B : ℝ) (Mom : ℝ → ℝ)
    (g : SpaceTime → ℝ) : Prop where
  measurable : Measurable g
  abs_le : ∀ u, |g u| ≤ B * (lam ^ 5)⁻¹
  integrable_moment : ∀ r : ℝ, 0 ≤ r →
    Integrable (fun u => |g u| * torusParabolicSize (u - x) ^ r)
  integral_moment_le : ∀ r : ℝ, 0 ≤ r →
    ∫ u, |g u| * torusParabolicSize (u - x) ^ r ≤ Mom r * lam ^ r

/-- The constant of `SemigroupTestProfile.integral_rpow_le`. -/
def semigroupTestMomConst (B : ℝ) (Mom : ℝ → ℝ) (a : ℝ) : ℝ :=
  if 0 ≤ a then Mom a else B * (80 / (5 + a)) + Mom 0

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

variable {x : SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ} {g : SpaceTime → ℝ}

namespace SemigroupTestProfile

theorem measurable_abs (h : SemigroupTestProfile x lam B Mom g) :
    Measurable (fun u => |g u|) :=
  continuous_abs.measurable.comp h.measurable

theorem integrable_abs (h : SemigroupTestProfile x lam B Mom g) :
    Integrable (fun u => |g u|) := by
  simpa using h.integrable_moment 0 le_rfl

theorem integrable (h : SemigroupTestProfile x lam B Mom g) : Integrable g :=
  (integrable_norm_iff h.measurable.aestronglyMeasurable).1 (by simpa using h.integrable_abs)

theorem integral_abs_le (h : SemigroupTestProfile x lam B Mom g) :
    ∫ u, |g u| ≤ Mom 0 := by
  simpa using h.integral_moment_le 0 le_rfl

theorem const_nonneg (h : SemigroupTestProfile x lam B Mom g) (hlam : 0 < lam) : 0 ≤ B := by
  have h0 := (abs_nonneg (g x)).trans (h.abs_le x)
  have hp : 0 < (lam ^ 5)⁻¹ := by positivity
  exact nonneg_of_mul_nonneg_left h0 hp

theorem mom_zero_nonneg (h : SemigroupTestProfile x lam B Mom g) : 0 ≤ Mom 0 :=
  (integral_nonneg fun _ => abs_nonneg _).trans h.integral_abs_le

theorem mom_nonneg (h : SemigroupTestProfile x lam B Mom g) (hlam : 0 < lam) {r : ℝ}
    (hr : 0 ≤ r) : 0 ≤ Mom r := by
  have h1 := h.integral_moment_le r hr
  have h0 : 0 ≤ ∫ u, |g u| * torusParabolicSize (u - x) ^ r :=
    integral_nonneg fun u => mul_nonneg (abs_nonneg _)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have hlp : 0 < lam ^ r := Real.rpow_pos_of_pos hlam _
  by_contra hneg
  nlinarith [mul_neg_of_neg_of_pos (not_le.1 hneg) hlp]

/-- The pointwise comparison of a negative power with its localisation. -/
theorem rpow_neg_le_localWeight_add {p lam : ℝ} (hp : 0 < p) (hlam : 0 < lam)
    (z : SpaceTime) :
    torusParabolicSize z ^ (-p) ≤ singularLocalWeight p lam z + lam ^ (-p) := by
  have hs := singularLocalWeight_nonneg p lam z
  have hlp : 0 ≤ lam ^ (-p) := Real.rpow_nonneg hlam.le _
  rcases (torusParabolicSize_nonneg z).eq_or_lt with h0 | hz
  · rw [← h0, Real.zero_rpow (by linarith)]
    linarith
  · by_cases hsl : torusParabolicSize z ≤ lam
    · have : singularLocalWeight p lam z = torusParabolicSize z ^ (-p) := by
        simp [singularLocalWeight, hz, hsl]
      rw [this]
      linarith
    · have h1 : torusParabolicSize z ^ (-p) ≤ lam ^ (-p) :=
        Real.rpow_le_rpow_of_nonpos hlam (lt_of_not_ge hsl).le (by linarith)
      linarith

/-- Weighted integral against a weight dominated by an integrable local weight plus a constant. -/
theorem integral_mul_weight_le (h : SemigroupTestProfile x lam B Mom g) {p : ℝ}
    (hlam : 0 < lam) {W L : SpaceTime → ℝ} (hWm : Measurable W) (hW0 : ∀ v, 0 ≤ W v)
    (hL : Integrable L) (hL0 : ∀ v, 0 ≤ L v) (hpt : ∀ v, W v ≤ L v + lam ^ (-p)) {I : ℝ}
    (hI : ∫ v, L v ≤ I) :
    Integrable (fun v => |g v| * W v) ∧
      ∫ v, |g v| * W v ≤ B * (lam ^ 5)⁻¹ * I + lam ^ (-p) * Mom 0 := by
  have hB := h.const_nonneg hlam
  have hlp : 0 ≤ lam ^ (-p) := Real.rpow_nonneg hlam.le _
  have hpt' : ∀ v, |g v| * W v ≤ B * (lam ^ 5)⁻¹ * L v + lam ^ (-p) * |g v| := by
    intro v
    have h1 := h.abs_le v
    calc |g v| * W v ≤ |g v| * (L v + lam ^ (-p)) :=
          mul_le_mul_of_nonneg_left (hpt v) (abs_nonneg _)
      _ = |g v| * L v + lam ^ (-p) * |g v| := by ring
      _ ≤ B * (lam ^ 5)⁻¹ * L v + lam ^ (-p) * |g v| := by
          have := mul_le_mul_of_nonneg_right h1 (hL0 v)
          linarith
  have hG : Integrable (fun v => B * (lam ^ 5)⁻¹ * L v + lam ^ (-p) * |g v|) :=
    (hL.const_mul _).add (h.integrable_abs.const_mul _)
  have hm : Measurable (fun v => |g v| * W v) := h.measurable_abs.mul hWm
  have hnn : ∀ v, 0 ≤ |g v| * W v := fun v => mul_nonneg (abs_nonneg _) (hW0 v)
  refine ⟨hG.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_), ?_⟩
  · rw [Real.norm_of_nonneg (hnn v)]
    exact hpt' v
  · calc ∫ v, |g v| * W v ≤ ∫ v, (B * (lam ^ 5)⁻¹ * L v + lam ^ (-p) * |g v|) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hG
            (Filter.Eventually.of_forall hpt')
      _ = (B * (lam ^ 5)⁻¹ * ∫ v, L v) + lam ^ (-p) * ∫ v, |g v| := by
          rw [integral_add (hL.const_mul _) (h.integrable_abs.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ B * (lam ^ 5)⁻¹ * I + lam ^ (-p) * Mom 0 := by
          have hc : 0 ≤ B * (lam ^ 5)⁻¹ := by positivity
          exact add_le_add (mul_le_mul_of_nonneg_left hI hc)
            (mul_le_mul_of_nonneg_left h.integral_abs_le hlp)

/-- The constant `B (lam⁵)⁻¹ (80/(5-p) lam^(5-p)) + lam^(-p) Mom 0` simplifies. -/
theorem neg_const_eq {p lam B m : ℝ} (hlam : 0 < lam) :
    B * (lam ^ 5)⁻¹ * (80 / (5 - p) * lam ^ (5 - p)) + lam ^ (-p) * m =
      (B * (80 / (5 - p)) + m) * lam ^ (-p) := by
  have h5 : (lam ^ 5)⁻¹ * lam ^ (5 - p) = lam ^ (-p) := by
    have : lam ^ (5 : ℕ) = lam ^ (5 : ℝ) := by norm_cast
    rw [this, ← Real.rpow_neg hlam.le, ← Real.rpow_add hlam]
    congr 1
    ring
  calc _ = B * (80 / (5 - p)) * ((lam ^ 5)⁻¹ * lam ^ (5 - p)) + lam ^ (-p) * m := by ring
    _ = _ := by rw [h5]; ring

/-- Negative moments: `∫ |g| s(· - x)^(-p) ≤ (80 B/(5-p) + Mom 0) lam^(-p)` for `0 < p < 5`. -/
theorem integral_rpow_neg_le (h : SemigroupTestProfile x lam B Mom g) {p : ℝ} (hp : 0 < p)
    (hp5 : p < 5) (hlam : 0 < lam) :
    Integrable (fun u => |g u| * torusParabolicSize (u - x) ^ (-p)) ∧
      ∫ u, |g u| * torusParabolicSize (u - x) ^ (-p) ≤
        (B * (80 / (5 - p)) + Mom 0) * lam ^ (-p) := by
  have hLi : Integrable (fun u => singularLocalWeight p lam (u - x)) :=
    (integrable_singularLocalWeight hp hp5 hlam).comp_sub_right x
  have hLint : ∫ u, singularLocalWeight p lam (u - x) ≤ 80 / (5 - p) * lam ^ (5 - p) := by
    rw [integral_sub_right_eq_self (fun z => singularLocalWeight p lam z) x]
    exact integral_singularLocalWeight_le hp hp5 hlam
  have key := h.integral_mul_weight_le (p := p) hlam
    (W := fun u => torusParabolicSize (u - x) ^ (-p))
    ((Phi43.measurable_torusParabolicSize.comp (measurable_id.sub measurable_const)).pow_const _)
    (fun v => Real.rpow_nonneg (torusParabolicSize_nonneg _) _) hLi
    (fun v => singularLocalWeight_nonneg _ _ _)
    (fun v => rpow_neg_le_localWeight_add hp hlam _) hLint
  exact ⟨key.1, key.2.trans (le_of_eq (neg_const_eq hlam))⟩

/-- Moments of every order `a > -5`: `∫ |g| s(· - x)^a ≤ C lam^a`. -/
theorem integral_rpow_le (h : SemigroupTestProfile x lam B Mom g) {a : ℝ} (ha : -5 < a)
    (hlam : 0 < lam) :
    Integrable (fun u => |g u| * torusParabolicSize (u - x) ^ a) ∧
      ∫ u, |g u| * torusParabolicSize (u - x) ^ a ≤
        semigroupTestMomConst B Mom a * lam ^ a := by
  by_cases h0 : 0 ≤ a
  · simp only [semigroupTestMomConst, h0, ite_true]
    exact ⟨h.integrable_moment a h0, h.integral_moment_le a h0⟩
  · have hp : 0 < -a := by linarith
    have := h.integral_rpow_neg_le hp (by linarith) hlam
    simp only [neg_neg] at this
    simp only [semigroupTestMomConst, h0, ite_false]
    have e : (5 : ℝ) - -a = 5 + a := by ring
    rw [e] at this
    exact this

/-- Convolution with a negative power, uniformly in the centre:
`∫ |g v| s(u - v)^(-q) dv ≤ (80 B/(5-q) + Mom 0) lam^(-q)` for `0 < q < 5`. -/
theorem integral_mul_rpow_sub_le (h : SemigroupTestProfile x lam B Mom g) {q : ℝ}
    (hq : 0 < q) (hq5 : q < 5) (hlam : 0 < lam) (u : SpaceTime) :
    Integrable (fun v => |g v| * torusParabolicSize (u - v) ^ (-q)) ∧
      ∫ v, |g v| * torusParabolicSize (u - v) ^ (-q) ≤
        (B * (80 / (5 - q)) + Mom 0) * lam ^ (-q) := by
  have hLi : Integrable (fun v => singularLocalWeight q lam (u - v)) :=
    integrable_comp_sub_left_spaceTime (integrable_singularLocalWeight hq hq5 hlam) u
  have hLint : ∫ v, singularLocalWeight q lam (u - v) ≤ 80 / (5 - q) * lam ^ (5 - q) := by
    rw [integral_comp_sub_left_spaceTime (fun z => singularLocalWeight q lam z) u]
    exact integral_singularLocalWeight_le hq hq5 hlam
  have key := h.integral_mul_weight_le (p := q) hlam
    (W := fun v => torusParabolicSize (u - v) ^ (-q))
    ((Phi43.measurable_torusParabolicSize.comp (measurable_const.sub measurable_id)).pow_const _)
    (fun v => Real.rpow_nonneg (torusParabolicSize_nonneg _) _) hLi
    (fun v => singularLocalWeight_nonneg _ _ _)
    (fun v => rpow_neg_le_localWeight_add hq hlam _) hLint
  exact ⟨key.1, key.2.trans (le_of_eq (neg_const_eq hlam))⟩

end SemigroupTestProfile

end RegularityStructures

end
