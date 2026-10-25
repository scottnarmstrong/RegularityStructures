/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramMultiCross
public import RegularityStructures.BPHZ.TreeI2Psi2DiagramMultiAlg

/-!
# Common notation for the difference bound of `I(Ψ²) Ψ²`

* `i2Psi2DiffF θ δ r r' d`: the target majorant
  `d^(-η) + d^(-2) (r^(2-η) + r'^(2-η)) + d^(-(2+2θ)) (r^(2-δ) + r'^(2-δ)) + r^(-η) + r'^(-η)`,
  `η = 2θ + δ`;
* `i2Psi2Triple K x y y' g₁ h a b c`: the integrand
  `|A(w)| |A'(w')| s(g₁ - w)^(-a) s(w' - w)^(-b) s(h - w')^(-c)`;
* `i2Psi2PointCfg x y y'`: `0 < r, r' ≤ 1`, `0 < d`, with `r = s(y - x)`, `r' = s(y' - x)`,
  `d = s(y - y')`;
* the relations `d ≤ 8 (r + r')`, `r' ≤ 16 (r + d)`, `r ≤ 16 (r' + d)`.
-/

@[expose] public section

namespace RegularityStructures

/-- The majorant of the difference bound: `η = 2θ + δ`,
`d^(-η) + d^(-2) (r^(2-η) + r'^(2-η)) + d^(-(2+2θ)) (r^(2-δ) + r'^(2-δ)) + (r^(-η) + r'^(-η))`. -/
noncomputable def i2Psi2DiffF (θ δ r r' d : ℝ) : ℝ :=
  d ^ (-(2 * θ + δ)) + d ^ (-(2 : ℝ)) * (r ^ (2 - (2 * θ + δ)) + r' ^ (2 - (2 * θ + δ))) +
    d ^ (-(2 + 2 * θ)) * (r ^ (2 - δ) + r' ^ (2 - δ)) + (r ^ (-(2 * θ + δ)) + r' ^ (-(2 * θ + δ)))

/-- The integrand `|A(w)| |A'(w')| s(g₁ - w)^(-a) s(w' - w)^(-b) s(h - w')^(-c)`. -/
noncomputable def i2Psi2Triple (K : SpaceTime → ℝ) (x y y' g₁ h : SpaceTime) (a b c : ℝ)
    (q : SpaceTime × SpaceTime) : ℝ :=
  |i2Psi2Increment K x y q.1| * |i2Psi2Increment K x y' q.2| *
    (torusParabolicSize (g₁ - q.1) ^ (-a) * torusParabolicSize (q.2 - q.1) ^ (-b) *
      torusParabolicSize (h - q.2) ^ (-c))

/-- The integrand `|A(w)| |A'(w')| s(g₁ - w)^(-a) s(g₂ - w)^(-b) s(h₁ - w')^(-c) s(h₂ - w')^(-e)`. -/
noncomputable def i2Psi2Quad (K : SpaceTime → ℝ) (x y y' : SpaceTime) (a b c e : ℝ)
    (q : SpaceTime × SpaceTime) : ℝ :=
  (|i2Psi2Increment K x y q.1| * (torusParabolicSize (y - q.1) ^ (-a) *
      torusParabolicSize (y' - q.1) ^ (-b))) *
    (|i2Psi2Increment K x y' q.2| * (torusParabolicSize (y' - q.2) ^ (-c) *
      torusParabolicSize (y - q.2) ^ (-e)))

/-- The configuration of the three points: `0 < r, r' ≤ 1` and `0 < d`. -/
def i2Psi2PointCfg (x y y' : SpaceTime) : Prop :=
  0 < torusParabolicSize (y - x) ∧ torusParabolicSize (y - x) ≤ 1 ∧
    0 < torusParabolicSize (y' - x) ∧ torusParabolicSize (y' - x) ≤ 1 ∧
    0 < torusParabolicSize (y - y')

end RegularityStructures

end

public section

namespace RegularityStructures

theorem i2Psi2PointCfg.time_le {x y y' : SpaceTime} (h : i2Psi2PointCfg x y y') :
    |y.1 - x.1| ≤ 1 ∧ |y'.1 - x.1| ≤ 1 := by
  obtain ⟨-, h1, -, h2, -⟩ := h
  exact ⟨by simpa [Prod.fst_sub] using abs_le_one_of_torusParabolicSize_le_one h1,
    by simpa [Prod.fst_sub] using abs_le_one_of_torusParabolicSize_le_one h2⟩

/-- The three quasi-triangle inequalities between `r`, `r'` and `d`. -/
theorem i2Psi2PointCfg.sizes {x y y' : SpaceTime} (h : i2Psi2PointCfg x y y') :
    torusParabolicSize (y - y') ≤ 8 * (torusParabolicSize (y - x) + torusParabolicSize (y' - x)) ∧
    torusParabolicSize (y' - x) ≤ 16 * (torusParabolicSize (y - x) + torusParabolicSize (y - y')) ∧
    torusParabolicSize (y - x) ≤ 16 * (torusParabolicSize (y' - x) + torusParabolicSize (y - y')) := by
  obtain ⟨hr, -, hr', -, hd⟩ := h
  refine ⟨torusParabolicSize_sub_le_of_sub, ?_, ?_⟩
  · have h1 := torusParabolicSize_sub_le_eight_mul (y' - y) (x - y)
    have e : y' - y - (x - y) = y' - x := by abel
    rw [e] at h1
    have h2 := torusParabolicSize_neg_le_two_mul (y - y')
    have h3 := torusParabolicSize_neg_le_two_mul (y - x)
    rw [neg_sub] at h2 h3
    linarith
  · have h1 := torusParabolicSize_sub_le_eight_mul (y - y') (x - y')
    have e : y - y' - (x - y') = y - x := by abel
    rw [e] at h1
    have h3 := torusParabolicSize_neg_le_two_mul (y' - x)
    rw [neg_sub] at h3
    linarith

theorem measurable_i2Psi2Triple {K : SpaceTime → ℝ} (hK : Measurable K) (x y y' g₁ h : SpaceTime)
    (a b c : ℝ) : Measurable (i2Psi2Triple K x y y' g₁ h a b c) := by
  have mA := measurable_i2Psi2Increment hK
  unfold i2Psi2Triple
  exact (((continuous_abs.measurable.comp (mA x y)).comp measurable_fst).mul
      ((continuous_abs.measurable.comp (mA x y')).comp measurable_snd)).mul
      ((((measurable_torusParabolicSize_sub_rpow g₁ _).comp measurable_fst).mul
        ((Phi43.measurable_torusParabolicSize.comp (measurable_snd.sub measurable_fst)).pow_const
          _)).mul ((measurable_torusParabolicSize_sub_rpow h _).comp measurable_snd))

theorem i2Psi2Triple_nonneg (K : SpaceTime → ℝ) (x y y' g₁ h : SpaceTime) (a b c : ℝ)
    (q : SpaceTime × SpaceTime) : 0 ≤ i2Psi2Triple K x y y' g₁ h a b c q := by
  unfold i2Psi2Triple
  have nr : ∀ (u : SpaceTime) (e : ℝ), 0 ≤ torusParabolicSize u ^ e := fun u e =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    (mul_nonneg (mul_nonneg (nr _ _) (nr _ _)) (nr _ _))

theorem measurable_i2Psi2Quad {K : SpaceTime → ℝ} (hK : Measurable K) (x y y' : SpaceTime)
    (a b c e : ℝ) : Measurable (i2Psi2Quad K x y y' a b c e) := by
  have mA := measurable_i2Psi2Increment hK
  unfold i2Psi2Quad
  exact (((continuous_abs.measurable.comp (mA x y)).comp measurable_fst).mul
      (((measurable_torusParabolicSize_sub_rpow y _).comp measurable_fst).mul
        ((measurable_torusParabolicSize_sub_rpow y' _).comp measurable_fst))).mul
      (((continuous_abs.measurable.comp (mA x y')).comp measurable_snd).mul
      (((measurable_torusParabolicSize_sub_rpow y' _).comp measurable_snd).mul
        ((measurable_torusParabolicSize_sub_rpow y _).comp measurable_snd)))

theorem i2Psi2Quad_nonneg (K : SpaceTime → ℝ) (x y y' : SpaceTime) (a b c e : ℝ)
    (q : SpaceTime × SpaceTime) : 0 ≤ i2Psi2Quad K x y y' a b c e q := by
  unfold i2Psi2Quad
  have nr : ∀ (u : SpaceTime) (e : ℝ), 0 ≤ torusParabolicSize u ^ e := fun u e =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (mul_nonneg (nr _ _) (nr _ _)))
    (mul_nonneg (abs_nonneg _) (mul_nonneg (nr _ _) (nr _ _)))

/-- The four pieces of `i2Psi2DiffF` are nonnegative. -/
theorem i2Psi2DiffF_parts_nonneg {θ δ r r' d : ℝ} (hr : 0 < r) (hr' : 0 < r') (hd : 0 < d) :
    0 ≤ d ^ (-(2 * θ + δ)) ∧ 0 ≤ d ^ (-(2 : ℝ)) * (r ^ (2 - (2 * θ + δ)) + r' ^ (2 - (2 * θ + δ))) ∧
      0 ≤ d ^ (-(2 + 2 * θ)) * (r ^ (2 - δ) + r' ^ (2 - δ)) ∧
      0 ≤ r ^ (-(2 * θ + δ)) + r' ^ (-(2 * θ + δ)) := by
  refine ⟨Real.rpow_nonneg hd.le _, mul_nonneg (Real.rpow_nonneg hd.le _)
    (add_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hr'.le _)),
    mul_nonneg (Real.rpow_nonneg hd.le _)
    (add_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hr'.le _)),
    add_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hr'.le _)⟩

theorem i2Psi2DiffF_nonneg {θ δ r r' d : ℝ} (hr : 0 < r) (hr' : 0 < r') (hd : 0 < d) :
    0 ≤ i2Psi2DiffF θ δ r r' d := by
  obtain ⟨h1, h2, h3, h4⟩ := i2Psi2DiffF_parts_nonneg (θ := θ) (δ := δ) hr hr' hd
  unfold i2Psi2DiffF
  linarith

end RegularityStructures

end
