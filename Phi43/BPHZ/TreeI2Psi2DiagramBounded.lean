/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramConv

/-!
# Bounded integrals of products of singular weights over a time slab

All the variables of the diagram integrals of the tree `I(Ψ²) Ψ²` lie in a time slab
`|t - τ| ≤ 2` (the kernels `K` are supported in `|t| ≤ 1` and the base points are within
distance `1` of `τ`).  On the slab every parabolic distance to a point of the slab is at most `3`,
so a product of weights `s(pᵢ - w)^(-λᵢ)` with total exponent `λ₁ + λ₂ + λ₃ < 5` has a bounded
integral: `i2Psi2LintBound_slab_triple`, [Hai14, (10.37a), Lemma 10.14].
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The indicator of the time slab `|t - τ| ≤ 2`. -/
def i2Psi2Slab (τ : ℝ) (w : SpaceTime) : ℝ :=
  if |w.1 - τ| ≤ 2 then 1 else 0

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem i2Psi2Slab_nonneg (τ : ℝ) (w : SpaceTime) : 0 ≤ i2Psi2Slab τ w := by
  unfold i2Psi2Slab; split_ifs <;> norm_num

theorem i2Psi2Slab_le_one (τ : ℝ) (w : SpaceTime) : i2Psi2Slab τ w ≤ 1 := by
  unfold i2Psi2Slab; split_ifs <;> norm_num

theorem i2Psi2Slab_of_le {τ : ℝ} {w : SpaceTime} (h : |w.1 - τ| ≤ 2) : i2Psi2Slab τ w = 1 := by
  unfold i2Psi2Slab; simp [h]

theorem abs_sub_le_two_of_i2Psi2Slab_ne_zero {τ : ℝ} {w : SpaceTime}
    (h : i2Psi2Slab τ w ≠ 0) : |w.1 - τ| ≤ 2 := by
  by_contra hc
  exact h (by unfold i2Psi2Slab; simp [hc])

theorem measurable_i2Psi2Slab (τ : ℝ) : Measurable (i2Psi2Slab τ) := by
  unfold i2Psi2Slab
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const) measurable_const
    measurable_const

theorem measurable_torusParabolicSize_sub_rpow (p : SpaceTime) (e : ℝ) :
    Measurable fun w : SpaceTime => torusParabolicSize (p - w) ^ e :=
  (Phi43.measurable_torusParabolicSize.comp (measurable_const.sub measurable_id)).pow_const _

theorem torusParabolicSize_le_three_of_abs_le {u : SpaceTime} (hu : |u.1| ≤ 4) :
    torusParabolicSize u ≤ 3 := by
  have h1 : √|u.1| ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
    exact hu
  have h2 := torusSpatialNorm_le_seven_eighth u.2
  unfold torusParabolicSize
  linarith

/-- Product of three weights, [Hai14, (10.37a)]. -/
theorem torusParabolicSize_rpow_neg_mul_three_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) {z₁ z₂ z₃ : SpaceTime} (h₁ : 0 < torusParabolicSize z₁)
    (h₂ : 0 < torusParabolicSize z₂) (h₃ : 0 < torusParabolicSize z₃) :
    torusParabolicSize z₁ ^ (-a) * torusParabolicSize z₂ ^ (-b) * torusParabolicSize z₃ ^ (-c) ≤
      torusParabolicSize z₁ ^ (-(a + b + c)) + torusParabolicSize z₂ ^ (-(a + b + c)) +
        2 * torusParabolicSize z₃ ^ (-(a + b + c)) := by
  have p12 := torusParabolicSize_rpow_neg_mul_le ha hb h₁ h₂
  have p13 := torusParabolicSize_rpow_neg_mul_le (add_nonneg ha hb) hc h₁ h₃
  have p23 := torusParabolicSize_rpow_neg_mul_le (add_nonneg ha hb) hc h₂ h₃
  have n3 : 0 ≤ torusParabolicSize z₃ ^ (-c) := Real.rpow_nonneg h₃.le _
  calc torusParabolicSize z₁ ^ (-a) * torusParabolicSize z₂ ^ (-b) *
        torusParabolicSize z₃ ^ (-c)
      ≤ (torusParabolicSize z₁ ^ (-(a + b)) + torusParabolicSize z₂ ^ (-(a + b))) *
        torusParabolicSize z₃ ^ (-c) := mul_le_mul_of_nonneg_right p12 n3
    _ = torusParabolicSize z₁ ^ (-(a + b)) * torusParabolicSize z₃ ^ (-c) +
        torusParabolicSize z₂ ^ (-(a + b)) * torusParabolicSize z₃ ^ (-c) := by ring
    _ ≤ _ := by linarith

/-- The weight `s(p - w)^(-e)` on the slab has a bounded integral. -/
theorem i2Psi2LintBound_slab_rpow {e : ℝ} (he : 0 < e) (he5 : e < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (p : SpaceTime), |p.1 - τ| ≤ 2 →
      i2Psi2LintBound volume (fun w => i2Psi2Slab τ w * torusParabolicSize (p - w) ^ (-e)) C := by
  refine ⟨80 / (5 - e) * 3 ^ (5 - e), mul_nonneg (div_nonneg (by norm_num) (by linarith))
    (Real.rpow_nonneg (by norm_num) _), ?_⟩
  intro τ p hp
  have h := (i2Psi2LintBound_singularLocalWeight he he5 (by norm_num : (0 : ℝ) < 3)).comp_sub_left
    (measurable_singularLocalWeight e 3) p
  refine h.mono (fun w => ?_) le_rfl
  by_cases hw : |w.1 - τ| ≤ 2
  · rw [i2Psi2Slab_of_le hw, one_mul]
    have h4 : |(p - w).1| ≤ 4 := by
      have : (p - w).1 = (p.1 - τ) - (w.1 - τ) := by simp only [Prod.fst_sub]; ring
      rw [this]
      calc |(p.1 - τ) - (w.1 - τ)| ≤ |p.1 - τ| + |w.1 - τ| := abs_sub _ _
        _ ≤ 4 := by linarith
    have h3 := torusParabolicSize_le_three_of_abs_le h4
    rcases (torusParabolicSize_nonneg (p - w)).eq_or_lt with h0 | h0
    · rw [← h0, Real.zero_rpow (by linarith)]
      exact singularLocalWeight_nonneg _ _ _
    · simp [singularLocalWeight, h0, h3]
  · have : i2Psi2Slab τ w = 0 := by unfold i2Psi2Slab; simp [hw]
    rw [this, zero_mul]
    exact singularLocalWeight_nonneg _ _ _

/-- A product of three weights `s(pᵢ - w)^(-λᵢ)` with total exponent in `(0, 5)` has a bounded
integral over the slab. -/
theorem i2Psi2LintBound_slab_triple {l₁ l₂ l₃ : ℝ} (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂) (h₃ : 0 ≤ l₃)
    (he : 0 < l₁ + l₂ + l₃) (he5 : l₁ + l₂ + l₃ < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (p₁ p₂ p₃ : SpaceTime), |p₁.1 - τ| ≤ 2 → |p₂.1 - τ| ≤ 2 →
      |p₃.1 - τ| ≤ 2 →
      i2Psi2LintBound volume (fun w => i2Psi2Slab τ w *
        (torusParabolicSize (p₁ - w) ^ (-l₁) * torusParabolicSize (p₂ - w) ^ (-l₂) *
          torusParabolicSize (p₃ - w) ^ (-l₃))) C := by
  obtain ⟨C, hC, hb⟩ := i2Psi2LintBound_slab_rpow he he5
  refine ⟨4 * C, by positivity, ?_⟩
  intro τ p₁ p₂ p₃ hp₁ hp₂ hp₃
  have m : ∀ p : SpaceTime, Measurable fun w : SpaceTime =>
      i2Psi2Slab τ w * torusParabolicSize (p - w) ^ (-(l₁ + l₂ + l₃)) := fun p =>
    (measurable_i2Psi2Slab τ).mul (measurable_torusParabolicSize_sub_rpow p _)
  have n : ∀ (p : SpaceTime) w, 0 ≤ i2Psi2Slab τ w *
      torusParabolicSize (p - w) ^ (-(l₁ + l₂ + l₃)) := fun p w =>
    mul_nonneg (i2Psi2Slab_nonneg _ _) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have b₁ := hb τ p₁ hp₁
  have b₂ := hb τ p₂ hp₂
  have b₃ := (hb τ p₃ hp₃).const_mul (by norm_num : (0 : ℝ) ≤ 2)
  have s1 := b₁.add (g := fun w => i2Psi2Slab τ w *
      torusParabolicSize (p₂ - w) ^ (-(l₁ + l₂ + l₃))) (m p₁).aemeasurable (n p₁) (n p₂) hC hC b₂
  have m12 : Measurable fun w : SpaceTime => i2Psi2Slab τ w *
      torusParabolicSize (p₁ - w) ^ (-(l₁ + l₂ + l₃)) + i2Psi2Slab τ w *
      torusParabolicSize (p₂ - w) ^ (-(l₁ + l₂ + l₃)) := (m p₁).add (m p₂)
  have s2 := s1.add (g := fun w => 2 * (i2Psi2Slab τ w *
      torusParabolicSize (p₃ - w) ^ (-(l₁ + l₂ + l₃)))) m12.aemeasurable
    (fun w => add_nonneg (n p₁ w) (n p₂ w)) (fun w => mul_nonneg (by norm_num) (n p₃ w))
    (add_nonneg hC hC) (mul_nonneg (by norm_num) hC) b₃
  refine s2.mono_ae ?_ (le_of_eq (by ring))
  filter_upwards [ae_torusParabolicSize_sub_pos p₁, ae_torusParabolicSize_sub_pos p₂,
    ae_torusParabolicSize_sub_pos p₃] with w hw₁ hw₂ hw₃
  have h := torusParabolicSize_rpow_neg_mul_three_le h₁ h₂ h₃ hw₁ hw₂ hw₃
  have hs := i2Psi2Slab_nonneg τ w
  calc i2Psi2Slab τ w * (torusParabolicSize (p₁ - w) ^ (-l₁) * torusParabolicSize (p₂ - w) ^ (-l₂) *
          torusParabolicSize (p₃ - w) ^ (-l₃))
      ≤ i2Psi2Slab τ w * (torusParabolicSize (p₁ - w) ^ (-(l₁ + l₂ + l₃)) +
        torusParabolicSize (p₂ - w) ^ (-(l₁ + l₂ + l₃)) +
          2 * torusParabolicSize (p₃ - w) ^ (-(l₁ + l₂ + l₃))) := mul_le_mul_of_nonneg_left h hs
    _ = _ := by ring

end RegularityStructures

end
