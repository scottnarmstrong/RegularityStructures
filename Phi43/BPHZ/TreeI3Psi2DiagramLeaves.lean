/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramLevel
public import RegularityStructures.BPHZ.TreeI3Psi2DiagramYoung
public import Phi43.BPHZ.TreeI3PsiOuter

/-!
# Leaves with symmetrised output for the diagrams of `I(Ψ³)Ψ²`

For the three points `z, z', 0` put `S_p(z, z') = s(z - z')^(-p) + s(z)^(-p) + s(z')^(-p)`.
Every ordered difference `s(a - b)^(-p)` of two of the points is at most `2^p S_p`.  Using this we
restate the two-power and three-power integral estimates with centres among `{z, z', 0}` in the
form `∫ ⋯ ≤ C S_η`, and prove that a product `S_a S_b` is at most a constant times `S_{a+b}`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- `S_p(z, z') = s(z - z')^(-p) + s(z - 0)^(-p) + s(z' - 0)^(-p)`. -/
def i3Psi2S (p : ℝ) (z z' : SpaceTime) : ℝ :=
  torusParabolicSize (z - z') ^ (-p) + torusParabolicSize (z - 0) ^ (-p) +
    torusParabolicSize (z' - 0) ^ (-p)

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem i3Psi2S_nonneg (p : ℝ) (z z' : SpaceTime) : 0 ≤ i3Psi2S p z z' := by
  unfold i3Psi2S
  have := Real.rpow_nonneg (torusParabolicSize_nonneg (z - z')) (-p)
  have := Real.rpow_nonneg (torusParabolicSize_nonneg (z - 0)) (-p)
  have := Real.rpow_nonneg (torusParabolicSize_nonneg (z' - 0)) (-p)
  linarith

/-- Every ordered difference of two of the points is controlled by `2^p S_p`. -/
theorem rpow_neg_le_i3Psi2S {p : ℝ} (hp : 0 < p) {z z' a b : SpaceTime}
    (hx : 0 < torusParabolicSize (z - z')) (hu : 0 < torusParabolicSize (z - 0))
    (hu' : 0 < torusParabolicSize (z' - 0)) (ha : a = z ∨ a = z' ∨ a = 0)
    (hb : b = z ∨ b = z' ∨ b = 0) :
    torusParabolicSize (a - b) ^ (-p) ≤ 2 ^ p * i3Psi2S p z z' := by
  have f1 := torusParabolicSize_rpow_neg_flip_le' hp.le hx
  have f2 := torusParabolicSize_rpow_neg_flip_le' hp.le hu
  have f3 := torusParabolicSize_rpow_neg_flip_le' hp.le hu'
  have e0 : ∀ x : SpaceTime, torusParabolicSize (x - x) ^ (-p) = 0 := by
    intro x
    rw [sub_self, torusParabolicSize_zero_spaceTime]
    exact Real.zero_rpow (neg_ne_zero.2 hp.ne')
  have P1 : (1 : ℝ) ≤ 2 ^ p := Real.one_le_rpow (by norm_num) hp.le
  have n1 := Real.rpow_nonneg (torusParabolicSize_nonneg (z - z')) (-p)
  have n2 := Real.rpow_nonneg (torusParabolicSize_nonneg (z - 0)) (-p)
  have n3 := Real.rpow_nonneg (torusParabolicSize_nonneg (z' - 0)) (-p)
  have g0 := e0 z
  have g1 := e0 z'
  have g2 := e0 (0 : SpaceTime)
  have m1 : torusParabolicSize (z - z') ^ (-p) ≤ 2 ^ p * torusParabolicSize (z - z') ^ (-p) :=
    le_mul_of_one_le_left n1 P1
  have m2 : torusParabolicSize (z - 0) ^ (-p) ≤ 2 ^ p * torusParabolicSize (z - 0) ^ (-p) :=
    le_mul_of_one_le_left n2 P1
  have m3 : torusParabolicSize (z' - 0) ^ (-p) ≤ 2 ^ p * torusParabolicSize (z' - 0) ^ (-p) :=
    le_mul_of_one_le_left n3 P1
  have q1 := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ p) n1
  have q2 := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ p) n2
  have q3 := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ p) n3
  unfold i3Psi2S
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> linarith

/-- Products `S_a S_b` are controlled by `S_{a+b}`. -/
theorem i3Psi2S_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) {z z' : SpaceTime}
    (hx : 0 < torusParabolicSize (z - z')) (hu : 0 < torusParabolicSize (z - 0))
    (hu' : 0 < torusParabolicSize (z' - 0)) :
    i3Psi2S a z z' * i3Psi2S b z z' ≤ 9 * 2 ^ (a + b) * i3Psi2S (a + b) z z' := by
  set x := torusParabolicSize (z - z')
  set u := torusParabolicSize (z - 0)
  set u' := torusParabolicSize (z' - 0)
  have P1 : (1 : ℝ) ≤ 2 ^ (a + b) := Real.one_le_rpow (by norm_num) hab.le
  have e : ∀ y : ℝ, 0 < y → y ^ (-a) * y ^ (-b) = y ^ (-(a + b)) := by
    intro y hy; rw [← Real.rpow_add hy]; congr 1; ring
  have n1 := Real.rpow_nonneg hx.le (-(a + b))
  have n2 := Real.rpow_nonneg hu.le (-(a + b))
  have n3 := Real.rpow_nonneg hu'.le (-(a + b))
  have y12 := rpow_neg_mul_two_le (p := x) (q := u) hx hu ha hb hab rfl
  have y21 := rpow_neg_mul_two_le (p := u) (q := x) hu hx ha hb hab rfl
  have y13 := rpow_neg_mul_two_le (p := x) (q := u') hx hu' ha hb hab rfl
  have y31 := rpow_neg_mul_two_le (p := u') (q := x) hu' hx ha hb hab rfl
  have y23 := rpow_neg_mul_two_le (p := u) (q := u') hu hu' ha hb hab rfl
  have y32 := rpow_neg_mul_two_le (p := u') (q := u) hu' hu ha hb hab rfl
  have d1 := e x hx
  have d2 := e u hu
  have d3 := e u' hu'
  unfold i3Psi2S
  have : (x ^ (-a) + u ^ (-a) + u' ^ (-a)) * (x ^ (-b) + u ^ (-b) + u' ^ (-b)) =
      x ^ (-a) * x ^ (-b) + u ^ (-a) * u ^ (-b) + u' ^ (-a) * u' ^ (-b) +
      (x ^ (-a) * u ^ (-b) + u ^ (-a) * x ^ (-b) + x ^ (-a) * u' ^ (-b) +
        u' ^ (-a) * x ^ (-b) + u ^ (-a) * u' ^ (-b) + u' ^ (-a) * u ^ (-b)) := by ring
  rw [this]
  generalize x ^ (-a) * u ^ (-b) = t1 at *
  generalize u ^ (-a) * x ^ (-b) = t2 at *
  generalize x ^ (-a) * u' ^ (-b) = t3 at *
  generalize u' ^ (-a) * x ^ (-b) = t4 at *
  generalize u ^ (-a) * u' ^ (-b) = t5 at *
  generalize u' ^ (-a) * u ^ (-b) = t6 at *
  generalize x ^ (-(a + b)) = X at *
  generalize u ^ (-(a + b)) = U at *
  generalize u' ^ (-(a + b)) = U' at *
  generalize (2 : ℝ) ^ (a + b) = P at *
  rw [d1, d2, d3]
  linarith [mul_nonneg (sub_nonneg.2 P1) n1, mul_nonneg (sub_nonneg.2 P1) n2,
    mul_nonneg (sub_nonneg.2 P1) n3]

/-- Two centred powers with centres among `{z, z', 0}`, total order `5 + η`. -/
theorem i3Psi2_leaf2 {a b η : ℝ} (ha : 0 < a) (ha5 : a < 5) (hb : 0 < b) (hb5 : b < 5)
    (hη : 0 < η) (hab : a + b = 5 + η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {z z' p q : SpaceTime}, 0 < torusParabolicSize (z - z') →
      0 < torusParabolicSize (z - 0) → 0 < torusParabolicSize (z' - 0) →
      (p = z ∨ p = z' ∨ p = 0) → (q = z ∨ q = z' ∨ q = 0) → 0 < torusParabolicSize (p - q) →
      SingularIntLe (fun w => singularPow a p w * singularPow b q w) (C * i3Psi2S η z z') := by
  obtain ⟨C, hC, h⟩ := singularIntLe_mul_two ha ha5 hb hb5 hη hab
  refine ⟨C * 2 ^ η, by positivity, fun {z z' p q} hx hu hu' hp hq hpq => ?_⟩
  refine (h p q hpq).mono_right ?_
  have := rpow_neg_le_i3Psi2S hη (z := _) (z' := _) (a := p) (b := q) hx hu hu' hp hq
  calc C * torusParabolicSize (p - q) ^ (-η) ≤ C * (2 ^ η * i3Psi2S η _ _) :=
        mul_le_mul_of_nonneg_left this hC
    _ = _ := by ring

/-- Three centred powers with centres among `{z, z', 0}`, the first two of total order `< 5`. -/
theorem i3Psi2_leaf3 {a b c η : ℝ} (ha : 0 < a) (hb : 0 < b) (hab5 : a + b < 5) (hc : 0 < c)
    (hc5 : c < 5) (hη : 0 < η) (habc : a + b + c = 5 + η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {z z' p q r : SpaceTime}, 0 < torusParabolicSize (z - z') →
      0 < torusParabolicSize (z - 0) → 0 < torusParabolicSize (z' - 0) →
      (p = z ∨ p = z' ∨ p = 0) → (q = z ∨ q = z' ∨ q = 0) → (r = z ∨ r = z' ∨ r = 0) →
      0 < torusParabolicSize (p - r) → 0 < torusParabolicSize (q - r) →
      SingularIntLe (fun w => singularPow a p w * singularPow b q w * singularPow c r w)
        (C * i3Psi2S η z z') := by
  obtain ⟨C, hC, h⟩ := singularIntLe_mul_three ha hb hab5 hc hc5 hη habc
  refine ⟨C * (2 * 2 ^ η), by positivity, fun {z z' p q r} hx hu hu' hp hq hr hpr hqr => ?_⟩
  refine (h p q r hpr hqr).mono_right ?_
  have h1 := rpow_neg_le_i3Psi2S hη (z := _) (z' := _) (a := p) (b := r) hx hu hu' hp hr
  have h2 := rpow_neg_le_i3Psi2S hη (z := _) (z' := _) (a := q) (b := r) hx hu hu' hq hr
  calc C * (torusParabolicSize (p - r) ^ (-η) + torusParabolicSize (q - r) ^ (-η))
      ≤ C * (2 ^ η * i3Psi2S η _ _ + 2 ^ η * i3Psi2S η _ _) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC
    _ = _ := by ring

end RegularityStructures

end
