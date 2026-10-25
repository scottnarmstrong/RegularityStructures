/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic

/-!
# Design note: two-mollifier differences of the covariance layer of `I(Ψ)Ψ`, `I(Ψ)Ψ²`

Let `X_i = ∫ Q F_i`, `i ∈ {0, 1}` (`0`: the model `(ρ, ε)`, `1`: the model `(ρ', ε')`).  Then
`E[(X₀ - X₁)²] = ∬ Q Q' Δ e`, `e_{ij}(y, y') = E[F_i(y) F_j(y')]`, with `Δ` the second difference
of a `2 × 2` array.  By Isserlis `e` is built from arrays `A_i`, `B_{ij}`, `R_{ij}`, `Q_{ij}` by
sums and pointwise products (`ProductIPsiPsiDiffIdentity`), so the bound of `Δ e` follows from a
calculus of *bounds on arrays* (this file):

`IsArr h b f₁ f₁' f₂` records `|h 1 1| ≤ b`, `|h 0 1 - h 1 1| ≤ f₁`, `|h 1 0 - h 1 1| ≤ f₁'`,
`|Δ h| ≤ f₂`, and is propagated through sums and pointwise products (`IsArr.mul`).  The data of the
basic arrays carries the factors `m^θ (1 + s^(-θ))` (`m = max ε ε'`) from the cross-covariance
difference bounds; capping each ratio by `1` makes every monomial of `Δ e` bounded by
`m^(2θ)` times the base bound times two ratio factors.
-/

@[expose] public section

namespace RegularityStructures.Phi43

/-- The second difference of a `2 × 2` array. -/
def arrSd (h : Fin 2 → Fin 2 → ℝ) : ℝ := h 0 0 - h 0 1 - h 1 0 + h 1 1

/-- Size data of a `2 × 2` array relative to the base entry `h 1 1`. -/
def IsArr (h : Fin 2 → Fin 2 → ℝ) (b f₁ f₁' f₂ : ℝ) : Prop :=
  |h 1 1| ≤ b ∧ |h 0 1 - h 1 1| ≤ f₁ ∧ |h 1 0 - h 1 1| ≤ f₁' ∧ |arrSd h| ≤ f₂

/-- Array data in *ratio form*: base `b`, ratio `ς ∈ [0, 1]`, first differences `≤ b ς` and second
difference `≤ b ς²`. -/
def IsArrR (h : Fin 2 → Fin 2 → ℝ) (b ς : ℝ) : Prop :=
  0 ≤ ς ∧ ς ≤ 1 ∧ IsArr h b (b * ς) (b * ς) (b * ς ^ 2)

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

theorem IsArr.mono {h : Fin 2 → Fin 2 → ℝ} {b f₁ f₁' f₂ c g₁ g₁' g₂ : ℝ}
    (H : IsArr h b f₁ f₁' f₂) (hb : b ≤ c) (h1 : f₁ ≤ g₁) (h1' : f₁' ≤ g₁') (h2 : f₂ ≤ g₂) :
    IsArr h c g₁ g₁' g₂ :=
  ⟨H.1.trans hb, H.2.1.trans h1, H.2.2.1.trans h1', H.2.2.2.trans h2⟩

theorem IsArr.add {a b : Fin 2 → Fin 2 → ℝ} {A0 A1 A1' A2 B0 B1 B1' B2 : ℝ}
    (Ha : IsArr a A0 A1 A1' A2) (Hb : IsArr b B0 B1 B1' B2) :
    IsArr (fun i j => a i j + b i j) (A0 + B0) (A1 + B1) (A1' + B1') (A2 + B2) := by
  obtain ⟨a0, a1, a1', a2⟩ := Ha
  obtain ⟨b0, b1, b1', b2⟩ := Hb
  refine ⟨(abs_add_le _ _).trans (add_le_add a0 b0), ?_, ?_, ?_⟩
  · refine le_trans (le_of_eq ?_) ((abs_add_le _ _).trans (add_le_add a1 b1))
    congr 1; ring
  · refine le_trans (le_of_eq ?_) ((abs_add_le _ _).trans (add_le_add a1' b1'))
    congr 1; ring
  · refine le_trans (le_of_eq ?_) ((abs_add_le _ _).trans (add_le_add a2 b2))
    unfold arrSd; congr 1; ring

theorem IsArr.const_mul {a : Fin 2 → Fin 2 → ℝ} {A0 A1 A1' A2 : ℝ} (c : ℝ)
    (Ha : IsArr a A0 A1 A1' A2) :
    IsArr (fun i j => c * a i j) (|c| * A0) (|c| * A1) (|c| * A1') (|c| * A2) := by
  obtain ⟨a0, a1, a1', a2⟩ := Ha
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only; rw [abs_mul]; exact mul_le_mul_of_nonneg_left a0 (abs_nonneg _)
  · simp only
    rw [← mul_sub, abs_mul]; exact mul_le_mul_of_nonneg_left a1 (abs_nonneg _)
  · simp only
    rw [← mul_sub, abs_mul]; exact mul_le_mul_of_nonneg_left a1' (abs_nonneg _)
  · unfold arrSd
    simp only
    rw [show c * a 0 0 - c * a 0 1 - c * a 1 0 + c * a 1 1 =
      c * (a 0 0 - a 0 1 - a 1 0 + a 1 1) by ring, abs_mul]
    exact mul_le_mul_of_nonneg_left a2 (abs_nonneg _)

theorem abs_sum_seven_le (x1 x2 x3 x4 x5 x6 x7 : ℝ) :
    |x1 + x2 + x3 + x4 + x5 + x6 + x7| ≤
      |x1| + |x2| + |x3| + |x4| + |x5| + |x6| + |x7| := by
  have h1 := abs_add_le (x1 + x2 + x3 + x4 + x5 + x6) x7
  have h2 := abs_add_le (x1 + x2 + x3 + x4 + x5) x6
  have h3 := abs_add_le (x1 + x2 + x3 + x4) x5
  have h4 := abs_add_le (x1 + x2 + x3) x4
  have h5 := abs_add_le (x1 + x2) x3
  have h6 := abs_add_le x1 x2
  linarith

/-- **Product of arrays.** -/
theorem IsArr.mul {a b : Fin 2 → Fin 2 → ℝ} {A0 A1 A1' A2 B0 B1 B1' B2 : ℝ}
    (Ha : IsArr a A0 A1 A1' A2) (Hb : IsArr b B0 B1 B1' B2) :
    IsArr (fun i j => a i j * b i j) (A0 * B0) (A1 * (B0 + B1) + A0 * B1)
      (A1' * (B0 + B1') + A0 * B1')
      (A0 * B2 + A2 * B0 + A1 * B1' + A1' * B1 + (A1 + A1') * B2 + A2 * (B1 + B1') + A2 * B2) := by
  obtain ⟨a0, a1, a1', a2⟩ := Ha
  obtain ⟨b0, b1, b1', b2⟩ := Hb
  have A1n : 0 ≤ A1 := (abs_nonneg _).trans a1
  have A1'n : 0 ≤ A1' := (abs_nonneg _).trans a1'
  have A0n : 0 ≤ A0 := (abs_nonneg _).trans a0
  have A2n : 0 ≤ A2 := (abs_nonneg _).trans a2
  have B1n : 0 ≤ B1 := (abs_nonneg _).trans b1
  have B1'n : 0 ≤ B1' := (abs_nonneg _).trans b1'
  have B0n : 0 ≤ B0 := (abs_nonneg _).trans b0
  have B2n : 0 ≤ B2 := (abs_nonneg _).trans b2
  have hb01 : |b 0 1| ≤ B0 + B1 := by
    have : b 0 1 = b 1 1 + (b 0 1 - b 1 1) := by ring
    rw [this]; exact (abs_add_le _ _).trans (add_le_add b0 b1)
  have hb10 : |b 1 0| ≤ B0 + B1' := by
    have : b 1 0 = b 1 1 + (b 1 0 - b 1 1) := by ring
    rw [this]; exact (abs_add_le _ _).trans (add_le_add b0 b1')
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only; rw [abs_mul]; exact mul_le_mul a0 b0 (abs_nonneg _) A0n
  · simp only
    have e : a 0 1 * b 0 1 - a 1 1 * b 1 1 =
        (a 0 1 - a 1 1) * b 0 1 + a 1 1 * (b 0 1 - b 1 1) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul a1 hb01 (abs_nonneg _) A1n
    · rw [abs_mul]; exact mul_le_mul a0 b1 (abs_nonneg _) A0n
  · simp only
    have e : a 1 0 * b 1 0 - a 1 1 * b 1 1 =
        (a 1 0 - a 1 1) * b 1 0 + a 1 1 * (b 1 0 - b 1 1) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul a1' hb10 (abs_nonneg _) A1'n
    · rw [abs_mul]; exact mul_le_mul a0 b1' (abs_nonneg _) A0n
  · have e : arrSd (fun i j => a i j * b i j) =
        a 1 1 * arrSd b + arrSd a * b 1 1 + (a 0 1 - a 1 1) * (b 1 0 - b 1 1) +
        (a 1 0 - a 1 1) * (b 0 1 - b 1 1) +
        ((a 0 1 - a 1 1) + (a 1 0 - a 1 1)) * arrSd b +
        arrSd a * ((b 0 1 - b 1 1) + (b 1 0 - b 1 1)) + arrSd a * arrSd b := by
      unfold arrSd; simp only; ring
    rw [e]
    have t1 : |a 1 1 * arrSd b| ≤ A0 * B2 := by
      rw [abs_mul]; exact mul_le_mul a0 b2 (abs_nonneg _) A0n
    have t2 : |arrSd a * b 1 1| ≤ A2 * B0 := by
      rw [abs_mul]; exact mul_le_mul a2 b0 (abs_nonneg _) A2n
    have t3 : |(a 0 1 - a 1 1) * (b 1 0 - b 1 1)| ≤ A1 * B1' := by
      rw [abs_mul]; exact mul_le_mul a1 b1' (abs_nonneg _) A1n
    have t4 : |(a 1 0 - a 1 1) * (b 0 1 - b 1 1)| ≤ A1' * B1 := by
      rw [abs_mul]; exact mul_le_mul a1' b1 (abs_nonneg _) A1'n
    have t5 : |((a 0 1 - a 1 1) + (a 1 0 - a 1 1)) * arrSd b| ≤ (A1 + A1') * B2 := by
      rw [abs_mul]
      exact mul_le_mul ((abs_add_le _ _).trans (add_le_add a1 a1')) b2 (abs_nonneg _) (by positivity)
    have t6 : |arrSd a * ((b 0 1 - b 1 1) + (b 1 0 - b 1 1))| ≤ A2 * (B1 + B1') := by
      rw [abs_mul]
      exact mul_le_mul a2 ((abs_add_le _ _).trans (add_le_add b1 b1')) (abs_nonneg _) A2n
    have t7 : |arrSd a * arrSd b| ≤ A2 * B2 := by
      rw [abs_mul]; exact mul_le_mul a2 b2 (abs_nonneg _) A2n
    have s7 := abs_sum_seven_le (a 1 1 * arrSd b) (arrSd a * b 1 1)
      ((a 0 1 - a 1 1) * (b 1 0 - b 1 1)) ((a 1 0 - a 1 1) * (b 0 1 - b 1 1))
      (((a 0 1 - a 1 1) + (a 1 0 - a 1 1)) * arrSd b)
      (arrSd a * ((b 0 1 - b 1 1) + (b 1 0 - b 1 1))) (arrSd a * arrSd b)
    linarith

/-- **Product of arrays in ratio form.** -/
theorem IsArrR.mul {a b : Fin 2 → Fin 2 → ℝ} {A B x y : ℝ} (Ha : IsArrR a A x)
    (Hb : IsArrR b B y) : IsArrR (fun i j => a i j * b i j) (16 * A * B) ((x + y) / 2) := by
  obtain ⟨x0, x1, Ha⟩ := Ha
  obtain ⟨y0, y1, Hb⟩ := Hb
  have An : 0 ≤ A := (abs_nonneg _).trans Ha.1
  have Bn : 0 ≤ B := (abs_nonneg _).trans Hb.1
  have H := IsArr.mul Ha Hb
  refine ⟨by linarith, by linarith, ?_⟩
  have hAB : 0 ≤ A * B := mul_nonneg An Bn
  refine H.mono ?_ ?_ ?_ ?_
  · nlinarith
  · nlinarith [mul_nonneg hAB x0, mul_nonneg hAB y0, mul_nonneg (mul_nonneg hAB x0) y0]
  · nlinarith [mul_nonneg hAB x0, mul_nonneg hAB y0, mul_nonneg (mul_nonneg hAB x0) y0]
  · have k4 : 0 ≤ x * y := mul_nonneg x0 y0
    have k1 : x * y ^ 2 ≤ x * y := by nlinarith [mul_nonneg (sub_nonneg.2 y1) k4]
    have k2 : x ^ 2 * y ≤ x * y := by nlinarith [mul_nonneg (sub_nonneg.2 x1) k4]
    have k3 : x ^ 2 * y ^ 2 ≤ x * y := by
      have : x * y ≤ 1 := by nlinarith
      nlinarith [mul_nonneg (sub_nonneg.2 this) k4]
    have key : y ^ 2 + x ^ 2 + 2 * (x * y) + 2 * (x * y ^ 2) + 2 * (x ^ 2 * y) + x ^ 2 * y ^ 2 ≤
        4 * (x + y) ^ 2 := by nlinarith [sq_nonneg (x - y)]
    have := mul_le_mul_of_nonneg_left key hAB
    nlinarith [this]

theorem IsArrR.to_isArr {h : Fin 2 → Fin 2 → ℝ} {b ς : ℝ} (H : IsArrR h b ς) :
    IsArr h b (b * ς) (b * ς) (b * ς ^ 2) := H.2.2

end RegularityStructures.Phi43

end
