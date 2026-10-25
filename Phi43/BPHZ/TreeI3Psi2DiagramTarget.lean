/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramLeaves

/-!
# Comparison with the target majorant

For `0 < s(z), s(z') ≤ 1` and `0 < s(z - z')`, the bounds produced by the diagrams,
`S_{1+δ}`, `s(z - z')^(-1) S_δ` and `s(z - z')^(-2) s(z)^(1-δ)`, are all dominated by the target
majorant `i3Psi2Target δ z z'` of [Hai14, p. 170--171].
-/

public section

namespace RegularityStructures

theorem i3Psi2Target_nonneg (δ : ℝ) (z z' : SpaceTime) : 0 ≤ i3Psi2Target δ z z' := by
  unfold i3Psi2Target
  have h : ∀ (a e : ℝ), 0 ≤ a → 0 ≤ a ^ e := fun a e ha => Real.rpow_nonneg ha e
  have := torusParabolicSize_nonneg (z - z')
  have := torusParabolicSize_nonneg z
  have := torusParabolicSize_nonneg z'
  have a1 := h _ (-(1 + δ)) (torusParabolicSize_nonneg (z - z'))
  have a2 := h _ (-(2 : ℝ)) (torusParabolicSize_nonneg (z - z'))
  have a3 := h _ (1 - δ) (torusParabolicSize_nonneg z)
  have a4 := h _ (1 - δ) (torusParabolicSize_nonneg z')
  have a5 := h _ (-(1 : ℝ)) (torusParabolicSize_nonneg (z - z'))
  have a6 := h _ (-δ) (torusParabolicSize_nonneg z)
  have a7 := h _ (-δ) (torusParabolicSize_nonneg z')
  have a8 := h _ (-(1 + 2 * δ)) (torusParabolicSize_nonneg z)
  have a9 := h _ (-(1 + 2 * δ)) (torusParabolicSize_nonneg z')
  have := mul_nonneg a2 (add_nonneg a3 a4)
  have := mul_nonneg a5 (add_nonneg a6 a7)
  linarith

theorem i3Psi2S_one_add_le_target {δ : ℝ} (hδ : 0 < δ) {z z' : SpaceTime}
    (hz : 0 < torusParabolicSize z) (hz' : 0 < torusParabolicSize z')
    (hz1 : torusParabolicSize z ≤ 1) (hz1' : torusParabolicSize z' ≤ 1) :
    i3Psi2S (1 + δ) z z' ≤ i3Psi2Target δ z z' := by
  have e1 : torusParabolicSize z ^ (-(1 + δ)) ≤ torusParabolicSize z ^ (-(1 + 2 * δ)) :=
    Real.rpow_le_rpow_of_exponent_ge hz hz1 (by linarith)
  have e2 : torusParabolicSize z' ^ (-(1 + δ)) ≤ torusParabolicSize z' ^ (-(1 + 2 * δ)) :=
    Real.rpow_le_rpow_of_exponent_ge hz' hz1' (by linarith)
  have h2 : 0 ≤ torusParabolicSize (z - z') ^ (-(2 : ℝ)) *
      (torusParabolicSize z ^ (1 - δ) + torusParabolicSize z' ^ (1 - δ)) :=
    mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (add_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  have h3 : 0 ≤ torusParabolicSize (z - z') ^ (-(1 : ℝ)) *
      (torusParabolicSize z ^ (-δ) + torusParabolicSize z' ^ (-δ)) :=
    mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (add_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  unfold i3Psi2S i3Psi2Target
  simp only [sub_zero]
  linarith

theorem inv_mul_i3Psi2S_le_target {δ : ℝ} {z z' : SpaceTime}
    (hx : 0 < torusParabolicSize (z - z')) :
    torusParabolicSize (z - z') ^ (-(1 : ℝ)) * i3Psi2S δ z z' ≤ i3Psi2Target δ z z' := by
  have e : torusParabolicSize (z - z') ^ (-(1 : ℝ)) * torusParabolicSize (z - z') ^ (-δ) =
      torusParabolicSize (z - z') ^ (-(1 + δ)) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have h2 : 0 ≤ torusParabolicSize (z - z') ^ (-(2 : ℝ)) *
      (torusParabolicSize z ^ (1 - δ) + torusParabolicSize z' ^ (1 - δ)) :=
    mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (add_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  have h4 : 0 ≤ torusParabolicSize z ^ (-(1 + 2 * δ)) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have h5 : 0 ≤ torusParabolicSize z' ^ (-(1 + 2 * δ)) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  unfold i3Psi2S i3Psi2Target
  simp only [sub_zero]
  rw [mul_add, mul_add, e]
  linarith

theorem inv_sq_mul_le_target_right {δ : ℝ} {z z' : SpaceTime} :
    torusParabolicSize (z - z') ^ (-(2 : ℝ)) * torusParabolicSize z' ^ (1 - δ) ≤
      i3Psi2Target δ z z' := by
  have h1 : 0 ≤ torusParabolicSize (z - z') ^ (-(2 : ℝ)) * torusParabolicSize z ^ (1 - δ) :=
    mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have h3 : 0 ≤ torusParabolicSize (z - z') ^ (-(1 : ℝ)) *
      (torusParabolicSize z ^ (-δ) + torusParabolicSize z' ^ (-δ)) :=
    mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (add_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  have h0 : 0 ≤ torusParabolicSize (z - z') ^ (-(1 + δ)) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have h4 : 0 ≤ torusParabolicSize z ^ (-(1 + 2 * δ)) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have h5 : 0 ≤ torusParabolicSize z' ^ (-(1 + 2 * δ)) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  unfold i3Psi2Target
  rw [mul_add]
  linarith

end RegularityStructures

end
