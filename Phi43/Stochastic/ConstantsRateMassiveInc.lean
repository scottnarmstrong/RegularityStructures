/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsRateHeatInc
public import Phi43.Stochastic.ConstantsRateMassiveBounds

/-!
# Space and time increments of the massive heat kernel at fixed time

The massive kernel is `G(τ, x) = e^{-τ} p_τ(x)` for `τ > 0`.  Spatial increments of `G` at a fixed
positive time and time increments at a fixed point (between positive times) are deduced from the
increments of the lifted heat kernel, with the factor `e^{-τ}` accounted for separately.
-/

@[expose] public noncomputable section

open Real Set

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem massive_eq_lift {τ : ℝ} (hτ : 0 < τ) (y : Fin 3 → ℝ) :
    massiveHeatKernel (τ, torusProj y) = exp (-τ) * heatKernelLift τ y := by
  simp only [massiveHeatKernel, hτ, ite_true]
  rw [heatKernel_comp_torusProj_eq_lift]

private theorem heatLiftNu_centered (x : Torus3) :
    heatLiftNu (torusCenteredRep x) = torusSpatialNorm x := by
  unfold heatLiftNu
  rw [torusProj_torusCenteredRep]

private theorem sum_abs_neg (g : Fin 3 → ℝ) : ∑ j, |(-g) j| = ∑ j, |g j| := by
  simp

theorem constantsRate_massive_space_small :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (x a : Torus3), 0 < τ → τ ≤ 1 →
      ∑ j, |torusCenteredRep a j| ≤ (√τ + torusSpatialNorm x) / 8 →
      |massiveHeatKernel (τ, x - a) - massiveHeatKernel (τ, x)| ≤
        C * (∑ j, |torusCenteredRep a j|) * (√τ + torusSpatialNorm x) ^ (-(4 : ℝ)) := by
  obtain ⟨C, hC, hinc⟩ := heatLift_increment_small
  refine ⟨C, hC, ?_⟩
  intro τ x a hτ hτ1 hA
  set y : Fin 3 → ℝ := torusCenteredRep x with hy
  set b : Fin 3 → ℝ := -torusCenteredRep a with hb
  have hx : torusProj y = x := torusProj_torusCenteredRep x
  have hproj : torusProj (y + b) = x - a := by
    rw [RegularityStructures.PDE.torusProj_add, hx, hb, RegularityStructures.PDE.torusProj_neg,
      torusProj_torusCenteredRep, sub_eq_add_neg]
  have hνy : heatLiftNu y = torusSpatialNorm x := heatLiftNu_centered x
  have hsum : ∑ j, |b j| = ∑ j, |torusCenteredRep a j| := sum_abs_neg _
  have h1 := hinc τ hτ hτ1 y b (by rw [hsum, hνy]; exact hA)
  rw [hsum, hνy] at h1
  have e1 : massiveHeatKernel (τ, x - a) = exp (-τ) * heatKernelLift τ (y + b) := by
    rw [← hproj]
    exact massive_eq_lift hτ _
  have e2 : massiveHeatKernel (τ, x) = exp (-τ) * heatKernelLift τ y := by
    rw [← hx]
    exact massive_eq_lift hτ _
  rw [e1, e2, ← mul_sub, abs_mul, abs_of_nonneg (exp_nonneg _)]
  have hexp : exp (-τ) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  calc
    exp (-τ) * |heatKernelLift τ (y + b) - heatKernelLift τ y| ≤
        1 * |heatKernelLift τ (y + b) - heatKernelLift τ y| :=
      mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact h1

theorem constantsRate_massive_space_large :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (x a : Torus3), 1 / 2 ≤ τ →
      |massiveHeatKernel (τ, x - a) - massiveHeatKernel (τ, x)| ≤
        C * exp (-τ) * ∑ j, |torusCenteredRep a j| := by
  obtain ⟨C, hC, hinc⟩ := heatLift_increment_large
  refine ⟨C, hC, ?_⟩
  intro τ x a hτ
  have hτ0 : 0 < τ := by linarith
  set y : Fin 3 → ℝ := torusCenteredRep x with hy
  set b : Fin 3 → ℝ := -torusCenteredRep a with hb
  have hx : torusProj y = x := torusProj_torusCenteredRep x
  have hproj : torusProj (y + b) = x - a := by
    rw [RegularityStructures.PDE.torusProj_add, hx, hb, RegularityStructures.PDE.torusProj_neg,
      torusProj_torusCenteredRep, sub_eq_add_neg]
  have hsum : ∑ j, |b j| = ∑ j, |torusCenteredRep a j| := sum_abs_neg _
  have h1 := hinc τ hτ y b
  rw [hsum] at h1
  have e1 : massiveHeatKernel (τ, x - a) = exp (-τ) * heatKernelLift τ (y + b) := by
    rw [← hproj]
    exact massive_eq_lift hτ0 _
  have e2 : massiveHeatKernel (τ, x) = exp (-τ) * heatKernelLift τ y := by
    rw [← hx]
    exact massive_eq_lift hτ0 _
  rw [e1, e2, ← mul_sub, abs_mul, abs_of_nonneg (exp_nonneg _)]
  calc
    exp (-τ) * |heatKernelLift τ (y + b) - heatKernelLift τ y| ≤
        exp (-τ) * (C * ∑ j, |torusCenteredRep a j|) :=
      mul_le_mul_of_nonneg_left h1 (exp_nonneg _)
    _ = C * exp (-τ) * ∑ j, |torusCenteredRep a j| := by ring

private theorem massive_time_split {τ η : ℝ} (hτ : 0 < τ) (hτη : 0 < τ + η) (hη : |η| ≤ 1)
    (y : Fin 3 → ℝ) :
    |massiveHeatKernel (τ + η, torusProj y) - massiveHeatKernel (τ, torusProj y)| ≤
      exp (-(τ + η)) * |heatKernelLift (τ + η) y - heatKernelLift τ y| +
        2 * |η| * massiveHeatKernel (τ, torusProj y) := by
  rw [massive_eq_lift hτη, massive_eq_lift hτ]
  have hid : exp (-(τ + η)) * heatKernelLift (τ + η) y - exp (-τ) * heatKernelLift τ y =
      exp (-(τ + η)) * (heatKernelLift (τ + η) y - heatKernelLift τ y) +
        (exp (-η) - 1) * (exp (-τ) * heatKernelLift τ y) := by
    have : exp (-(τ + η)) = exp (-η) * exp (-τ) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [this]
    ring
  rw [hid]
  have hG0 : 0 ≤ exp (-τ) * heatKernelLift τ y := by
    rw [← massive_eq_lift hτ]
    exact massiveHeatKernel_nonneg _
  have hexp : |exp (-η) - 1| ≤ 2 * |η| := by
    have := Real.abs_exp_sub_one_le (x := -η) (by rwa [abs_neg])
    rwa [abs_neg] at this
  calc
    |exp (-(τ + η)) * (heatKernelLift (τ + η) y - heatKernelLift τ y) +
        (exp (-η) - 1) * (exp (-τ) * heatKernelLift τ y)| ≤
        |exp (-(τ + η)) * (heatKernelLift (τ + η) y - heatKernelLift τ y)| +
          |(exp (-η) - 1) * (exp (-τ) * heatKernelLift τ y)| := abs_add_le _ _
    _ = exp (-(τ + η)) * |heatKernelLift (τ + η) y - heatKernelLift τ y| +
          |exp (-η) - 1| * (exp (-τ) * heatKernelLift τ y) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (exp_nonneg _), abs_of_nonneg hG0]
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_right hexp hG0
      linarith

theorem constantsRate_massive_time_small :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ η Q : ℝ) (x : Torus3), 0 < Q → 0 < τ → 0 < τ + η → |η| ≤ 1 →
      (∀ σ ∈ uIcc τ (τ + η), 0 < σ ∧ σ ≤ 1 ∧ Q ≤ √σ + torusSpatialNorm x) →
      |massiveHeatKernel (τ + η, x) - massiveHeatKernel (τ, x)| ≤
        C * |η| * Q ^ (-(5 : ℝ)) + 2 * |η| * massiveHeatKernel (τ, x) := by
  obtain ⟨C, hC, hinc⟩ := heatLift_time_increment_small
  refine ⟨C, hC, ?_⟩
  intro τ η Q x hQ hτ hτη hη hσ
  set y : Fin 3 → ℝ := torusCenteredRep x with hy
  have hx : torusProj y = x := torusProj_torusCenteredRep x
  have hνy : heatLiftNu y = torusSpatialNorm x := heatLiftNu_centered x
  have h1 := hinc τ η Q y hQ (by
    intro σ hs
    obtain ⟨a, b, c⟩ := hσ σ hs
    exact ⟨a, b, by rw [hνy]; exact c⟩)
  have h2 := massive_time_split hτ hτη hη y
  rw [hx] at h2
  have hexp : exp (-(τ + η)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  refine h2.trans ?_
  have := mul_le_mul hexp h1 (abs_nonneg _) zero_le_one
  linarith

theorem constantsRate_massive_time_large :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ η : ℝ) (x : Torus3), 0 < τ → 0 < τ + η → |η| ≤ 1 →
      (∀ σ ∈ uIcc τ (τ + η), 1 / 2 ≤ σ) →
      |massiveHeatKernel (τ + η, x) - massiveHeatKernel (τ, x)| ≤
        C * |η| * exp (-(τ + η)) + 2 * |η| * massiveHeatKernel (τ, x) := by
  obtain ⟨C, hC, hinc⟩ := heatLift_time_increment_large
  refine ⟨C, hC, ?_⟩
  intro τ η x hτ hτη hη hσ
  set y : Fin 3 → ℝ := torusCenteredRep x with hy
  have hx : torusProj y = x := torusProj_torusCenteredRep x
  have h1 := hinc τ η y hσ
  have h2 := massive_time_split hτ hτη hη y
  rw [hx] at h2
  refine h2.trans ?_
  have := mul_le_mul_of_nonneg_left h1 (exp_nonneg (-(τ + η)))
  nlinarith [this]

end RegularityStructures.Phi43

end
