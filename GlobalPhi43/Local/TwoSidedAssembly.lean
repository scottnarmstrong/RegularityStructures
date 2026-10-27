/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.WeightedFuture
public import GlobalPhi43.Local.TwoSidedBudget

/-! The small-past bound implies the full two-sided radius bound
using precisely the original U budget and the three-point rectangle for all time orders. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped BigOperators

theorem two_sided_remainder_of_causal_bound {I : Type*} (A : Finset I) (β : I → ℝ)
    (U : ParabolicSpace → ParabolicSpace → ℝ) (ν : ParabolicSpace → Fin 3 → ℝ)
    {r d d₀ η γ B Q M : ℝ} (hd : 0 < d) (hdd₀ : d ≤ d₀)
    (hη : 0 < η) (hηsmall : η ≤ 1 / 16) (hγ : 1 ≤ γ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hβγ : ∀ i ∈ A, β i ≤ γ)
    (hU : ∀ e ∈ Ioc (0 : ℝ) d₀, ∀ a ∈ cylinderInterior r e,
      ∀ b ∈ cylinderInterior r e, pdist a b ≤ e → |U a b| ≤ B)
    (hpast : ∀ a ∈ cylinderInterior r d, ∀ b ∈ pastBall a (2 * η * d),
      |affineRemainder U ν a b| ≤ Q * (pdist a b / d) ^ γ)
    {x y : ParabolicSpace} (hx : x ∈ cylinderInterior r d)
    (hy : y ∈ cylinderInterior r d) (hne : y ≠ x) (hxy : pdist x y ≤ d)
    (hthree : ∀ b ∈ sourceCylinder r, b ∈ symmetricBall x (d / 2) →
      ∀ z ∈ sourceCylinder r, z ∈ symmetricBall b (d / 4) →
      d ^ γ * |U x z - U x b - U b z| ≤
        M * ∑ i ∈ A, pdist x b ^ β i * pdist b z ^ (γ - β i)) :
    |affineRemainder U ν x y| ≤
      (twoSidedFactor A β η γ * (B + Q + M)) * (pdist x y / d) ^ γ := by
  let L := largePairBudget η γ B Q
  let Qp := max Q L
  let Qf := Qp * (1 + (Real.sqrt 2) ^ γ) + M * ∑ i ∈ A, (Real.sqrt 2) ^ (γ - β i)
  have hρ := pdist_pos_of_ne hne
  have hp : 0 < (pdist x y / d) ^ γ := Real.rpow_pos_of_pos (div_pos hρ hd) _
  have hηhalf : η ≤ 1 / 2 := by linarith
  have hpastfull : ∀ a ∈ cylinderInterior r d, ∀ b ∈ pastBall a (d / 4),
      |affineRemainder U ν a b| ≤ Qp * (pdist a b / d) ^ γ := by
    intro a ha b hb
    exact past_extension_bound U ν hd hdd₀ hη hηhalf hγ hB hQ hU hpast ha hb
  have hbound : |affineRemainder U ν x y| ≤ max L (max Q Qf) * (pdist x y / d) ^ γ := by
    by_cases hfar : 2 * η * d ≤ pdist x y
    · have hl := step5_large_pair U ν hd hdd₀ hη hηhalf hγ hB hQ hU hpast hx hy hfar hxy
      exact ((div_le_iff₀ hp).mp hl).trans
        (mul_le_mul_of_nonneg_right (le_max_left L (max Q Qf)) hp.le)
    · have hsmall : pdist x y < 2 * η * d := lt_of_not_ge hfar
      by_cases ht : y.1 < x.1
      · exact (hpast x hx y ⟨hsmall, ht⟩).trans
          (mul_le_mul_of_nonneg_right ((le_max_left Q Qf).trans (le_max_right L (max Q Qf))) hp.le)
      · have hsmall' : pdist x y ≤ d / 8 := by nlinarith
        have hf := small_future_pair_weighted A β U ν hd (by linarith)
          (le_trans hQ (le_max_left Q L)) hM hβγ hpastfull hx hy (le_of_not_gt ht) hρ hsmall' hthree
        exact hf.trans (mul_le_mul_of_nonneg_right
          ((le_max_right Q Qf).trans (le_max_right L (max Q Qf))) hp.le)
  exact hbound.trans (mul_le_mul_of_nonneg_right (two_sided_budget_le A β hη hB hQ hM) hp.le)

end GlobalPhi43.Local
