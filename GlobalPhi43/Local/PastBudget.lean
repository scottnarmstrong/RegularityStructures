/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.ProbeStep5

/-! The large-past-pair part of the scale argument uses the same U budget at depth 3d/4. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set

/-- The original radius-local U budget applies to every tested causal pair,
even though its second point need not belong to D_d. -/
theorem past_pair_U_budget (U : ParabolicSpace → ParabolicSpace → ℝ)
    {r d d₀ B : ℝ} (hd : 0 < d) (hdd₀ : d ≤ d₀)
    (hU : ∀ e ∈ Ioc (0 : ℝ) d₀, ∀ a ∈ cylinderInterior r e,
      ∀ b ∈ cylinderInterior r e, pdist a b ≤ e → |U a b| ≤ B)
    {x y : ParabolicSpace} (hx : x ∈ cylinderInterior r d)
    (hy : y ∈ pastBall x (d / 4)) : |U x y| ≤ B := by
  have hx' : x ∈ cylinderInterior r (3 * d / 4) :=
    cylinderInterior_mono (by positivity) (by linarith) hx
  have hy' : y ∈ cylinderInterior r (3 * d / 4) :=
    pastBall_subset_interior (by positivity) (by positivity) (by linarith) hx hy
  exact hU (3 * d / 4) ⟨by positivity, by linarith⟩ x hx' y hy' (by linarith [hy.1])

/-- The same coefficient bound controls the larger past ball of Q_-.
There is no stronger U norm on the sampled endpoints. -/
theorem step5_large_past_pair
    (U : ParabolicSpace → ParabolicSpace → ℝ) (ν : ParabolicSpace → Fin 3 → ℝ)
    {r d d₀ η γ B Q : ℝ} (hd : 0 < d) (hdd₀ : d ≤ d₀)
    (hη : 0 < η) (hηsmall : η ≤ 1 / 2) (hγ : 1 ≤ γ) (hB : 0 ≤ B) (hQ : 0 ≤ Q)
    (hU : ∀ e ∈ Ioc (0 : ℝ) d₀, ∀ a ∈ cylinderInterior r e,
      ∀ b ∈ cylinderInterior r e, pdist a b ≤ e → |U a b| ≤ B)
    (hpast : ∀ a ∈ cylinderInterior r d, ∀ b ∈ pastBall a (2 * η * d),
      |affineRemainder U ν a b| ≤ Q * (pdist a b / d) ^ γ)
    {x y : ParabolicSpace} (hx : x ∈ cylinderInterior r d)
    (hy : y ∈ pastBall x (d / 4)) (hfar : 2 * η * d ≤ pdist x y) :
    |affineRemainder U ν x y| / (pdist x y / d) ^ γ ≤
      B / (2 * η) ^ γ +
        3 * ((B + Q * η ^ γ) / η) / (2 * η) ^ (γ - 1) := by
  apply large_remainder_bound U ν x y hd (by positivity) hγ hB
    (by positivity) hfar (past_pair_U_budget U hd hdd₀ hU hx hy)
  exact fun i => step5_coefficient_bound U ν hd hdd₀ hη hηsmall hU hpast hx i

end GlobalPhi43.Local
