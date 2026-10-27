/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.TwoSidedAssembly
public import GlobalPhi43.Local.RadiusNormAssembly

/-! The exact weighted-norm assembly after the causal analytic estimate.
This theorem does not assume or assert that the PDE has supplied that estimate. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped BigOperators

/-- A preselected constant converts the small-past budget to the literal
radius-local Schauder bound, with both time orders and the identical radius cutoff. -/
theorem two_sided_radius_norm_of_causal_bound {I : Type*} (A : Finset I) (β : I → ℝ)
    {η γ : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 16) (hγ : 1 ≤ γ)
    (hβγ : ∀ i ∈ A, β i ≤ γ) :
    ∃ C > 0, ∀ (U : ParabolicSpace → ParabolicSpace → ℝ) (ν : ParabolicSpace → Fin 3 → ℝ)
      (r d₀ B Q M : ℝ), 0 ≤ B → 0 ≤ Q → 0 ≤ M →
      (∀ e ∈ Ioc (0 : ℝ) d₀, ∀ a ∈ cylinderInterior r e,
        ∀ b ∈ cylinderInterior r e, pdist a b ≤ e → |U a b| ≤ B) →
      (∀ d ∈ Ioc (0 : ℝ) d₀, ∀ a ∈ cylinderInterior r d, ∀ b ∈ pastBall a (2 * η * d),
        |affineRemainder U ν a b| ≤ Q * (pdist a b / d) ^ γ) →
      (∀ d ∈ Ioc (0 : ℝ) d₀, ∀ x ∈ cylinderInterior r d,
        ∀ b ∈ sourceCylinder r, b ∈ symmetricBall x (d / 2) →
        ∀ z ∈ sourceCylinder r, z ∈ symmetricBall b (d / 4) →
        d ^ γ * |U x z - U x b - U b z| ≤
          M * ∑ i ∈ A, pdist x b ^ β i * pdist b z ^ (γ - β i)) →
      weightedRadiusAffineSeminorm (fun p => U p.1 p.2) r d₀ γ ≤ ENNReal.ofReal (C * (B + Q + M)) := by
  refine ⟨twoSidedFactor A β η γ, twoSidedFactor_pos A β hη, ?_⟩
  intro U ν r d₀ B Q M hB hQ hM hU hpast hthree
  apply weightedRadiusAffineSeminorm_le _ ν
  intro d hd x hx y hy hne hxy
  exact two_sided_remainder_of_causal_bound A β U ν hd.1 hd.2 hη hηsmall hγ hB hQ hM hβγ
    hU (hpast d hd) hx hy hne hxy (hthree d hd x hx)

end GlobalPhi43.Local
