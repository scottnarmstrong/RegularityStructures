/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.FutureRemainder

/-! Estimates with the exact d^gamma boundary weight retained. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set
open scoped BigOperators

/-- Normalize both causal remainders and the three-point majorant at the same depth.
The output has exactly the quotient weight in the final radius seminorm. -/
theorem small_future_pair_weighted {I : Type*} (A : Finset I) (β : I → ℝ)
    (U : ParabolicSpace → ParabolicSpace → ℝ) (ν : ParabolicSpace → Fin 3 → ℝ)
    {r d γ Q M : ℝ} (hd : 0 < d) (hγ : 0 ≤ γ) (hQ : 0 ≤ Q) (hM : 0 ≤ M)
    (hβγ : ∀ i ∈ A, β i ≤ γ)
    (hpast : ∀ a ∈ cylinderInterior r d, ∀ b ∈ pastBall a (d / 4),
      |affineRemainder U ν a b| ≤ Q * (pdist a b / d) ^ γ)
    {x y : ParabolicSpace} (hx : x ∈ cylinderInterior r d)
    (hy : y ∈ cylinderInterior r d) (hfuture : x.1 ≤ y.1)
    (hρ : 0 < pdist x y) (hsmall : pdist x y ≤ d / 8)
    (hthree : ∀ b ∈ MW20.sourceCylinder r, b ∈ symmetricBall x (d / 2) →
      ∀ z ∈ MW20.sourceCylinder r, z ∈ symmetricBall b (d / 4) →
      d ^ γ * |U x z - U x b - U b z| ≤
        M * ∑ i ∈ A, pdist x b ^ β i * pdist b z ^ (γ - β i)) :
    |affineRemainder U ν x y| ≤
      (Q * (1 + (Real.sqrt 2) ^ γ) + M * ∑ i ∈ A, (Real.sqrt 2) ^ (γ - β i)) *
        (pdist x y / d) ^ γ := by
  have hp : 0 < d ^ γ := Real.rpow_pos_of_pos hd _
  have hcausal : ∀ a ∈ cylinderInterior r d, ∀ b ∈ pastBall a (d / 4),
      |affineRemainder U ν a b| ≤ (Q / d ^ γ) * pdist a b ^ γ := by
    intro a ha b hb
    have hh := hpast a ha b hb
    rw [Real.div_rpow (pdist_nonneg a b) hd.le] at hh
    convert hh using 1; ring
  have htrip : ∀ b ∈ MW20.sourceCylinder r, b ∈ symmetricBall x (d / 2) →
      ∀ z ∈ MW20.sourceCylinder r, z ∈ symmetricBall b (d / 4) →
      |U x z - U x b - U b z| ≤
        (M / d ^ γ) * ∑ i ∈ A, pdist x b ^ β i * pdist b z ^ (γ - β i) := by
    intro b hb hbx z hz hzb
    have hh := hthree b hb hbx z hz hzb
    have hh' : |U x z - U x b - U b z| ≤
        (M * ∑ i ∈ A, pdist x b ^ β i * pdist b z ^ (γ - β i)) / d ^ γ :=
      (le_div_iff₀ hp).2 (by rw [mul_comm]; exact hh)
    convert hh' using 1; ring
  have hh := small_future_pair A β U ν hd hγ (div_nonneg hQ hp.le)
    (div_nonneg hM hp.le) hβγ hcausal hx hy hfuture hρ hsmall htrip
  rw [Real.div_rpow hρ.le hd.le]
  convert hh using 1; ring

end GlobalPhi43.Local
