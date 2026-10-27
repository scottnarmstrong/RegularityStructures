/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.FutureBridge
public import GlobalPhi43.Local.SmoothingComparison

/-! The algebra and finite-power estimate for the future-pair bridge.
The incoming causal remainder estimates are explicit; this module does not
postulate or prove the remaining causal Schauder theorem. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures
open scoped BigOperators

/-- R(a,b), with the same spatial coefficient at every radius and time order. -/
def affineRemainder (U : ParabolicSpace → ParabolicSpace → ℝ)
    (ν : ParabolicSpace → Fin 3 → ℝ) (a b : ParabolicSpace) : ℝ :=
  U a b - spatialLinear (ν a) (b - a)

/-- Sharing y's spatial coordinate cancels the coefficient at y entirely.
No derivative or Holder bound of ν is needed in the future-pair argument. -/
theorem affineRemainder_vertical_identity
    (U : ParabolicSpace → ParabolicSpace → ℝ) (ν : ParabolicSpace → Fin 3 → ℝ)
    (x y z : ParabolicSpace) (hz : z.2 = y.2) :
    affineRemainder U ν x y = affineRemainder U ν x z - affineRemainder U ν y z -
      (U x z - U x y - U y z) := by
  unfold affineRemainder spatialLinear
  simp only [Prod.snd_sub, hz, sub_self, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  ring

/-- The bridge estimate before multiplication by the boundary weight.
Setting s=sqrt(2), rho=d(x,y) gives exactly the finite constants used in
section 3 of the causal review. Only the two causal remainders and the
all-time-order three-point defect occur on the right. -/
theorem future_remainder_bound {I : Type*} (A : Finset I) (β : I → ℝ)
    (U : ParabolicSpace → ParabolicSpace → ℝ) (ν : ParabolicSpace → Fin 3 → ℝ)
    (x y z : ParabolicSpace) {γ ρ s Q M : ℝ}
    (hz : z.2 = y.2) (hγ : 0 ≤ γ) (hρ : 0 < ρ) (hs : 0 ≤ s)
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hβγ : ∀ i ∈ A, β i ≤ γ)
    (hyz : pdist y z ≤ s * ρ)
    (hxrem : |affineRemainder U ν x z| ≤ Q * ρ ^ γ)
    (hyrem : |affineRemainder U ν y z| ≤ Q * pdist y z ^ γ)
    (hthree : |U x z - U x y - U y z| ≤
      M * ∑ i ∈ A, ρ ^ β i * pdist y z ^ (γ - β i)) :
    |affineRemainder U ν x y| ≤
      (Q * (1 + s ^ γ) + M * ∑ i ∈ A, s ^ (γ - β i)) * ρ ^ γ := by
  have hybound : |affineRemainder U ν y z| ≤ Q * s ^ γ * ρ ^ γ := by
    calc
      _ ≤ Q * (s * ρ) ^ γ := hyrem.trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (pdist_nonneg y z) hyz hγ) hQ)
      _ = _ := by rw [Real.mul_rpow hs hρ.le]; ring
  have hsum : (∑ i ∈ A, ρ ^ β i * pdist y z ^ (γ - β i)) ≤
      (∑ i ∈ A, s ^ (γ - β i)) * ρ ^ γ := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    calc
      _ ≤ ρ ^ β i * (s * ρ) ^ (γ - β i) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (pdist_nonneg y z) hyz (sub_nonneg.mpr (hβγ i hi)))
          (Real.rpow_nonneg hρ.le _)
      _ = s ^ (γ - β i) * (ρ ^ β i * ρ ^ (γ - β i)) := by
        rw [Real.mul_rpow hs hρ.le]
        ring
      _ = _ := by
        rw [← Real.rpow_add hρ]
        have he : β i + (γ - β i) = γ := by ring
        rw [he]
  have hthree' := hthree.trans (mul_le_mul_of_nonneg_left hsum hM)
  calc
    _ ≤ (|affineRemainder U ν x z| + |affineRemainder U ν y z|) +
        |U x z - U x y - U y z| := by
      rw [affineRemainder_vertical_identity U ν x y z hz]
      exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ (Q * ρ ^ γ + Q * s ^ γ * ρ ^ γ) +
        M * ((∑ i ∈ A, s ^ (γ - β i)) * ρ ^ γ) :=
      add_le_add (add_le_add hxrem hybound) hthree'
    _ = _ := by ring

/-- The small future/equal-time conversion on the full local rectangle.
The causal bound `hpast` is assumed; the three-point bound is used on
the time-free triple. No regularity of the coefficient map is
assumed and no derivative norm is added. -/
theorem small_future_pair {I : Type*} (A : Finset I) (β : I → ℝ)
    (U : ParabolicSpace → ParabolicSpace → ℝ) (ν : ParabolicSpace → Fin 3 → ℝ)
    {r d γ Q M : ℝ} (hd : 0 < d) (hγ : 0 ≤ γ) (hQ : 0 ≤ Q) (hM : 0 ≤ M)
    (hβγ : ∀ i ∈ A, β i ≤ γ)
    (hpast : ∀ a ∈ cylinderInterior r d, ∀ b ∈ pastBall a (d / 4),
      |affineRemainder U ν a b| ≤ Q * pdist a b ^ γ)
    {x y : ParabolicSpace} (hx : x ∈ cylinderInterior r d)
    (hy : y ∈ cylinderInterior r d) (hfuture : x.1 ≤ y.1)
    (hρ : 0 < pdist x y) (hsmall : pdist x y ≤ d / 8)
    (hthree : ∀ b ∈ MW20.sourceCylinder r, b ∈ symmetricBall x (d / 2) →
      ∀ z ∈ MW20.sourceCylinder r, z ∈ symmetricBall b (d / 4) →
      |U x z - U x b - U b z| ≤
        M * ∑ i ∈ A, pdist x b ^ β i * pdist b z ^ (γ - β i)) :
    |affineRemainder U ν x y| ≤
      (Q * (1 + (Real.sqrt 2) ^ γ) + M * ∑ i ∈ A, (Real.sqrt 2) ^ (γ - β i)) *
        pdist x y ^ γ := by
  let z := verticalBridge x y
  have hzhalf : z ∈ cylinderInterior r (d / 2) :=
    verticalBridge_interior_half hd hx hy hsmall
  have htimes := verticalBridge_time_lt hρ hfuture
  have hright := verticalBridge_distance_right_lt hd hfuture hsmall
  have hleft : pdist x z < d / 4 := by
    rw [verticalBridge_distance_left]
    linarith
  have hxrem : |affineRemainder U ν x z| ≤ Q * pdist x y ^ γ := by
    simpa only [z, verticalBridge_distance_left] using hpast x hx z ⟨hleft, htimes.1⟩
  have hyrem := hpast y hy z ⟨hright, htimes.2⟩
  have htrip := hthree y (cylinderInterior_mem_domain hd.le hy)
    (by change pdist x y < d / 2; linarith)
    z (cylinderInterior_mem_domain (by positivity) hzhalf) hright
  exact future_remainder_bound A β U ν x y z rfl hγ hρ (Real.sqrt_nonneg 2)
    hQ hM hβγ (verticalBridge_distance_right hfuture) hxrem hyrem htrip

end GlobalPhi43.Local
