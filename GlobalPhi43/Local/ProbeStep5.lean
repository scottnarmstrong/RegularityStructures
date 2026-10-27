/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.LargeRemainder

/-! Coefficient extraction from the original radius-local U budget
and the small-past remainder estimate. No new data norm is introduced. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set

/-- The radius-local budget supplies each probe at the reduced depth d-s.
Here η=epsilon/32 in the source, so the small-past cutoff is 2ηd. -/
theorem step5_coefficient_bound
    (U : ParabolicSpace → ParabolicSpace → ℝ) (ν : ParabolicSpace → Fin 3 → ℝ)
    {r d d₀ η γ B Q : ℝ} (hd : 0 < d) (hdd₀ : d ≤ d₀)
    (hη : 0 < η) (hηsmall : η ≤ 1 / 2)
    (hU : ∀ e ∈ Ioc (0 : ℝ) d₀, ∀ a ∈ cylinderInterior r e,
      ∀ b ∈ cylinderInterior r e, pdist a b ≤ e → |U a b| ≤ B)
    (hpast : ∀ a ∈ cylinderInterior r d, ∀ b ∈ pastBall a (2 * η * d),
      |affineRemainder U ν a b| ≤ Q * (pdist a b / d) ^ γ)
    {x : ParabolicSpace} (hx : x ∈ cylinderInterior r d) (i : Fin 3) :
    d * |ν x i| ≤ (B + Q * η ^ γ) / η := by
  have hs : 0 < η * d := mul_pos hη hd
  have hsd : η * d ≤ d := by nlinarith
  have he : 0 < d - η * d := by nlinarith
  have hx' : x ∈ cylinderInterior r (d - η * d) :=
    cylinderInterior_mono he.le (by nlinarith) hx
  have hw := coefficientProbe_interior hs.le hsd hx i
  have hprobe := hU (d - η * d) ⟨he, by nlinarith⟩ x hx'
    (coefficientProbe x (η * d) i) hw
    (by rw [coefficientProbe_distance x hs.le]; nlinarith)
  have hrem := hpast x hx (coefficientProbe x (η * d) i)
    (coefficientProbe_past hs (by nlinarith) i)
  rw [coefficientProbe_distance x hs.le, mul_div_cancel_right₀ η hd.ne'] at hrem
  have hb := coefficient_bound_from_probe U ν x i (γ := 0) (Q := Q * η ^ γ)
    hs hprobe (by simpa using hrem)
  have hb' := (le_div_iff₀ hs).mp hb
  simp only [Real.rpow_zero, mul_one] at hb'
  apply (le_div_iff₀ hη).2
  nlinarith [abs_nonneg (ν x i)]

/-- Coefficient estimates on the target two-sided rectangle. All constants depend only on
η and γ; B and Q are precisely the existing U and small-past budgets. -/
theorem step5_large_pair
    (U : ParabolicSpace → ParabolicSpace → ℝ) (ν : ParabolicSpace → Fin 3 → ℝ)
    {r d d₀ η γ B Q : ℝ} (hd : 0 < d) (hdd₀ : d ≤ d₀)
    (hη : 0 < η) (hηsmall : η ≤ 1 / 2) (hγ : 1 ≤ γ) (hB : 0 ≤ B) (hQ : 0 ≤ Q)
    (hU : ∀ e ∈ Ioc (0 : ℝ) d₀, ∀ a ∈ cylinderInterior r e,
      ∀ b ∈ cylinderInterior r e, pdist a b ≤ e → |U a b| ≤ B)
    (hpast : ∀ a ∈ cylinderInterior r d, ∀ b ∈ pastBall a (2 * η * d),
      |affineRemainder U ν a b| ≤ Q * (pdist a b / d) ^ γ)
    {x y : ParabolicSpace} (hx : x ∈ cylinderInterior r d)
    (hy : y ∈ cylinderInterior r d) (hfar : 2 * η * d ≤ pdist x y)
    (hnear : pdist x y ≤ d) :
    |affineRemainder U ν x y| / (pdist x y / d) ^ γ ≤
      B / (2 * η) ^ γ +
        3 * ((B + Q * η ^ γ) / η) / (2 * η) ^ (γ - 1) := by
  apply large_remainder_bound U ν x y hd (by positivity) hγ hB
    (by positivity) hfar (hU d ⟨hd, hdd₀⟩ x hx y hy hnear)
  exact fun i => step5_coefficient_bound U ν hd hdd₀ hη hηsmall hU hpast hx i

end GlobalPhi43.Local
