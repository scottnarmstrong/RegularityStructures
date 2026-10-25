/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2TestedSize

/-!
# Hölder increments of a difference of two kernels by interpolation

If two kernels `J_a`, `J_b` have increments `|J(u + h) - J(u)| ≤ B s(h) s(u)^(-4)` and their
difference satisfies `|J_a - J_b| ≤ B m s^(-4)`, then the increments of the difference satisfy, for
`θ ∈ (0, 1]`, `|Δ(u + h) - Δ(u)| ≤ 17 B m^θ s(h)^(1-θ) s(u)^(-(3+θ)-(1-θ))` whenever
`s(h) ≤ s(u)/2` (interpolation `min(a, b) ≤ a^(1-θ) b^θ`).
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem min_le_rpow_mul_rpow {a b θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hθ : 0 ≤ θ)
    (hθ1 : θ ≤ 1) {x : ℝ} (h1 : x ≤ a) (h2 : x ≤ b) : x ≤ a ^ (1 - θ) * b ^ θ := by
  rcases le_total a b with hab | hab
  · calc x ≤ a := h1
      _ = a ^ (1 - θ) * a ^ θ := by
          rw [← Real.rpow_add' ha (by linarith)]; simp
      _ ≤ a ^ (1 - θ) * b ^ θ :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha hab hθ) (Real.rpow_nonneg ha _)
  · calc x ≤ b := h2
      _ = b ^ (1 - θ) * b ^ θ := by
          rw [← Real.rpow_add' hb (by linarith)]; simp
      _ ≤ a ^ (1 - θ) * b ^ θ :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hb hab (by linarith))
            (Real.rpow_nonneg hb _)

private theorem interp_alg {B m r T θ : ℝ} (hB : 0 ≤ B) (hm : 0 ≤ m) (hr : 0 ≤ r) (hT : 0 < T)
    (hθ1 : θ ≤ 1) :
    ((2 * B * r) * T) ^ (1 - θ) * ((17 * B * m) * T) ^ θ ≤ (17 * B) * m ^ θ * r ^ (1 - θ) * T := by
  rw [Real.mul_rpow (by positivity) hT.le, Real.mul_rpow (by positivity) hT.le,
    Real.mul_rpow (by positivity) hr, Real.mul_rpow (by positivity) hm,
    Real.mul_rpow (by positivity) hB, Real.mul_rpow (by positivity) hB]
  have eB : B ^ (1 - θ) * B ^ θ = B := by
    rw [← Real.rpow_add' hB (by linarith)]; simp
  have eT : T ^ (1 - θ) * T ^ θ = T := by
    rw [← Real.rpow_add' hT.le (by linarith)]; simp
  have e17 : (17 : ℝ) ^ (1 - θ) * 17 ^ θ = 17 := by
    rw [← Real.rpow_add' (by norm_num) (by linarith)]; simp
  have h2 : (2 : ℝ) ^ (1 - θ) ≤ 17 ^ (1 - θ) :=
    Real.rpow_le_rpow (by norm_num) (by norm_num) (by linarith)
  have p1 : 0 ≤ (17 : ℝ) ^ θ := Real.rpow_nonneg (by norm_num) _
  have pB1 : 0 ≤ B ^ (1 - θ) := Real.rpow_nonneg hB _
  have pB2 : 0 ≤ B ^ θ := Real.rpow_nonneg hB _
  have pT1 : 0 ≤ T ^ (1 - θ) := Real.rpow_nonneg hT.le _
  have pT2 : 0 ≤ T ^ θ := Real.rpow_nonneg hT.le _
  have pm : 0 ≤ m ^ θ := Real.rpow_nonneg hm _
  have pr : 0 ≤ r ^ (1 - θ) := Real.rpow_nonneg hr _
  calc 2 ^ (1 - θ) * B ^ (1 - θ) * r ^ (1 - θ) * T ^ (1 - θ) *
        (17 ^ θ * B ^ θ * m ^ θ * T ^ θ)
      = (2 ^ (1 - θ) * 17 ^ θ) * (B ^ (1 - θ) * B ^ θ) * (T ^ (1 - θ) * T ^ θ) *
        (r ^ (1 - θ) * m ^ θ) := by ring
    _ ≤ (17 ^ (1 - θ) * 17 ^ θ) * (B ^ (1 - θ) * B ^ θ) * (T ^ (1 - θ) * T ^ θ) *
        (r ^ (1 - θ) * m ^ θ) := by
        gcongr
    _ = (17 * B) * m ^ θ * r ^ (1 - θ) * T := by rw [e17, eB, eT]; ring

/-- **Hölder increments of the difference of two kernels.** -/
theorem holder_increment_sub_of_bounds {Ja Jb : SpaceTime → ℝ} {B m θ : ℝ} (hB : 0 ≤ B)
    (hm : 0 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hJa : ∀ u h : SpaceTime, 0 < torusParabolicSize u → torusParabolicSize h ≤ torusParabolicSize u / 2 →
      |Ja (u + h) - Ja u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)))
    (hJb : ∀ u h : SpaceTime, 0 < torusParabolicSize u → torusParabolicSize h ≤ torusParabolicSize u / 2 →
      |Jb (u + h) - Jb u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)))
    (hΔ : ∀ x, 0 < torusParabolicSize x →
      |Ja x - Jb x| ≤ B * m * torusParabolicSize x ^ (-(4 : ℝ))) :
    ∀ u h : SpaceTime, 0 < torusParabolicSize u → torusParabolicSize h ≤ torusParabolicSize u / 2 →
      |(Ja (u + h) - Jb (u + h)) - (Ja u - Jb u)| ≤
        (17 * B) * m ^ θ * torusParabolicSize h ^ (1 - θ) *
          torusParabolicSize u ^ (-(3 + θ) - (1 - θ)) := by
  intro u h hu hh
  set t := torusParabolicSize u with ht
  set r := torusParabolicSize h with hr
  have hr0 : 0 ≤ r := torusParabolicSize_nonneg h
  have hsum : t / 2 ≤ torusParabolicSize (u + h) := by
    have := torusParabolicSize_sub_le_add u h
    linarith
  have hpos : 0 < torusParabolicSize (u + h) := lt_of_lt_of_le (by positivity) hsum
  set T := t ^ (-(4 : ℝ)) with hT
  have hT0 : 0 < T := Real.rpow_pos_of_pos hu _
  have hT16 : torusParabolicSize (u + h) ^ (-(4 : ℝ)) ≤ 16 * T := by
    have h1 : torusParabolicSize (u + h) ^ (-(4 : ℝ)) ≤ (t / 2) ^ (-(4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hsum (by norm_num)
    have h2 : (t / 2) ^ (-(4 : ℝ)) = 16 * T := by
      rw [Real.div_rpow hu.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      have : (2 : ℝ) ^ (4 : ℝ) = 16 := by norm_num
      rw [this, hT]
      field_simp
    exact h1.trans h2.le
  have b1 : |(Ja (u + h) - Jb (u + h)) - (Ja u - Jb u)| ≤ (2 * B * r) * T := by
    have e : (Ja (u + h) - Jb (u + h)) - (Ja u - Jb u) =
        (Ja (u + h) - Ja u) - (Jb (u + h) - Jb u) := by ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have := hJa u h hu hh
    have := hJb u h hu hh
    linarith
  have b2 : |(Ja (u + h) - Jb (u + h)) - (Ja u - Jb u)| ≤ (17 * B * m) * T := by
    refine (abs_sub _ _).trans ?_
    have x1 := hΔ (u + h) hpos
    have x2 := hΔ u hu
    have : B * m * torusParabolicSize (u + h) ^ (-(4 : ℝ)) ≤ B * m * (16 * T) :=
      mul_le_mul_of_nonneg_left hT16 (mul_nonneg hB hm)
    linarith
  have key := min_le_rpow_mul_rpow (a := (2 * B * r) * T) (b := (17 * B * m) * T) (θ := θ)
    (by positivity) (by positivity) hθ.le hθ1 b1 b2
  refine key.trans ((interp_alg hB hm hr0 hT0 hθ1).trans (le_of_eq ?_))
  have e : (-(3 + θ) - (1 - θ) : ℝ) = -(4 : ℝ) := by ring
  rw [e]

end RegularityStructures.Phi43

end
