/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiSlab

/-!
# Outer leaves of the secondary and chaos-two pairings

The products `s(y - w)^(-3) s(u - w)^(-1) s(c - w)^(-(1+δ))` of total order `5 + δ` which appear
in the last integration of the diagrams with two `Q²`-links.  If the centres are such that no
two of the three coincide, or the coincidence is `y = c` or `u = c`, the integral is bounded by
`s(a - b)^(-δ)` for the remaining pairs of centres.

Source: [Hai14] = arXiv:1303.5113v4, (10.37a), Lemma 10.14, p. 167--168.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

private theorem alg_case_one {Ca Cb Cc s1 s2 s3 s4 : ℝ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (hCc : 0 ≤ Cc) (n1 : 0 ≤ s1) (n2 : 0 ≤ s2) (n3 : 0 ≤ s3) (n4 : 0 ≤ s4) :
    Ca * (s1 + s2) ≤ (Ca + 2 * Cb + 2 * Cc) * (s1 + s2 + s3 + s4) := by
  nlinarith [mul_nonneg hCa (add_nonneg n3 n4), mul_nonneg hCb (add_nonneg (add_nonneg n1 n2)
    (add_nonneg n3 n4)), mul_nonneg hCc (add_nonneg (add_nonneg n1 n2) (add_nonneg n3 n4))]

private theorem alg_case_two {Ca Cb Cc s1 s2 s3 s4 : ℝ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (hCc : 0 ≤ Cc) (n1 : 0 ≤ s1) (n2 : 0 ≤ s2) (n3 : 0 ≤ s3) (n4 : 0 ≤ s4) :
    Cc * (s3 + s3) ≤ (Ca + 2 * Cb + 2 * Cc) * (s1 + s2 + s3 + s4) := by
  nlinarith [mul_nonneg hCa (add_nonneg (add_nonneg n2 n3) n4), mul_nonneg hCb
    (add_nonneg (add_nonneg n2 n3) n4), mul_nonneg hCc n2, mul_nonneg hCc n4,
    mul_nonneg hCc n3, mul_nonneg hCa n1, mul_nonneg hCb n1, mul_nonneg hCc n1]

private theorem alg_case_three {Ca Cb Cc s1 s2 s3 s4 : ℝ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (hCc : 0 ≤ Cc) (n1 : 0 ≤ s1) (n2 : 0 ≤ s2) (n3 : 0 ≤ s3) (n4 : 0 ≤ s4) :
    Cb * (s4 + s4) ≤ (Ca + 2 * Cb + 2 * Cc) * (s1 + s2 + s3 + s4) := by
  nlinarith [mul_nonneg hCa (add_nonneg (add_nonneg n1 n3) n4), mul_nonneg hCc
    (add_nonneg (add_nonneg n1 n3) n4), mul_nonneg hCb n1, mul_nonneg hCb n3,
    mul_nonneg hCb n4, mul_nonneg hCa n2, mul_nonneg hCb n2, mul_nonneg hCc n2]

/-- The outer leaf: integral of `s(y-w)^(-3) s(u-w)^(-1) s(c-w)^(-(1+δ))`. -/
theorem singularIntLe_outer_leaf {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y u c : SpaceTime,
      ((0 < torusParabolicSize (y - c) ∧ 0 < torusParabolicSize (u - c)) ∨
        (y = c ∧ 0 < torusParabolicSize (y - u) ∧ 0 < torusParabolicSize (u - y)) ∨
        (u = c ∧ 0 < torusParabolicSize (y - u) ∧ 0 < torusParabolicSize (u - y))) →
      SingularIntLe (fun w => singularPow 3 y w * singularPow 1 u w * singularPow (1 + δ) c w)
        (L * (torusParabolicSize (y - c) ^ (-δ) + torusParabolicSize (u - c) ^ (-δ) +
          torusParabolicSize (y - u) ^ (-δ) + torusParabolicSize (u - y) ^ (-δ))) := by
  obtain ⟨Ca, hCa, ha⟩ := singularIntLe_mul_three (a := 3) (b := 1) (c := 1 + δ) (η := δ)
    (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) hδ (by ring)
  obtain ⟨Cb, hCb, hb⟩ := singularIntLe_mul_three (a := 1) (b := 1 + δ) (c := 3) (η := δ)
    (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) hδ (by ring)
  obtain ⟨Cc, hCc, hc⟩ := singularIntLe_mul_three (a := 3) (b := 1 + δ) (c := 1) (η := δ)
    (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num) hδ (by ring)
  refine ⟨Ca + 2 * Cb + 2 * Cc, by positivity, fun y u c h => ?_⟩
  have n1 : 0 ≤ torusParabolicSize (y - c) ^ (-δ) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have n2 : 0 ≤ torusParabolicSize (u - c) ^ (-δ) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have n3 : 0 ≤ torusParabolicSize (y - u) ^ (-δ) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have n4 : 0 ≤ torusParabolicSize (u - y) ^ (-δ) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  rcases h with ⟨h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩
  · refine (ha y u c h1 h2).mono_right ?_
    exact alg_case_one hCa hCb hCc n1 n2 n3 n4
  · have e : (fun w => singularPow 3 y w * singularPow 1 u w * singularPow (1 + δ) y w) =
        fun w => singularPow 3 y w * singularPow (1 + δ) y w * singularPow 1 u w := by
      funext w; ring
    rw [e]
    refine (hc y y u h1 h1).mono_right ?_
    exact alg_case_two hCa hCb hCc n1 n2 n3 n4
  · have e : (fun w => singularPow 3 y w * singularPow 1 u w * singularPow (1 + δ) u w) =
        fun w => singularPow 1 u w * singularPow (1 + δ) u w * singularPow 3 y w := by
      funext w; ring
    rw [e]
    refine (hb u u y h2 h2).mono_right ?_
    exact alg_case_three hCa hCb hCc n1 n2 n3 n4

end RegularityStructures

end
