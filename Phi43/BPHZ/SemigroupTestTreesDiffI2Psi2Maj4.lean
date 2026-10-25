/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI2Psi2Quad
public import Phi43.BPHZ.TreeI2Psi2DiagramMultiChaosFour

/-!
# The chaos-`4` majorant of the difference of `I(Ψ²) Ψ²`, for arbitrary `x, y, y'`

`i2Psi2Diff_maj4_global`: for `θ ∈ (0, 1/8]`, `∫∫ i2Psi2Maj4 θ K x y y'` is at most
`C B² (1 + D)² (1 + |y.1 - x.1|) i2Psi2DiffSg θ x y y'`, with `D` bounding `s(a - b)` on the time
slab (`I2Psi2DiffSlab`).  There is no smallness assumption on `s(y - x)`, `s(y' - x)`.
-/

public section

open MeasureTheory

namespace RegularityStructures

theorem i2Psi2Triple_zero_eq_quad (K : SpaceTime → ℝ) (x y y' : SpaceTime) (a c : ℝ) :
    i2Psi2Triple K x y y' y' y a 0 c = i2Psi2Quad K x y y' 0 a 0 c := by
  funext q
  simp only [i2Psi2Triple, i2Psi2Quad, neg_zero, Real.rpow_zero]
  ring

theorem i2Psi2Diff_term_le {c B2 U F τ g S : ℝ} (hc : 0 ≤ c) (hB2 : 0 ≤ B2) (hU0 : 0 ≤ U)
    (hU : U ≤ F) (hτ : 0 ≤ τ) (hg0 : 0 ≤ g) (hgS : g ≤ S) :
    c * B2 * U * τ * g ≤ c * B2 * F * τ * S := by
  have hS : 0 ≤ S := hg0.trans hgS
  have hF : 0 ≤ F := hU0.trans hU
  have h1 : U * τ * g ≤ F * τ * S :=
    mul_le_mul (mul_le_mul_of_nonneg_right hU hτ) hgS hg0 (mul_nonneg hF hτ)
  calc c * B2 * U * τ * g = (c * B2) * (U * τ * g) := by ring
    _ ≤ (c * B2) * (F * τ * S) := mul_le_mul_of_nonneg_left h1 (mul_nonneg hc hB2)
    _ = _ := by ring

theorem i2Psi2Diff_prod_term_le {c B2 U F τ P S : ℝ} (hc : 0 ≤ c) (hB2 : 0 ≤ B2) (hU0 : 0 ≤ U)
    (hU : U * U ≤ F) (hτ : 1 ≤ τ) (hP0 : 0 ≤ P) (hPS : P ≤ 5 * S) :
    c * B2 * U * U * P ≤ 5 * c * B2 * F * τ * S := by
  have hS : 0 ≤ S := by nlinarith
  have hF : 0 ≤ F := (mul_nonneg hU0 hU0).trans hU
  have h1 : U * U * P ≤ F * (τ * (5 * S)) := by
    refine mul_le_mul hU ?_ hP0 hF
    calc P ≤ 5 * S := hPS
      _ = 1 * (5 * S) := by ring
      _ ≤ τ * (5 * S) := mul_le_mul_of_nonneg_right hτ (by positivity)
  calc c * B2 * U * U * P = (c * B2) * (U * U * P) := by ring
    _ ≤ (c * B2) * (F * (τ * (5 * S))) := mul_le_mul_of_nonneg_left h1 (mul_nonneg hc hB2)
    _ = _ := by ring

/-- **The chaos-`4` majorant, globally.** -/
theorem i2Psi2Diff_maj4_global {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ} {B : ℝ}, SingularKernelData K Q B →
      ∀ (x y y' : SpaceTime) {D : ℝ}, 0 ≤ D → I2Psi2DiffSlab x y y' D →
      0 < torusParabolicSize (y - y') → 0 < torusParabolicSize (x - y) →
      0 < torusParabolicSize (x - y') →
      I2Psi2DiffIntBd (i2Psi2Maj4 θ K x y y')
        (C * B ^ 2 * (1 + D) ^ 2 * (1 + |y.1 - x.1|) * i2Psi2DiffSg θ x y y') := by
  obtain ⟨C1, hC1, h1⟩ := i2Psi2Diff_triple_slab (a := 0) (b := 2 + 2 * θ) (c := 0)
    (δ := 1 / 4) (η := 2 * θ + 1 / 4) le_rfl (by linarith) le_rfl (by norm_num) (by linarith)
    (by norm_num) (by linarith) (by linarith) (by linarith)
  obtain ⟨C2, hC2, h2⟩ := i2Psi2Diff_triple_slab (a := 0) (b := 2) (c := 0)
    (δ := 1 / 4) (η := 1 / 4) le_rfl (by norm_num) le_rfl (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C5, hC5, h5⟩ := i2Psi2Diff_triple_slab (a := 1 + 2 * θ) (b := 1) (c := 1)
    (δ := 1 / 4) (η := 1 / 4) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith)
  obtain ⟨C6, hC6, h6⟩ := i2Psi2Diff_triple_slab (a := 1) (b := 1 + 2 * θ) (c := 1)
    (δ := 1 / 4) (η := 2 * θ + 1 / 4) (by norm_num) (by linarith) (by norm_num) (by norm_num)
    (by linarith) (by norm_num) (by linarith) (by linarith) (by linarith)
  obtain ⟨C7, hC7, h7⟩ := i2Psi2Diff_triple_slab (a := 1) (b := 1) (c := 1 + 2 * θ)
    (δ := 1 / 4) (η := 2 * θ + 1 / 4) (by norm_num) (by norm_num) (by linarith) (by norm_num)
    (by linarith) (by linarith) (by norm_num) (by linarith) (by linarith)
  obtain ⟨C8, hC8, h8⟩ := i2Psi2Diff_triple_slab (a := 1) (b := 1) (c := 1)
    (δ := 1 / 4) (η := 1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Q3, hQ3, q3⟩ := i2Psi2Diff_quad_global (a := 0) (b := 2 + 2 * θ) (c := 0) (e := 2)
    (δ := 1 / 4) (η₁ := 2 * θ + 1 / 4) (η₂ := 1 / 4) le_rfl (by linarith) le_rfl (by norm_num)
    (by norm_num) (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num)
    (by norm_num) (by linarith) (by norm_num)
  obtain ⟨Q4, hQ4, q4⟩ := i2Psi2Diff_quad_global (a := 0) (b := 2) (c := 0) (e := 2 + 2 * θ)
    (δ := 1 / 4) (η₁ := 1 / 4) (η₂ := 2 * θ + 1 / 4) le_rfl (by norm_num) le_rfl (by linarith)
    (by norm_num) (by norm_num) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by norm_num) (by linarith)
  refine ⟨C1 + C2 + C5 + C6 + C7 + C8 + 5 * Q3 + 5 * Q4, by positivity, ?_⟩
  intro K Q B hK x y y' D hD0 hD hyy hxy hxy'
  have hB := hK.nonneg
  have nn : ∀ (u : SpaceTime) (e : ℝ), 0 ≤ torusParabolicSize u ^ e := fun u e =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  set U : ℝ := D ^ (1 / 4 : ℝ) with hU
  set τ : ℝ := 1 + |y.1 - x.1| with hτ
  set Sg : ℝ := i2Psi2DiffSg θ x y y' with hSg
  have hU0 : 0 ≤ U := Real.rpow_nonneg hD0 _
  have hUD : U ≤ 1 + D := rpow_quarter_le_one_add hD0
  have hF1 : 1 ≤ 1 + D := by linarith
  have hUF : U ≤ (1 + D) ^ 2 := by nlinarith
  have hUU : U * U ≤ (1 + D) ^ 2 := by
    have := mul_le_mul hUD hUD hU0 (by linarith)
    nlinarith
  have hτ1 : 1 ≤ τ := by have := abs_nonneg (y.1 - x.1); linarith
  have hτ0 : 0 ≤ τ := by linarith
  have hSg0 : 0 ≤ Sg := i2Psi2DiffSg_nonneg θ x y y'
  have nXy := nn (x - y) (-(1 : ℝ))
  have nXy' := nn (x - y') (-(1 : ℝ))
  have hdS : ∀ e : ℝ, 0 ≤ e → e ≤ 2 + 2 * θ → torusParabolicSize (y - y') ^ (-e) ≤ Sg := by
    intro e he0 he
    have := i2Psi2Diff_rpow_neg_le hyy he0 he
    simp only [hSg, i2Psi2DiffSg]
    linarith
  have d2 := hdS 2 (by norm_num) (by linarith)
  have d2' := hdS (2 + 2 * θ) (by linarith) le_rfl
  have d1 := hdS 1 (by norm_num) (by linarith)
  have d1' := hdS (1 + 2 * θ) (by linarith) (by linarith)
  have nd := nn (y - y')
  -- the eight monomials
  have b1 := (h1 hK x y y' y' y hD0 hD).mul_const (nd (-(2 : ℝ)))
  have b2 := (h2 hK x y y' y' y hD0 hD).mul_const (nd (-(2 + 2 * θ)))
  have b3 := q3 hK x y y' hD0 hD hyy hxy hxy'
  have b4 := q4 hK x y y' hD0 hD hyy hxy hxy'
  rw [← i2Psi2Triple_zero_eq_quad] at b3 b4
  have b5 := (h5 hK x y y' y' y hD0 hD).mul_const (nd (-(1 : ℝ)))
  have b6 := (h6 hK x y y' y' y hD0 hD).mul_const (nd (-(1 : ℝ)))
  have b7 := (h7 hK x y y' y' y hD0 hD).mul_const (nd (-(1 : ℝ)))
  have b8 := (h8 hK x y y' y' y hD0 hD).mul_const (nd (-(1 + 2 * θ)))
  have hsum := (((((((b1.add b2).add b3).add b4).add b5).add b6).add b7).add b8)
  refine (show I2Psi2DiffIntBd (i2Psi2Maj4 θ K x y y') _ from hsum).mono_right ?_
  have hB2 : 0 ≤ B ^ 2 := sq_nonneg B
  have t1 := i2Psi2Diff_term_le (F := (1 + D) ^ 2) hC1 hB2 hU0 hUF hτ0 (nd (-(2 : ℝ))) d2
  have t2 := i2Psi2Diff_term_le (F := (1 + D) ^ 2) hC2 hB2 hU0 hUF hτ0 (nd (-(2 + 2 * θ))) d2'
  have t5 := i2Psi2Diff_term_le (F := (1 + D) ^ 2) hC5 hB2 hU0 hUF hτ0 (nd (-(1 : ℝ))) d1
  have t6 := i2Psi2Diff_term_le (F := (1 + D) ^ 2) hC6 hB2 hU0 hUF hτ0 (nd (-(1 : ℝ))) d1
  have t7 := i2Psi2Diff_term_le (F := (1 + D) ^ 2) hC7 hB2 hU0 hUF hτ0 (nd (-(1 : ℝ))) d1
  have t8 := i2Psi2Diff_term_le (F := (1 + D) ^ 2) hC8 hB2 hU0 hUF hτ0 (nd (-(1 + 2 * θ))) d1'
  obtain ⟨a1, a2, a3, a4⟩ := i2Psi2Diff_sq_pieces (θ := θ) (z := 2 * θ + 1 / 4) hθ.le
    (by linarith) (by linarith) hyy hxy hxy'
  obtain ⟨c1, c2, c3, c4⟩ := i2Psi2Diff_sq_pieces (θ := θ) (z := 1 / 4) hθ.le
    (by norm_num) (by norm_num) hyy hxy hxy'
  have P3 := prod_add_le_sq_sum (torusParabolicSize (y - y') ^ (-(2 * θ + 1 / 4)))
    (torusParabolicSize (x - y') ^ (-(2 * θ + 1 / 4))) (torusParabolicSize (y' - y) ^ (-(1 / 4 : ℝ)))
    (torusParabolicSize (x - y) ^ (-(1 / 4 : ℝ)))
  have P4 := prod_add_le_sq_sum (torusParabolicSize (y - y') ^ (-(1 / 4 : ℝ)))
    (torusParabolicSize (x - y') ^ (-(1 / 4 : ℝ))) (torusParabolicSize (y' - y) ^ (-(2 * θ + 1 / 4)))
    (torusParabolicSize (x - y) ^ (-(2 * θ + 1 / 4)))
  have n3 : 0 ≤ (torusParabolicSize (y - y') ^ (-(2 * θ + 1 / 4)) +
      torusParabolicSize (x - y') ^ (-(2 * θ + 1 / 4))) *
      (torusParabolicSize (y' - y) ^ (-(1 / 4 : ℝ)) + torusParabolicSize (x - y) ^ (-(1 / 4 : ℝ))) :=
    mul_nonneg (add_nonneg (nn _ _) (nn _ _)) (add_nonneg (nn _ _) (nn _ _))
  have n4 : 0 ≤ (torusParabolicSize (y - y') ^ (-(1 / 4 : ℝ)) +
      torusParabolicSize (x - y') ^ (-(1 / 4 : ℝ))) *
      (torusParabolicSize (y' - y) ^ (-(2 * θ + 1 / 4)) +
        torusParabolicSize (x - y) ^ (-(2 * θ + 1 / 4))) :=
    mul_nonneg (add_nonneg (nn _ _) (nn _ _)) (add_nonneg (nn _ _) (nn _ _))
  have p3 := i2Psi2Diff_prod_term_le (F := (1 + D) ^ 2) hQ3 hB2 hU0 hUU hτ1 n3 (S := Sg)
    (by linarith)
  have p4 := i2Psi2Diff_prod_term_le (F := (1 + D) ^ 2) hQ4 hB2 hU0 hUU hτ1 n4 (S := Sg)
    (by linarith)
  linarith [t1, t2, t5, t6, t7, t8, p3, p4]

end RegularityStructures

end
