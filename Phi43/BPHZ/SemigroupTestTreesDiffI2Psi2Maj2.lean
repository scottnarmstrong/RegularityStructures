/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI2Psi2Maj4
public import Phi43.BPHZ.TreeI2Psi2DiagramMultiChaosTwo

/-!
# The chaos-`2` majorant of the difference of `I(Ψ²) Ψ²`, for arbitrary `x, y, y'`

`i2Psi2Diff_maj2_global`: for `θ ∈ (0, 1/8]`, `∫∫ i2Psi2Maj2 θ K x y y'` is at most
`C B² (1 + D)² (1 + |y.1 - x.1|) i2Psi2DiffSg θ x y y'`, with `D` bounding `s(a - b)` on the time
slab (`I2Psi2DiffSlab`).
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- **The chaos-`2` majorant, globally.** -/
theorem i2Psi2Diff_maj2_global {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ} {B : ℝ}, SingularKernelData K Q B →
      ∀ (x y y' : SpaceTime) {D : ℝ}, 0 ≤ D → I2Psi2DiffSlab x y y' D →
      0 < torusParabolicSize (y - y') → 0 < torusParabolicSize (x - y) →
      0 < torusParabolicSize (x - y') →
      I2Psi2DiffIntBd (i2Psi2Maj2 θ K x y y')
        (C * B ^ 2 * (1 + D) ^ 2 * (1 + |y.1 - x.1|) * i2Psi2DiffSg θ x y y') := by
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
  obtain ⟨Q1, hQ1, q1⟩ := i2Psi2Diff_quad_global (a := 1 + 2 * θ) (b := 1) (c := 1) (e := 1)
    (δ := 1 / 4) (η₁ := 2 * θ + 1 / 4) (η₂ := 1 / 4) (by linarith) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by linarith) (by norm_num) (by linarith) (by norm_num)
    (by norm_num) (by norm_num) (by linarith) (by norm_num)
  obtain ⟨Q2, hQ2, q2⟩ := i2Psi2Diff_quad_global (a := 1) (b := 1 + 2 * θ) (c := 1) (e := 1)
    (δ := 1 / 4) (η₁ := 2 * θ + 1 / 4) (η₂ := 1 / 4) (by norm_num) (by linarith) (by norm_num)
    (by norm_num) (by norm_num) (by linarith) (by norm_num) (by norm_num) (by linarith)
    (by norm_num) (by norm_num) (by linarith) (by norm_num)
  obtain ⟨Q3, hQ3, q3⟩ := i2Psi2Diff_quad_global (a := 1) (b := 1) (c := 1 + 2 * θ) (e := 1)
    (δ := 1 / 4) (η₁ := 1 / 4) (η₂ := 2 * θ + 1 / 4) (by norm_num) (by norm_num) (by linarith)
    (by norm_num) (by norm_num) (by norm_num) (by linarith) (by norm_num) (by norm_num)
    (by linarith) (by norm_num) (by norm_num) (by linarith)
  obtain ⟨Q4, hQ4, q4⟩ := i2Psi2Diff_quad_global (a := 1) (b := 1) (c := 1) (e := 1 + 2 * θ)
    (δ := 1 / 4) (η₁ := 1 / 4) (η₂ := 2 * θ + 1 / 4) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num) (by norm_num)
    (by norm_num) (by linarith) (by norm_num) (by linarith)
  refine ⟨C5 + C6 + C7 + C8 + 5 * Q1 + 5 * Q2 + 5 * Q3 + 5 * Q4, by positivity, ?_⟩
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
  have d1 := hdS 1 (by norm_num) (by linarith)
  have d1' := hdS (1 + 2 * θ) (by linarith) (by linarith)
  have nd := nn (y - y')
  have b5 := (h5 hK x y y' y y' hD0 hD).mul_const (nd (-(1 : ℝ)))
  have b6 := (h6 hK x y y' y y' hD0 hD).mul_const (nd (-(1 : ℝ)))
  have b7 := (h7 hK x y y' y y' hD0 hD).mul_const (nd (-(1 : ℝ)))
  have b8 := (h8 hK x y y' y y' hD0 hD).mul_const (nd (-(1 + 2 * θ)))
  have b1 := q1 hK x y y' hD0 hD hyy hxy hxy'
  have b2 := q2 hK x y y' hD0 hD hyy hxy hxy'
  have b3 := q3 hK x y y' hD0 hD hyy hxy hxy'
  have b4 := q4 hK x y y' hD0 hD hyy hxy hxy'
  have hsum := (((((((b5.add b6).add b7).add b8).add b1).add b2).add b3).add b4)
  refine (show I2Psi2DiffIntBd (i2Psi2Maj2 θ K x y y') _ from hsum).mono_right ?_
  have hB2 : 0 ≤ B ^ 2 := sq_nonneg B
  have t5 := i2Psi2Diff_term_le (F := (1 + D) ^ 2) hC5 hB2 hU0 hUF hτ0 (nd (-(1 : ℝ))) d1
  have t6 := i2Psi2Diff_term_le (F := (1 + D) ^ 2) hC6 hB2 hU0 hUF hτ0 (nd (-(1 : ℝ))) d1
  have t7 := i2Psi2Diff_term_le (F := (1 + D) ^ 2) hC7 hB2 hU0 hUF hτ0 (nd (-(1 : ℝ))) d1
  have t8 := i2Psi2Diff_term_le (F := (1 + D) ^ 2) hC8 hB2 hU0 hUF hτ0 (nd (-(1 + 2 * θ))) d1'
  obtain ⟨a1, a2, a3, a4⟩ := i2Psi2Diff_sq_pieces (θ := θ) (z := 2 * θ + 1 / 4) hθ.le
    (by linarith) (by linarith) hyy hxy hxy'
  obtain ⟨c1, c2, c3, c4⟩ := i2Psi2Diff_sq_pieces (θ := θ) (z := 1 / 4) hθ.le
    (by norm_num) (by norm_num) hyy hxy hxy'
  have PA := prod_add_le_sq_sum (torusParabolicSize (y - y') ^ (-(2 * θ + 1 / 4)))
    (torusParabolicSize (x - y') ^ (-(2 * θ + 1 / 4))) (torusParabolicSize (y' - y) ^ (-(1 / 4 : ℝ)))
    (torusParabolicSize (x - y) ^ (-(1 / 4 : ℝ)))
  have PB := prod_add_le_sq_sum (torusParabolicSize (y - y') ^ (-(1 / 4 : ℝ)))
    (torusParabolicSize (x - y') ^ (-(1 / 4 : ℝ))) (torusParabolicSize (y' - y) ^ (-(2 * θ + 1 / 4)))
    (torusParabolicSize (x - y) ^ (-(2 * θ + 1 / 4)))
  have nA : 0 ≤ (torusParabolicSize (y - y') ^ (-(2 * θ + 1 / 4)) +
      torusParabolicSize (x - y') ^ (-(2 * θ + 1 / 4))) *
      (torusParabolicSize (y' - y) ^ (-(1 / 4 : ℝ)) + torusParabolicSize (x - y) ^ (-(1 / 4 : ℝ))) :=
    mul_nonneg (add_nonneg (nn _ _) (nn _ _)) (add_nonneg (nn _ _) (nn _ _))
  have nB : 0 ≤ (torusParabolicSize (y - y') ^ (-(1 / 4 : ℝ)) +
      torusParabolicSize (x - y') ^ (-(1 / 4 : ℝ))) *
      (torusParabolicSize (y' - y) ^ (-(2 * θ + 1 / 4)) +
        torusParabolicSize (x - y) ^ (-(2 * θ + 1 / 4))) :=
    mul_nonneg (add_nonneg (nn _ _) (nn _ _)) (add_nonneg (nn _ _) (nn _ _))
  have p1 := i2Psi2Diff_prod_term_le (F := (1 + D) ^ 2) hQ1 hB2 hU0 hUU hτ1 nA (S := Sg)
    (by linarith)
  have p2 := i2Psi2Diff_prod_term_le (F := (1 + D) ^ 2) hQ2 hB2 hU0 hUU hτ1 nA (S := Sg)
    (by linarith)
  have p3 := i2Psi2Diff_prod_term_le (F := (1 + D) ^ 2) hQ3 hB2 hU0 hUU hτ1 nB (S := Sg)
    (by linarith)
  have p4 := i2Psi2Diff_prod_term_le (F := (1 + D) ^ 2) hQ4 hB2 hU0 hUU hτ1 nB (S := Sg)
    (by linarith)
  linarith [t5, t6, t7, t8, p1, p2, p3, p4]

end RegularityStructures

end
