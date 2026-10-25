/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2FieldDifference
public import Phi43.BPHZ.TreeI3PsiTestedPairing
public import Phi43.BPHZ.TreeI2Psi2FieldMean
public import Phi43.BPHZ.TreeWickSquare
public import Phi43.BPHZ.TreeWickCube

/-!
# Pair integrability of the field of `I(Ψ³) Ψ²`

For fixed `ε > 0` and base point `x`, the field `F(y) = hairerI3Psi2Field N ρ ε ξ x · y` satisfies
`E F(y)² ≤ M` uniformly in `y` (but not in `ε`).  This follows from the covariance identity
`hairerI3Psi2Field_integral_mul` (chaos `5`, `3`, `1` and the cross terms) and the bound `|Q_ε| ≤ c`
on the covariance.  Consequently `E|F(y) F(ȳ)| ≤ M`, `F(y) ∈ L²`, and `F` is jointly measurable:
these are the hypotheses of the tested second-moment Fubini theorem
`integral_abs_integral_mul_sq_le`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ : Ω → SpaceTime → ℝ}

/-- **Joint measurability of the field of `I(Ψ³) Ψ²`.** -/
theorem measurable_hairerI3Psi2Field_uncurry (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (x : SpaceTime) :
    Measurable (fun q : Ω × SpaceTime => hairerI3Psi2Field N ρ ε ξ x q.1 q.2) := by
  have hK := measurable_constantsComparison_hairerKernelTorus N
  have hC := measurable_hairerPsiWickCube_uncurry N hξ
  have hS := measurable_hairerPsiWickSquare_uncurry N hξ
  have hΨ := measurable_hairerPsiField_uncurry N hξ
  have h1 : Measurable (fun r : (Ω × SpaceTime) × SpaceTime =>
      hairerKernelTorus N (r.1.2 - r.2)) :=
    hK.comp ((measurable_snd.comp measurable_fst).sub measurable_snd)
  have h2 : Measurable (fun r : (Ω × SpaceTime) × SpaceTime => hairerKernelTorus N (x - r.2)) :=
    hK.comp (measurable_const.sub measurable_snd)
  have h3 : Measurable (fun r : (Ω × SpaceTime) × SpaceTime =>
      hairerPsiWickCube N ρ ε ξ r.1.1 r.2) :=
    Measurable.comp (g := fun q : Ω × SpaceTime => hairerPsiWickCube N ρ ε ξ q.1 q.2)
      (f := fun r : (Ω × SpaceTime) × SpaceTime => (r.1.1, r.2)) hC
      (measurable_fst.fst.prodMk measurable_snd)
  have hint : Measurable (fun r : (Ω × SpaceTime) × SpaceTime =>
      hairerI2Psi2Kernel N x r.1.2 r.2 * hairerPsiWickCube N ρ ε ξ r.1.1 r.2) :=
    (h1.sub h2).mul h3
  have hI : Measurable (fun q : Ω × SpaceTime => ∫ w,
      hairerI2Psi2Kernel N x q.2 w * hairerPsiWickCube N ρ ε ξ q.1 w) :=
    hint.stronglyMeasurable.integral_prod_right'.measurable
  exact (hI.mul hS).sub (measurable_const.mul hΨ)

private theorem abs_integral_prod_kernel_le' {g g' : SpaceTime → ℝ}
    {χ : SpaceTime → SpaceTime → ℝ} {S : ℝ} (hg : Integrable g) (hg' : Integrable g')
    (hS : ∀ w w', |χ w w'| ≤ S) :
    |∫ q : SpaceTime × SpaceTime, g q.1 * g' q.2 * χ q.1 q.2| ≤
      (∫ w, |g w|) * (∫ w, |g' w|) * S := by
  have hb : Integrable (fun q : SpaceTime × SpaceTime => |g q.1| * |g' q.2| * S) :=
    (hg.abs.mul_prod hg'.abs).mul_const S
  have h := norm_integral_le_of_norm_le
    (f := fun q : SpaceTime × SpaceTime => g q.1 * g' q.2 * χ q.1 q.2) hb
    (Filter.Eventually.of_forall fun q => ?_)
  · rw [Real.norm_eq_abs, integral_mul_const] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    exact integral_prod_mul (μ := (volume : Measure SpaceTime)) (ν := volume)
      (fun w => |g w|) (fun w => |g' w|)
  · rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hS _ _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))

private theorem abs_integral_cross_le {g : SpaceTime → ℝ} {χ : SpaceTime → ℝ} {S : ℝ}
    (hg : Integrable g) (hS : ∀ w, |χ w| ≤ S) :
    |∫ w, g w * χ w| ≤ (∫ w, |g w|) * S := by
  have hb : Integrable (fun w : SpaceTime => |g w| * S) := hg.abs.mul_const S
  have h := norm_integral_le_of_norm_le (f := fun w : SpaceTime => g w * χ w) hb
    (Filter.Eventually.of_forall fun w => ?_)
  · rw [Real.norm_eq_abs, integral_mul_const] at h
    exact h
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hS _) (abs_nonneg _)

private theorem abs_mul_le_half_sq_add' (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 :=
  abs_le.2 ⟨by nlinarith [sq_nonneg (a + b)], by nlinarith [sq_nonneg (a - b)]⟩

/-- **Uniform second moment of the field of `I(Ψ³) Ψ²`** (uniform in `y`, not in `ε`). -/
theorem exists_hairerI3Psi2Field_sq_integral_le (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (x : SpaceTime) :
    ∃ M : ℝ, ∀ y : SpaceTime, Integrable (fun ω => hairerI3Psi2Field N ρ ε ξ x ω y ^ 2) P ∧
      ∫ ω, hairerI3Psi2Field N ρ ε ξ x ω y ^ 2 ∂P ≤ M := by
  set S := hairerWickConstant N ρ ε with hSdef
  set C := hairerSunsetConstant N ρ ε with hCdef
  set L := 2 * ∫ w, |hairerKernelTorus N w| with hLdef
  have hc : ∀ z, |hairerCrossCovariance N ρ ε ε z| ≤ S := by
    intro z
    rw [hairerCrossCovariance_self]
    exact abs_hairerCovariance_le_wickConstant N hρ hε hW hξ z
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hc 0)
  refine ⟨L * L * (120 * S ^ 5) + L * L * (216 * S ^ 5) + L * L * (36 * S ^ 5) +
    3 * |C| * (L * (6 * S ^ 3)) + 3 * |C| * (L * (6 * S ^ 3)) + 9 * |C| * |C| * S, ?_⟩
  intro y
  obtain ⟨hint, heq⟩ := hairerI3Psi2Field_integral_mul N hρ hε hε hW hξ hξ x y y
  simp only [← sq] at hint heq
  refine ⟨hint, heq.trans_le ?_⟩
  have hch := fun w w' : SpaceTime => abs_hairerWickCubeSquareChaos_le (S := S)
    (hc (w - y)) (hc (w' - y)) (hc (w - w')) (hc (w - y)) (hc (y - w')) (hc (y - y))
  have hg := integrable_hairerI2Psi2Kernel N x y
  have hL : (∫ w, |hairerI2Psi2Kernel N x y w|) ≤ L :=
    integral_abs_hairerKernelTorus_diff_le N x y
  have hL0 : 0 ≤ ∫ w, |hairerI2Psi2Kernel N x y w| := integral_nonneg fun _ => abs_nonneg _
  have b5 := abs_integral_prod_kernel_le' hg hg
    (χ := fun w w' => hairerI3Psi2Chaos5 N ρ ε ε ε ε y y w w') (S := 120 * S ^ 5)
    fun w w' => (hch w w').1
  have b3 := abs_integral_prod_kernel_le' hg hg
    (χ := fun w w' => hairerI3Psi2Chaos3 N ρ ε ε ε ε y y w w') (S := 216 * S ^ 5)
    fun w w' => (hch w w').2.1
  have b1 := abs_integral_prod_kernel_le' hg hg
    (χ := fun w w' => hairerI3Psi2Chaos1 N ρ ε ε ε ε y y w w') (S := 36 * S ^ 5)
    fun w w' => (hch w w').2.2
  have hcross : ∀ w, |hairerI3Psi2CrossKernel N ρ ε ε ε y y w| ≤ 6 * S ^ 3 := by
    intro w
    unfold hairerI3Psi2CrossKernel
    have h1 := hc (w - y)
    have h0 := abs_nonneg (hairerCrossCovariance N ρ ε ε (w - y))
    rw [abs_mul, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    calc 6 * |hairerCrossCovariance N ρ ε ε (w - y)| ^ 2 *
          |hairerCrossCovariance N ρ ε ε (w - y)| ≤ 6 * S ^ 2 * S := by gcongr
      _ = 6 * S ^ 3 := by ring
  have bx := abs_integral_cross_le hg hcross
  have hlast : |hairerCrossCovariance N ρ ε ε (y - y)| ≤ S := hc _
  have e4 : (∫ w, |hairerI2Psi2Kernel N x y w|) * (∫ w, |hairerI2Psi2Kernel N x y w|) *
      (120 * S ^ 5) ≤ L * L * (120 * S ^ 5) := by gcongr
  have e3 : (∫ w, |hairerI2Psi2Kernel N x y w|) * (∫ w, |hairerI2Psi2Kernel N x y w|) *
      (216 * S ^ 5) ≤ L * L * (216 * S ^ 5) := by gcongr
  have e2 : (∫ w, |hairerI2Psi2Kernel N x y w|) * (∫ w, |hairerI2Psi2Kernel N x y w|) *
      (36 * S ^ 5) ≤ L * L * (36 * S ^ 5) := by gcongr
  have ex : (∫ w, |hairerI2Psi2Kernel N x y w|) * (6 * S ^ 3) ≤ L * (6 * S ^ 3) := by gcongr
  have hx1 : |3 * C * (∫ w, hairerI2Psi2Kernel N x y w * hairerI3Psi2CrossKernel N ρ ε ε ε y y w)| ≤
      3 * |C| * (L * (6 * S ^ 3)) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    gcongr
    exact bx.trans ex
  have hlast' : |9 * C * C * hairerCrossCovariance N ρ ε ε (y - y)| ≤ 9 * |C| * |C| * S := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 9)]
    gcongr
  have a5 := (abs_le.1 (b5.trans (by gcongr))).2
  have a3 := (abs_le.1 (b3.trans (by gcongr))).2
  have a1 := (abs_le.1 (b1.trans (by gcongr))).2
  have a4 := (abs_le.1 hx1).2
  have a4' := (abs_le.1 hx1).1
  have a6 := (abs_le.1 hlast').2
  rw [← hCdef]
  linarith

/-- **Pair integrability and a uniform first-moment bound for the field of `I(Ψ³) Ψ²`.** -/
theorem exists_hairerI3Psi2Field_pair_integral_abs_le (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (x : SpaceTime) :
    ∃ M : ℝ, ∀ y y' : SpaceTime,
      Integrable (fun ω => hairerI3Psi2Field N ρ ε ξ x ω y * hairerI3Psi2Field N ρ ε ξ x ω y') P ∧
      ∫ ω, |hairerI3Psi2Field N ρ ε ξ x ω y * hairerI3Psi2Field N ρ ε ξ x ω y'| ∂P ≤ M := by
  obtain ⟨M, hM⟩ := exists_hairerI3Psi2Field_sq_integral_le N hρ hε hW hξ x
  refine ⟨M, fun y y' => ?_⟩
  obtain ⟨i1, b1⟩ := hM y
  obtain ⟨i2, b2⟩ := hM y'
  have hint := (hairerI3Psi2Field_integral_mul N hρ hε hε hW hξ hξ x y y').1
  refine ⟨hint, ?_⟩
  calc ∫ ω, |hairerI3Psi2Field N ρ ε ξ x ω y * hairerI3Psi2Field N ρ ε ξ x ω y'| ∂P
      ≤ ∫ ω, (hairerI3Psi2Field N ρ ε ξ x ω y ^ 2 + hairerI3Psi2Field N ρ ε ξ x ω y' ^ 2) / 2
          ∂P := integral_mono hint.abs ((i1.add i2).div_const 2) fun ω =>
            abs_mul_le_half_sq_add' _ _
    _ = (∫ ω, hairerI3Psi2Field N ρ ε ξ x ω y ^ 2 ∂P +
          ∫ ω, hairerI3Psi2Field N ρ ε ξ x ω y' ^ 2 ∂P) / 2 := by
        rw [integral_div, integral_add i1 i2]
    _ ≤ M := by linarith

/-- The field of `I(Ψ³) Ψ²` at a point is square integrable. -/
theorem hairerI3Psi2Field_memLp (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (x y : SpaceTime) :
    MemLp (fun ω => hairerI3Psi2Field N ρ ε ξ x ω y) 2 P := by
  have hm : Measurable (fun ω => hairerI3Psi2Field N ρ ε ξ x ω y) :=
    Measurable.comp (g := fun q : Ω × SpaceTime => hairerI3Psi2Field N ρ ε ξ x q.1 q.2)
      (f := fun ω : Ω => (ω, y)) (measurable_hairerI3Psi2Field_uncurry N hξ x)
      (measurable_id.prodMk measurable_const)
  obtain ⟨M, hM⟩ := exists_hairerI3Psi2Field_sq_integral_le N hρ hε hW hξ x
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 (hM y).1

end RegularityStructures.Phi43

end
