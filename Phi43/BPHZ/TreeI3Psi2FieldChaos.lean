/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2FieldMoment
public import Phi43.BPHZ.TreeI2Psi2FieldChaosFour

/-!
# The tree `I(Ψ³) Ψ²`: covariance of kernel-integrated Wick cubes, four-argument form

For scales `ε₀, …, ε₃`, noises `ξᵢ`, kernels `g₁, g₃ ∈ L¹`, and points `y, y'`, put `Y₀, Y₂` the
Wick cubes and `Y₁, Y₃` the Wick squares at scales `ε₀, …, ε₃`.  By stochastic Fubini and the
diagram formula (W4),
`E[(∫ g₁ Y₀) Y₁(y) ((∫ g₃ Y₂) Y₃(y'))] = ∫∫ g₁(w) g₃(w') (χ₅ + χ₃ + χ₁)(w, w') dw dw'`
with the chaos-`5`, `3`, `1` kernels of `TreeI3Psi2FieldWick`, whose entries are the cross
covariances `Q_{εᵢ εⱼ}(zᵢ - zⱼ)` for `(z₀, z₁, z₂, z₃) = (w, y, w', y')` [Hai14, p. 170-171].
All three pieces are separately integrable.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem abs_mul_five_le_pow {a b c d e S : ℝ} (ha : |a| ≤ S) (hb : |b| ≤ S)
    (hc : |c| ≤ S) (hd : |d| ≤ S) (he : |e| ≤ S) : |a * b * c * d * e| ≤ S ^ 5 := by
  have h0 : 0 ≤ S := (abs_nonneg _).trans ha
  rw [abs_mul, abs_mul, abs_mul, abs_mul]
  calc |a| * |b| * |c| * |d| * |e| ≤ S * S * S * S * S := by
        gcongr
    _ = S ^ 5 := by ring

private theorem abs_const_mul_le' {k x S : ℝ} (hk : 0 ≤ k) (hx : |x| ≤ S) :
    |k * x| ≤ k * S := by
  rw [abs_mul, abs_of_nonneg hk]
  gcongr

/-- The chaos kernels are bounded by a multiple of the fifth power of a bound on the entries. -/
theorem abs_hairerWickCubeSquareChaos_le {S c01 c23 c02 c03 c12 c13 : ℝ} (h01 : |c01| ≤ S)
    (h23 : |c23| ≤ S) (h02 : |c02| ≤ S) (h03 : |c03| ≤ S) (h12 : |c12| ≤ S) (h13 : |c13| ≤ S) :
    |hairerWickCubeSquareChaos5 c02 c03 c12 c13| ≤ 120 * S ^ 5 ∧
    |hairerWickCubeSquareChaos3 c01 c23 c02 c03 c12 c13| ≤ 216 * S ^ 5 ∧
    |hairerWickCubeSquareChaos1 c01 c23 c02| ≤ 36 * S ^ 5 := by
  have m1 := abs_const_mul_le' (k := 12) (by norm_num) (abs_mul_five_le_pow h02 h02 h02 h13 h13)
  have m2 := abs_const_mul_le' (k := 72) (by norm_num) (abs_mul_five_le_pow h02 h02 h03 h12 h13)
  have m3 := abs_const_mul_le' (k := 36) (by norm_num) (abs_mul_five_le_pow h02 h03 h03 h12 h12)
  have m4 := abs_const_mul_le' (k := 72) (by norm_num) (abs_mul_five_le_pow h01 h02 h02 h13 h23)
  have m5 := abs_const_mul_le' (k := 144) (by norm_num) (abs_mul_five_le_pow h01 h02 h03 h12 h23)
  have m6 := abs_const_mul_le' (k := 36) (by norm_num) (abs_mul_five_le_pow h01 h01 h02 h23 h23)
  refine ⟨?_, ?_, ?_⟩
  · have e : hairerWickCubeSquareChaos5 c02 c03 c12 c13 =
        12 * (c02 * c02 * c02 * c13 * c13) + 72 * (c02 * c02 * c03 * c12 * c13) +
          36 * (c02 * c03 * c03 * c12 * c12) := by
      unfold hairerWickCubeSquareChaos5
      ring
    rw [e]
    calc _ ≤ |12 * (c02 * c02 * c02 * c13 * c13) + 72 * (c02 * c02 * c03 * c12 * c13)| +
          |36 * (c02 * c03 * c03 * c12 * c12)| := abs_add_le _ _
      _ ≤ |12 * (c02 * c02 * c02 * c13 * c13)| + |72 * (c02 * c02 * c03 * c12 * c13)| +
          |36 * (c02 * c03 * c03 * c12 * c12)| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ 120 * S ^ 5 := by linarith
  · have e : hairerWickCubeSquareChaos3 c01 c23 c02 c03 c12 c13 =
        72 * (c01 * c02 * c02 * c13 * c23) + 144 * (c01 * c02 * c03 * c12 * c23) := by
      unfold hairerWickCubeSquareChaos3
      ring
    rw [e]
    exact (abs_add_le _ _).trans (by linarith)
  · have e : hairerWickCubeSquareChaos1 c01 c23 c02 = 36 * (c01 * c01 * c02 * c23 * c23) := by
      unfold hairerWickCubeSquareChaos1
      ring
    rw [e]
    linarith

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : Fin 4 → ℝ} {ξ : Fin 4 → Ω → SpaceTime → ℝ}

/-- The three chaos pieces `g₁(w) g₃(w') χₖ(w, w')` are integrable. -/
theorem integrable_hairerI3Psi2Chaos (N : ℕ) (hρ : IsMollifier ρ) (hε : ∀ i, 0 < ε i)
    (hW : IsWhiteNoise P W) (hξ : ∀ i, IsRegularisedNoise P W ρ (ε i) (ξ i))
    {g₁ g₃ : SpaceTime → ℝ} (hg₁ : Integrable g₁) (hg₃ : Integrable g₃) (y y' : SpaceTime) :
    Integrable (fun q : SpaceTime × SpaceTime => g₁ q.1 * g₃ q.2 *
      hairerI3Psi2Chaos5 N ρ (ε 0) (ε 1) (ε 2) (ε 3) y y' q.1 q.2) ∧
    Integrable (fun q : SpaceTime × SpaceTime => g₁ q.1 * g₃ q.2 *
      hairerI3Psi2Chaos3 N ρ (ε 0) (ε 1) (ε 2) (ε 3) y y' q.1 q.2) ∧
    Integrable (fun q : SpaceTime × SpaceTime => g₁ q.1 * g₃ q.2 *
      hairerI3Psi2Chaos1 N ρ (ε 0) (ε 1) (ε 2) (ε 3) y y' q.1 q.2) := by
  have hQm : ∀ i j, Measurable (hairerCrossCovariance N ρ (ε i) (ε j)) :=
    fun i j => measurable_hairerCrossCovariance N hρ _ _
  have m02 : Measurable fun q : SpaceTime × SpaceTime =>
      hairerCrossCovariance N ρ (ε 0) (ε 2) (q.1 - q.2) :=
    (hQm 0 2).comp (measurable_fst.sub measurable_snd)
  have m03 : Measurable fun q : SpaceTime × SpaceTime =>
      hairerCrossCovariance N ρ (ε 0) (ε 3) (q.1 - y') :=
    (hQm 0 3).comp (measurable_fst.sub measurable_const)
  have m12 : Measurable fun q : SpaceTime × SpaceTime =>
      hairerCrossCovariance N ρ (ε 1) (ε 2) (y - q.2) :=
    (hQm 1 2).comp (measurable_const.sub measurable_snd)
  have m13 : Measurable fun _ : SpaceTime × SpaceTime =>
      hairerCrossCovariance N ρ (ε 1) (ε 3) (y - y') := measurable_const
  have m01 : Measurable fun q : SpaceTime × SpaceTime =>
      hairerCrossCovariance N ρ (ε 0) (ε 1) (q.1 - y) :=
    (hQm 0 1).comp (measurable_fst.sub measurable_const)
  have m23 : Measurable fun q : SpaceTime × SpaceTime =>
      hairerCrossCovariance N ρ (ε 2) (ε 3) (q.2 - y') :=
    (hQm 2 3).comp (measurable_snd.sub measurable_const)
  have hbd := fun q : SpaceTime × SpaceTime => abs_hairerWickCubeSquareChaos_le
    (abs_hairerCrossCovariance_le_sum N hρ hε hW hξ 0 1 (q.1 - y))
    (abs_hairerCrossCovariance_le_sum N hρ hε hW hξ 2 3 (q.2 - y'))
    (abs_hairerCrossCovariance_le_sum N hρ hε hW hξ 0 2 (q.1 - q.2))
    (abs_hairerCrossCovariance_le_sum N hρ hε hW hξ 0 3 (q.1 - y'))
    (abs_hairerCrossCovariance_le_sum N hρ hε hW hξ 1 2 (y - q.2))
    (abs_hairerCrossCovariance_le_sum N hρ hε hW hξ 1 3 (y - y'))
  have hgg := hg₁.mul_prod hg₃
  refine ⟨?_, ?_, ?_⟩
  · refine hgg.mul_bdd (c := 120 * (∑ k : Fin 4, hairerWickConstant N ρ (ε k)) ^ 5) ?_
      (Filter.Eventually.of_forall fun q => ?_)
    · unfold hairerI3Psi2Chaos5 hairerWickCubeSquareChaos5
      exact (by fun_prop : Measurable _).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact (hbd q).1
  · refine hgg.mul_bdd (c := 216 * (∑ k : Fin 4, hairerWickConstant N ρ (ε k)) ^ 5) ?_
      (Filter.Eventually.of_forall fun q => ?_)
    · unfold hairerI3Psi2Chaos3 hairerWickCubeSquareChaos3
      exact (by fun_prop : Measurable _).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact (hbd q).2.1
  · refine hgg.mul_bdd (c := 36 * (∑ k : Fin 4, hairerWickConstant N ρ (ε k)) ^ 5) ?_
      (Filter.Eventually.of_forall fun q => ?_)
    · unfold hairerI3Psi2Chaos1 hairerWickCubeSquareChaos1
      exact (by fun_prop : Measurable _).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact (hbd q).2.2

/-- **Covariance of kernel-integrated Wick cubes against Wick squares, four-argument form.**
With `Y₀, Y₂` the Wick cubes and `Y₁, Y₃` the Wick squares at scales `ε₀, …, ε₃`, the quantity
`E[(∫ g₁ Y₀) Y₁(y) ((∫ g₃ Y₂) Y₃(y'))]` is the sum of the three integrals of
`g₁(w) g₃(w') χₖ(w, w')`, `k = 5, 3, 1`, where the kernels `χₖ` are built from the cross
covariances `Q_{εᵢ εⱼ}(zᵢ - zⱼ)` at `(z₀, z₁, z₂, z₃) = (w, y, w', y')`; the integrand on the left
is integrable. -/
theorem hairerI3Psi2_integral_mul_four (N : ℕ) (hρ : IsMollifier ρ) (hε : ∀ i, 0 < ε i)
    (hW : IsWhiteNoise P W) (hξ : ∀ i, IsRegularisedNoise P W ρ (ε i) (ξ i))
    {g₁ g₃ : SpaceTime → ℝ} (hg₁ : Integrable g₁) (hg₃ : Integrable g₃) (y y' : SpaceTime) :
    Integrable (fun ω => (∫ w, g₁ w * hairerPsiWickCube N ρ (ε 0) (ξ 0) ω w) *
        hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y *
        ((∫ w, g₃ w * hairerPsiWickCube N ρ (ε 2) (ξ 2) ω w) *
          hairerPsiWickSquare N ρ (ε 3) (ξ 3) ω y')) P ∧
    ∫ ω, (∫ w, g₁ w * hairerPsiWickCube N ρ (ε 0) (ξ 0) ω w) *
        hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y *
        ((∫ w, g₃ w * hairerPsiWickCube N ρ (ε 2) (ξ 2) ω w) *
          hairerPsiWickSquare N ρ (ε 3) (ξ 3) ω y') ∂P =
      (∫ q : SpaceTime × SpaceTime, g₁ q.1 * g₃ q.2 *
        hairerI3Psi2Chaos5 N ρ (ε 0) (ε 1) (ε 2) (ε 3) y y' q.1 q.2) +
      (∫ q : SpaceTime × SpaceTime, g₁ q.1 * g₃ q.2 *
        hairerI3Psi2Chaos3 N ρ (ε 0) (ε 1) (ε 2) (ε 3) y y' q.1 q.2) +
      ∫ q : SpaceTime × SpaceTime, g₁ q.1 * g₃ q.2 *
        hairerI3Psi2Chaos1 N ρ (ε 0) (ε 1) (ε 2) (ε 3) y y' q.1 q.2 := by
  have hprob := hW.isProbabilityMeasure
  have hYc : ∀ i, Measurable (fun q : Ω × SpaceTime =>
      hairerPsiWickCube N ρ (ε i) (ξ i) q.1 q.2) :=
    fun i => measurable_hairerPsiWickCube_uncurry N (hξ i)
  have hYs : ∀ i, Measurable (fun q : Ω × SpaceTime =>
      hairerPsiWickSquare N ρ (ε i) (ξ i) q.1 q.2) :=
    fun i => measurable_hairerPsiWickSquare_uncurry N (hξ i)
  have hA : Measurable (fun ω => hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y) :=
    Measurable.comp (g := fun q : Ω × SpaceTime => hairerPsiWickSquare N ρ (ε 1) (ξ 1) q.1 q.2)
      (f := fun ω : Ω => (ω, y)) (hYs 1) (measurable_id.prodMk measurable_const)
  have hB : Measurable (fun ω => hairerPsiWickSquare N ρ (ε 3) (ξ 3) ω y') :=
    Measurable.comp (g := fun q : Ω × SpaceTime => hairerPsiWickSquare N ρ (ε 3) (ξ 3) q.1 q.2)
      (f := fun ω : Ω => (ω, y')) (hYs 3) (measurable_id.prodMk measurable_const)
  obtain ⟨M, hM⟩ := exists_integral_abs_hairerWickCubeSquareFourProduct_le N hρ hε hW hξ
  obtain ⟨hω, hq, heq⟩ := integral_integral_mul_mul_eq_integral_prod (P := P)
    (Y₁ := hairerPsiWickCube N ρ (ε 0) (ξ 0)) (Y₃ := hairerPsiWickCube N ρ (ε 2) (ξ 2))
    (A := fun ω => hairerPsiWickSquare N ρ (ε 1) (ξ 1) ω y)
    (B := fun ω => hairerPsiWickSquare N ρ (ε 3) (ξ 3) ω y') (hYc 0) (hYc 2) hA hB hg₁ hg₃
    (fun w w' => integrable_hairerWickCubeSquareFourProduct N hρ hε hW hξ y y' w w')
    (fun w w' => hM y y' w w')
  obtain ⟨p5, p3, p1⟩ := integrable_hairerI3Psi2Chaos N hρ hε hW hξ hg₁ hg₃ y y'
  refine ⟨hω, ?_⟩
  have p53 : Integrable (fun q : SpaceTime × SpaceTime => g₁ q.1 * g₃ q.2 *
      hairerI3Psi2Chaos5 N ρ (ε 0) (ε 1) (ε 2) (ε 3) y y' q.1 q.2 + g₁ q.1 * g₃ q.2 *
      hairerI3Psi2Chaos3 N ρ (ε 0) (ε 1) (ε 2) (ε 3) y y' q.1 q.2) := p5.add p3
  rw [heq, ← integral_add p5 p3, ← integral_add p53 p1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  have h4 := integral_hairerWickCubeSquareFourProduct N hρ hε hW hξ y y' q.1 q.2
  unfold hairerWickCubeSquareFourProduct at h4
  beta_reduce
  rw [h4]
  ring

end RegularityStructures.Phi43

end
