/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2CrossChaos
public import Phi43.BPHZ.TreeI2Psi2FieldChaosFour
public import Phi43.BPHZ.TreeI3Psi2DifferenceTwoChaos

/-!
# The tree `I(Ψ²) Ψ²`: the four-argument covariance identity at several mollifiers

With the chaos kernels `χ₄, χ₂, χ₀` of `TreeI2Psi2CrossChaos`, for `g₁, g₃ ∈ L¹`,
`E[(∫ g₁ Y₀) Y₁(y) ((∫ g₃ Y₂) Y₃(y'))] = ∫∫ g₁ g₃ χ₄ + ∫∫ g₁ g₃ χ₂ + ∫∫ g₁ g₃ χ₀`
(`hairerI2Psi2_integral_mul_four_two`), each piece integrable.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {ρ : Fin 4 → ℝ × (Fin 3 → ℝ) → ℝ} {ε : Fin 4 → ℝ} {ξ : Fin 4 → Ω → SpaceTime → ℝ}

/-- The three chaos pieces `g₁(w) g₃(w') χₖ(w, w')` are integrable. -/
theorem integrable_hairerI2Psi2ChaosTwo (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i)) (hε : ∀ i, 0 < ε i)
    (hW : IsWhiteNoise P W) (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i))
    {g₁ g₃ : SpaceTime → ℝ} (hg₁ : Integrable g₁) (hg₃ : Integrable g₃) (y y' : SpaceTime) :
    Integrable (fun q : SpaceTime × SpaceTime => g₁ q.1 * g₃ q.2 *
      hairerI2Psi2Chaos4Two N ρ ε y y' q.1 q.2) ∧
    Integrable (fun q : SpaceTime × SpaceTime => g₁ q.1 * g₃ q.2 *
      hairerI2Psi2Chaos2Two N ρ ε y y' q.1 q.2) ∧
    Integrable (fun q : SpaceTime × SpaceTime => g₁ q.1 * g₃ q.2 *
      hairerI2Psi2Chaos0Two N ρ ε y y' q.1 q.2) := by
  have hQm : ∀ i j, Measurable (hairerCrossCovarianceTwo N (ρ i) (ε i) (ρ j) (ε j)) :=
    fun i j => measurable_hairerCrossCovarianceTwo N (hρ i) (hρ j) _ _
  have m02 : Measurable fun q : SpaceTime × SpaceTime =>
      hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 2) (ε 2) (q.1 - q.2) :=
    (hQm 0 2).comp (measurable_fst.sub measurable_snd)
  have m03 : Measurable fun q : SpaceTime × SpaceTime =>
      hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 3) (ε 3) (q.1 - y') :=
    (hQm 0 3).comp (measurable_fst.sub measurable_const)
  have m12 : Measurable fun q : SpaceTime × SpaceTime =>
      hairerCrossCovarianceTwo N (ρ 1) (ε 1) (ρ 2) (ε 2) (y - q.2) :=
    (hQm 1 2).comp (measurable_const.sub measurable_snd)
  have m13 : Measurable fun _ : SpaceTime × SpaceTime =>
      hairerCrossCovarianceTwo N (ρ 1) (ε 1) (ρ 3) (ε 3) (y - y') := measurable_const
  have m01 : Measurable fun q : SpaceTime × SpaceTime =>
      hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 1) (ε 1) (q.1 - y) :=
    (hQm 0 1).comp (measurable_fst.sub measurable_const)
  have m23 : Measurable fun q : SpaceTime × SpaceTime =>
      hairerCrossCovarianceTwo N (ρ 2) (ε 2) (ρ 3) (ε 3) (q.2 - y') :=
    (hQm 2 3).comp (measurable_snd.sub measurable_const)
  have hbd := fun q : SpaceTime × SpaceTime => abs_hairerWickSquareFourChaos_le
    (abs_hairerCrossCovarianceTwo_le_sum N hρ hε hW hξ 0 1 (q.1 - y))
    (abs_hairerCrossCovarianceTwo_le_sum N hρ hε hW hξ 2 3 (q.2 - y'))
    (abs_hairerCrossCovarianceTwo_le_sum N hρ hε hW hξ 0 2 (q.1 - q.2))
    (abs_hairerCrossCovarianceTwo_le_sum N hρ hε hW hξ 0 3 (q.1 - y'))
    (abs_hairerCrossCovarianceTwo_le_sum N hρ hε hW hξ 1 2 (y - q.2))
    (abs_hairerCrossCovarianceTwo_le_sum N hρ hε hW hξ 1 3 (y - y'))
  have hgg := hg₁.mul_prod hg₃
  refine ⟨?_, ?_, ?_⟩
  · refine hgg.mul_bdd (c := 24 * (∑ k : Fin 4, hairerWickConstant N (ρ k) (ε k)) ^ 4) ?_
      (Filter.Eventually.of_forall fun q => ?_)
    · unfold hairerI2Psi2Chaos4Two hairerWickSquareFourChaos4
      exact (by fun_prop : Measurable _).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact (hbd q).1
  · refine hgg.mul_bdd (c := 32 * (∑ k : Fin 4, hairerWickConstant N (ρ k) (ε k)) ^ 4) ?_
      (Filter.Eventually.of_forall fun q => ?_)
    · unfold hairerI2Psi2Chaos2Two hairerWickSquareFourChaos2
      exact (by fun_prop : Measurable _).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact (hbd q).2.1
  · refine hgg.mul_bdd (c := 4 * (∑ k : Fin 4, hairerWickConstant N (ρ k) (ε k)) ^ 4) ?_
      (Filter.Eventually.of_forall fun q => ?_)
    · unfold hairerI2Psi2Chaos0Two hairerWickSquareFourChaos0
      exact (by fun_prop : Measurable _).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact (hbd q).2.2

/-- **Covariance of kernel-integrated Wick squares, four-argument form.**
With `Yᵢ = :Ψ²_{εᵢ}:` the quantity `E[(∫ g₁ Y₀) Y₁(y) ((∫ g₃ Y₂) Y₃(y'))]` is the sum of the
three integrals of `g₁(w) g₃(w') χₖ(w, w')`, `k = 4, 2, 0`, where the kernels `χₖ` are built from
the cross covariances `Q_{εᵢ εⱼ}(zᵢ - zⱼ)` at `(z₀, z₁, z₂, z₃) = (w, y, w', y')`; the integrand
on the left is integrable. -/
theorem hairerI2Psi2_integral_mul_four_two (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i)) (hε : ∀ i, 0 < ε i)
    (hW : IsWhiteNoise P W) (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i))
    {g₁ g₃ : SpaceTime → ℝ} (hg₁ : Integrable g₁) (hg₃ : Integrable g₃) (y y' : SpaceTime) :
    Integrable (fun ω => (∫ w, g₁ w * hairerPsiWickSquare N (ρ 0) (ε 0) (ξ 0) ω w) *
        hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y *
        ((∫ w, g₃ w * hairerPsiWickSquare N (ρ 2) (ε 2) (ξ 2) ω w) *
          hairerPsiWickSquare N (ρ 3) (ε 3) (ξ 3) ω y')) P ∧
    ∫ ω, (∫ w, g₁ w * hairerPsiWickSquare N (ρ 0) (ε 0) (ξ 0) ω w) *
        hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y *
        ((∫ w, g₃ w * hairerPsiWickSquare N (ρ 2) (ε 2) (ξ 2) ω w) *
          hairerPsiWickSquare N (ρ 3) (ε 3) (ξ 3) ω y') ∂P =
      (∫ q : SpaceTime × SpaceTime, g₁ q.1 * g₃ q.2 *
        hairerI2Psi2Chaos4Two N ρ ε y y' q.1 q.2) +
      (∫ q : SpaceTime × SpaceTime, g₁ q.1 * g₃ q.2 *
        hairerI2Psi2Chaos2Two N ρ ε y y' q.1 q.2) +
      ∫ q : SpaceTime × SpaceTime, g₁ q.1 * g₃ q.2 *
        hairerI2Psi2Chaos0Two N ρ ε y y' q.1 q.2 := by
  have hprob := hW.isProbabilityMeasure
  have hYm : ∀ i, Measurable (fun q : Ω × SpaceTime =>
      hairerPsiWickSquare N (ρ i) (ε i) (ξ i) q.1 q.2) :=
    fun i => measurable_hairerPsiWickSquare_uncurry N (hξ i)
  have hA : Measurable (fun ω => hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y) :=
    Measurable.comp (g := fun q : Ω × SpaceTime => hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) q.1 q.2)
      (f := fun ω : Ω => (ω, y)) (hYm 1) (measurable_id.prodMk measurable_const)
  have hB : Measurable (fun ω => hairerPsiWickSquare N (ρ 3) (ε 3) (ξ 3) ω y') :=
    Measurable.comp (g := fun q : Ω × SpaceTime => hairerPsiWickSquare N (ρ 3) (ε 3) (ξ 3) q.1 q.2)
      (f := fun ω : Ω => (ω, y')) (hYm 3) (measurable_id.prodMk measurable_const)
  obtain ⟨hω, hq, heq⟩ := integral_integral_mul_mul_eq_integral_prod (P := P)
    (Y₁ := hairerPsiWickSquare N (ρ 0) (ε 0) (ξ 0)) (Y₃ := hairerPsiWickSquare N (ρ 2) (ε 2) (ξ 2))
    (A := fun ω => hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y)
    (B := fun ω => hairerPsiWickSquare N (ρ 3) (ε 3) (ξ 3) ω y') (hYm 0) (hYm 2) hA hB hg₁ hg₃
    (fun w w' => integrable_hairerWickSquareFourProductTwo N hρ hε hW hξ y y' w w')
    (fun w w' => integral_abs_hairerWickSquareFourProductTwo_le N hρ hε hW hξ y y' w w')
  obtain ⟨p4, p2, p0⟩ := integrable_hairerI2Psi2ChaosTwo N hρ hε hW hξ hg₁ hg₃ y y'
  refine ⟨hω, ?_⟩
  have p42 : Integrable (fun q : SpaceTime × SpaceTime => g₁ q.1 * g₃ q.2 *
      hairerI2Psi2Chaos4Two N ρ ε y y' q.1 q.2 + g₁ q.1 * g₃ q.2 *
      hairerI2Psi2Chaos2Two N ρ ε y y' q.1 q.2) := p4.add p2
  rw [heq, ← integral_add p4 p2, ← integral_add p42 p0]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  have h4 := integral_hairerWickSquareFourProductTwo N hρ hε hW hξ y y' q.1 q.2
  unfold hairerWickSquareFourProductTwo at h4
  beta_reduce
  rw [h4]
  ring

end RegularityStructures.Phi43

end
