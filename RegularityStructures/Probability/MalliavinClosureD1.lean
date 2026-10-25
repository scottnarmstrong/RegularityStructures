/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureLaw
public import RegularityStructures.Probability.MalliavinClosureConcatenation

set_option linter.style.haveILetI false

/-!
# Well-definedness of the cylindrical white-noise derivative

Two smooth, polynomial-growth cylindrical representations of the same random variable have the
same white-noise derivative, provided the displayed derivative difference is square-integrable.
The proof concatenates the test-function lists and uses the standard square-root representation of
the resulting finite Gaussian vector.  This is the representation-independence part of
[HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

theorem cylindricalDerivative_wellDefined
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ}
    {n m : ℕ} {h : Fin n → SpaceTime → ℝ} {k : Fin m → SpaceTime → ℝ}
    {f : (Fin n → ℝ) → ℝ} {g : (Fin m → ℝ) → ℝ}
    (hW : IsWhiteNoise P W)
    (hmem_h : ∀ i, MemLp (h i) 2) (hmem_k : ∀ j, MemLp (k j) 2)
    (hcont_f : ContDiff ℝ 1 f) (hcont_g : ContDiff ℝ 1 g)
    (hgrowth_sub : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin (n + m) → ℝ,
        |f (malliavinConcatLeftCLM n m x) -
            g (malliavinConcatRightCLM n m x)| +
          ‖fderiv ℝ (fun y => f (malliavinConcatLeftCLM n m y) -
            g (malliavinConcatRightCLM n m y)) x‖ ≤
          K * (1 + ‖x‖) ^ M)
    (hfg : cylindricalFunctional W h f =ᵐ[P] cylindricalFunctional W k g)
    (hDsub : MemLp (fun p : Ω × SpaceTime =>
      cylindricalDerivative W (malliavinConcatTest h k)
        (fun y => f (malliavinConcatLeftCLM n m y) -
          g (malliavinConcatRightCLM n m y)) p.1 p.2) 2
      (whiteNoiseDerivativeMeasure P)) :
    (fun p : Ω × SpaceTime => cylindricalDerivative W h f p.1 p.2) =ᵐ[
      whiteNoiseDerivativeMeasure P]
      (fun p : Ω × SpaceTime => cylindricalDerivative W k g p.1 p.2) := by
  let Z : Ω → Fin (n + m) → ℝ := fun ω =>
    fun i => W (malliavinConcatTest h k i) ω
  have hmem_concat : ∀ i, MemLp (malliavinConcatTest h k i) 2 := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa [malliavinConcatTest] using hmem_h j
    · intro j
      simpa [malliavinConcatTest] using hmem_k j
  have hZ : IsCentredGaussianVector P Z
      (fun i j => ∫ z, malliavinConcatTest h k i z * malliavinConcatTest h k j z) := by
    simpa [Z] using hW.2 (n + m) (malliavinConcatTest h k) hmem_concat
  letI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  obtain ⟨A, hAsymm, hAsq, hlaw⟩ := centredGaussianVector_standard_representation hZ
  have hcoord : ∀ (ω : Ω),
      (∀ i, Z ω (Fin.castAdd m i) = W (h i) ω) ∧
      (∀ j, Z ω (Fin.natAdd n j) = W (k j) ω) := by
    intro ω
    constructor
    · intro i
      simp [Z, malliavinConcatTest]
    · intro j
      simp [Z, malliavinConcatTest]
  exact cylindricalDerivative_eq_of_ae_eq_concat_coordinates hZ hAsymm hAsq hlaw
    hcont_f hcont_g hgrowth_sub hfg hcoord hmem_h hmem_k hDsub

end RegularityStructures

end
