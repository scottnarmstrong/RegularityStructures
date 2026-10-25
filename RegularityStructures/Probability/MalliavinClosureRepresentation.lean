/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureZero

/-!
# Uniqueness for a fixed cylindrical coordinate list

The zero-derivative theorem gives representation independence whenever two smooth functions use
the same finite white-noise coordinate list.  The standard-representation and integrability data
are retained as explicit hypotheses; concatenating two different lists requires the finite-index
transport lemmas recorded separately below.  This is the first representation-independence step
for [HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem coordinateDerivative_sub_local {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ}
    (hcont_f : ContDiff ℝ 1 f) (hcont_g : ContDiff ℝ 1 g)
    (i : Fin n) (x : Fin n → ℝ) :
    coordinateDerivative (fun y => f y - g y) i x =
      coordinateDerivative f i x - coordinateDerivative g i x := by
  have hsub := ((hcont_f.differentiable one_ne_zero x).hasFDerivAt.sub
    (hcont_g.differentiable one_ne_zero x).hasFDerivAt)
  have hsub' : HasFDerivAt (fun y => f y - g y)
      (fderiv ℝ f x - fderiv ℝ g x) x := by
    exact hsub
  unfold coordinateDerivative
  rw [hsub'.fderiv]
  simp only [sub_apply]

theorem cylindricalDerivative_eq_of_ae_eq_same_coordinates
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ}
    {n : ℕ} {h : Fin n → SpaceTime → ℝ}
    {f g : (Fin n → ℝ) → ℝ}
    {X : Ω → Fin n → ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hX : IsCentredGaussianVector P X
      (fun i j => ∫ z, h i z * h j z))
    (hAsymm : A.IsSymm)
    (hAsq : A * A = fun i j => ∫ z, h i z * h j z)
    (hlaw : P.map X = (standardGaussianMeasure n).map
      (Matrix.mulVecLin A))
    (hcont_f : ContDiff ℝ 1 f) (hcont_g : ContDiff ℝ 1 g)
    (hgrowth_sub : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin n → ℝ,
        |f x - g x| + ‖fderiv ℝ (fun y => f y - g y) x‖ ≤
          K * (1 + ‖x‖) ^ M)
    (hfg : cylindricalFunctional W h f =ᵐ[P] cylindricalFunctional W h g)
    (hcoord : ∀ (ω : Ω) (i : Fin n), X ω i = W (h i) ω)
    (hmem : ∀ i, MemLp (h i) 2)
    (hDsub : MemLp (fun p : Ω × SpaceTime =>
      cylindricalDerivative W h (fun y => f y - g y) p.1 p.2) 2
      (whiteNoiseDerivativeMeasure P)) :
    (fun p : Ω × SpaceTime => cylindricalDerivative W h f p.1 p.2) =ᵐ[
      whiteNoiseDerivativeMeasure P]
      (fun p : Ω × SpaceTime => cylindricalDerivative W h g p.1 p.2) := by
  have hzero : (fun ω => (f - g) (fun i => W (h i) ω)) =ᵐ[P] 0 := by
    filter_upwards [hfg] with ω hω
    change f (fun i => W (h i) ω) - g (fun i => W (h i) ω) = 0
    exact sub_eq_zero.mpr hω
  have hzero' : (fun ω => (f - g) (X ω)) =ᵐ[P] 0 := by
    filter_upwards [hzero] with ω hω
    have hcoords : (fun i => W (h i) ω) = X ω := by
      funext i
      rw [hcoord]
    rw [← hcoords]
    exact hω
  have hz := cylindricalDerivative_eq_zero_of_ae_eq_zero hX hAsymm hAsq hlaw
    (hcont_f.sub hcont_g) hgrowth_sub hzero' hcoord hmem hDsub
  filter_upwards [hz] with p hp
  have hident : cylindricalDerivative W h (fun y => f y - g y) p.1 p.2 =
      cylindricalDerivative W h f p.1 p.2 - cylindricalDerivative W h g p.1 p.2 := by
    unfold cylindricalDerivative
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [coordinateDerivative_sub_local hcont_f hcont_g]
    ring
  rw [hident] at hp
  exact sub_eq_zero.mp hp

end RegularityStructures

end
