/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureCore
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Cylindrical calculus and transport to the graph closure

This module proves the two algebraic calculus identities on the cylindrical core and records the
topological closure transport lemma used to extend them once the corresponding `L²` composition
maps have been established.  Integrability of every transformed value and derivative is an
explicit hypothesis, as required for the graph definition.  The derivative identities are the
finite-dimensional chain and product rules underlying [HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω]

theorem coordinateDerivative_comp_scalar {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {φ : ℝ → ℝ}
    (hcont_f : ContDiff ℝ 1 f) (hcont_φ : ContDiff ℝ 1 φ)
    (i : Fin n) (x : Fin n → ℝ) :
    coordinateDerivative (fun y => φ (f y)) i x =
      deriv φ (f x) * coordinateDerivative f i x := by
  have hcomp := (hcont_φ.differentiable one_ne_zero (f x)).hasFDerivAt.comp
    x (hcont_f.differentiable one_ne_zero x).hasFDerivAt
  have hcomp' : HasFDerivAt (fun y => φ (f y))
      (fderiv ℝ φ (f x) ∘L fderiv ℝ f x) x := by
    simpa [Function.comp_def] using hcomp
  have hscalar (v : ℝ) : fderiv ℝ φ (f x) v = deriv φ (f x) * v := by
    calc
      fderiv ℝ φ (f x) v = fderiv ℝ φ (f x) (v • (1 : ℝ)) := by simp
      _ = v • fderiv ℝ φ (f x) (1 : ℝ) := by rw [map_smul]
      _ = deriv φ (f x) * v := by
        rw [fderiv_apply_one_eq_deriv]
        simp [smul_eq_mul, mul_comm]
  unfold coordinateDerivative
  rw [hcomp'.fderiv, ContinuousLinearMap.comp_apply, hscalar]

theorem coordinateDerivative_mul {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ}
    (hcont_f : ContDiff ℝ 1 f) (hcont_g : ContDiff ℝ 1 g)
    (i : Fin n) (x : Fin n → ℝ) :
    coordinateDerivative (fun y => f y * g y) i x =
      coordinateDerivative f i x * g x + f x * coordinateDerivative g i x := by
  have hmul := ((hcont_f.differentiable one_ne_zero x).hasFDerivAt.mul
    (hcont_g.differentiable one_ne_zero x).hasFDerivAt)
  have hmul' : HasFDerivAt (fun y => f y * g y)
      (f x • fderiv ℝ g x + g x • fderiv ℝ f x) x := by
    exact hmul
  unfold coordinateDerivative
  rw [hmul'.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem cylindricalMalliavinGraph_chain_rule
    {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {n : ℕ} {h : Fin n → SpaceTime → ℝ} {f : (Fin n → ℝ) → ℝ}
    {φ : ℝ → ℝ}
    (hmem : ∀ i, MemLp (h i) 2)
    (hcont_f : ContDiff ℝ 1 f) (hcont_φ : ContDiff ℝ 1 φ)
    (_hgrowth : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin n → ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ K * (1 + ‖x‖) ^ M)
    (hgrowth_φf : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin n → ℝ, |φ (f x)| +
        ‖fderiv ℝ (fun y => φ (f y)) x‖ ≤ K * (1 + ‖x‖) ^ M)
    (_hF : MemLp (cylindricalFunctional W h f) 2 P)
    (_hD : MemLp (fun p : Ω × SpaceTime =>
      ∑ i, coordinateDerivative f i (fun j => W (h j) p.1) * h i p.2) 2
      (whiteNoiseDerivativeMeasure P))
    (hφF : MemLp (fun ω => φ (cylindricalFunctional W h f ω)) 2 P)
    (hφD : MemLp (fun p : Ω × SpaceTime =>
      ∑ i, coordinateDerivative (fun y => φ (f y)) i
          (fun j => W (h j) p.1) * h i p.2) 2
      (whiteNoiseDerivativeMeasure P)) :
    (hφF.toLp (fun ω => φ (cylindricalFunctional W h f ω)),
      hφD.toLp (fun p : Ω × SpaceTime =>
        ∑ i, coordinateDerivative (fun y => φ (f y)) i
            (fun j => W (h j) p.1) * h i p.2)) ∈
      cylindricalMalliavinGraph P W := by
  refine ⟨n, h, (fun y => φ (f y)), ?_, ?_, hgrowth_φf, hφF, hφD, rfl⟩
  · exact hmem
  · exact hcont_φ.comp hcont_f

theorem cylindricalMalliavinGraph_product_rule
    {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {n : ℕ} {h : Fin n → SpaceTime → ℝ}
    {f g : (Fin n → ℝ) → ℝ}
    (hmem : ∀ i, MemLp (h i) 2)
    (hcont_f : ContDiff ℝ 1 f) (hcont_g : ContDiff ℝ 1 g)
    (_hgrowth : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin n → ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ K * (1 + ‖x‖) ^ M)
    (hgrowth_prod : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin n → ℝ, |f x * g x| +
        ‖fderiv ℝ (fun y => f y * g y) x‖ ≤ K * (1 + ‖x‖) ^ M)
    (_hF : MemLp (cylindricalFunctional W h f) 2 P)
    (_hD : MemLp (fun p : Ω × SpaceTime =>
      ∑ i, coordinateDerivative f i (fun j => W (h j) p.1) * h i p.2) 2
      (whiteNoiseDerivativeMeasure P))
    (hgF : MemLp (fun ω => cylindricalFunctional W h f ω *
      cylindricalFunctional W h g ω) 2 P)
    (hgD : MemLp (fun p : Ω × SpaceTime =>
      ∑ i, coordinateDerivative (fun y => f y * g y) i
          (fun j => W (h j) p.1) * h i p.2) 2
      (whiteNoiseDerivativeMeasure P)) :
    (hgF.toLp (fun ω => cylindricalFunctional W h f ω *
        cylindricalFunctional W h g ω),
      hgD.toLp (fun p : Ω × SpaceTime =>
        ∑ i, coordinateDerivative (fun y => f y * g y) i
            (fun j => W (h j) p.1) * h i p.2)) ∈
      cylindricalMalliavinGraph P W := by
  refine ⟨n, h, (fun y => f y * g y), ?_, ?_, hgrowth_prod, hgF, hgD, rfl⟩
  · exact hmem
  · exact hcont_f.mul hcont_g

theorem malliavin_closure_map
    {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    (T : (Lp ℝ 2 P × Lp ℝ 2 (whiteNoiseDerivativeMeasure P)) →
      (Lp ℝ 2 P × Lp ℝ 2 (whiteNoiseDerivativeMeasure P)))
    (hT : Continuous T)
    (hcore : ∀ q, q ∈ cylindricalMalliavinGraph P W →
      T q ∈ cylindricalMalliavinGraph P W)
    (u : MalliavinSobolev P W) :
    T u.1 ∈ MalliavinSobolev P W := by
  exact hT.continuousWithinAt.mem_closure u.2 (by
    intro q hq
    exact hcore q hq)

end RegularityStructures

end
