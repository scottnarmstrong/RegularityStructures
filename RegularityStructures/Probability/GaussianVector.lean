/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.WhiteNoise
public import RegularityStructures.Probability.GaussianMoments
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Centred Gaussian vectors

Basic facts about `IsCentredGaussianVector P X C` (`RegularityStructures.Probability.WhiteNoise`):

* `X` has a Gaussian law, so `P` is a probability measure and every coordinate has moments of
  all orders;
* the covariance matrix `C` is symmetric;
* every linear form `∑ₘ aₘ X_{σ m}` is a centred real Gaussian with variance
  `∑ₘ ∑ₘ' aₘ aₘ' C_{σ m, σ m'}`, so its fourth and sixth moments are `3 v²` and `15 v³`;
* the law of `-X` is the law of `X`, so `E[g(X)] = 0` for every measurable odd `g`; in particular
  `E[Xᵢ Xⱼ Xₖ] = 0`.

It also records that a white noise lives on a probability space
(`IsWhiteNoise.isProbabilityMeasure`).
-/

public section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures.IsCentredGaussianVector

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ}
  {C : Fin n → Fin n → ℝ}

theorem hasGaussianLaw (h : IsCentredGaussianVector P X C) : HasGaussianLaw X P :=
  ⟨h.1, h.2.1⟩

theorem isProbabilityMeasure (h : IsCentredGaussianVector P X C) : IsProbabilityMeasure P :=
  h.hasGaussianLaw.isProbabilityMeasure

theorem integral_apply (h : IsCentredGaussianVector P X C) (i : Fin n) :
    ∫ ω, X ω i ∂P = 0 :=
  h.2.2.1 i

theorem integral_mul (h : IsCentredGaussianVector P X C) (i j : Fin n) :
    ∫ ω, X ω i * X ω j ∂P = C i j :=
  h.2.2.2 i j

/-- The covariance matrix of a Gaussian vector is symmetric. -/
theorem symm (h : IsCentredGaussianVector P X C) (i j : Fin n) : C i j = C j i := by
  rw [← h.integral_mul, ← h.integral_mul]
  simp_rw [mul_comm]

/-- Every linear form `∑ₘ aₘ X_{σ m}` of a Gaussian vector has a Gaussian law. -/
theorem hasGaussianLaw_linear (h : IsCentredGaussianVector P X C) {ι : Type*} [Fintype ι]
    (σ : ι → Fin n) (a : ι → ℝ) :
    HasGaussianLaw (fun ω => ∑ m, a m * X ω (σ m)) P := by
  have := h.hasGaussianLaw.map_fun
    (∑ m, a m • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (σ m))
  convert this using 2 with ω
  simp

theorem hasGaussianLaw_apply (h : IsCentredGaussianVector P X C) (i : Fin n) :
    HasGaussianLaw (fun ω => X ω i) P :=
  h.hasGaussianLaw.map_fun (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)

theorem integrable_pow_apply (h : IsCentredGaussianVector P X C) (i : Fin n) (k : ℕ) :
    Integrable (fun ω => X ω i ^ k) P :=
  (h.hasGaussianLaw_apply i).integrable_pow k

theorem integrable_apply (h : IsCentredGaussianVector P X C) (i : Fin n) :
    Integrable (fun ω => X ω i) P := by
  simpa using h.integrable_pow_apply i 1

theorem memLp_two_apply (h : IsCentredGaussianVector P X C) (i : Fin n) :
    MemLp (fun ω => X ω i) 2 P :=
  (h.hasGaussianLaw_apply i).memLp_two

theorem integrable_mul (h : IsCentredGaussianVector P X C) (i j : Fin n) :
    Integrable (fun ω => X ω i * X ω j) P :=
  (h.memLp_two_apply i).integrable_mul (h.memLp_two_apply j)

/-- Products of powers of two coordinates are integrable. -/
theorem integrable_pow_mul_pow (h : IsCentredGaussianVector P X C) (i j : Fin n) (p q : ℕ) :
    Integrable (fun ω => X ω i ^ p * X ω j ^ q) P := by
  refine Integrable.mono' ((h.integrable_pow_apply i (2 * p)).add
    (h.integrable_pow_apply j (2 * q))) ((h.integrable_pow_apply i p).aestronglyMeasurable.mul
      (h.integrable_pow_apply j q).aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
  have h1 := two_mul_le_add_sq |X ω i ^ p| |X ω j ^ q|
  rw [sq_abs, sq_abs, ← pow_mul, ← pow_mul, mul_comm p 2, mul_comm q 2] at h1
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul]
  nlinarith [abs_nonneg (X ω i ^ p), abs_nonneg (X ω j ^ q)]

/-! ### Linear forms -/

section Linear

variable {ι : Type*} [Fintype ι]

theorem integral_linear (h : IsCentredGaussianVector P X C) (σ : ι → Fin n) (a : ι → ℝ) :
    ∫ ω, ∑ m, a m * X ω (σ m) ∂P = 0 := by
  rw [integral_finsetSum _ fun m _ => (h.integrable_apply (σ m)).const_mul (a m)]
  simp [integral_const_mul, h.integral_apply]

/-- The variance of a linear form: `E[(∑ₘ aₘ X_{σ m})²] = ∑ₘ ∑ₘ' aₘ aₘ' C_{σ m, σ m'}`. -/
theorem integral_linear_sq (h : IsCentredGaussianVector P X C) (σ : ι → Fin n) (a : ι → ℝ) :
    ∫ ω, (∑ m, a m * X ω (σ m)) ^ 2 ∂P = ∑ m, ∑ m', a m * a m' * C (σ m) (σ m') := by
  have hpt : ∀ ω, (∑ m, a m * X ω (σ m)) ^ 2 =
      ∑ m, ∑ m', a m * a m' * (X ω (σ m) * X ω (σ m')) := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun m' _ =>
    (h.integrable_mul (σ m) (σ m')).const_mul _]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ fun m' _ => (h.integrable_mul (σ m) (σ m')).const_mul _]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [integral_const_mul, h.integral_mul]

theorem integrable_linear_pow (h : IsCentredGaussianVector P X C) (σ : ι → Fin n) (a : ι → ℝ)
    (k : ℕ) :
    Integrable (fun ω => (∑ m, a m * X ω (σ m)) ^ k) P :=
  (h.hasGaussianLaw_linear σ a).integrable_pow k

/-- Fourth moment of a linear form: `E[L⁴] = 3 (∑ₘ ∑ₘ' aₘ aₘ' C_{σ m, σ m'})²`. -/
theorem integral_linear_pow_four (h : IsCentredGaussianVector P X C) (σ : ι → Fin n)
    (a : ι → ℝ) :
    ∫ ω, (∑ m, a m * X ω (σ m)) ^ 4 ∂P =
      3 * (∑ m, ∑ m', a m * a m' * C (σ m) (σ m')) ^ 2 := by
  rw [(h.hasGaussianLaw_linear σ a).integral_pow_four (h.integral_linear σ a),
    h.integral_linear_sq]

end Linear

/-! ### Symmetry of the law and odd moments -/

end RegularityStructures.IsCentredGaussianVector

namespace RegularityStructures.IsWhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}

/-- A white noise lives on a probability space. -/
theorem isProbabilityMeasure (hW : IsWhiteNoise P W) : IsProbabilityMeasure P :=
  (hW.2 1 (fun _ => 0) fun _ => MemLp.zero).isProbabilityMeasure

end RegularityStructures.IsWhiteNoise

end
