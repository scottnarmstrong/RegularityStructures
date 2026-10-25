/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaMomentSecond
public import Phi43.BPHZ.TreeWickCube
public import Phi43.BPHZ.TreeI2Psi2Field
public import Phi43.BPHZ.TreeI2Psi2DifferenceMean
public import Phi43.BPHZ.HairerCovarianceBounds
public import Phi43.BPHZ.TreeI2Psi2DiagramMultiSq
import Mathlib.Tactic

/-!
# Second moments of the recentred convolutions `v₂` and `v₃`

With `K = hairerKernelTorus N` and the increment `δK_{x,y}(w) = K(y - w) - K(x - w)`
(`hairerI2Psi2Kernel`), the entries of the structure-group element `Γ_{yx}` of the renormalised
model contain the recentred convolutions of [Hai14, Lemma 5.16]

* `v₂(x, y) = ∫ δK_{x,y}(w) :Ψ²:(w) dw` (`gammaWickSq`), degree `1 - 2κ`;
* `v₃(x, y) = ∫ δK_{x,y}(w) :Ψ³:(w) dw` (`gammaWickCube`), degree `1/2 - 3κ`.

For `d = s(y - x) ≤ 1`, uniformly in the regularisation `ε ∈ (0, 1]`, the base point and the
probability space:

* `gammaWickSq_second_moment_le`: `E v₂² ≤ C d^(2-δ)` for every `δ ∈ (0, 1]`;
* `gammaWickCube_second_moment_le`: `E v₃² ≤ C d^(1-δ)` for every `δ ∈ (0, 1]`.

The proofs combine `E[:Ψ²:(u) :Ψ²:(v)] = 2 Q_ε(u - v)²`, `E[:Ψ³:(u) :Ψ³:(v)] = 6 Q_ε(u - v)³`
with the covariance bound `|Q_ε| ≲ s⁻¹` and the principal pairing estimate
`i2Psi2LintBound_diag_sq` for `∬ |δK| |δK| s^(-e)` (exponent `e = 2, 3`).
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- The recentred convolution `v₂(x, y) = ∫ (K(y - w) - K(x - w)) :Ψ²:(w) dw`. -/
def gammaWickSq {Ω : Type*} (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (ξ : Ω → SpaceTime → ℝ)
    (x y : SpaceTime) (ω : Ω) : ℝ :=
  ∫ w, hairerI2Psi2Kernel N x y w * hairerPsiWickSquare N ρ ε ξ ω w

/-- The recentred convolution `v₃(x, y) = ∫ (K(y - w) - K(x - w)) :Ψ³:(w) dw`. -/
def gammaWickCube {Ω : Type*} (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (ξ : Ω → SpaceTime → ℝ)
    (x y : SpaceTime) (ω : Ω) : ℝ :=
  ∫ w, hairerI2Psi2Kernel N x y w * hairerPsiWickCube N ρ ε ξ ω w

end RegularityStructures.Phi43

end

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- A parabolic size at most `1` bounds the time displacement by `1`. -/
theorem gammaMoment_abs_time_le_one {t : ℝ} {z : SpaceTime} (h : torusParabolicSize z ≤ 1)
    (ht : t = z.1) : |t| ≤ 1 := by
  subst ht
  have h1 : √|z.1| ≤ 1 := by
    have := torusSpatialNorm_nonneg z.2
    unfold torusParabolicSize at h
    linarith
  exact Real.sqrt_le_one.1 h1

private theorem abs_cov_sq_le {Q : SpaceTime → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hQ : ∀ u : SpaceTime, 0 < torusParabolicSize u →
      |Q u| ≤ B * torusParabolicSize u ^ (-(1 : ℝ))) {u v : SpaceTime}
    (h : 0 < torusParabolicSize (v - u)) :
    |2 * Q (u - v) ^ 2| ≤ (8 * B ^ 2) * torusParabolicSize (v - u) ^ (-(2 : ℝ)) := by
  have h1 := sq_cov_flip_le hB hQ h
  rw [abs_of_nonneg (by positivity)]
  linarith

private theorem abs_cov_cube_le {Q : SpaceTime → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hQ : ∀ u : SpaceTime, 0 < torusParabolicSize u →
      |Q u| ≤ B * torusParabolicSize u ^ (-(1 : ℝ))) {u v : SpaceTime}
    (h : 0 < torusParabolicSize (v - u)) :
    |6 * Q (u - v) ^ 3| ≤ (48 * B ^ 3) * torusParabolicSize (v - u) ^ (-(3 : ℝ)) := by
  have h1 := abs_cov_flip_le hB hQ h
  have h3 : (torusParabolicSize (v - u) ^ (-(1 : ℝ))) ^ 3 =
      torusParabolicSize (v - u) ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h.le]
    norm_num
  have h0 : 0 ≤ |Q (u - v)| := abs_nonneg _
  have h2 : |Q (u - v)| ^ 3 ≤ (2 * B * torusParabolicSize (v - u) ^ (-(1 : ℝ))) ^ 3 :=
    pow_le_pow_left₀ h0 h1 3
  rw [mul_pow, h3] at h2
  rw [abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  nlinarith [Real.rpow_nonneg h.le (-(3 : ℝ))]

private theorem rpow_mul_self_eq {r δ : ℝ} (hr : 0 ≤ r) (hδ : δ ≤ 1) :
    r ^ (1 - δ / 2) * r ^ (1 - δ / 2) = r ^ (2 - δ) := by
  rw [← Real.rpow_add' hr (by linarith)]
  congr 1
  ring

private theorem rpow_mul_self_eq' {r δ : ℝ} (hr : 0 ≤ r) (hδ : δ ≤ 1) :
    r ^ ((1 - δ) / 2) * r ^ ((1 - δ) / 2) = r ^ (1 - δ) := by
  rcases hδ.lt_or_eq with h | h
  · rw [← Real.rpow_add' hr (by linarith)]
    congr 1
    ring
  · subst h
    simp

/-- **Second moment of `v₂`.**  For every `δ ∈ (0, 1]`, `E v₂(x, y)² ≤ C s(y - x)^(2-δ)` for
`s(y - x) ≤ 1`, uniformly in `ε ∈ (0, 1]`, the base point and the probability space. -/
theorem gammaWickSq_second_moment_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : SpaceTime, torusParabolicSize (y - x) ≤ 1 →
        ∫ ω, gammaWickSq N ρ ε ξ x y ω ^ 2 ∂P ≤ C * torusParabolicSize (y - x) ^ (2 - δ) := by
  obtain ⟨BK, hBK, hK⟩ := i2Psi2KernelHyp_hairerKernelTorus N
  obtain ⟨CD, hCD, hD⟩ := i2Psi2LintBound_diag_sq (γ := 1 - δ / 2) (γ' := 1 - δ / 2) (e := 2)
    (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by linarith)
    (by linarith)
  obtain ⟨BQ, hBQ, hQ⟩ := hairerCovariance_abs_le N ρ hρ
  refine ⟨(8 * BQ ^ 2) * (CD * BK ^ 2), by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y hd
  have := hW.isProbabilityMeasure
  have hxy : |y.1 - x.1| ≤ 1 := gammaMoment_abs_time_le_one hd rfl
  have hcov := hairerPsiWickSquare_integral_mul N hρ hε.1 hW hξ
  have hlint := hD hK x y y hxy hxy
  have key := gammaMoment_second_le_of_lintBound (P := P)
    (Y := hairerPsiWickSquare N ρ ε ξ) (measurable_hairerPsiWickSquare_uncurry N hξ)
    (fun u => hairerPsiWickSquare_memLp N hρ hε.1 hW hξ u) (M₀ := 2 * hairerCovariance N ρ ε 0 ^ 2)
    (fun u => by rw [hcov u u, sub_self])
    (R := fun z => 2 * hairerCovariance N ρ ε z ^ 2) hcov (p := 2) (A := 8 * BQ ^ 2)
    (by positivity) (fun u v h => abs_cov_sq_le hBQ (hQ hε.1 hε.2) h)
    (measurable_hairerI2Psi2Kernel N x y) (integrable_hairerI2Psi2Kernel N x y)
    (M := CD * BK ^ 2 * torusParabolicSize (y - x) ^ (1 - δ / 2) *
      torusParabolicSize (y - x) ^ (1 - δ / 2))
    (mul_nonneg (mul_nonneg (mul_nonneg hCD (sq_nonneg _)) (Real.rpow_nonneg
      (torusParabolicSize_nonneg _) _)) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)) hlint
  have e : ∀ ω, |∫ w, hairerPsiWickSquare N ρ ε ξ ω w * hairerI2Psi2Kernel N x y w| ^ 2 =
      gammaWickSq N ρ ε ξ x y ω ^ 2 := fun ω => by
    simp only [gammaWickSq, sq_abs, mul_comm]
  simp only [e] at key
  refine key.trans (le_of_eq ?_)
  rw [mul_assoc (CD * BK ^ 2), rpow_mul_self_eq (torusParabolicSize_nonneg _) hδ1]
  ring

/-- **Second moment of `v₃`.**  For every `δ ∈ (0, 1]`, `E v₃(x, y)² ≤ C s(y - x)^(1-δ)` for
`s(y - x) ≤ 1`, uniformly in `ε ∈ (0, 1]`, the base point and the probability space. -/
theorem gammaWickCube_second_moment_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : SpaceTime, torusParabolicSize (y - x) ≤ 1 →
        ∫ ω, gammaWickCube N ρ ε ξ x y ω ^ 2 ∂P ≤ C * torusParabolicSize (y - x) ^ (1 - δ) := by
  obtain ⟨BK, hBK, hK⟩ := i2Psi2KernelHyp_hairerKernelTorus N
  obtain ⟨CD, hCD, hD⟩ := i2Psi2LintBound_diag_sq (γ := (1 - δ) / 2) (γ' := (1 - δ) / 2) (e := 3)
    (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num) (by linarith)
    (by linarith)
  obtain ⟨BQ, hBQ, hQ⟩ := hairerCovariance_abs_le N ρ hρ
  refine ⟨(48 * BQ ^ 3) * (CD * BK ^ 2), by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y hd
  have := hW.isProbabilityMeasure
  have hxy : |y.1 - x.1| ≤ 1 := gammaMoment_abs_time_le_one hd rfl
  have hcov := hairerPsiWickCube_integral_mul N hρ hε.1 hW hξ
  have hlint := hD hK x y y hxy hxy
  have key := gammaMoment_second_le_of_lintBound (P := P)
    (Y := hairerPsiWickCube N ρ ε ξ) (measurable_hairerPsiWickCube_uncurry N hξ)
    (fun u => hairerPsiWickCube_memLp N hρ hε.1 hW hξ u) (M₀ := 6 * hairerCovariance N ρ ε 0 ^ 3)
    (fun u => by rw [hcov u u, sub_self])
    (R := fun z => 6 * hairerCovariance N ρ ε z ^ 3) hcov (p := 3) (A := 48 * BQ ^ 3)
    (by positivity) (fun u v h => abs_cov_cube_le hBQ (hQ hε.1 hε.2) h)
    (measurable_hairerI2Psi2Kernel N x y) (integrable_hairerI2Psi2Kernel N x y)
    (M := CD * BK ^ 2 * torusParabolicSize (y - x) ^ ((1 - δ) / 2) *
      torusParabolicSize (y - x) ^ ((1 - δ) / 2))
    (mul_nonneg (mul_nonneg (mul_nonneg hCD (sq_nonneg _)) (Real.rpow_nonneg
      (torusParabolicSize_nonneg _) _)) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)) hlint
  have e : ∀ ω, |∫ w, hairerPsiWickCube N ρ ε ξ ω w * hairerI2Psi2Kernel N x y w| ^ 2 =
      gammaWickCube N ρ ε ξ x y ω ^ 2 := fun ω => by
    simp only [gammaWickCube, sq_abs, mul_comm]
  simp only [e] at key
  refine key.trans (le_of_eq ?_)
  rw [mul_assoc (CD * BK ^ 2), rpow_mul_self_eq' (torusParabolicSize_nonneg _) hδ1]
  ring

end RegularityStructures.Phi43

end
