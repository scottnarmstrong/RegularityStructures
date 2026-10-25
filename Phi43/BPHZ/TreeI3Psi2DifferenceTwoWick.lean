/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.CrossMollifierGaussian
public import Phi43.BPHZ.TreeI3Psi2FieldWick
public import Phi43.BPHZ.TreeI3Psi2FieldMoment
public import Phi43.BPHZ.TreeWickDifferenceCov
public import Phi43.BPHZ.TreeWickSquare

/-!
# The tree `I(Ψ³) Ψ²`: Wick products at several scales and mollifiers

Generalisation of `TreeI3Psi2FieldWick` and `TreeI3Psi2FieldMoment` to a family of four noises built
from possibly different mollifiers `ρ i` and scales `ε i`; the entries of the covariance matrix of the
Gaussian vector `(Ψ_{ρ i, ε i}(z i))_i` are `hairerCrossCovarianceTwo N (ρ i) (ε i) (ρ j) (ε j)`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The chaos-`5` kernel `χ₅(w, w')` of `E[Y₀(w) Y₁(y) Y₂(w') Y₃(y')]` with mixed mollifiers. -/
def hairerI3Psi2Chaos5Two (N : ℕ) (ρ : Fin 4 → ℝ × (Fin 3 → ℝ) → ℝ) (ε : Fin 4 → ℝ)
    (y y' w w' : SpaceTime) : ℝ :=
  hairerWickCubeSquareChaos5 (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 2) (ε 2) (w - w'))
    (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 3) (ε 3) (w - y'))
    (hairerCrossCovarianceTwo N (ρ 1) (ε 1) (ρ 2) (ε 2) (y - w'))
    (hairerCrossCovarianceTwo N (ρ 1) (ε 1) (ρ 3) (ε 3) (y - y'))

/-- The chaos-`3` kernel `χ₃(w, w')` with mixed mollifiers. -/
def hairerI3Psi2Chaos3Two (N : ℕ) (ρ : Fin 4 → ℝ × (Fin 3 → ℝ) → ℝ) (ε : Fin 4 → ℝ)
    (y y' w w' : SpaceTime) : ℝ :=
  hairerWickCubeSquareChaos3 (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 1) (ε 1) (w - y))
    (hairerCrossCovarianceTwo N (ρ 2) (ε 2) (ρ 3) (ε 3) (w' - y'))
    (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 2) (ε 2) (w - w'))
    (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 3) (ε 3) (w - y'))
    (hairerCrossCovarianceTwo N (ρ 1) (ε 1) (ρ 2) (ε 2) (y - w'))
    (hairerCrossCovarianceTwo N (ρ 1) (ε 1) (ρ 3) (ε 3) (y - y'))

/-- The chaos-`1` kernel `χ₁(w, w')` with mixed mollifiers. -/
def hairerI3Psi2Chaos1Two (N : ℕ) (ρ : Fin 4 → ℝ × (Fin 3 → ℝ) → ℝ) (ε : Fin 4 → ℝ)
    (y y' w w' : SpaceTime) : ℝ :=
  hairerWickCubeSquareChaos1 (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 1) (ε 1) (w - y))
    (hairerCrossCovarianceTwo N (ρ 2) (ε 2) (ρ 3) (ε 3) (w' - y'))
    (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 2) (ε 2) (w - w'))

/-- The product `Y₀(w) Y₁(y) Y₂(w') Y₃(y')` of Wick cubes and squares at mixed mollifiers. -/
def hairerWickCubeSquareFourProductTwo {Ω : Type*} (N : ℕ) (ρ : Fin 4 → ℝ × (Fin 3 → ℝ) → ℝ)
    (ε : Fin 4 → ℝ) (ξ : Fin 4 → Ω → SpaceTime → ℝ) (y y' w w' : SpaceTime) (ω : Ω) : ℝ :=
  hairerPsiWickCube N (ρ 0) (ε 0) (ξ 0) ω w * hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y *
    hairerPsiWickCube N (ρ 2) (ε 2) (ξ 2) ω w' * hairerPsiWickSquare N (ρ 3) (ε 3) (ξ 3) ω y'

end RegularityStructures.Phi43

end

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}

/-- **Cross covariances of two mollifiers are bounded by the Wick constants:**
`|Q_{(ρ,ε),(ρ',ε')}(x)| ≤ (c_{ρ,ε} + c_{ρ',ε'}) / 2`. -/
theorem abs_hairerCrossCovarianceTwo_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (hε : 0 < ε) (hε' : 0 < ε')
    (hW : IsWhiteNoise P W) {ξ ξ' : Ω → SpaceTime → ℝ} (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ' ε' ξ') (x : SpaceTime) :
    |hairerCrossCovarianceTwo N ρ ε ρ' ε' x| ≤
      (hairerWickConstant N ρ ε + hairerWickConstant N ρ' ε') / 2 := by
  have := hW.isProbabilityMeasure
  have h := hairerPsiField_isCentredGaussianVector_two_mollifier N hρ hρ' hε hε' hW hξ hξ' x 0
  have h01 := h.integral_mul 0 1
  have h00 := h.integral_mul 0 0
  have h11 := h.integral_mul 1 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_self, sub_zero,
    hairerCrossCovarianceTwo_self, hairerCrossCovariance_self,
    ← hairerWickConstant_eq_covariance_zero] at h01 h00 h11
  have i0 := h.integrable_mul 0 0
  have i1 := h.integrable_mul 1 1
  have i01 := h.integrable_mul 0 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at i0 i1 i01
  rw [← h01]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ ω, |hairerPsiField N ξ ω x * hairerPsiField N ξ' ω 0| ∂P
      ≤ ∫ ω, (hairerPsiField N ξ ω x * hairerPsiField N ξ ω x +
          hairerPsiField N ξ' ω 0 * hairerPsiField N ξ' ω 0) / 2 ∂P := by
        refine integral_mono i01.abs ((i0.add i1).div_const 2) fun ω => ?_
        rw [abs_mul]
        nlinarith [sq_nonneg (|hairerPsiField N ξ ω x| - |hairerPsiField N ξ' ω 0|),
          abs_mul_abs_self (hairerPsiField N ξ ω x),
          abs_mul_abs_self (hairerPsiField N ξ' ω 0)]
    _ = _ := by rw [integral_div, integral_add i0 i1, h00, h11]

/-- The cross covariances at four mollifiers and scales are bounded by the sum of the Wick
constants. -/
theorem abs_hairerCrossCovarianceTwo_le_sum (N : ℕ) {ρ : Fin 4 → ℝ × (Fin 3 → ℝ) → ℝ}
    {ε : Fin 4 → ℝ} {ξ : Fin 4 → Ω → SpaceTime → ℝ} (hρ : ∀ i, IsMollifier (ρ i))
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) (i j : Fin 4) (x : SpaceTime) :
    |hairerCrossCovarianceTwo N (ρ i) (ε i) (ρ j) (ε j) x| ≤
      ∑ k : Fin 4, hairerWickConstant N (ρ k) (ε k) := by
  have h := abs_hairerCrossCovarianceTwo_le N (hρ i) (hρ j) (hε i) (hε j) hW (hξ i) (hξ j) x
  have hc0 : ∀ k, 0 ≤ hairerWickConstant N (ρ k) (ε k) := fun k =>
    integral_nonneg fun z => sq_nonneg _
  have hi : hairerWickConstant N (ρ i) (ε i) ≤ ∑ k : Fin 4, hairerWickConstant N (ρ k) (ε k) :=
    Finset.single_le_sum (f := fun k => hairerWickConstant N (ρ k) (ε k)) (fun k _ => hc0 k)
      (Finset.mem_univ i)
  have hj : hairerWickConstant N (ρ j) (ε j) ≤ ∑ k : Fin 4, hairerWickConstant N (ρ k) (ε k) :=
    Finset.single_le_sum (f := fun k => hairerWickConstant N (ρ k) (ε k)) (fun k _ => hc0 k)
      (Finset.mem_univ j)
  linarith

omit [MeasurableSpace Ω] in
/-- The Wick square of `Ψ_{ρ i, ε i}` at `z i` is a Wick monomial of the multi-mollifier vector. -/
theorem hairerPsiWickSquare_eq_wickMonomial_multiscaleTwo (N : ℕ) {n : ℕ}
    (ρ : Fin n → ℝ × (Fin 3 → ℝ) → ℝ) (ε : Fin n → ℝ) (ξ : Fin n → Ω → SpaceTime → ℝ)
    (z : Fin n → SpaceTime) (ω : Ω) (i : Fin n) :
    hairerPsiWickSquare N (ρ i) (ε i) (ξ i) ω (z i) =
      wickMonomial (fun a b => hairerCrossCovarianceTwo N (ρ a) (ε a) (ρ b) (ε b) (z a - z b))
        [i, i] (fun j => hairerPsiField N (ξ j) ω (z j)) := by
  rw [wickMonomial_pair_self, hairerPsiWickSquare, hairerWickConstant_eq_covariance_zero,
    sub_self, hairerCrossCovarianceTwo_self, hairerCrossCovariance_self]

omit [MeasurableSpace Ω] in
/-- The Wick cube of `Ψ_{ρ i, ε i}` at `z i` is a Wick monomial of the multi-mollifier vector. -/
theorem hairerPsiWickCube_eq_wickMonomial_multiscaleTwo (N : ℕ) {n : ℕ}
    (ρ : Fin n → ℝ × (Fin 3 → ℝ) → ℝ) (ε : Fin n → ℝ) (ξ : Fin n → Ω → SpaceTime → ℝ)
    (z : Fin n → SpaceTime) (ω : Ω) (i : Fin n) :
    hairerPsiWickCube N (ρ i) (ε i) (ξ i) ω (z i) =
      wickMonomial (fun a b => hairerCrossCovarianceTwo N (ρ a) (ε a) (ρ b) (ε b) (z a - z b))
        [i, i, i] (fun j => hairerPsiField N (ξ j) ω (z j)) := by
  rw [wickMonomial_triple_self, hairerPsiWickCube, hairerWickConstant_eq_covariance_zero,
    sub_self, hairerCrossCovarianceTwo_self, hairerCrossCovariance_self]

variable {ρ : Fin 4 → ℝ × (Fin 3 → ℝ) → ℝ} {ε : Fin 4 → ℝ} {ξ : Fin 4 → Ω → SpaceTime → ℝ}

omit [MeasurableSpace Ω] in
/-- The product of Wick cubes and squares at four mollifiers is a product of Wick monomials. -/
theorem hairerWickCubeSquareFourProductTwo_eq_wickMonomial (N : ℕ) (z : Fin 4 → SpaceTime)
    (ω : Ω) :
    hairerPsiWickCube N (ρ 0) (ε 0) (ξ 0) ω (z 0) * hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω (z 1) *
        hairerPsiWickCube N (ρ 2) (ε 2) (ξ 2) ω (z 2) *
        hairerPsiWickSquare N (ρ 3) (ε 3) (ξ 3) ω (z 3) =
      wickMonomial (fun a b => hairerCrossCovarianceTwo N (ρ a) (ε a) (ρ b) (ε b) (z a - z b))
          (List.replicate 3 0) (fun j => hairerPsiField N (ξ j) ω (z j)) *
        wickMonomial (fun a b => hairerCrossCovarianceTwo N (ρ a) (ε a) (ρ b) (ε b) (z a - z b))
          (List.replicate 2 1) (fun j => hairerPsiField N (ξ j) ω (z j)) *
        wickMonomial (fun a b => hairerCrossCovarianceTwo N (ρ a) (ε a) (ρ b) (ε b) (z a - z b))
          (List.replicate 3 2) (fun j => hairerPsiField N (ξ j) ω (z j)) *
        wickMonomial (fun a b => hairerCrossCovarianceTwo N (ρ a) (ε a) (ρ b) (ε b) (z a - z b))
          (List.replicate 2 3) (fun j => hairerPsiField N (ξ j) ω (z j)) := by
  have c0 := hairerPsiWickCube_eq_wickMonomial_multiscaleTwo N ρ ε ξ z ω 0
  have c2 := hairerPsiWickCube_eq_wickMonomial_multiscaleTwo N ρ ε ξ z ω 2
  have s1 := hairerPsiWickSquare_eq_wickMonomial_multiscaleTwo N ρ ε ξ z ω 1
  have s3 := hairerPsiWickSquare_eq_wickMonomial_multiscaleTwo N ρ ε ξ z ω 3
  rw [c0, c2, s1, s3]
  rfl

/-- **Four Wick monomials at several mollifiers** (W4 for the tree `Ψ`). -/
theorem hairerPsiWickCubeSquare_integral_mul_four_two (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i))
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) (z : Fin 4 → SpaceTime) :
    ∫ ω, hairerPsiWickCube N (ρ 0) (ε 0) (ξ 0) ω (z 0) *
        hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω (z 1) *
        hairerPsiWickCube N (ρ 2) (ε 2) (ξ 2) ω (z 2) *
        hairerPsiWickSquare N (ρ 3) (ε 3) (ξ 3) ω (z 3) ∂P =
      hairerWickCubeSquareChaos5
          (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 2) (ε 2) (z 0 - z 2))
          (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 3) (ε 3) (z 0 - z 3))
          (hairerCrossCovarianceTwo N (ρ 1) (ε 1) (ρ 2) (ε 2) (z 1 - z 2))
          (hairerCrossCovarianceTwo N (ρ 1) (ε 1) (ρ 3) (ε 3) (z 1 - z 3)) +
        hairerWickCubeSquareChaos3
          (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 1) (ε 1) (z 0 - z 1))
          (hairerCrossCovarianceTwo N (ρ 2) (ε 2) (ρ 3) (ε 3) (z 2 - z 3))
          (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 2) (ε 2) (z 0 - z 2))
          (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 3) (ε 3) (z 0 - z 3))
          (hairerCrossCovarianceTwo N (ρ 1) (ε 1) (ρ 2) (ε 2) (z 1 - z 2))
          (hairerCrossCovarianceTwo N (ρ 1) (ε 1) (ρ 3) (ε 3) (z 1 - z 3)) +
        hairerWickCubeSquareChaos1
          (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 1) (ε 1) (z 0 - z 1))
          (hairerCrossCovarianceTwo N (ρ 2) (ε 2) (ρ 3) (ε 3) (z 2 - z 3))
          (hairerCrossCovarianceTwo N (ρ 0) (ε 0) (ρ 2) (ε 2) (z 0 - z 2)) := by
  have h := hairerPsiField_isCentredGaussianVector_multiscaleTwo N hρ hε hW hξ z
  have hw := integral_wick_three_mul_wick_two_mul_wick_three_mul_wick_two h 0 1 2 3
  simp_rw [hairerWickCubeSquareFourProductTwo_eq_wickMonomial N z]
  rw [hw]
  unfold hairerWickCubeSquareChaos5 hairerWickCubeSquareChaos3 hairerWickCubeSquareChaos1
  ring

/-- The product of Wick cubes and squares at four mollifiers is integrable. -/
theorem integrable_hairerPsiWickCubeSquare_four_two (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i))
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) (z : Fin 4 → SpaceTime) :
    Integrable (fun ω => hairerPsiWickCube N (ρ 0) (ε 0) (ξ 0) ω (z 0) *
      hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω (z 1) *
      hairerPsiWickCube N (ρ 2) (ε 2) (ξ 2) ω (z 2) *
      hairerPsiWickSquare N (ρ 3) (ε 3) (ξ 3) ω (z 3)) P := by
  have h := hairerPsiField_isCentredGaussianVector_multiscaleTwo N hρ hε hW hξ z
  have hi := h.integrable_prod_wickMonomial (L := ![List.replicate 3 0, List.replicate 2 1,
    List.replicate 3 2, List.replicate 2 3])
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three] at hi
  exact hi.congr (Filter.Eventually.of_forall fun ω =>
    (hairerWickCubeSquareFourProductTwo_eq_wickMonomial N z ω).symm)

/-- The expectation of the four-fold product is the sum of the three chaos kernels. -/
theorem integral_hairerWickCubeSquareFourProductTwo (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i))
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) (y y' w w' : SpaceTime) :
    ∫ ω, hairerWickCubeSquareFourProductTwo N ρ ε ξ y y' w w' ω ∂P =
      hairerI3Psi2Chaos5Two N ρ ε y y' w w' + hairerI3Psi2Chaos3Two N ρ ε y y' w w' +
        hairerI3Psi2Chaos1Two N ρ ε y y' w w' := by
  have h := hairerPsiWickCubeSquare_integral_mul_four_two N hρ hε hW hξ ![w, y, w', y']
  simpa [hairerWickCubeSquareFourProductTwo, hairerI3Psi2Chaos5Two, hairerI3Psi2Chaos3Two,
    hairerI3Psi2Chaos1Two] using h

/-- The four-fold product is integrable. -/
theorem integrable_hairerWickCubeSquareFourProductTwo (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i))
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) (y y' w w' : SpaceTime) :
    Integrable (hairerWickCubeSquareFourProductTwo N ρ ε ξ y y' w w') P := by
  have h := integrable_hairerPsiWickCubeSquare_four_two N hρ hε hW hξ ![w, y, w', y']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three] at h
  exact h

private theorem abs_mul_four_le'' (a b c d : ℝ) :
    |a * b * c * d| ≤ (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) / 4 := by
  have h1 : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  have h2 : |c * d| ≤ (c ^ 2 + d ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|c| - |d|), sq_abs c, sq_abs d]
  have h3 : |a * b * c * d| ≤ (a ^ 2 + b ^ 2) / 2 * ((c ^ 2 + d ^ 2) / 2) := by
    rw [mul_assoc, abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  nlinarith [sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (a ^ 2 - d ^ 2), sq_nonneg (b ^ 2 - c ^ 2),
    sq_nonneg (b ^ 2 - d ^ 2)]

/-- **Uniform first-moment bound for the four-fold product at mixed mollifiers.** -/
theorem exists_integral_abs_hairerWickCubeSquareFourProductTwo_le (N : ℕ)
    (hρ : ∀ i, IsMollifier (ρ i)) (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) :
    ∃ M : ℝ, ∀ y y' w w' : SpaceTime,
      ∫ ω, |hairerWickCubeSquareFourProductTwo N ρ ε ξ y y' w w' ω| ∂P ≤ M := by
  have hprob := hW.isProbabilityMeasure
  obtain ⟨A0, -, hA0⟩ := exists_integral_hairerPsiWickCube_pow_four_le (ρ := ρ 0) (P := P) (W := W)
  obtain ⟨A2, -, hA2⟩ := exists_integral_hairerPsiWickCube_pow_four_le (ρ := ρ 2) (P := P) (W := W)
  refine ⟨(A0 * (6 * hairerWickConstant N (ρ 0) (ε 0) ^ 3) ^ 2 +
    60 * hairerWickConstant N (ρ 1) (ε 1) ^ 4 +
    A2 * (6 * hairerWickConstant N (ρ 2) (ε 2) ^ 3) ^ 2 +
    60 * hairerWickConstant N (ρ 3) (ε 3) ^ 4) / 4, fun y y' w w' => ?_⟩
  have i0 := integrable_hairerPsiWickCube_pow_four N (hρ 0) (hε 0) hW (hξ 0) w
  have i1 := integrable_hairerPsiWickSquare_pow_four N (hρ 1) (hε 1) hW (hξ 1) y
  have i2 := integrable_hairerPsiWickCube_pow_four N (hρ 2) (hε 2) hW (hξ 2) w'
  have i3 := integrable_hairerPsiWickSquare_pow_four N (hρ 3) (hε 3) hW (hξ 3) y'
  have j01 : Integrable (fun ω => hairerPsiWickCube N (ρ 0) (ε 0) (ξ 0) ω w ^ 4 +
      hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y ^ 4) P := i0.add i1
  have j012 : Integrable (fun ω => hairerPsiWickCube N (ρ 0) (ε 0) (ξ 0) ω w ^ 4 +
      hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y ^ 4 +
      hairerPsiWickCube N (ρ 2) (ε 2) (ξ 2) ω w' ^ 4) P := j01.add i2
  have j0123 : Integrable (fun ω => hairerPsiWickCube N (ρ 0) (ε 0) (ξ 0) ω w ^ 4 +
      hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y ^ 4 +
      hairerPsiWickCube N (ρ 2) (ε 2) (ξ 2) ω w' ^ 4 +
      hairerPsiWickSquare N (ρ 3) (ε 3) (ξ 3) ω y' ^ 4) P := j012.add i3
  calc _ ≤ ∫ ω, (hairerPsiWickCube N (ρ 0) (ε 0) (ξ 0) ω w ^ 4 +
        hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y ^ 4 +
        hairerPsiWickCube N (ρ 2) (ε 2) (ξ 2) ω w' ^ 4 +
        hairerPsiWickSquare N (ρ 3) (ε 3) (ξ 3) ω y' ^ 4) / 4 ∂P :=
        integral_mono (integrable_hairerWickCubeSquareFourProductTwo N hρ hε hW hξ y y' w w').abs
          (j0123.div_const 4) fun ω => abs_mul_four_le'' _ _ _ _
    _ = (∫ ω, hairerPsiWickCube N (ρ 0) (ε 0) (ξ 0) ω w ^ 4 ∂P +
        ∫ ω, hairerPsiWickSquare N (ρ 1) (ε 1) (ξ 1) ω y ^ 4 ∂P +
        ∫ ω, hairerPsiWickCube N (ρ 2) (ε 2) (ξ 2) ω w' ^ 4 ∂P +
        ∫ ω, hairerPsiWickSquare N (ρ 3) (ε 3) (ξ 3) ω y' ^ 4 ∂P) / 4 := by
        rw [integral_div, integral_add j012 i3, integral_add j01 i2, integral_add i0 i1]
    _ ≤ _ := by
        rw [integral_hairerPsiWickSquare_pow_four N (hρ 1) (hε 1) hW (hξ 1) y,
          integral_hairerPsiWickSquare_pow_four N (hρ 3) (hε 3) hW (hξ 3) y']
        have a0 := hA0 N (hρ 0) (hε 0) hW (hξ 0) w
        have a2 := hA2 N (hρ 2) (hε 2) hW (hξ 2) w'
        linarith

end RegularityStructures.Phi43

end
