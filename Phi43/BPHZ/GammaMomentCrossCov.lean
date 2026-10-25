/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeWickDifferenceCov
public import Phi43.BPHZ.CrossMollifierGaussian
public import Phi43.BPHZ.CrossMollifierDifference
import Mathlib.Tactic
public import Phi43.BPHZ.TreeWickSquare

/-!
# Covariance of the differences of Wick powers with two mollifiers

For regularised noises `ξ` (mollifier `ρ`, scale `ε`) and `ξ'` (mollifier `ρ'`, scale `ε'`) of the
same white noise, and `a, b, c, d = Q(K_{ρ,ε}, K_{ρ,ε}), Q(K_{ρ,ε}, K_{ρ',ε'}),
Q(K_{ρ',ε'}, K_{ρ,ε}), Q(K_{ρ',ε'}, K_{ρ',ε'})` evaluated at `u - v`
(`hairerCrossCovarianceTwo`):

* `E[(:Ψ²:_{ρ,ε} - :Ψ²:_{ρ',ε'})(u) (:Ψ²:_{ρ,ε} - :Ψ²:_{ρ',ε'})(v)] = 2 (a² - b² - c² + d²)`,
* `E[(:Ψ³:_{ρ,ε} - :Ψ³:_{ρ',ε'})(u) (:Ψ³:_{ρ,ε} - :Ψ³:_{ρ',ε'})(v)] = 6 (a³ - b³ - c³ + d³)`.

This is `TreeWickDifferenceCov` for two different mollifiers, from the four-dimensional Gaussian
vector `(Ψ_{ρ,ε}(u), Ψ_{ρ',ε'}(u), Ψ_{ρ,ε}(v), Ψ_{ρ',ε'}(v))`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- The Wick square of `Ψ_{ρ i, ε i}` at `z i` is the Wick monomial `:X_i²:` of the multi-mollifier
vector. -/
theorem hairerPsiWickSquare_eq_wickMonomial_multiTwo (N : ℕ) {n : ℕ}
    (ρ : Fin n → ℝ × (Fin 3 → ℝ) → ℝ) (ε : Fin n → ℝ) (ξ : Fin n → Ω → SpaceTime → ℝ)
    (z : Fin n → SpaceTime) (ω : Ω) (i : Fin n) :
    hairerPsiWickSquare N (ρ i) (ε i) (ξ i) ω (z i) =
      wickMonomial (fun a b => hairerCrossCovarianceTwo N (ρ a) (ε a) (ρ b) (ε b) (z a - z b))
        [i, i] (fun j => hairerPsiField N (ξ j) ω (z j)) := by
  rw [wickMonomial_pair_self, hairerPsiWickSquare, hairerWickConstant_eq_covariance_zero,
    sub_self]
  rfl

omit [MeasurableSpace Ω] in
/-- The Wick cube of `Ψ_{ρ i, ε i}` at `z i` is the Wick monomial `:X_i³:` of the multi-mollifier
vector. -/
theorem hairerPsiWickCube_eq_wickMonomial_multiTwo (N : ℕ) {n : ℕ}
    (ρ : Fin n → ℝ × (Fin 3 → ℝ) → ℝ) (ε : Fin n → ℝ) (ξ : Fin n → Ω → SpaceTime → ℝ)
    (z : Fin n → SpaceTime) (ω : Ω) (i : Fin n) :
    hairerPsiWickCube N (ρ i) (ε i) (ξ i) ω (z i) =
      wickMonomial (fun a b => hairerCrossCovarianceTwo N (ρ a) (ε a) (ρ b) (ε b) (z a - z b))
        [i, i, i] (fun j => hairerPsiField N (ξ j) ω (z j)) := by
  rw [wickMonomial_triple_self, hairerPsiWickCube, hairerWickConstant_eq_covariance_zero,
    sub_self]
  rfl

/-- The four-dimensional Gaussian vector `(Ψ_{ρ,ε}(u), Ψ_{ρ',ε'}(u), Ψ_{ρ,ε}(v), Ψ_{ρ',ε'}(v))`. -/
theorem hairerPsiField_isCentredGaussianVector_fourTwo (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε')
    {ξ ξ' : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ' ε' ξ') (u v : SpaceTime) :
    IsCentredGaussianVector P
      (fun ω j => hairerPsiField N (![ξ, ξ', ξ, ξ'] j) ω (![u, u, v, v] j))
      (fun a b => hairerCrossCovarianceTwo N (![ρ, ρ', ρ, ρ'] a) (![ε, ε', ε, ε'] a)
        (![ρ, ρ', ρ, ρ'] b) (![ε, ε', ε, ε'] b) (![u, u, v, v] a - ![u, u, v, v] b)) :=
  hairerPsiField_isCentredGaussianVector_multiscaleTwo N (ρ := ![ρ, ρ', ρ, ρ'])
    (ε := ![ε, ε', ε, ε']) (ξ := ![ξ, ξ', ξ, ξ']) (fun i => by fin_cases i <;> simpa)
    (fun i => by fin_cases i <;> simpa) hW (fun i => by fin_cases i <;> simpa) ![u, u, v, v]

/-- **Covariance of the difference of Wick squares, two mollifiers.** -/
theorem hairerPsiWickSquare_sub_integral_mulTwo (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε')
    {ξ ξ' : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ' ε' ξ') (u v : SpaceTime) :
    ∫ ω, (hairerPsiWickSquare N ρ ε ξ ω u - hairerPsiWickSquare N ρ' ε' ξ' ω u) *
        (hairerPsiWickSquare N ρ ε ξ ω v - hairerPsiWickSquare N ρ' ε' ξ' ω v) ∂P =
      2 * (hairerCrossCovarianceTwo N ρ ε ρ ε (u - v) ^ 2 -
        hairerCrossCovarianceTwo N ρ ε ρ' ε' (u - v) ^ 2 -
        hairerCrossCovarianceTwo N ρ' ε' ρ ε (u - v) ^ 2 +
        hairerCrossCovarianceTwo N ρ' ε' ρ' ε' (u - v) ^ 2) := by
  have h := hairerPsiField_isCentredGaussianVector_fourTwo N hρ hρ' hε hε' hW hξ hξ' u v
  have h2 := integral_wick_replicate_sub_mul_sub h (k := 2) (by norm_num) 0 1 2 3
  have e : ∀ (i : Fin 4) (ω : Ω), hairerPsiWickSquare N (![ρ, ρ', ρ, ρ'] i) (![ε, ε', ε, ε'] i)
      (![ξ, ξ', ξ, ξ'] i) ω (![u, u, v, v] i) = wickMonomial
      (fun a b => hairerCrossCovarianceTwo N (![ρ, ρ', ρ, ρ'] a) (![ε, ε', ε, ε'] a)
        (![ρ, ρ', ρ, ρ'] b) (![ε, ε', ε, ε'] b) (![u, u, v, v] a - ![u, u, v, v] b))
      (List.replicate 2 i) (fun j => hairerPsiField N (![ξ, ξ', ξ, ξ'] j) ω (![u, u, v, v] j)) :=
    fun i ω => hairerPsiWickSquare_eq_wickMonomial_multiTwo N _ _ _ _ ω i
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  have e3 := e 3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    List.replicate] at e0 e1 e2 e3 h2
  simp only [e0, e1, e2, e3]
  rw [h2]
  simp [Nat.factorial]

/-- **Covariance of the difference of Wick cubes, two mollifiers.** -/
theorem hairerPsiWickCube_sub_integral_mulTwo (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε')
    {ξ ξ' : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ' ε' ξ') (u v : SpaceTime) :
    ∫ ω, (hairerPsiWickCube N ρ ε ξ ω u - hairerPsiWickCube N ρ' ε' ξ' ω u) *
        (hairerPsiWickCube N ρ ε ξ ω v - hairerPsiWickCube N ρ' ε' ξ' ω v) ∂P =
      6 * (hairerCrossCovarianceTwo N ρ ε ρ ε (u - v) ^ 3 -
        hairerCrossCovarianceTwo N ρ ε ρ' ε' (u - v) ^ 3 -
        hairerCrossCovarianceTwo N ρ' ε' ρ ε (u - v) ^ 3 +
        hairerCrossCovarianceTwo N ρ' ε' ρ' ε' (u - v) ^ 3) := by
  have h := hairerPsiField_isCentredGaussianVector_fourTwo N hρ hρ' hε hε' hW hξ hξ' u v
  have h2 := integral_wick_replicate_sub_mul_sub h (k := 3) (by norm_num) 0 1 2 3
  have e : ∀ (i : Fin 4) (ω : Ω), hairerPsiWickCube N (![ρ, ρ', ρ, ρ'] i) (![ε, ε', ε, ε'] i)
      (![ξ, ξ', ξ, ξ'] i) ω (![u, u, v, v] i) = wickMonomial
      (fun a b => hairerCrossCovarianceTwo N (![ρ, ρ', ρ, ρ'] a) (![ε, ε', ε, ε'] a)
        (![ρ, ρ', ρ, ρ'] b) (![ε, ε', ε, ε'] b) (![u, u, v, v] a - ![u, u, v, v] b))
      (List.replicate 3 i) (fun j => hairerPsiField N (![ξ, ξ', ξ, ξ'] j) ω (![u, u, v, v] j)) :=
    fun i ω => hairerPsiWickCube_eq_wickMonomial_multiTwo N _ _ _ _ ω i
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  have e3 := e 3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    List.replicate] at e0 e1 e2 e3 h2
  simp only [e0, e1, e2, e3]
  rw [h2]
  simp [Nat.factorial]

/-- The difference of Wick squares of two mollifications is square integrable. -/
theorem hairerPsiWickSquare_sub_memLpTwo (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε')
    {ξ ξ' : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ' ε' ξ') (z : SpaceTime) :
    MemLp (fun ω => hairerPsiWickSquare N ρ ε ξ ω z - hairerPsiWickSquare N ρ' ε' ξ' ω z) 2 P :=
  (hairerPsiWickSquare_memLp N hρ hε hW hξ z).sub (hairerPsiWickSquare_memLp N hρ' hε' hW hξ' z)

/-- The difference of Wick cubes of two mollifications is square integrable. -/
theorem hairerPsiWickCube_sub_memLpTwo (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε')
    {ξ ξ' : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ' ε' ξ') (z : SpaceTime) :
    MemLp (fun ω => hairerPsiWickCube N ρ ε ξ ω z - hairerPsiWickCube N ρ' ε' ξ' ω z) 2 P :=
  (hairerPsiWickCube_memLp N hρ hε hW hξ z).sub (hairerPsiWickCube_memLp N hρ' hε' hW hξ' z)

end RegularityStructures.Phi43

end
