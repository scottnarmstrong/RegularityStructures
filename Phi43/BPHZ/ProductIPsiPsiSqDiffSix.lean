/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiDiffFour
public import Phi43.BPHZ.ProductIPsiPsiSqCovSix
import Mathlib.Tactic
public import Phi43.BPHZ.TreeWickSquare

/-!
# Six-point formula for `Ψ` with two models

For an arbitrary assignment of models `s k` to the points `z k` (`k < 6`), with
`q a b = qMix (s a) (s b) (z a - z b)`, Gaussian integration by parts gives
`E[Ψ_{s 0}(z 0) ⋯ Ψ_{s 5}(z 5)] = Σ_{j = 1}^{5} q 0 j · (three pairings of the other four)`
(`psiMix_integral_mul_six`).
-/

@[expose] public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The pair covariance `Q_{s a, s b}(z a - z b)` of the points `a`, `b`. -/
noncomputable def psiMixPair (N : ℕ) (ρ : Fin 2 → ℝ × (Fin 3 → ℝ) → ℝ) (ε : Fin 2 → ℝ)
    (s : Fin 6 → Fin 2) (z : Fin 6 → SpaceTime) (a b : Fin 6) : ℝ :=
  qMix N ρ ε (s a) (s b) (z a - z b)

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {ρ : Fin 2 → ℝ × (Fin 3 → ℝ) → ℝ} {ε : Fin 2 → ℝ} {ξ : Fin 2 → Ω → SpaceTime → ℝ}

/-- **Six-point formula, arbitrary models.** -/
theorem psiMix_integral_mul_six (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i)) (hε : ∀ i, 0 < ε i)
    (hW : IsWhiteNoise P W) (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i))
    (s : Fin 6 → Fin 2) (z : Fin 6 → SpaceTime) :
    Integrable (fun ω => hairerPsiField N (ξ (s 0)) ω (z 0) * hairerPsiField N (ξ (s 1)) ω (z 1) *
      hairerPsiField N (ξ (s 2)) ω (z 2) * hairerPsiField N (ξ (s 3)) ω (z 3) *
      hairerPsiField N (ξ (s 4)) ω (z 4) * hairerPsiField N (ξ (s 5)) ω (z 5)) P ∧
    ∫ ω, hairerPsiField N (ξ (s 0)) ω (z 0) * hairerPsiField N (ξ (s 1)) ω (z 1) *
      hairerPsiField N (ξ (s 2)) ω (z 2) * hairerPsiField N (ξ (s 3)) ω (z 3) *
      hairerPsiField N (ξ (s 4)) ω (z 4) * hairerPsiField N (ξ (s 5)) ω (z 5) ∂P =
    psiMixPair N ρ ε s z 0 1 * (psiMixPair N ρ ε s z 2 3 * psiMixPair N ρ ε s z 4 5 +
        psiMixPair N ρ ε s z 2 4 * psiMixPair N ρ ε s z 3 5 +
        psiMixPair N ρ ε s z 2 5 * psiMixPair N ρ ε s z 3 4) +
    psiMixPair N ρ ε s z 0 2 * (psiMixPair N ρ ε s z 1 3 * psiMixPair N ρ ε s z 4 5 +
        psiMixPair N ρ ε s z 1 4 * psiMixPair N ρ ε s z 3 5 +
        psiMixPair N ρ ε s z 1 5 * psiMixPair N ρ ε s z 3 4) +
    psiMixPair N ρ ε s z 0 3 * (psiMixPair N ρ ε s z 1 2 * psiMixPair N ρ ε s z 4 5 +
        psiMixPair N ρ ε s z 1 4 * psiMixPair N ρ ε s z 2 5 +
        psiMixPair N ρ ε s z 1 5 * psiMixPair N ρ ε s z 2 4) +
    psiMixPair N ρ ε s z 0 4 * (psiMixPair N ρ ε s z 1 2 * psiMixPair N ρ ε s z 3 5 +
        psiMixPair N ρ ε s z 1 3 * psiMixPair N ρ ε s z 2 5 +
        psiMixPair N ρ ε s z 1 5 * psiMixPair N ρ ε s z 2 3) +
    psiMixPair N ρ ε s z 0 5 * (psiMixPair N ρ ε s z 1 2 * psiMixPair N ρ ε s z 3 4 +
        psiMixPair N ρ ε s z 1 3 * psiMixPair N ρ ε s z 2 4 +
        psiMixPair N ρ ε s z 1 4 * psiMixPair N ρ ε s z 2 3) := by
  have h := hairerPsiField_isCentredGaussianVector_multiscaleTwo N (ρ := fun k => ρ (s k))
    (ε := fun k => ε (s k)) (ξ := fun k => ξ (s k)) (fun k => hρ _) (fun k => hε _) hW
    (fun k => hξ _) z
  have hP := h.isProbabilityMeasure
  refine ⟨?_, ?_⟩
  · have := h.integrable_prod_apply (σ := fun i : Fin 6 => i) Finset.univ
    simpa [Fin.prod_univ_six, mul_assoc] using this
  · have e : ∀ ω, hairerPsiField N (ξ (s 0)) ω (z 0) * hairerPsiField N (ξ (s 1)) ω (z 1) *
        hairerPsiField N (ξ (s 2)) ω (z 2) * hairerPsiField N (ξ (s 3)) ω (z 3) *
        hairerPsiField N (ξ (s 4)) ω (z 4) * hairerPsiField N (ξ (s 5)) ω (z 5) =
        (fun ω (i : Fin 6) => hairerPsiField N (ξ (s i)) ω (z i)) ω 0 *
          ∏ k ∈ ({1, 2, 3, 4, 5} : Finset (Fin 6)),
            (fun ω (i : Fin 6) => hairerPsiField N (ξ (s i)) ω (z i)) ω k := by
      intro ω
      simp [Finset.prod_insert, mul_assoc]
    simp_rw [e]
    rw [h.integral_mul_prod_eq_sum (σ := fun i : Fin 6 => i) 0 ({1, 2, 3, 4, 5} : Finset (Fin 6))]
    have e1 : ({1, 2, 3, 4, 5} : Finset (Fin 6)).erase 1 = {2, 3, 4, 5} := by decide
    have e2 : ({1, 2, 3, 4, 5} : Finset (Fin 6)).erase 2 = {1, 3, 4, 5} := by decide
    have e3 : ({1, 2, 3, 4, 5} : Finset (Fin 6)).erase 3 = {1, 2, 4, 5} := by decide
    have e4 : ({1, 2, 3, 4, 5} : Finset (Fin 6)).erase 4 = {1, 2, 3, 5} := by decide
    have e5 : ({1, 2, 3, 4, 5} : Finset (Fin 6)).erase 5 = {1, 2, 3, 4} := by decide
    have hsum : ∀ f : Fin 6 → ℝ, ∑ j ∈ ({1, 2, 3, 4, 5} : Finset (Fin 6)), f j =
        f 1 + f 2 + f 3 + f 4 + f 5 := by
      intro f
      simp [Finset.sum_insert, add_assoc]
    rw [hsum]
    simp only [e1, e2, e3, e4, e5]
    have P4 : ∀ (i j k l : Fin 6), i ∉ ({j, k, l} : Finset (Fin 6)) →
        j ∉ ({k, l} : Finset (Fin 6)) → k ≠ l →
        ∫ ω, ∏ x ∈ ({i, j, k, l} : Finset (Fin 6)), hairerPsiField N (ξ (s x)) ω (z x) ∂P =
          psiMixPair N ρ ε s z i j * psiMixPair N ρ ε s z k l +
          psiMixPair N ρ ε s z i k * psiMixPair N ρ ε s z j l +
          psiMixPair N ρ ε s z i l * psiMixPair N ρ ε s z j k := by
      intro i j k l hi hj hk
      simp only [Finset.prod_insert hi, Finset.prod_insert hj, Finset.prod_pair hk]
      have := (psiMix_integral_mul_four N hρ hε hW hξ (fun m => s (![i, j, k, l] m))
        (fun m => z (![i, j, k, l] m))).2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at this
      simp_rw [← mul_assoc]
      rw [this]
      rfl
    rw [P4 2 3 4 5 (by decide) (by decide) (by decide), P4 1 3 4 5 (by decide) (by decide) (by decide),
      P4 1 2 4 5 (by decide) (by decide) (by decide), P4 1 2 3 5 (by decide) (by decide) (by decide),
      P4 1 2 3 4 (by decide) (by decide) (by decide)]
    rfl

theorem qMix_self (N : ℕ) (ρ : Fin 2 → ℝ × (Fin 3 → ℝ) → ℝ) (ε : Fin 2 → ℝ) (i : Fin 2)
    (z : SpaceTime) : qMix N ρ ε i i z = hairerCovariance N (ρ i) (ε i) z := rfl

/-- **The Wick-square block, arbitrary models.** -/
theorem psiMix_wick_block (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i)) (hε : ∀ i, 0 < ε i)
    (hW : IsWhiteNoise P W) (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) (i j : Fin 2)
    (w a w' b : SpaceTime) :
    Integrable (fun ω => hairerPsiField N (ξ i) ω w *
      (hairerPsiField N (ξ i) ω a ^ 2 - hairerCovariance N (ρ i) (ε i) 0) *
      hairerPsiField N (ξ j) ω w' *
      (hairerPsiField N (ξ j) ω b ^ 2 - hairerCovariance N (ρ j) (ε j) 0)) P ∧
    ∫ ω, hairerPsiField N (ξ i) ω w * (hairerPsiField N (ξ i) ω a ^ 2 -
        hairerCovariance N (ρ i) (ε i) 0) * hairerPsiField N (ξ j) ω w' *
        (hairerPsiField N (ξ j) ω b ^ 2 - hairerCovariance N (ρ j) (ε j) 0) ∂P =
      2 * qMix N ρ ε i j (w - w') * qMix N ρ ε i j (a - b) ^ 2 +
      4 * (qMix N ρ ε i i (w - a) * qMix N ρ ε j j (w' - b) * qMix N ρ ε i j (a - b)) +
      4 * (qMix N ρ ε i j (w - b) * qMix N ρ ε i j (a - w') * qMix N ρ ε i j (a - b)) := by
  obtain ⟨ci, hci⟩ : ∃ c, c = hairerCovariance N (ρ i) (ε i) 0 := ⟨_, rfl⟩
  obtain ⟨cj, hcj⟩ : ∃ c, c = hairerCovariance N (ρ j) (ε j) 0 := ⟨_, rfl⟩
  rw [← hci, ← hcj]
  have h6 := psiMix_integral_mul_six N hρ hε hW hξ ![i, i, i, j, j, j] ![w, a, a, w', b, b]
  have h4a := psiMix_integral_mul_four N hρ hε hW hξ ![i, j, j, j] ![w, w', b, b]
  have h4b := psiMix_integral_mul_four N hρ hε hW hξ ![i, i, i, j] ![w, a, a, w']
  have h2 := psiMix_integral_mul_two N hρ hε hW hξ i j w w'
  have i2 : Integrable (fun ω => hairerPsiField N (ξ i) ω w * hairerPsiField N (ξ j) ω w') P := by
    have mi := (hairerPsiField_memLp N (hρ i) (hε i) hW (hξ i) w)
    have mj := (hairerPsiField_memLp N (hρ j) (hε j) hW (hξ j) w')
    exact mi.integrable_mul mj
  have h6i : Integrable (fun ω => hairerPsiField N (ξ i) ω w * hairerPsiField N (ξ i) ω a * hairerPsiField N (ξ i) ω a * hairerPsiField N (ξ j) ω w' * hairerPsiField N (ξ j) ω b * hairerPsiField N (ξ j) ω b) P := h6.1
  have h6e : ∫ ω, hairerPsiField N (ξ i) ω w * hairerPsiField N (ξ i) ω a * hairerPsiField N (ξ i) ω a * hairerPsiField N (ξ j) ω w' * hairerPsiField N (ξ j) ω b * hairerPsiField N (ξ j) ω b ∂P =
      qMix N ρ ε i i (w - a) * (qMix N ρ ε i j (a - w') * qMix N ρ ε j j (b - b) + qMix N ρ ε i j (a - b) * qMix N ρ ε j j (w' - b) + qMix N ρ ε i j (a - b) * qMix N ρ ε j j (w' - b)) +
      qMix N ρ ε i i (w - a) * (qMix N ρ ε i j (a - w') * qMix N ρ ε j j (b - b) + qMix N ρ ε i j (a - b) * qMix N ρ ε j j (w' - b) + qMix N ρ ε i j (a - b) * qMix N ρ ε j j (w' - b)) +
      qMix N ρ ε i j (w - w') * (qMix N ρ ε i i (a - a) * qMix N ρ ε j j (b - b) + qMix N ρ ε i j (a - b) * qMix N ρ ε i j (a - b) + qMix N ρ ε i j (a - b) * qMix N ρ ε i j (a - b)) +
      qMix N ρ ε i j (w - b) * (qMix N ρ ε i i (a - a) * qMix N ρ ε j j (w' - b) + qMix N ρ ε i j (a - w') * qMix N ρ ε i j (a - b) + qMix N ρ ε i j (a - b) * qMix N ρ ε i j (a - w')) +
      qMix N ρ ε i j (w - b) * (qMix N ρ ε i i (a - a) * qMix N ρ ε j j (w' - b) + qMix N ρ ε i j (a - w') * qMix N ρ ε i j (a - b) + qMix N ρ ε i j (a - b) * qMix N ρ ε i j (a - w')) := h6.2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h4a h4b
  have e : ∀ ω, hairerPsiField N (ξ i) ω w * (hairerPsiField N (ξ i) ω a ^ 2 - ci) *
        hairerPsiField N (ξ j) ω w' * (hairerPsiField N (ξ j) ω b ^ 2 - cj) =
      ((hairerPsiField N (ξ i) ω w * hairerPsiField N (ξ i) ω a * hairerPsiField N (ξ i) ω a * hairerPsiField N (ξ j) ω w' * hairerPsiField N (ξ j) ω b * hairerPsiField N (ξ j) ω b) -
        ci * (hairerPsiField N (ξ i) ω w * hairerPsiField N (ξ j) ω w' *
          hairerPsiField N (ξ j) ω b * hairerPsiField N (ξ j) ω b)) -
        cj * (hairerPsiField N (ξ i) ω w * hairerPsiField N (ξ i) ω a * hairerPsiField N (ξ i) ω a *
          hairerPsiField N (ξ j) ω w') +
        ci * cj * (hairerPsiField N (ξ i) ω w * hairerPsiField N (ξ j) ω w') := fun ω => by ring
  have j1 : Integrable (fun ω => (hairerPsiField N (ξ i) ω w * hairerPsiField N (ξ i) ω a * hairerPsiField N (ξ i) ω a * hairerPsiField N (ξ j) ω w' * hairerPsiField N (ξ j) ω b * hairerPsiField N (ξ j) ω b) -
      ci * (hairerPsiField N (ξ i) ω w * hairerPsiField N (ξ j) ω w' *
        hairerPsiField N (ξ j) ω b * hairerPsiField N (ξ j) ω b)) P :=
    h6i.sub (h4a.1.const_mul _)
  have j2 : Integrable (fun ω => ((hairerPsiField N (ξ i) ω w * hairerPsiField N (ξ i) ω a * hairerPsiField N (ξ i) ω a * hairerPsiField N (ξ j) ω w' * hairerPsiField N (ξ j) ω b * hairerPsiField N (ξ j) ω b) -
      ci * (hairerPsiField N (ξ i) ω w * hairerPsiField N (ξ j) ω w' *
        hairerPsiField N (ξ j) ω b * hairerPsiField N (ξ j) ω b)) -
      cj * (hairerPsiField N (ξ i) ω w * hairerPsiField N (ξ i) ω a * hairerPsiField N (ξ i) ω a *
        hairerPsiField N (ξ j) ω w')) P := j1.sub (h4b.1.const_mul _)
  have j3 : Integrable (fun ω => hairerPsiField N (ξ i) ω w * (hairerPsiField N (ξ i) ω a ^ 2 - ci) *
      hairerPsiField N (ξ j) ω w' * (hairerPsiField N (ξ j) ω b ^ 2 - cj)) P := by
    refine (j2.add (i2.const_mul (ci * cj))).congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]; rw [e]
  refine ⟨j3, ?_⟩
  simp_rw [e]
  rw [integral_add j2 (i2.const_mul _), integral_sub j1 (h4b.1.const_mul _),
    integral_sub h6i (h4a.1.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, h6e, h4a.2, h4b.2, h2]
  simp only [sub_self, qMix_self, ← hci, ← hcj]
  ring

/-- **Uniform `L¹` bound of the Wick-square block, arbitrary models.** -/
theorem psiMix_wick_block_abs_le (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i)) (hε : ∀ i, 0 < ε i)
    (hW : IsWhiteNoise P W) (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) (i j : Fin 2)
    (w a w' b : SpaceTime) :
    ∫ ω, |hairerPsiField N (ξ i) ω w * (hairerPsiField N (ξ i) ω a ^ 2 -
        hairerCovariance N (ρ i) (ε i) 0) * hairerPsiField N (ξ j) ω w' *
        (hairerPsiField N (ξ j) ω b ^ 2 - hairerCovariance N (ρ j) (ε j) 0)| ∂P ≤
      (3 * hairerCovariance N (ρ i) (ε i) 0 ^ 2 + 60 * hairerCovariance N (ρ i) (ε i) 0 ^ 4 +
        3 * hairerCovariance N (ρ j) (ε j) 0 ^ 2 + 60 * hairerCovariance N (ρ j) (ε j) 0 ^ 4) / 4 := by
  have hi := (psiMix_wick_block N hρ hε hW hξ i j w a w' b).1
  have hS : ∀ (k : Fin 2) z ω, hairerPsiField N (ξ k) ω z ^ 2 - hairerCovariance N (ρ k) (ε k) 0 =
      hairerPsiWickSquare N (ρ k) (ε k) (ξ k) ω z := fun k z ω => by
    rw [hairerPsiWickSquare, hairerWickConstant_eq_covariance_zero]
  have hS4i : ∀ k z, Integrable (fun ω => (hairerPsiField N (ξ k) ω z ^ 2 -
      hairerCovariance N (ρ k) (ε k) 0) ^ 4) P := fun k z => by
    simp only [hS]
    exact integrable_hairerPsiWickSquare_pow_four N (hρ k) (hε k) hW (hξ k) z
  have hS4 : ∀ k z, ∫ ω, (hairerPsiField N (ξ k) ω z ^ 2 - hairerCovariance N (ρ k) (ε k) 0) ^ 4 ∂P =
      60 * hairerCovariance N (ρ k) (ε k) 0 ^ 4 := fun k z => by
    simp only [hS]
    rw [integral_hairerPsiWickSquare_pow_four N (hρ k) (hε k) hW (hξ k) z,
      hairerWickConstant_eq_covariance_zero]
  have hΨ4 := fun k z => psiMix_pow_four N hρ hε hW hξ k z
  have s12 : Integrable (fun ω => hairerPsiField N (ξ i) ω w ^ 4 +
      (hairerPsiField N (ξ i) ω a ^ 2 - hairerCovariance N (ρ i) (ε i) 0) ^ 4) P :=
    (hΨ4 i w).1.add (hS4i i a)
  have s123 : Integrable (fun ω => hairerPsiField N (ξ i) ω w ^ 4 +
      (hairerPsiField N (ξ i) ω a ^ 2 - hairerCovariance N (ρ i) (ε i) 0) ^ 4 +
      hairerPsiField N (ξ j) ω w' ^ 4) P := s12.add (hΨ4 j w').1
  have s1234 : Integrable (fun ω => hairerPsiField N (ξ i) ω w ^ 4 +
      (hairerPsiField N (ξ i) ω a ^ 2 - hairerCovariance N (ρ i) (ε i) 0) ^ 4 +
      hairerPsiField N (ξ j) ω w' ^ 4 +
      (hairerPsiField N (ξ j) ω b ^ 2 - hairerCovariance N (ρ j) (ε j) 0) ^ 4) P :=
    s123.add (hS4i j b)
  have hdom := s1234.div_const 4
  have hpt : ∀ ω, |hairerPsiField N (ξ i) ω w * (hairerPsiField N (ξ i) ω a ^ 2 -
      hairerCovariance N (ρ i) (ε i) 0) * hairerPsiField N (ξ j) ω w' *
      (hairerPsiField N (ξ j) ω b ^ 2 - hairerCovariance N (ρ j) (ε j) 0)| ≤
      (hairerPsiField N (ξ i) ω w ^ 4 +
      (hairerPsiField N (ξ i) ω a ^ 2 - hairerCovariance N (ρ i) (ε i) 0) ^ 4 +
      hairerPsiField N (ξ j) ω w' ^ 4 +
      (hairerPsiField N (ξ j) ω b ^ 2 - hairerCovariance N (ρ j) (ε j) 0) ^ 4) / 4 := fun ω =>
    abs_mul_four_le_pow_four _ _ _ _
  refine (integral_mono hi.abs hdom hpt).trans (le_of_eq ?_)
  rw [integral_div, integral_add s123 (hS4i j b), integral_add s12 (hΨ4 j w').1,
    integral_add (hΨ4 i w).1 (hS4i i a), hS4, hS4, (hΨ4 i w).2, (hΨ4 j w').2]

end RegularityStructures.Phi43

end
