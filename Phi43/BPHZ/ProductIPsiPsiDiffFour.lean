/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.CrossMollifierGaussian
public import Phi43.BPHZ.ProductIPsiPsiCovFour
public import Phi43.BPHZ.ProductIPsiPsiDiffArray
import Mathlib.Tactic

/-!
# Four- and six-point formulas for `Ψ` with two models

Two models `i ∈ Fin 2` with mollifiers `ρ i`, scales `ε i` and noises `ξ i` of the same white noise.
`qMix i j = hairerCrossCovarianceTwo N (ρ i) (ε i) (ρ j) (ε j)`.  For an arbitrary assignment of
models `s k` to the points `z k`, Isserlis gives
`E[Ψ_{s 0}(z 0) ⋯ Ψ_{s 3}(z 3)] = Q_{s0 s1}(z0 - z1) Q_{s2 s3}(z2 - z3) + …`
(`psiMix_integral_mul_four`) and the integration-by-parts recursion for six points.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The cross covariance of models `i`, `j`. -/
def qMix (N : ℕ) (ρ : Fin 2 → ℝ × (Fin 3 → ℝ) → ℝ) (ε : Fin 2 → ℝ) (i j : Fin 2) :
    SpaceTime → ℝ :=
  hairerCrossCovarianceTwo N (ρ i) (ε i) (ρ j) (ε j)

end RegularityStructures.Phi43

end

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {ρ : Fin 2 → ℝ × (Fin 3 → ℝ) → ℝ} {ε : Fin 2 → ℝ} {ξ : Fin 2 → Ω → SpaceTime → ℝ}

/-- **Four-point formula, arbitrary models.** -/
theorem psiMix_integral_mul_four (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i)) (hε : ∀ i, 0 < ε i)
    (hW : IsWhiteNoise P W) (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i))
    (s : Fin 4 → Fin 2) (z : Fin 4 → SpaceTime) :
    Integrable (fun ω => hairerPsiField N (ξ (s 0)) ω (z 0) * hairerPsiField N (ξ (s 1)) ω (z 1) *
      hairerPsiField N (ξ (s 2)) ω (z 2) * hairerPsiField N (ξ (s 3)) ω (z 3)) P ∧
    ∫ ω, hairerPsiField N (ξ (s 0)) ω (z 0) * hairerPsiField N (ξ (s 1)) ω (z 1) *
      hairerPsiField N (ξ (s 2)) ω (z 2) * hairerPsiField N (ξ (s 3)) ω (z 3) ∂P =
      qMix N ρ ε (s 0) (s 1) (z 0 - z 1) * qMix N ρ ε (s 2) (s 3) (z 2 - z 3) +
      qMix N ρ ε (s 0) (s 2) (z 0 - z 2) * qMix N ρ ε (s 1) (s 3) (z 1 - z 3) +
      qMix N ρ ε (s 0) (s 3) (z 0 - z 3) * qMix N ρ ε (s 1) (s 2) (z 1 - z 2) := by
  have h := hairerPsiField_isCentredGaussianVector_multiscaleTwo N (ρ := fun k => ρ (s k))
    (ε := fun k => ε (s k)) (ξ := fun k => ξ (s k)) (fun k => hρ _) (fun k => hε _) hW
    (fun k => hξ _) z
  have hP := h.isProbabilityMeasure
  refine ⟨?_, ?_⟩
  · have := h.integrable_prod_apply (σ := fun i : Fin 4 => i) Finset.univ
    simpa [Fin.prod_univ_four, mul_assoc] using this
  · have e : ∀ ω, hairerPsiField N (ξ (s 0)) ω (z 0) * hairerPsiField N (ξ (s 1)) ω (z 1) *
        hairerPsiField N (ξ (s 2)) ω (z 2) * hairerPsiField N (ξ (s 3)) ω (z 3) =
        (fun ω (i : Fin 4) => hairerPsiField N (ξ (s i)) ω (z i)) ω 0 *
          ∏ k ∈ ({1, 2, 3} : Finset (Fin 4)),
            (fun ω (i : Fin 4) => hairerPsiField N (ξ (s i)) ω (z i)) ω k := by
      intro ω
      simp [Finset.prod_insert, mul_assoc]
    simp_rw [e]
    rw [h.integral_mul_prod_eq_sum (σ := fun i : Fin 4 => i) 0 ({1, 2, 3} : Finset (Fin 4))]
    have e1 : ({1, 2, 3} : Finset (Fin 4)).erase 1 = {2, 3} := by decide
    have e2 : ({1, 2, 3} : Finset (Fin 4)).erase 2 = {1, 3} := by decide
    have e3 : ({1, 2, 3} : Finset (Fin 4)).erase 3 = {1, 2} := by decide
    have hsum : ∀ f : Fin 4 → ℝ, ∑ j ∈ ({1, 2, 3} : Finset (Fin 4)), f j = f 1 + f 2 + f 3 := by
      intro f
      simp [Finset.sum_insert, add_assoc]
    rw [hsum]
    simp only [e1, e2, e3]
    have P2 : ∀ (i j : Fin 4), i ≠ j →
        ∫ ω, ∏ k ∈ ({i, j} : Finset (Fin 4)), hairerPsiField N (ξ (s k)) ω (z k) ∂P =
          qMix N ρ ε (s i) (s j) (z i - z j) := by
      intro i j hij
      simp only [Finset.prod_pair hij]
      have := h.integral_mul i j
      simpa [qMix] using this
    rw [P2 2 3 (by decide), P2 1 3 (by decide), P2 1 2 (by decide)]
    simp only [qMix]

/-- **Two-point formula, arbitrary models.** -/
theorem psiMix_integral_mul_two (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i)) (hε : ∀ i, 0 < ε i)
    (hW : IsWhiteNoise P W) (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) (i j : Fin 2)
    (a b : SpaceTime) :
    ∫ ω, hairerPsiField N (ξ i) ω a * hairerPsiField N (ξ j) ω b ∂P =
      qMix N ρ ε i j (a - b) := by
  have h := hairerPsiField_isCentredGaussianVector_multiscaleTwo N (ρ := ![ρ i, ρ j])
    (ε := ![ε i, ε j]) (ξ := ![ξ i, ξ j]) (z := ![a, b]) (fun k => by fin_cases k <;> simp [hρ])
    (fun k => by fin_cases k <;> simp [hε]) hW (fun k => by fin_cases k <;> simp [hξ])
  have := h.integral_mul 0 1
  simpa [qMix] using this

/-- Each `Ψ_i(z)` has `E Ψ_i(z)⁴ = 3 Q_ii(0)²`, integrable. -/
theorem psiMix_pow_four (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i)) (hε : ∀ i, 0 < ε i)
    (hW : IsWhiteNoise P W) (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) (i : Fin 2)
    (z : SpaceTime) :
    Integrable (fun ω => hairerPsiField N (ξ i) ω z ^ 4) P ∧
      ∫ ω, hairerPsiField N (ξ i) ω z ^ 4 ∂P = 3 * hairerCovariance N (ρ i) (ε i) 0 ^ 2 := by
  refine ⟨?_, hairerPsiField_integral_pow_four N (hρ i) (hε i) hW (hξ i) z⟩
  have := (hairerPsiField_integral_mul_four N (hρ i) (hε i) hW (hξ i) z z z z).1
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only; ring

/-- **Uniform `L¹` bound of the four-fold product with arbitrary models.** -/
theorem psiMix_abs_mul_four_le (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i)) (hε : ∀ i, 0 < ε i)
    (hW : IsWhiteNoise P W) (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i))
    (s : Fin 4 → Fin 2) (z : Fin 4 → SpaceTime) :
    ∫ ω, |hairerPsiField N (ξ (s 0)) ω (z 0) * hairerPsiField N (ξ (s 1)) ω (z 1) *
      hairerPsiField N (ξ (s 2)) ω (z 2) * hairerPsiField N (ξ (s 3)) ω (z 3)| ∂P ≤
      (3 * hairerCovariance N (ρ (s 0)) (ε (s 0)) 0 ^ 2 + 3 * hairerCovariance N (ρ (s 1)) (ε (s 1)) 0 ^ 2 +
        3 * hairerCovariance N (ρ (s 2)) (ε (s 2)) 0 ^ 2 +
        3 * hairerCovariance N (ρ (s 3)) (ε (s 3)) 0 ^ 2) / 4 := by
  have hm := (psiMix_integral_mul_four N hρ hε hW hξ s z).1
  have a0 := psiMix_pow_four N hρ hε hW hξ (s 0) (z 0)
  have a1 := psiMix_pow_four N hρ hε hW hξ (s 1) (z 1)
  have a2 := psiMix_pow_four N hρ hε hW hξ (s 2) (z 2)
  have a3 := psiMix_pow_four N hρ hε hW hξ (s 3) (z 3)
  have s12 : Integrable (fun ω => hairerPsiField N (ξ (s 0)) ω (z 0) ^ 4 +
      hairerPsiField N (ξ (s 1)) ω (z 1) ^ 4) P := a0.1.add a1.1
  have s123 : Integrable (fun ω => hairerPsiField N (ξ (s 0)) ω (z 0) ^ 4 +
      hairerPsiField N (ξ (s 1)) ω (z 1) ^ 4 + hairerPsiField N (ξ (s 2)) ω (z 2) ^ 4) P :=
    s12.add a2.1
  have s1234 : Integrable (fun ω => hairerPsiField N (ξ (s 0)) ω (z 0) ^ 4 +
      hairerPsiField N (ξ (s 1)) ω (z 1) ^ 4 + hairerPsiField N (ξ (s 2)) ω (z 2) ^ 4 +
      hairerPsiField N (ξ (s 3)) ω (z 3) ^ 4) P := s123.add a3.1
  calc _ ≤ ∫ ω, (hairerPsiField N (ξ (s 0)) ω (z 0) ^ 4 + hairerPsiField N (ξ (s 1)) ω (z 1) ^ 4 +
        hairerPsiField N (ξ (s 2)) ω (z 2) ^ 4 + hairerPsiField N (ξ (s 3)) ω (z 3) ^ 4) / 4 ∂P :=
        integral_mono hm.abs (s1234.div_const 4) fun ω => abs_mul_four_le_pow_four _ _ _ _
    _ = _ := by
        rw [integral_div, integral_add s123 a3.1, integral_add s12 a2.1, integral_add a0.1 a1.1,
          a0.2, a1.2, a2.2, a3.2]

end RegularityStructures.Phi43

end
