/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeWickCube
public import Phi43.BPHZ.TreeWickSquare

/-!
# Covariance of the differences of Wick powers at two scales

Let `ξ`, `ξ'` be regularisations of the same white noise at scales `ε`, `ε'`, and
`a, b, c, d = Q_{εε}, Q_{εε'}, Q_{ε'ε}, Q_{ε'ε'}` the cross covariances at `u - v`
(`hairerCrossCovariance`).  Applying the diagram formula to the four-dimensional Gaussian vector
`(Ψ_ε(u), Ψ_ε'(u), Ψ_ε(v), Ψ_ε'(v))` gives

* `E[(:Ψ_ε²:(u) - :Ψ_ε'²:(u)) (:Ψ_ε²:(v) - :Ψ_ε'²:(v))] = 2 (a² - b² - c² + d²)`,
* `E[(:Ψ_ε³:(u) - :Ψ_ε'³:(u)) (:Ψ_ε³:(v) - :Ψ_ε'³:(v))] = 6 (a³ - b³ - c³ + d³)`,

where `b = Q_{εε'}(u - v)` and `c = Q_{ε'ε}(u - v) = Q_{εε'}(v - u)` agree when the kernel is
symmetric, which gives the form `2 (Q_{εε}² - 2 Q_{εε'}² + Q_{ε'ε'}²)`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- The Wick square of `Ψ_{ε i}` at `z i` is the Wick monomial `:X_i²:` of the multiscale vector. -/
theorem hairerPsiWickSquare_eq_wickMonomial_multiscale (N : ℕ) {n : ℕ} (ε : Fin n → ℝ)
    (ξ : Fin n → Ω → SpaceTime → ℝ) (z : Fin n → SpaceTime) (ω : Ω) (i : Fin n) :
    hairerPsiWickSquare N ρ (ε i) (ξ i) ω (z i) =
      wickMonomial (fun a b => hairerCrossCovariance N ρ (ε a) (ε b) (z a - z b)) [i, i]
        (fun j => hairerPsiField N (ξ j) ω (z j)) := by
  rw [wickMonomial_pair_self, hairerPsiWickSquare, hairerWickConstant_eq_covariance_zero,
    sub_self, hairerCrossCovariance_self]

omit [MeasurableSpace Ω] in
/-- The Wick cube of `Ψ_{ε i}` at `z i` is the Wick monomial `:X_i³:` of the multiscale vector. -/
theorem hairerPsiWickCube_eq_wickMonomial_multiscale (N : ℕ) {n : ℕ} (ε : Fin n → ℝ)
    (ξ : Fin n → Ω → SpaceTime → ℝ) (z : Fin n → SpaceTime) (ω : Ω) (i : Fin n) :
    hairerPsiWickCube N ρ (ε i) (ξ i) ω (z i) =
      wickMonomial (fun a b => hairerCrossCovariance N ρ (ε a) (ε b) (z a - z b)) [i, i, i]
        (fun j => hairerPsiField N (ξ j) ω (z j)) := by
  rw [wickMonomial_triple_self, hairerPsiWickCube, hairerWickConstant_eq_covariance_zero,
    sub_self, hairerCrossCovariance_self]

private theorem integral_sub_mul_sub_of_integrable {ι : Type*} {M : ι → Ω → ℝ}
    (hi : ∀ a b, Integrable (fun ω => M a ω * M b ω) P) (a₀ a₁ b₀ b₁ : ι) :
    ∫ ω, (M a₀ ω - M a₁ ω) * (M b₀ ω - M b₁ ω) ∂P =
      ∫ ω, M a₀ ω * M b₀ ω ∂P - ∫ ω, M a₀ ω * M b₁ ω ∂P - ∫ ω, M a₁ ω * M b₀ ω ∂P +
        ∫ ω, M a₁ ω * M b₁ ω ∂P := by
  have j1 : Integrable (fun ω => M a₀ ω * M b₀ ω - M a₀ ω * M b₁ ω) P := (hi _ _).sub (hi _ _)
  have j2 : Integrable (fun ω => M a₀ ω * M b₀ ω - M a₀ ω * M b₁ ω - M a₁ ω * M b₀ ω) P :=
    j1.sub (hi _ _)
  have hpt : ∀ ω, (M a₀ ω - M a₁ ω) * (M b₀ ω - M b₁ ω) =
      M a₀ ω * M b₀ ω - M a₀ ω * M b₁ ω - M a₁ ω * M b₀ ω + M a₁ ω * M b₁ ω :=
    fun ω => by ring
  simp_rw [hpt]
  rw [integral_add j2 (hi _ _), integral_sub j1 (hi _ _), integral_sub (hi _ _) (hi _ _)]

/-- **Covariance of differences of Wick monomials of a Gaussian vector.** -/
theorem integral_wick_replicate_sub_mul_sub {n : ℕ} {X : Ω → Fin n → ℝ} {C : Fin n → Fin n → ℝ}
    (h : IsCentredGaussianVector P X C) {k : ℕ} (hk : k ≤ 3) (a₀ a₁ b₀ b₁ : Fin n) :
    ∫ ω, (wickMonomial C (List.replicate k a₀) (X ω) - wickMonomial C (List.replicate k a₁) (X ω)) *
        (wickMonomial C (List.replicate k b₀) (X ω) - wickMonomial C (List.replicate k b₁) (X ω))
        ∂P =
      (k.factorial : ℝ) * (C a₀ b₀ ^ k - C a₀ b₁ ^ k - C a₁ b₀ ^ k + C a₁ b₁ ^ k) := by
  have hi : ∀ a b : Fin n, Integrable (fun ω => wickMonomial C (List.replicate k a) (X ω) *
      wickMonomial C (List.replicate k b) (X ω)) P := fun a b => by
    simpa [Fin.prod_univ_two] using
      h.integrable_prod_wickMonomial (L := ![List.replicate k a, List.replicate k b])
  have := integral_sub_mul_sub_of_integrable
    (M := fun (a : Fin n) ω => wickMonomial C (List.replicate k a) (X ω)) hi a₀ a₁ b₀ b₁
  rw [this, integral_wick_replicate_mul_wick_replicate h a₀ b₀ hk hk,
    integral_wick_replicate_mul_wick_replicate h a₀ b₁ hk hk,
    integral_wick_replicate_mul_wick_replicate h a₁ b₀ hk hk,
    integral_wick_replicate_mul_wick_replicate h a₁ b₁ hk hk]
  simp only [ite_true]
  ring

end RegularityStructures.Phi43

end
