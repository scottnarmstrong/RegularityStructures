/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedExtensionNegativeBounds
public import Phi43.Structure.RenormalisedExtensionPositiveTails
public import Phi43.Structure.CanonicalSmoothMomentBounds
public import RegularityStructures.Abstract.Model

/-!
# Full compact Pi bounds of the actual corrected smooth Model

Derived positive cancellation and polynomial tails are combined using Q
moments, with no model-bound input [Hai14, Proposition 8.27, Theorem 8.44].
-/

public noncomputable section

open Set

namespace RegularityStructures.Phi43

private theorem reg_pi (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (hf : PolyBounded noise.zeta) (C : RenormalisationConstants) (x : ParabolicSpace)
    (a : Symbol → ℝ) {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    (renormalisedSmoothExtensionModel N κ noise hf C).regPi x a t z =
      parabolicSemigroup.apply t
        ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x
          (phi43CoordinateEquiv.symm a)) z := by
  change (if 0 < t then _ else 0) = _
  simp only [ht, ite_true, LinearEquiv.coe_coe]

/-- The genuine canonical Model satisfies Pi bounds on its whole fixed-point cutoff. -/
private theorem pi_bound (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (hf : PolyBounded noise.zeta) (C : RenormalisationConstants) {S : Set ParabolicSpace} (hS : IsCompact S) :
    ∃ B : ℝ, 0 ≤ B ∧ (renormalisedSmoothExtensionModel N κ noise hf C).PiBoundOn (gamma κ) B S := by
  obtain ⟨D, hD0, hD⟩ := renormalisedSmoothExtensionModel_bounded_diagonal N κ noise hf C hS
  have hb (τ : Symbol) : ∃ B : ℝ, 0 ≤ B ∧ ∀ (_hτ : homogeneity κ τ < gamma κ),
      ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x ∈ S,
        |(renormalisedSmoothExtensionModel N κ noise hf C).regPi x (Pi.single τ 1) t x| ≤
          B * t ^ (homogeneity κ τ / parabolicSemigroup.order) := by
    by_cases hpos : 0 < homogeneity κ τ
    · by_cases hcut : homogeneity κ τ < gamma κ
      · obtain ⟨A, B, hA0, hB0, n, hn, hbound⟩ :=
          renormalisedExtensionPi_positive_two_power_bound N κ noise hf C τ hpos hcut hS
        refine ⟨A * parabolicSemigroup.momentConst (homogeneity κ τ) +
          B * parabolicSemigroup.momentConst n,
          add_nonneg (mul_nonneg hA0 (parabolicSemigroup.momentConst_nonneg _))
            (mul_nonneg hB0 (parabolicSemigroup.momentConst_nonneg _)), ?_⟩
        intro _ t ht x hx
        rw [reg_pi N κ noise hf C x _ ht.1]
        have he : phi43CoordinateEquiv.symm (Pi.single τ 1) = basis τ := by
          apply phi43CoordinateEquiv.injective
          simp [phi43CoordinateEquiv_basis]
        rw [he]
        exact canonicalSmooth_apply_two_power_bound
          (renormalisedExtensionPi_growth N noise hf C x (basis τ)) x hpos.le hn hA0 hB0
          (hbound x hx) ht.1 ht.2
      · exact ⟨0, le_rfl, fun hτ => (hcut hτ).elim⟩
    · refine ⟨D, hD0, fun _ t ht x hx => (hD τ t ht x hx).trans ?_⟩
      exact le_mul_of_one_le_right hD0
        (Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2
          (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hpos)
            parabolicSemigroup.order_pos.le))
  choose B hB0 hB using hb
  refine ⟨∑ τ : Symbol, B τ, Finset.sum_nonneg (fun τ _ => hB0 τ), ?_⟩
  intro τ hτ t ht x hx
  exact (hB τ hτ t ht x hx).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun σ _ => hB0 σ) (Finset.mem_univ τ))
    (Real.rpow_nonneg ht.1.le _))

/-- Full compact Pi bounds under the explicit polynomial growth bound on the
first four derivatives of the noise. -/
theorem canonicalRenormalisedModel_pi_bounds (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) {S : Set ParabolicSpace} (hS : IsCompact S) :
    ∃ B : ℝ, 0 ≤ B ∧
      (canonicalRenormalisedModel N κ noise Cg q hg C).PiBoundOn (gamma κ) B S :=
  pi_bound N κ noise (canonicalNoise_polyBounded_of_derivatives noise Cg q hg) C hS

end RegularityStructures.Phi43

end

