/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedExtensionJoint
import RegularityStructures.Analysis.Kernel.GeneratorLip

/-!
# Source-local positive model estimates

For smooth noise, the positive retained symbols below the fixed-point cutoff
obey their pointwise parabolic homogeneity bound on compact sets
[Hai14, Proposition 8.27, Theorem 8.44]. This is an ordinary function estimate, not yet the
whole-space Q-regularised model bound.
-/

public noncomputable section

namespace RegularityStructures.Phi43

private theorem degree_le_one_below_cutoff (κ : Kappa) (τ : Symbol)
    (hτ : homogeneity κ τ < gamma κ) : homogeneity κ τ ≤ 1 := by
  have hκ0 := κ.property.1
  have hκ1 := κ.property.2
  cases τ <;> simp only [homogeneity, gamma] at hτ ⊢ <;> linarith

private theorem norm_le_parabolicNorm_small {v : ParabolicSpace}
    (hv : parabolicNorm v ≤ 1) : ‖v‖ ≤ parabolicNorm v := by
  have hs : Real.sqrt |v.1| ≤ parabolicNorm v := by
    unfold parabolicNorm
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have ht : |v.1| ≤ 1 := by
    have hsq := Real.sq_sqrt (abs_nonneg v.1)
    have hsn := Real.sqrt_nonneg |v.1|
    nlinarith
  exact RegularityStructures.norm_le_parabolicNorm ht

/-- Local pointwise homogeneity bounds on the positive fixed-point sector,
without any temporal growth hypothesis on the smooth periodic noise. -/
theorem renormalisedExtensionPi_positive_local_bound (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (C : RenormalisationConstants) {S : Set ParabolicSpace} (hS : IsCompact S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : Symbol, 0 < homogeneity κ τ →
      homogeneity κ τ < gamma κ → ∀ x ∈ S, ∀ y ∈ S,
        parabolicNorm (y - x) ≤ 1 →
        |(hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x (basis τ) y| ≤
          B * parabolicNorm (y - x) ^ homogeneity κ τ := by
  obtain ⟨B, hC0, hC⟩ := renormalisedExtensionPi_positive_compact_lipschitz N κ noise C hS
  refine ⟨B, hC0, fun τ hτ hτγ x hx y hy hxy => ?_⟩
  have hp : parabolicNorm (y - x) ≤ parabolicNorm (y - x) ^ homogeneity κ τ := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge' (parabolicNorm_nonneg _) hxy hτ.le
        (degree_le_one_below_cutoff κ τ hτγ))
  exact (hC τ hτ x hx y hy).trans (mul_le_mul_of_nonneg_left
    ((norm_le_parabolicNorm_small hxy).trans hp) hC0)

end RegularityStructures.Phi43

end

