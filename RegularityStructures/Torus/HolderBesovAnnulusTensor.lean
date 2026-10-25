/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesovAnnulusReproducer
public import RegularityStructures.Torus.HolderBesovCutoffKernel

/-!
# Tensor decomposition of the annular reproducer

The tensor cutoff difference telescopes into three terms. In term `i`, the coordinate `i` carries
the Green profile and the other coordinates carry fixed cutoffs. Their periodic kernels have
uniformly bounded L1 norms. This is the annular multiplier input to the equivalence of the heat norm
(2.3) of the statement with the Littlewood--Paley norm.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal SchwartzMap

namespace RegularityStructures

/-- The inner cutoff `phi(8u)` as a fixed Schwartz profile. -/
def torusLPAnnulusInnerProfile : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ ℝ 8 (by norm_num)).toContinuousLinearEquiv torusLPCutoffProfile

theorem torusLPAnnulusInnerProfile_apply (u : ℝ) :
    torusLPAnnulusInnerProfile u = (torusLPBump (8 * u) : ℂ) := rfl

theorem torusLPAnnulusInnerProfile_eq_zero {u : ℝ} (hu : 2 ≤ |u|) :
    torusLPAnnulusInnerProfile u = 0 := by
  change torusLPCutoffProfile (8 * u) = 0
  apply torusLPCutoffProfile_eq_zero
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  linarith only [hu]

/-- The term with a Green factor in coordinate `i`, inner cutoffs before it and outer after it. -/
def torusLPAnnulusFactor (M : ℕ) (i j : Fin 3) : 𝓢(ℝ, ℂ) :=
  if j < i then torusLPAnnulusInnerProfile
  else if j = i then torusLPAnnulusGreenProfile M else torusLPCutoffProfile

theorem torusLPAnnulusFactor_eq_zero (M : ℕ) (i j : Fin 3) {u : ℝ} (hu : 2 ≤ |u|) :
    torusLPAnnulusFactor M i j u = 0 := by
  unfold torusLPAnnulusFactor
  split_ifs
  · exact torusLPAnnulusInnerProfile_eq_zero hu
  · exact torusLPAnnulusGreenProfile_eq_zero M hu
  · exact torusLPCutoffProfile_eq_zero hu

/-- The finite periodised tensor kernel for one Green-factor term. -/
def torusLPAnnulusGreenKernel (M : ℕ) (i : Fin 3) (n : ℕ) : C(Torus3, ℂ) :=
  torusTensorFiniteKernel (torusLPAnnulusFactor M i) (n + 2)

theorem lintegral_torusLPAnnulusGreenKernel_bound_uniform (M : ℕ) (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      (∫⁻ x : Torus3, ‖torusLPAnnulusGreenKernel M i n x‖ₑ) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hb⟩ := torusTensorFiniteKernel_bound_uniform
    (torusLPAnnulusFactor M i) (fun j _ hu => torusLPAnnulusFactor_eq_zero M i j hu)
  exact ⟨C, hC, fun n => hb (n + 2)⟩

theorem torusLP_annulus_tensor_decomposition (M : ℕ) (v : Fin 3 → ℝ) :
    (∏ j : Fin 3, (torusLPBump (v j) : ℂ)) -
      (∏ j : Fin 3, (torusLPBump (8 * v j) : ℂ)) =
      ∑ i : Fin 3, (∏ j : Fin 3, torusLPAnnulusFactor M i j (v j)) *
        (v i : ℂ) ^ (2 * M) := by
  have h₀ := torusLPAnnulusGreenProfile_mul_pow M (v 0)
  have h₁ := torusLPAnnulusGreenProfile_mul_pow M (v 1)
  have h₂ := torusLPAnnulusGreenProfile_mul_pow M (v 2)
  norm_num [torusLPAnnulusFactor, Fin.prod_univ_three, Fin.sum_univ_three,
    torusLPAnnulusInnerProfile_apply, torusLPCutoffProfile_apply]
  linear_combination
    -((torusLPBump (v 1) : ℂ) * (torusLPBump (v 2) : ℂ)) * h₀ -
    ((torusLPBump (8 * v 0) : ℂ) * (torusLPBump (v 2) : ℂ)) * h₁ -
    ((torusLPBump (8 * v 0) : ℂ) * (torusLPBump (8 * v 1) : ℂ)) * h₂

theorem torusLPAnnulusGreen_symbol_identity (M n : ℕ) (k : Fin 3 → ℤ) :
    (∑ i : Fin 3,
      (∏ j : Fin 3, torusLPAnnulusFactor M i j ((k j : ℝ) / (2 : ℝ) ^ (n + 2))) *
        (((k i : ℝ) / (2 : ℝ) ^ (n + 2) : ℝ) : ℂ) ^ (2 * M)) *
      (torusDyadicFrequencySymbol (n + 1) k : ℂ) =
        (torusDyadicFrequencySymbol (n + 1) k : ℂ) := by
  have he : (∑ i : Fin 3,
      (∏ j : Fin 3, torusLPAnnulusFactor M i j ((k j : ℝ) / (2 : ℝ) ^ (n + 2))) *
        (((k i : ℝ) / (2 : ℝ) ^ (n + 2) : ℝ) : ℂ) ^ (2 * M)) =
      (torusLPAnnulusReproducer n k : ℂ) := by
    rw [← torusLP_annulus_tensor_decomposition M
      (fun j : Fin 3 => (k j : ℝ) / (2 : ℝ) ^ (n + 2))]
    simp only [torusLPAnnulusReproducer, torusLowFrequencySymbol,
      Complex.ofReal_sub, Complex.ofReal_prod, div_eq_mul_inv]
    congr 1 <;> apply Finset.prod_congr rfl <;> intro j _ <;>
      rw [mul_comm (k j : ℝ)]
  rw [he, ← Complex.ofReal_mul, torusDyadicFrequencySymbol_succ_reproducer]

end RegularityStructures

end
