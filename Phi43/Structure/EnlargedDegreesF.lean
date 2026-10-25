/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedPolynomialF
public import Phi43.Structure.HomogeneityNonintegrality
import Mathlib.Tactic.Linarith

/-!
# Degrees in the finite planted completion

Hairer [Hai14, Assumption 5.3, Section 9.4]. Every newly planted symbol
lies above the fixed-point cutoff. The twelve-plant completion, unlike
the full degree-four tree algebra, has no additional integer resonances
in the current Kappa interval. Polynomial symbols are explicitly excluded.
-/

public section

namespace RegularityStructures.Phi43

theorem phi43PlantSource_degree_gt_gamma (κ : Kappa) (τ : Phi43PlantSource) :
    gamma κ < phi43DegreeF κ (.planted τ) := by
  have hκ0 := κ.2.1
  have hκ1 := κ.2.2
  cases τ <;> simp only [gamma, phi43DegreeF, Phi43PlantSource.symbol, homogeneity] <;>
    linarith

private theorem old_source_ne_int (κ : Kappa) (τ : Phi43PlantSource) (n : ℤ) :
    homogeneity κ τ.symbol ≠ (n : ℝ) := by
  apply phi43_nonpolynomial_homogeneity_ne_int
  all_goals cases τ <;> simp [Phi43PlantSource.symbol]

theorem phi43PlantSource_degree_ne_int (κ : Kappa) (τ : Phi43PlantSource) (n : ℤ) :
    phi43DegreeF κ (.planted τ) ≠ (n : ℝ) := by
  intro h
  have ht := old_source_ne_int κ τ (n - 2)
  apply ht
  push_cast
  change homogeneity κ τ.symbol + 2 = (n : ℝ) at h
  linarith only [h]

theorem phi43DegreeF_nonpolynomial_ne_int (κ : Kappa) (τ : SymbolF)
    (hτ : τ ∉ Set.range phi43PolyEmbF) (n : ℤ) :
    phi43DegreeF κ τ ≠ (n : ℝ) := by
  cases τ with
  | planted τ => exact phi43PlantSource_degree_ne_int κ τ n
  | old τ =>
    have hn : τ ∉ Set.range phi43QuadraticPolyEmb :=
      fun h => hτ ((phi43PolyEmbF_old_range τ).2 h)
    rw [phi43QuadraticPolyEmb_range] at hn
    apply phi43_nonpolynomial_homogeneity_ne_int
    · exact fun h => hn (Or.inl h)
    · exact fun h => hn (Or.inr (Or.inl h))
    · exact fun i h => hn (Or.inr (Or.inr (Or.inl ⟨i, h⟩)))
    · exact fun p h => hn (Or.inr (Or.inr (Or.inr ⟨p, h⟩)))

theorem phi43DegreeF_nonpolynomial_shifted_ne_nat (κ : Kappa) (τ : SymbolF)
    (hτ : τ ∉ Set.range phi43PolyEmbF) (n : ℕ) :
    (n : ℝ) ≠ phi43DegreeF κ τ + 2 := by
  intro h
  apply phi43DegreeF_nonpolynomial_ne_int κ τ hτ ((n : ℤ) - 2)
  push_cast
  linarith only [h]

end RegularityStructures.Phi43

end
