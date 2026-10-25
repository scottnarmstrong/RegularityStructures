/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.PolyCompat
public import RegularityStructures.Abstract.Integration.JMapLinear
public import RegularityStructures.Analysis.Heat.Schauder.TaylorSum

/-!
# Multilevel Schauder: the polynomial components of `𝒦_γ f`

Components of `J(y) τ`, `N_γ f(y)` along `X^k`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

theorem single_emb_apply {P : PolynomialSector 𝒯 N'} (k k' : PolyIndex N') :
    (Pi.single (P.emb k') 1 : ι → ℝ) (P.emb k) = if k' = k then 1 else 0 := by
  by_cases h : k' = k
  · subst h; simp
  · have : P.emb k ≠ P.emb k' := fun e => h (P.emb_injective e).symm
    simp [this, h]

theorem choose_factorial_ratio (a b : ℕ) :
    ((Nat.factorial a : ℕ) : ℝ) / (Nat.factorial (a + b) : ℕ) * ((a + b).choose a : ℕ) =
      1 / (Nat.factorial b : ℕ) := by
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
  rw [Nat.add_sub_cancel_left] at h
  have ha : ((Nat.factorial a : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero a)
  have hb : ((Nat.factorial b : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero b)
  have hab : ((Nat.factorial (a + b) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero _)
  have h' : (((a + b).choose a : ℕ) : ℝ) * (Nat.factorial a : ℕ) * (Nat.factorial b : ℕ) =
      (Nat.factorial (a + b) : ℕ) := by exact_mod_cast h
  field_simp
  rw [← h']
  ring

theorem coeff_translate_eq (h : Fin 4 → ℝ) (k l : Fin 4 →₀ ℕ) :
    (multiFactorial k : ℝ) / multiFactorial (k + l) *
        ∏ i, (h i ^ ((k + l) i - k i) * (((k + l) i).choose (k i) : ℕ)) =
      coeffT h l := by
  unfold multiFactorial coeffT
  rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hc := choose_factorial_ratio (k i) (l i)
  simp only [Finsupp.add_apply, Nat.add_sub_cancel_left]
  calc ((Nat.factorial (k i) : ℕ) : ℝ) / (Nat.factorial (k i + l i) : ℕ) *
        (h i ^ l i * (((k i + l i).choose (k i) : ℕ) : ℝ))
      = h i ^ l i * (((Nat.factorial (k i) : ℕ) : ℝ) / (Nat.factorial (k i + l i) : ℕ) *
          (((k i + l i).choose (k i) : ℕ) : ℝ)) := by ring
    _ = _ := by rw [hc]; ring

theorem weight_add_tsub {k l : Fin 4 →₀ ℕ} (h : k ≤ l) :
    Finsupp.weight parabolicWeight l =
      Finsupp.weight parabolicWeight k + Finsupp.weight parabolicWeight (l - k) := by
  conv_lhs => rw [← add_tsub_cancel_of_le h]
  exact map_add _ _ _

end RegularityStructures

end
