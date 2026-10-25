/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.ModelSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

/-!
# Weighted coefficient estimates in the finite symbol algebra

Finite-dimensional algebraic ingredients for the canonical Gamma bounds
of Hairer [Hai14, Proposition 8.27]. The product estimate uses the proved
homogeneity additivity of the actual retained product, including its zeros.
These are algebraic inequalities, not assumed model-bound certificates.
-/

public noncomputable section

namespace RegularityStructures.Phi43

/-- A single homogeneous basis contribution has its declared weighted bound. -/
theorem gammaWeightedBasis_bound (κ : Kappa) {d A α c : ℝ} (hd : 0 < d) (hA : 0 ≤ A)
    (τ : Symbol) (hc : |c| ≤ A * d ^ (α - homogeneity κ τ)) (σ : Symbol) :
    |(c • basis τ) σ| ≤ A * d ^ (α - homogeneity κ σ) := by
  by_cases h : τ = σ
  · subst σ
    simpa [basis] using hc
  · simp only [basis, Finsupp.smul_apply, Finsupp.single_apply, h, ite_false,
      smul_eq_mul, mul_zero, abs_zero]
    exact mul_nonneg hA (Real.rpow_nonneg hd.le _)

/-- Weighted coefficient bounds are subadditive. -/
theorem gammaWeighted_add_bound (κ : Kappa) {d A B α : ℝ} {a b : T}
    (ha : ∀ σ, |a σ| ≤ A * d ^ (α - homogeneity κ σ))
    (hb : ∀ σ, |b σ| ≤ B * d ^ (α - homogeneity κ σ)) (σ : Symbol) :
    |(a + b) σ| ≤ (A + B) * d ^ (α - homogeneity κ σ) := by
  rw [Finsupp.add_apply, add_mul]
  exact (abs_add_le _ _).trans (add_le_add (ha σ) (hb σ))

/-- A finite sum of homogeneous coefficient bounds. -/
theorem gammaWeighted_sum_bound (κ : Kappa) {ι : Type*} (s : Finset ι)
    {d α : ℝ} (A : ι → ℝ) (v : ι → T)
    (hv : ∀ i ∈ s, ∀ σ, |v i σ| ≤ A i * d ^ (α - homogeneity κ σ)) (σ : Symbol) :
    |(∑ i ∈ s, v i) σ| ≤ (∑ i ∈ s, A i) * d ^ (α - homogeneity κ σ) := by
  rw [Finsupp.finsetSum_apply, Finset.sum_mul]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => hv i hi σ)

private theorem multiply_coord (a b : T) (σ : Symbol) :
    (a * b) σ = ∑ τ : Symbol, ∑ υ : Symbol, a τ * b υ * (basisProduct τ υ) σ := by
  change (multiply a b) σ = _
  unfold multiply basisProductLinear
  simp only [Finsupp.linearCombination_apply]
  have ha : (a.sum fun τ c => c • (b.sum fun υ d => d • basisProduct τ υ)) =
      ∑ τ : Symbol, a τ • (b.sum fun υ d => d • basisProduct τ υ) :=
    Finsupp.sum_fintype _ _ (fun _ => by simp)
  have hb (τ : Symbol) : (b.sum fun υ d => d • basisProduct τ υ) =
      ∑ υ : Symbol, b υ • basisProduct τ υ :=
    Finsupp.sum_fintype _ _ (fun _ => by simp)
  rw [ha]
  simp_rw [hb]
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc]

/-- The actual retained product preserves weighted coefficient bounds,
with a finite dimension factor and the sum of the two input degrees. -/
theorem gammaWeighted_multiply_bound (κ : Kappa) {d A B α β : ℝ} (hd : 0 < d)
    (hA : 0 ≤ A) (hB : 0 ≤ B) {a b : T}
    (ha : ∀ σ, |a σ| ≤ A * d ^ (α - homogeneity κ σ))
    (hb : ∀ σ, |b σ| ≤ B * d ^ (β - homogeneity κ σ)) (σ : Symbol) :
    |(a * b) σ| ≤ ((Fintype.card Symbol : ℝ) ^ 2 * A * B) *
      d ^ (α + β - homogeneity κ σ) := by
  have hp (τ υ : Symbol) : |a τ * b υ * (basisProduct τ υ) σ| ≤
      (A * B) * d ^ (α + β - homogeneity κ σ) := by
    cases h : productSymbol τ υ with
    | none =>
        simp only [basisProduct, h, Finsupp.zero_apply, mul_zero, abs_zero]
        exact mul_nonneg (mul_nonneg hA hB) (Real.rpow_nonneg hd.le _)
    | some ρ =>
        by_cases hρ : ρ = σ
        · subst ρ
          have hdeg := homogeneity_product κ h
          simp only [basisProduct, h, basis, Finsupp.single_eq_same, mul_one, abs_mul]
          calc
            |a τ| * |b υ| ≤ (A * d ^ (α - homogeneity κ τ)) *
                (B * d ^ (β - homogeneity κ υ)) :=
              mul_le_mul (ha τ) (hb υ) (abs_nonneg _) (mul_nonneg hA (Real.rpow_nonneg hd.le _))
            _ = (A * B) * d ^ ((α - homogeneity κ τ) + (β - homogeneity κ υ)) := by
              rw [Real.rpow_add hd]
              ring
            _ = _ := by rw [hdeg]; congr 2; ring
        · simp only [basisProduct, h, basis, Finsupp.single_apply, hρ, ite_false,
            mul_zero, abs_zero]
          exact mul_nonneg (mul_nonneg hA hB) (Real.rpow_nonneg hd.le _)
  rw [multiply_coord]
  calc
    _ ≤ ∑ τ : Symbol, ∑ υ : Symbol, |a τ * b υ * (basisProduct τ υ) σ| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun τ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _τ : Symbol, ∑ _υ : Symbol, (A * B) * d ^ (α + β - homogeneity κ σ) :=
      Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun υ _ => hp τ υ
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end RegularityStructures.Phi43

end
