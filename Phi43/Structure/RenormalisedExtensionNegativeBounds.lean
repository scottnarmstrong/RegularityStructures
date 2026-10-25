/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedExtensionModel
public import RegularityStructures.Abstract.Model

/-!+# Compact negative-sector model bounds for smooth noise

The whole retained smooth lift is uniformly bounded after Q-regularisation
on compact sets and scales at most one. Consequently its negative sector
satisfies the required homogeneity bounds [Hai14, Proposition 8.27, Theorem 8.44].
Positive-sector cancellation estimates are a separate obligation.
-/

public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Phi43

private theorem apply_bounded_on_compact {g : ParabolicSpace → ℝ} (hg : PolyBounded g)
    {S : Set ParabolicSpace} (hS : IsCompact S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x ∈ S,
      |parabolicSemigroup.apply t g x| ≤ B := by
  obtain ⟨hgm, B, n, hB⟩ := hg
  have hB0 := nonneg_of_bound hB
  obtain ⟨C, hC⟩ := exists_kernelPowMoment_le n
  have hC' : ∀ t : ℝ, 0 < t → t ≤ 1 → kernelPowMoment n t ≤ max C 0 :=
    fun t ht ht1 => (hC t ht ht1).trans (le_max_left _ _)
  have hc : Continuous (fun x : ParabolicSpace => (1 + parabolicNorm x) ^ n) :=
    (continuous_const.add continuous_parabolicNorm).pow n
  obtain ⟨R, hR⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨B * (max C 0 * max R 0),
    mul_nonneg hB0 (mul_nonneg (le_max_right _ _) (le_max_right _ _)), ?_⟩
  intro t ht x hx
  have hr : (1 + parabolicNorm x) ^ n ≤ max R 0 := by
    have hR' : |(1 + parabolicNorm x) ^ n| ≤ R := by
      simpa only [Real.norm_eq_abs] using hR x hx
    exact (le_abs_self _).trans (hR'.trans (le_max_left _ _))
  exact (abs_apply_le_of_kernelPowMoment_le hgm hB hC' ht.1 ht.2 x).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr (le_max_right _ _)) hB0)

/-- A compact uniform bound for the regularised diagonal on the entire
retained space. Unlike the positive model bounds this needs no cancellation. -/
theorem renormalisedSmoothExtensionModel_bounded_diagonal (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (hf : PolyBounded noise.zeta) (C : RenormalisationConstants)
    {S : Set ParabolicSpace} (hS : IsCompact S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : Symbol, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x ∈ S,
      |(renormalisedSmoothExtensionModel N κ noise hf C).regPi x (Pi.single τ 1) t x| ≤ B := by
  have hb (τ σ : Symbol) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x ∈ S,
      |structureGroupMap ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionCharacter C x)
          (basis τ) σ *
        parabolicSemigroup.apply t
          ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGlobalBasis C σ) x| ≤ B := by
    obtain ⟨A, hA⟩ := hS.exists_bound_of_continuousOn
      (continuous_renormalisedExtensionStructureGroup_coeff N noise C τ σ).continuousOn
    obtain ⟨B, hB0, hB⟩ := apply_bounded_on_compact
      (renormalisedExtensionGlobalBasis_growth N κ noise hf C σ) hS
    refine ⟨max A 0 * B, mul_nonneg (le_max_right _ _) hB0, ?_⟩
    intro t ht x hx
    rw [abs_mul]
    have ha : |structureGroupMap
        ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionCharacter C x) (basis τ) σ| ≤ max A 0 := by
      have ha' := hA x hx
      exact le_trans (by simpa only [Real.norm_eq_abs] using ha') (le_max_left _ _)
    exact mul_le_mul ha (hB t ht x hx) (abs_nonneg _) (le_max_right _ _)
  choose B hB0 hB using hb
  refine ⟨∑ τ : Symbol, ∑ σ : Symbol, B τ σ,
    Finset.sum_nonneg (fun τ _ => Finset.sum_nonneg (fun σ _ => hB0 τ σ)), ?_⟩
  intro τ t ht x hx
  have he : phi43CoordinateEquiv.symm (Pi.single τ 1) = basis τ := by
    apply phi43CoordinateEquiv.injective
    simp [phi43CoordinateEquiv_basis]
  change |(renormalisedExtensionDistribution N (κ := κ) noise hf C x
    (phi43CoordinateEquiv.symm (Pi.single τ 1)) : ℝ → ParabolicSpace → ℝ) t x| ≤ _
  rw [he, renormalisedExtensionDistribution_reg_eq_sum N noise hf C x _ ht.1]
  calc
    _ ≤ ∑ σ : Symbol, |structureGroupMap
          ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionCharacter C x) (basis τ) σ *
        parabolicSemigroup.apply t
          ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGlobalBasis C σ) x| := by
      simpa only [Real.norm_eq_abs] using
        (norm_sum_le (Finset.univ : Finset Symbol)
          (fun σ => structureGroupMap
            ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionCharacter C x) (basis τ) σ *
            parabolicSemigroup.apply t
              ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGlobalBasis C σ) x))
    _ ≤ ∑ σ : Symbol, B τ σ := Finset.sum_le_sum (fun σ _ => hB τ σ t ht x hx)
    _ ≤ _ := Finset.single_le_sum
      (fun τ _ => Finset.sum_nonneg (fun σ _ => hB0 τ σ)) (Finset.mem_univ τ)

end RegularityStructures.Phi43

end

