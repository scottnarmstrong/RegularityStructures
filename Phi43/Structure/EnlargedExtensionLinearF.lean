/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedIntegrationAxiomsF
public import Phi43.Structure.EnlargedUnipotentEquivF

/-!
# Literal linear extension of an old action to the new plants

Hairer [Hai14, Theorem 5.14]. The zero additional Taylor correction sends
each new plant I(tau) to I(Gamma tau). This file constructs the linear
map and proves its grading properties. Group membership is separate.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- Literal basis action with zero new polynomial correction. -/
def phi43PlantExtensionBasisF (L : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ)) :
    SymbolF → SymbolF → ℝ
  | .old τ => phi43OldEmbF (L (Pi.single τ 1))
  | .planted τ => phi43IntegrationF (phi43OldEmbF (L (Pi.single τ.symbol 1)))

/-- Linear extension of the old action and the new integration formula. -/
def phi43PlantExtensionLinearF (L : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ)) :
    (SymbolF → ℝ) →ₗ[ℝ] (SymbolF → ℝ) where
  toFun a := ∑ τ : SymbolF, a τ • phi43PlantExtensionBasisF L τ
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

theorem phi43PlantExtensionLinearF_single (L : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
    (τ : SymbolF) :
    phi43PlantExtensionLinearF L (Pi.single τ 1) = phi43PlantExtensionBasisF L τ := by
  simp [phi43PlantExtensionLinearF, Pi.single_apply]

theorem phi43PlantExtensionLinearF_old (L : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
    (a : Symbol → ℝ) :
    phi43PlantExtensionLinearF L (phi43OldEmbF a) = phi43OldEmbF (L a) := by
  conv_lhs => rw [eq_sum_single a]
  conv_rhs => rw [eq_sum_single a]
  simp only [map_sum, map_smul, phi43OldEmbF_single, phi43PlantExtensionLinearF_single,
    phi43PlantExtensionBasisF]

theorem phi43OldEmbF_lower (κ : Kappa) (α : ℝ) (a : Symbol → ℝ)
    (ha : a ∈ lowerSubspace (homogeneity κ) α) :
    phi43OldEmbF a ∈ lowerSubspace (phi43DegreeF κ) α := by
  intro τ hτ
  cases τ with
  | old τ => exact ha τ hτ
  | planted τ => rfl

theorem phi43IntegrationF_lower (κ : Kappa) (α : ℝ) (a : SymbolF → ℝ)
    (ha : a ∈ lowerSubspace (phi43DegreeF κ) α) :
    phi43IntegrationF a ∈ lowerSubspace (phi43DegreeF κ) (α + 2) := by
  rw [mem_lowerSubspace_iff_eq_sum.1 ha, map_sum]
  apply Submodule.sum_mem
  intro τ hτ
  have ht := (Finset.mem_filter.1 hτ).2
  have he : (Pi.single τ (a τ) : SymbolF → ℝ) = a τ • Pi.single τ 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [he, map_smul, phi43IntegrationF_single]
  cases hi : phi43IntegrationSymbolF τ with
  | none => simp only [smul_zero]; exact Submodule.zero_mem _
  | some σ =>
    apply Submodule.smul_mem
    apply single_mem_lowerSubspace
    rw [phi43IntegrationSymbolF_degree κ hi]
    linarith only [ht]

theorem phi43PlantExtensionLinearF_unipotent (κ : Kappa)
    (L : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
    (hL : IsGradedUnipotent (homogeneity κ) L) :
    IsGradedUnipotent (phi43DegreeF κ) (phi43PlantExtensionLinearF L) := by
  intro τ
  rw [phi43PlantExtensionLinearF_single]
  cases τ with
  | old τ =>
    change phi43OldEmbF (L (Pi.single τ 1)) - Pi.single (.old τ) 1 ∈ _
    rw [← phi43OldEmbF_single, ← map_sub]
    exact phi43OldEmbF_lower κ _ _ (hL τ)
  | planted τ =>
    change phi43IntegrationF (phi43OldEmbF (L (Pi.single τ.symbol 1))) -
      Pi.single (.planted τ) 1 ∈ _
    rw [← phi43IntegrationF_old_source, ← phi43OldEmbF_single, ← map_sub, ← map_sub]
    exact phi43IntegrationF_lower κ _ _ (phi43OldEmbF_lower κ _ _ (hL τ.symbol))

end RegularityStructures.Phi43

end
