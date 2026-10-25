/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedPolynomialF

/-!
# Basis criteria for the integration-extension group

Hairer [Hai14, Definition 5.7, Theorem 5.14]. Membership can be checked on
the explicit finite basis. In particular each newly planted symbol has
the required action modulo the polynomial subspace. Triangularity is
essential: an unrestricted polynomial correction need not lower degree.
This file does not assert existence of an extension of every old action.
-/

public section

namespace RegularityStructures.Phi43

theorem phi43ExtensionGroupF_planted_mod_polynomial (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (SymbolF → ℝ))
    (hg : g ∈ (phi43RegularityStructureF κ).group) (τ : Phi43PlantSource) :
    g.val (Pi.single (.planted τ) 1) -
      phi43IntegrationF (g.val (Pi.single (.old τ.symbol) 1)) ∈
        (phi43PolynomialSectorF κ).subspace := by
  rw [phi43PolynomialSectorF_subspace]
  have h := hg.2.choose_spec.2.2.1 (Pi.single (.old τ.symbol) 1)
  rw [phi43IntegrationF_old_source] at h
  simpa only [neg_sub] using (phi43PolynomialSubspaceF κ).neg_mem h

theorem phi43ExtensionGroupF_mem_of_basis (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (SymbolF → ℝ))
    (htri : IsGradedUnipotent (phi43DegreeF κ) g.val)
    (g₀ : LinearMap.GeneralLinearGroup ℝ (Symbol → ℝ))
    (hg₀ : g₀ ∈ (phi43RegularityStructure κ).group)
    (hold : ∀ a, g.val (phi43OldEmbF a) = phi43OldEmbF (g₀.val a))
    (hI : ∀ τ : SymbolF,
      phi43IntegrationF (g.val (Pi.single τ 1)) -
        g.val (phi43IntegrationF (Pi.single τ 1)) ∈ phi43PolynomialSubspaceF κ)
    (hn : ∀ τ : SymbolF, g.val (Pi.single τ 1) (.old .noise) =
      (Pi.single τ 1 : SymbolF → ℝ) (.old .noise)) :
    g ∈ (phi43RegularityStructureF κ).group := by
  refine ⟨htri, g₀, hg₀, hold, ?_, ?_⟩
  · intro a
    have he : phi43IntegrationF (g.val a) - g.val (phi43IntegrationF a) =
        ∑ τ : SymbolF, a τ • (phi43IntegrationF (g.val (Pi.single τ 1)) -
          g.val (phi43IntegrationF (Pi.single τ 1))) := by
      conv_lhs => rw [eq_sum_single a]
      simp only [map_sum, map_smul, Finset.sum_sub_distrib, smul_sub]
    rw [he]
    exact Submodule.sum_mem _ fun τ _ => Submodule.smul_mem _ _ (hI τ)
  · intro a
    conv_lhs => rw [eq_sum_single a]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, hn]
    simpa only [Finset.sum_apply, Pi.smul_apply] using
      congrFun (eq_sum_single a).symm (.old .noise)

end RegularityStructures.Phi43

end
