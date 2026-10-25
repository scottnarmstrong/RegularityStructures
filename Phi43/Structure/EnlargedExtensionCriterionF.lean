/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedExtensionGroupF
import Mathlib.Tactic.Abel

/-!
# The local planted criterion for enlarged-group membership

Hairer [Hai14, Theorem 5.14]. A graded-unipotent automorphism extending
the old action belongs to the enlarged group exactly when each new
plant obeys I Gamma modulo polynomials. Global commutation and the
noise-coordinate identity are consequences, not further assumptions.
-/

public section

namespace RegularityStructures.Phi43

private theorem mem_of_planted (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (SymbolF → ℝ))
    (htri : IsGradedUnipotent (phi43DegreeF κ) g.val)
    (g₀ : LinearMap.GeneralLinearGroup ℝ (Symbol → ℝ))
    (hg₀ : g₀ ∈ (phi43RegularityStructure κ).group)
    (hold : ∀ a, g.val (phi43OldEmbF a) = phi43OldEmbF (g₀.val a))
    (hp : ∀ τ : Phi43PlantSource,
      g.val (Pi.single (.planted τ) 1) -
        phi43IntegrationF (g.val (Pi.single (.old τ.symbol) 1)) ∈
          (phi43PolynomialSectorF κ).subspace) :
    g ∈ (phi43RegularityStructureF κ).group := by
  let g' := phi43PlantExtensionGroupElementF κ g₀ hg₀
  have hg' : g' ∈ (phi43RegularityStructureF κ).group :=
    phi43PlantExtensionGroupElementF_mem κ g₀ hg₀
  let H : (SymbolF → ℝ) →ₗ[ℝ] (SymbolF → ℝ) := g.val - g'.val
  have hH : ∀ a, H a ∈ phi43PolynomialSubspaceF κ := by
    intro a
    rw [eq_sum_single a, map_sum]
    apply Submodule.sum_mem
    intro τ _
    rw [map_smul]
    apply Submodule.smul_mem
    cases τ with
    | old τ =>
      change g.val (Pi.single (.old τ) 1) -
        phi43PlantExtensionLinearF g₀.val (Pi.single (.old τ) 1) ∈ _
      rw [← phi43OldEmbF_single, hold, phi43PlantExtensionLinearF_old, sub_self]
      exact Submodule.zero_mem _
    | planted τ =>
      have ht := hp τ
      rw [phi43PolynomialSectorF_subspace] at ht
      rw [← phi43OldEmbF_single, hold] at ht
      change g.val (Pi.single (.planted τ) 1) -
        phi43PlantExtensionLinearF g₀.val (Pi.single (.planted τ) 1) ∈ _
      rw [phi43PlantExtensionLinearF_single]
      exact ht
  refine ⟨htri, g₀, hg₀, hold, ?_, ?_⟩
  · intro a
    have hIH : phi43IntegrationF (H a) = 0 :=
      phi43IntegrationF_polynomial_zero κ _
        (by rw [phi43PolynomialSectorF_subspace]; exact hH a)
    change phi43IntegrationF (g.val a - g'.val a) = 0 at hIH
    rw [map_sub, sub_eq_zero] at hIH
    have he : phi43IntegrationF (g.val a) - g.val (phi43IntegrationF a) =
        (phi43IntegrationF (g'.val a) - g'.val (phi43IntegrationF a)) - H (phi43IntegrationF a) := by
      rw [hIH]
      change _ = _ - (g.val (phi43IntegrationF a) - g'.val (phi43IntegrationF a))
      abel
    rw [he]
    exact (phi43PolynomialSubspaceF κ).sub_mem (hg'.2.choose_spec.2.2.1 a)
      (hH (phi43IntegrationF a))
  · intro a
    have hn : SymbolF.old .noise ∉ Set.range phi43PolyEmbF := by
      rw [phi43PolyEmbF_old_range, phi43QuadraticPolyEmb_range]
      simp
    have hh := (phi43PolynomialSubspaceF_mem κ (H a)).1 (hH a) _ hn
    change g.val a (.old .noise) - g'.val a (.old .noise) = 0 at hh
    rw [phi43ExtensionGroupF_noise_coord κ g' hg'] at hh
    exact sub_eq_zero.1 hh

theorem phi43ExtensionGroupF_mem_iff_planted (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (SymbolF → ℝ)) :
    g ∈ (phi43RegularityStructureF κ).group ↔
      IsGradedUnipotent (phi43DegreeF κ) g.val ∧
      ∃ g₀ ∈ (phi43RegularityStructure κ).group,
        (∀ a, g.val (phi43OldEmbF a) = phi43OldEmbF (g₀.val a)) ∧
        ∀ τ : Phi43PlantSource,
          g.val (Pi.single (.planted τ) 1) -
            phi43IntegrationF (g.val (Pi.single (.old τ.symbol) 1)) ∈
              (phi43PolynomialSectorF κ).subspace := by
  constructor
  · intro hg
    obtain ⟨g₀, hg₀, hold⟩ := phi43ExtensionGroupF_old_action κ g hg
    exact ⟨hg.1, g₀, hg₀, hold, phi43ExtensionGroupF_planted_mod_polynomial κ g hg⟩
  · rintro ⟨htri, g₀, hg₀, hold, hp⟩
    exact mem_of_planted κ g htri g₀ hg₀ hold hp

end RegularityStructures.Phi43

end
