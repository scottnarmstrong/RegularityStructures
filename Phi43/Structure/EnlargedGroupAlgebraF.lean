/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedIntegrationF
public import Phi43.Structure.QuadraticPolynomialSector
import Mathlib.Tactic.Abel

/-!
# Algebra of the finite integration-extension group

Hairer [Hai14, Definition 5.7, Theorem 5.14]. Polynomial vectors in the
extension are the literal images of the degree-at-most-two old polynomial
vectors. Compatibility with the old action transports their invariance.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The polynomial space in the finite planted completion. -/
def phi43PolynomialSubspaceF (κ : Kappa) : Submodule ℝ (SymbolF → ℝ) :=
  (phi43PolynomialSectorQuadratic κ).subspace.map phi43OldEmbF

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

theorem phi43OldCompatibleF_inv
    (g : LinearMap.GeneralLinearGroup ℝ (SymbolF → ℝ))
    (g₀ : LinearMap.GeneralLinearGroup ℝ (Symbol → ℝ))
    (h : ∀ a, g.val (phi43OldEmbF a) = phi43OldEmbF (g₀.val a)) :
    ∀ a, (g⁻¹).val (phi43OldEmbF a) = phi43OldEmbF ((g₀⁻¹).val a) := by
  intro a
  have he := congrArg (fun v => (g⁻¹).val v) (h ((g₀⁻¹).val a))
  simpa only [← Module.End.mul_apply, Units.inv_mul, Units.mul_inv,
    Module.End.one_apply] using he.symm

theorem phi43OldCompatibleF_polynomial (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (SymbolF → ℝ))
    (g₀ : LinearMap.GeneralLinearGroup ℝ (Symbol → ℝ))
    (hg₀ : g₀ ∈ (phi43RegularityStructure κ).group)
    (h : ∀ a, g.val (phi43OldEmbF a) = phi43OldEmbF (g₀.val a))
    {v : SymbolF → ℝ} (hv : v ∈ phi43PolynomialSubspaceF κ) :
    g.val v ∈ phi43PolynomialSubspaceF κ := by
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hv
  rw [h]
  apply Submodule.mem_map_of_mem
  exact (phi43PolynomialSectorQuadratic κ).invariant g₀ hg₀ a ha

end RegularityStructures.Phi43

end

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The integration-extension group: old action, triangularity, integration
commutation modulo polynomials, and unchanged raw-noise coordinate.
These are algebraic restrictions on linear automorphisms, not model bounds. -/
def phi43ExtensionGroupF (κ : Kappa) :
    Subgroup (LinearMap.GeneralLinearGroup ℝ (SymbolF → ℝ)) where
  carrier := {g | IsGradedUnipotent (phi43DegreeF κ) g ∧
    ∃ g₀ ∈ (phi43RegularityStructure κ).group,
      (∀ a, g.val (phi43OldEmbF a) = phi43OldEmbF (g₀.val a)) ∧
      (∀ a, phi43IntegrationF (g.val a) - g.val (phi43IntegrationF a) ∈
        phi43PolynomialSubspaceF κ) ∧
      ∀ a, g.val a (.old .noise) = a (.old .noise)}
  one_mem' := by
    refine ⟨isGradedUnipotent_id, 1, one_mem _, ?_, ?_, ?_⟩
    · intro a; rfl
    · intro a
      change phi43IntegrationF a - phi43IntegrationF a ∈ _
      rw [sub_self]
      exact Submodule.zero_mem _
    · intro a; rfl
  mul_mem' := by
    rintro g h ⟨hg, g₀, hg₀, he, hc, hn⟩ ⟨hh, h₀, hh₀, hf, hd, hm⟩
    refine ⟨hg.comp hh, g₀ * h₀, mul_mem hg₀ hh₀, ?_, ?_, ?_⟩
    · intro a
      change g.val (h.val (phi43OldEmbF a)) = phi43OldEmbF (g₀.val (h₀.val a))
      rw [hf, he]
    · intro a
      change phi43IntegrationF (g.val (h.val a)) - g.val (h.val (phi43IntegrationF a)) ∈ _
      have hp := phi43OldCompatibleF_polynomial κ g g₀ hg₀ he (hd a)
      have ht := (phi43PolynomialSubspaceF κ).add_mem (hc (h.val a)) hp
      simpa only [map_sub, sub_add_sub_cancel] using ht
    · intro a
      change g.val (h.val a) (.old .noise) = a (.old .noise)
      rw [hn, hm]
  inv_mem' := by
    rintro g ⟨hg, g₀, hg₀, he, hc, hn⟩
    have hi := phi43OldCompatibleF_inv g g₀ he
    refine ⟨hg.inv, g₀⁻¹, inv_mem hg₀, hi, ?_, ?_⟩
    · intro a
      have hp := phi43OldCompatibleF_polynomial κ g⁻¹ g₀⁻¹ (inv_mem hg₀) hi
        (hc ((g⁻¹).val a))
      have ht := (phi43PolynomialSubspaceF κ).neg_mem hp
      have ha : g.val ((g⁻¹).val a) = a := by
        change (g * g⁻¹).val a = a
        rw [mul_inv_cancel]
        rfl
      have hb : (g⁻¹).val (g.val (phi43IntegrationF ((g⁻¹).val a))) =
          phi43IntegrationF ((g⁻¹).val a) := by
        change (g⁻¹ * g).val _ = _
        rw [inv_mul_cancel]
        rfl
      rw [ha, map_sub, hb, neg_sub] at ht
      exact ht
    · intro a
      have ht := hn ((g⁻¹).val a)
      have ha : g.val ((g⁻¹).val a) = a := by
        change (g * g⁻¹).val a = a
        rw [mul_inv_cancel]
        rfl
      rw [ha] at ht
      exact ht.symm

end RegularityStructures.Phi43

end
