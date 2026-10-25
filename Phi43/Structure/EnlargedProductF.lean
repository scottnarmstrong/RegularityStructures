/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedAbstractF
public import RegularityStructures.Abstract.ProductDefs
import Mathlib.Tactic.Ring

/-!
# Retained product on the finite planted completion

Hairer [Hai14, Definitions 4.1 and 4.6, Section 9.4]. Old products retain
the original table. Multiplication by the unit retains each new plant;
other products involving a new plant are outside this finite product
table. This file proves grading, not the regular-pair hypotheses.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- Literal retained product table, with a unit on the new plants as well. -/
def phi43ProductSymbolF : SymbolF → SymbolF → Option SymbolF
  | .old τ, .old σ => (productSymbol τ σ).map SymbolF.old
  | .old .one, .planted τ => some (.planted τ)
  | .planted τ, .old .one => some (.planted τ)
  | _, _ => none

/-- Basis product in the enlarged coordinate space. -/
def phi43ProductBasisF (τ σ : SymbolF) : SymbolF → ℝ :=
  match phi43ProductSymbolF τ σ with
  | some υ => Pi.single υ 1
  | none => 0

/-- Bilinear extension of the retained basis table. -/
def phi43ProductLinearF : (SymbolF → ℝ) →ₗ[ℝ] (SymbolF → ℝ) →ₗ[ℝ] (SymbolF → ℝ) where
  toFun a :=
    { toFun := fun b => ∑ τ : SymbolF, ∑ σ : SymbolF, (a τ * b σ) • phi43ProductBasisF τ σ
      map_add' := by
        intro b c
        simp only [Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c b
        funext υ
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          Finset.sum_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro τ _
        apply Finset.sum_congr rfl
        intro σ _
        ring }
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro c
    funext υ
    simp only [LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib, Finset.sum_apply]
  map_smul' := by
    intro c a
    apply LinearMap.ext
    intro b
    funext υ
    simp only [LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.sum_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ _
    apply Finset.sum_congr rfl
    intro σ _
    ring

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

theorem phi43ProductSymbolF_degree (κ : Kappa) {τ σ υ : SymbolF}
    (h : phi43ProductSymbolF τ σ = some υ) :
    phi43DegreeF κ υ = phi43DegreeF κ τ + phi43DegreeF κ σ := by
  cases τ with
  | old τ =>
    cases σ with
    | old σ =>
      simp only [phi43ProductSymbolF, Option.map_eq_some_iff] at h
      obtain ⟨υ', hp, rfl⟩ := h
      exact homogeneity_product κ hp
    | planted σ =>
      cases τ <;> simp only [phi43ProductSymbolF, Option.some.injEq, reduceCtorEq] at h
      subst υ
      simp [phi43DegreeF, homogeneity]
  | planted τ =>
    cases σ with
    | old σ =>
      cases σ <;> simp only [phi43ProductSymbolF, Option.some.injEq, reduceCtorEq] at h
      subst υ
      simp [phi43DegreeF, homogeneity]
    | planted σ => simp [phi43ProductSymbolF] at h

theorem phi43ProductBasisF_homogeneous (κ : Kappa) (τ σ : SymbolF) :
    phi43ProductBasisF τ σ ∈ RegularityStructures.homogeneousSubspace
      (phi43DegreeF κ) (phi43DegreeF κ τ + phi43DegreeF κ σ) := by
  unfold phi43ProductBasisF
  cases h : phi43ProductSymbolF τ σ with
  | none => exact Submodule.zero_mem _
  | some υ =>
    rw [← phi43ProductSymbolF_degree κ h]
    exact single_mem_homogeneousSubspace υ 1

end RegularityStructures.Phi43

end

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The graded retained product for the finite planted structure. -/
def phi43ProductF (κ : Kappa) : (phi43RegularityStructureF κ).GradedProduct where
  mul := phi43ProductLinearF
  mul_mem_homogeneousSubspace := by
    intro α β a b ha hb
    change (∑ τ : SymbolF, ∑ σ : SymbolF, (a τ * b σ) • phi43ProductBasisF τ σ) ∈
      RegularityStructures.homogeneousSubspace (phi43DegreeF κ) (α + β)
    apply Submodule.sum_mem
    intro τ _
    apply Submodule.sum_mem
    intro σ _
    by_cases hτ : phi43DegreeF κ τ = α
    · by_cases hσ : phi43DegreeF κ σ = β
      · subst α β
        exact Submodule.smul_mem _ _ (phi43ProductBasisF_homogeneous κ τ σ)
      · rw [hb σ hσ, mul_zero, zero_smul]
        exact Submodule.zero_mem _
    · rw [ha τ hτ, zero_mul, zero_smul]
      exact Submodule.zero_mem _

end RegularityStructures.Phi43

end
