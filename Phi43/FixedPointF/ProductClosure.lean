/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.FixedPointF.RegularPairs

/-!
# `V ⋆ V ⊆ W` for the enlarged product

[Hai14, Section 9.4]. Every retained product of two symbols of `V` is a symbol of `W`
(`Ψ ⋆ Ψ = Ψ²`, `Ψ ⋆ X_i = ΨX_i`, `Ψ ⋆ I(Ψ) = I(Ψ)Ψ`, `Ψ ⋆ I(Ψ²) = I(Ψ²)Ψ`, `Ψ ⋆ I(Ψ³) = I(Ψ³)Ψ`,
`I(Ψ³) ⋆ I(Ψ³) = I(Ψ³)²`, unit products, polynomial products).
-/

public section

namespace RegularityStructures.Phi43

private theorem wBool_of_product (τ σ c : Symbol) (hτ : phi43VBool (.old τ) = true)
    (hσ : phi43VBool (.old σ) = true) (h : productSymbol τ σ = some c) :
    phi43WBool (.old c) = true := by
  cases τ <;> cases σ <;> simp [phi43VBool, productSymbol] at hτ hσ h <;> subst h <;>
    simp [phi43WBool, phi43VBool]

private theorem wBool_of_productF (τ σ υ : SymbolF) (hτ : phi43VBool τ = true)
    (hσ : phi43VBool σ = true) (h : phi43ProductSymbolF τ σ = some υ) :
    phi43WBool υ = true := by
  cases τ with
  | old τ =>
    cases σ with
    | old σ =>
      simp only [phi43ProductSymbolF, Option.map_eq_some_iff] at h
      obtain ⟨c, hc, rfl⟩ := h
      exact wBool_of_product τ σ c hτ hσ hc
    | planted σ =>
      cases τ <;> simp only [phi43ProductSymbolF, Option.some.injEq, reduceCtorEq] at h
      subst h
      simp [phi43WBool, phi43VBool]
  | planted τ =>
    cases σ with
    | old σ =>
      cases σ <;> simp only [phi43ProductSymbolF, Option.some.injEq, reduceCtorEq] at h
      subst h
      simp [phi43WBool, phi43VBool]
    | planted σ => simp [phi43ProductSymbolF] at h

theorem phi43ProductF_mul_mem (κ : Kappa) :
    ∀ a ∈ phi43SectorV, ∀ b ∈ phi43SectorV, (phi43ProductF κ).mul a b ∈ phi43SectorW := by
  refine RegularityStructure.GradedProduct.mul_mem_of_single _ isCoordClosed_phi43SectorV
    fun τ σ hτ hσ => ?_
  have hτ' := phi43VBool_of_single_mem hτ
  have hσ' := phi43VBool_of_single_mem hσ
  change phi43ProductLinearF _ _ ∈ _
  rw [phi43ProductLinearF_basis]
  unfold phi43ProductBasisF
  cases h : phi43ProductSymbolF τ σ with
  | none => exact Submodule.zero_mem _
  | some υ => exact single_mem_phi43SectorW (wBool_of_productF τ σ υ hτ' hσ' h)

end RegularityStructures.Phi43

end
