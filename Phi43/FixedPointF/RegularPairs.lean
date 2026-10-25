/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.FixedPointF.Degrees
public import Phi43.FixedPointF.GroupAction
public import Phi43.FixedPointF.ProductGeneric
import Mathlib.Tactic.Linarith

/-!
# Regular pairs and product closure for the sectors `V ⊂ W` of the enlarged structure

[Hai14, Definition 4.6, Section 9.4]. Writing `γ₀ = gamma κ = 1 + 3κ` and `α = -1/2 - κ`:

* `(V, V)` is `(γ₀ + α)`-regular and `(V, W)` is `(γ₀ + α + α)`-regular for `phi43ProductF κ`;
* `V ⋆ V ⊆ W`.

On the basis vectors, a pair below the threshold either has a retained product (hence
`Γ e_c = Γ e_τ ⋆ Γ e_σ` by `structureGroupMap_product`), or involves a planted symbol, whose degree
`≥ 3/2 - 5κ` is above the threshold (this is where `κ < 1/16` is used).
-/

public section

namespace RegularityStructures.Phi43

theorem phi43VBool_of_single_mem {j : SymbolF} (h : (Pi.single j 1 : SymbolF → ℝ) ∈ phi43SectorV) :
    phi43VBool j = true := by
  by_contra hj
  have := mem_phi43SectorV.1 h j (by simpa using hj)
  simp at this

theorem phi43WBool_of_single_mem {j : SymbolF} (h : (Pi.single j 1 : SymbolF → ℝ) ∈ phi43SectorW) :
    phi43WBool j = true := by
  by_contra hj
  have := mem_phi43SectorW.1 h j (by simpa using hj)
  simp at this

private theorem exists_product_VV (κ : Kappa) {τ σ : Symbol} (hτ : phi43VBool (.old τ) = true)
    (hσ : phi43VBool (.old σ) = true)
    (h : homogeneity κ τ + homogeneity κ σ < gamma κ + (-1 / 2 - κ.1)) :
    ∃ c, productSymbol τ σ = some c := by
  have h0 := κ.2.1
  have h1 := κ.2.2
  cases τ <;> cases σ <;> simp [phi43VBool, productSymbol, homogeneity, gamma] at hτ hσ h ⊢ <;>
    linarith

private theorem exists_product_VW (κ : Kappa) {τ σ : Symbol} (hτ : phi43VBool (.old τ) = true)
    (hσ : phi43WBool (.old σ) = true)
    (h : homogeneity κ τ + homogeneity κ σ <
      gamma κ + (-1 / 2 - κ.1) + (-1 / 2 - κ.1)) :
    ∃ c, productSymbol τ σ = some c := by
  have h0 := κ.2.1
  have h1 := κ.2.2
  cases τ <;> cases σ <;>
    simp [phi43VBool, phi43WBool, productSymbol, homogeneity, gamma] at hτ hσ h ⊢ <;> linarith

private theorem mul_old_basis (κ : Kappa) {τ σ c : Symbol} (h : productSymbol τ σ = some c) :
    (phi43ProductF κ).mul (Pi.single (.old τ) 1) (Pi.single (.old σ) 1) =
      Pi.single (.old c) 1 := by
  change phi43ProductLinearF _ _ = _
  rw [phi43ProductLinearF_basis]
  simp [phi43ProductBasisF, phi43ProductSymbolF, h]

/-- Multiplicativity of the enlarged group on the basis vectors with a retained old product. -/
theorem phi43ExtensionGroupF_mul_old_basis (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (SymbolF → ℝ))
    (hg : g ∈ (phi43RegularityStructureF κ).group) {τ σ c : Symbol}
    (h : productSymbol τ σ = some c) :
    g.val ((phi43ProductF κ).mul (Pi.single (.old τ) 1) (Pi.single (.old σ) 1)) =
      (phi43ProductF κ).mul (g.val (Pi.single (.old τ) 1)) (g.val (Pi.single (.old σ) 1)) := by
  obtain ⟨p, hp⟩ := phi43ExtensionGroupF_old_params κ g hg
  rw [mul_old_basis κ h, hp, hp, hp]
  change _ = phi43ProductLinearF _ _
  rw [phi43ProductLinearF_oldEmb, ← structureGroupMap_basis, structureGroupMap_product p τ σ c h,
    structureGroupMap_basis, structureGroupMap_basis]

theorem phi43ProductF_isRegularPair_VV (κ : Kappa) :
    (phi43ProductF κ).IsRegularPair phi43SectorV phi43SectorV (gamma κ + (-1 / 2 - κ.1)) := by
  have h0 := κ.2.1
  have h1 := κ.2.2
  refine RegularityStructure.GradedProduct.isRegularPair_of_single _ isCoordClosed_phi43SectorV
    isCoordClosed_phi43SectorV fun g hg τ σ hτ hσ hsum => ?_
  have hτ' := phi43VBool_of_single_mem hτ
  have hσ' := phi43VBool_of_single_mem hσ
  have hdτ := phi43DegreeF_V_ge κ hτ'
  have hdσ := phi43DegreeF_V_ge κ hσ'
  cases τ with
  | planted τ =>
    have := phi43DegreeF_planted_ge κ τ
    change phi43DegreeF κ (.planted τ) + phi43DegreeF κ σ < _ at hsum
    simp only [gamma] at hsum
    linarith
  | old τ =>
    cases σ with
    | planted σ =>
      have := phi43DegreeF_planted_ge κ σ
      change phi43DegreeF κ (.old τ) + phi43DegreeF κ (.planted σ) < _ at hsum
      simp only [gamma, phi43DegreeF] at hsum hdτ ⊢
      simp only [phi43DegreeF] at this hdτ
      linarith
    | old σ =>
      obtain ⟨c, hc⟩ := exists_product_VV κ hτ' hσ' hsum
      exact phi43ExtensionGroupF_mul_old_basis κ g hg hc

theorem phi43ProductF_isRegularPair_VW (κ : Kappa) :
    (phi43ProductF κ).IsRegularPair phi43SectorV phi43SectorW
      (gamma κ + (-1 / 2 - κ.1) + (-1 / 2 - κ.1)) := by
  have h0 := κ.2.1
  have h1 := κ.2.2
  refine RegularityStructure.GradedProduct.isRegularPair_of_single _ isCoordClosed_phi43SectorV
    isCoordClosed_phi43SectorW fun g hg τ σ hτ hσ hsum => ?_
  have hτ' := phi43VBool_of_single_mem hτ
  have hσ' := phi43WBool_of_single_mem hσ
  have hdτ := phi43DegreeF_V_ge κ hτ'
  have hdσ := phi43DegreeF_W_ge κ hσ'
  cases τ with
  | planted τ =>
    have := phi43DegreeF_planted_ge κ τ
    change phi43DegreeF κ (.planted τ) + phi43DegreeF κ σ < _ at hsum
    simp only [gamma] at hsum
    linarith
  | old τ =>
    cases σ with
    | planted σ =>
      have := phi43DegreeF_planted_ge κ σ
      change phi43DegreeF κ (.old τ) + phi43DegreeF κ (.planted σ) < _ at hsum
      simp only [gamma, phi43DegreeF] at hsum hdτ ⊢
      simp only [phi43DegreeF] at this hdτ
      linarith
    | old σ =>
      obtain ⟨c, hc⟩ := exists_product_VW κ hτ' hσ' hsum
      exact phi43ExtensionGroupF_mul_old_basis κ g hg hc

end RegularityStructures.Phi43

end
