/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Pinned.ModelAgreement
public import Phi43Statements.Defs.IsRenormalisedCanonicalModel
import Mathlib.Tactic

/-!
# `Π` is pinned on the negative symbols, the polynomials and the integrals

For two models `Z`, `Z'` satisfying `Statements.IsRenormalisedCanonicalModel N κ noise C`, the
regularisations `Q_t Π_x e_τ` (`t > 0`) agree for every `τ` in `F₋`, `τ = 1`, `τ = X_i`,
`τ ∈ {I(Ψ), I(Ψ²), I(Ψ³)}`: `F₋` is pinned by hypothesis, the polynomials by polynomial
compatibility, and `I(Ψ^k) = I e_{Ψ^k}` by the kernel-realising clause, whose germ only depends
on `Π e_{Ψ^k}` (`Model.regPi_integral_eq_of_realises`).
-/

@[expose] public section

namespace RegularityStructures.Phi43

/-- The symbols on which every model satisfying `IsRenormalisedCanonicalModel` has the same `Π`. -/
def IsPinnedSymbol (τ : Symbol) : Prop :=
  τ ∈ fMinus ∨ τ = .one ∨ (∃ i : Fin 3, τ = .x i) ∨ τ = .iPsi ∨ τ = .iPsiSq ∨ τ = .iPsiCube

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

open RegularityStructures

theorem one_mem_range_phi43PolyEmb : Symbol.one ∈ Set.range phi43PolyEmb :=
  ⟨⟨0, by simp [weight_parabolicWeight]⟩, by simp [phi43PolyEmb]⟩

theorem x_mem_range_phi43PolyEmb (i : Fin 3) : Symbol.x i ∈ Set.range phi43PolyEmb := by
  fin_cases i
  · exact ⟨⟨Finsupp.single (1 : Fin 4) 1, by simp [weight_parabolicWeight]⟩,
      phi43PolyEmb_eq_x0 rfl⟩
  · exact ⟨⟨Finsupp.single (2 : Fin 4) 1, by simp [weight_parabolicWeight]⟩,
      phi43PolyEmb_eq_x1 rfl⟩
  · exact ⟨⟨Finsupp.single (3 : Fin 4) 1, by simp [weight_parabolicWeight]⟩,
      phi43PolyEmb_eq_x2 rfl⟩

theorem single_mem_phi43PolynomialSector_subspace (κ : Kappa) {σ : Symbol}
    (hσ : σ ∈ Set.range phi43PolyEmb) :
    (Pi.single σ 1 : Symbol → ℝ) ∈ (phi43PolynomialSector κ).subspace := by
  intro i hi
  have : i ≠ σ := fun h => hi (h ▸ hσ)
  simp [this]

theorem phi43AbstractIntegration_single_psi :
    phi43AbstractIntegration (Pi.single .psi 1) = Pi.single .iPsi 1 := by
  funext i
  rw [phi43AbstractIntegration_apply_coord]
  cases i <;> simp

theorem phi43AbstractIntegration_single_psiSq :
    phi43AbstractIntegration (Pi.single .psiSq 1) = Pi.single .iPsiSq 1 := by
  funext i
  rw [phi43AbstractIntegration_apply_coord]
  cases i <;> simp

theorem phi43AbstractIntegration_single_psiCube :
    phi43AbstractIntegration (Pi.single .psiCube 1) = Pi.single .iPsiCube 1 := by
  funext i
  rw [phi43AbstractIntegration_apply_coord]
  cases i <;> simp

theorem single_mem_phi43IntegrationSector {σ : Symbol} (h : σ = .psi ∨ σ = .psiSq ∨ σ = .psiCube) :
    (Pi.single σ 1 : Symbol → ℝ) ∈ phi43IntegrationSector := by
  intro τ h1 h2 h3 h4
  rcases h with rfl | rfl | rfl <;> simp_all

end RegularityStructures.Phi43

end
