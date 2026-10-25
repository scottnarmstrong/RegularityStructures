/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Pinned.PinnedPi
import Mathlib.Tactic
public import RegularityStructures.Abstract.Model

/-!
# `Π` agreement of two renormalised canonical models

Main result `regPi_eq_of_isRenormalisedCanonicalModel`: two models `Z`, `Z'` with
`Statements.IsRenormalisedCanonicalModel N κ noise C` have the same `Q_t Π_x e_τ` (`t > 0`) for every
pinned symbol `τ` (`IsPinnedSymbol`): `F₋`, the polynomials `1`, `X_i`, and the integrals
`I(Ψ)`, `I(Ψ²)`, `I(Ψ³)`.
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {κ : Kappa} {noise : CanonicalNoise} {C : RenormalisationConstants}
  {Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup}

theorem psi_mem_fMinus : Symbol.psi ∈ fMinus := by simp [mem_fMinus_iff_isFMinus, isFMinus]

theorem psiSq_mem_fMinus : Symbol.psiSq ∈ fMinus := by simp [mem_fMinus_iff_isFMinus, isFMinus]

theorem psiCube_mem_fMinus : Symbol.psiCube ∈ fMinus := by
  simp [mem_fMinus_iff_isFMinus, isFMinus]

theorem regPi_eq_of_mem_fMinus (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Statements.IsRenormalisedCanonicalModel N κ noise C Z') {τ : Symbol} (hτ : τ ∈ fMinus)
    (x : ParabolicSpace) {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    Z.regPi x (Pi.single τ 1) t z = Z'.regPi x (Pi.single τ 1) t z := by
  rw [hZ.2.1 τ hτ x t ht z, hZ'.2.1 τ hτ x t ht z]

private theorem regPi_eq_integral (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Statements.IsRenormalisedCanonicalModel N κ noise C Z') {σ τ : Symbol}
    (hσ : σ ∈ fMinus) (hσV : σ = .psi ∨ σ = .psiSq ∨ σ = .psiCube)
    (hI : phi43AbstractIntegration (Pi.single σ 1) = Pi.single τ 1) (hdeg : homogeneity κ σ < gamma κ)
    (x : ParabolicSpace) {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    Z.regPi x (Pi.single τ 1) t z = Z'.regPi x (Pi.single τ 1) t z := by
  rw [← hI]
  exact Model.regPi_integral_eq_of_realises hZ.1.realises hZ'.1.realises
    (i := σ) hdeg (single_mem_phi43IntegrationSector hσV) x
    (fun t ht z => regPi_eq_of_mem_fMinus hZ hZ' hσ x ht z) ht z

/-- **`Π` is pinned.** Two renormalised canonical models have the same `Q_t Π_x e_τ` on every
pinned symbol. -/
theorem regPi_eq_of_isRenormalisedCanonicalModel
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Statements.IsRenormalisedCanonicalModel N κ noise C Z') {τ : Symbol}
    (hτ : IsPinnedSymbol τ) (x : ParabolicSpace) {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    Z.regPi x (Pi.single τ 1) t z = Z'.regPi x (Pi.single τ 1) t z := by
  have hk := kappa_pos κ
  have hk' := kappa_lt_kappa₀ κ
  rcases hτ with h | rfl | ⟨i, rfl⟩ | rfl | rfl | rfl
  · exact regPi_eq_of_mem_fMinus hZ hZ' h x ht z
  · exact Model.regPi_eq_of_mem_polynomialSector hZ.1.poly hZ'.1.poly x
      (single_mem_phi43PolynomialSector_subspace κ one_mem_range_phi43PolyEmb) t z
  · exact Model.regPi_eq_of_mem_polynomialSector hZ.1.poly hZ'.1.poly x
      (single_mem_phi43PolynomialSector_subspace κ (x_mem_range_phi43PolyEmb i)) t z
  · exact regPi_eq_integral hZ hZ' psi_mem_fMinus (Or.inl rfl)
      phi43AbstractIntegration_single_psi
      (by simp only [homogeneity, gamma]; linarith) x ht z
  · exact regPi_eq_integral hZ hZ' psiSq_mem_fMinus (Or.inr (Or.inl rfl))
      phi43AbstractIntegration_single_psiSq
      (by simp only [homogeneity, gamma]; linarith) x ht z
  · exact regPi_eq_integral hZ hZ' psiCube_mem_fMinus (Or.inr (Or.inr rfl))
      phi43AbstractIntegration_single_psiCube
      (by simp only [homogeneity, gamma]; linarith) x ht z

end RegularityStructures.Phi43

end
