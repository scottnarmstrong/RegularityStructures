/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedExtensionTensorH0
public import Phi43.Structure.RenormalisedExtensionModel
public import RegularityStructures.Abstract.Model

/-!
# Prescribed negative-sector Pi of the actual corrected Model

This proves the negative-sector Pi clause of the canonical-model predicate
`Statements.IsRenormalisedCanonicalModel` from the proved function identities,
not by assuming compatibility data [Hai14, (8.34), Theorem 8.44].
-/

public noncomputable section

namespace RegularityStructures.Phi43

theorem canonicalRenormalisedModel_regPi_tensor_fMinus (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) (τ : Symbol) (hτ : τ ∈ fMinus)
    (x : ParabolicSpace) (t : ℝ) (ht : 0 < t) (z : ParabolicSpace) :
    (canonicalRenormalisedModel N κ noise Cg q hg C).regPi x (Pi.single τ 1) t z =
      parabolicSemigroup.apply t
        ((hairerCanonicalData (κ := κ) N noise).renormalisedPi C x (basis τ)) z := by
  have he : phi43CoordinateEquiv.symm (Pi.single τ 1) = basis τ := by
    apply phi43CoordinateEquiv.injective
    simp [phi43CoordinateEquiv_basis]
  rw [canonicalRenormalisedModel_regPi N κ noise Cg q hg C x _ ht, he]
  have hF : IsHairerF0 τ := by
    rw [mem_fMinus_iff_isFMinus] at hτ
    cases τ <;> simp_all [isFMinus, IsHairerF0]
  rw [renormalisedExtensionPi_eq_tensor_on_H0 N κ noise C x τ (Or.inl hF)]

end RegularityStructures.Phi43

end
