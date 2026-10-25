/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedExtensionJoint
public import Phi43.Structure.RenormalisedExtensionModel
public import Phi43.Structure.RenormalisedExtensionTensorH0
public import Phi43.Structure.CanonicalGlobalModelEnvelopes
public import Phi43.Structure.CanonicalDiagonal
public import Phi43Statements.Defs.IsRenormalisedCanonicalModel

/-!
# The function representatives of the renormalised canonical model below degree `κ`

The symbols of degree `< κ` are `F₋ ∪ {1}`.  `phi43BaseFunctions N κ noise C x τ` is the function
`Π^M_x τ` for `τ ∈ F₋`, the constant `1` for `τ = 1`, and `0` otherwise.  Lemmas:

* `homogeneity_lt_kappa_iff`: `deg τ < κ ↔ τ ∈ F₋ ∨ τ = 1`;
* `phi43BaseFunctions_continuous`: joint continuity in `(x, y)`;
* `phi43BaseFunctions_polyBounded`, `phi43BaseFunctions_diag_polyBounded`: polynomial growth in
  `y` and along the diagonal, from the noise growth premise.

Source: [Hai14, (8.34), Remark 3.15].
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open Classical in
/-- The function representatives of `Π_x τ` for `deg τ < κ`: `Π^M_x τ` on `F₋`, `1` on the unit,
`0` elsewhere. -/
def phi43BaseFunctions (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants) :
    ParabolicSpace → Symbol → ParabolicSpace → ℝ := fun x τ =>
  if τ ∈ fMinus then (hairerCanonicalData (κ := κ) N noise).renormalisedPi C x (basis τ)
  else if τ = .one then fun _ => 1 else 0

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

/-- The symbols of degree `< κ` are exactly `F₋` and the unit. -/
theorem homogeneity_lt_kappa_iff (κ : Kappa) (τ : Symbol) :
    homogeneity κ τ < κ.1 ↔ τ ∈ fMinus ∨ τ = .one := by
  have hk : 0 < κ.1 := κ.2.1
  have hk' : κ.1 < 1 / 16 := κ.2.2
  rw [mem_fMinus_iff_isFMinus]
  cases τ <;> simp only [homogeneity, isFMinus] <;> simp <;> linarith

theorem isHairerF0_of_mem_fMinus {τ : Symbol} (hτ : τ ∈ fMinus) : IsHairerF0 τ := by
  rw [mem_fMinus_iff_isFMinus] at hτ
  cases τ <;> simp_all [isFMinus, IsHairerF0]

theorem phi43BaseFunctions_of_mem_fMinus (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants) {τ : Symbol} (hτ : τ ∈ fMinus) (x : ParabolicSpace) :
    phi43BaseFunctions N κ noise C x τ =
      (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x (basis τ) := by
  rw [renormalisedExtensionPi_eq_tensor_on_H0 N κ noise C x τ (Or.inl (isHairerF0_of_mem_fMinus hτ))]
  simp [phi43BaseFunctions, hτ]

theorem phi43BaseFunctions_one (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants) (x : ParabolicSpace) :
    phi43BaseFunctions N κ noise C x .one = fun _ => 1 := by
  have : (Symbol.one) ∉ fMinus := by simp [mem_fMinus_iff_isFMinus, isFMinus]
  simp [phi43BaseFunctions, this]

theorem phi43BaseFunctions_other (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants) {τ : Symbol} (h1 : τ ∉ fMinus) (h2 : τ ≠ .one)
    (x : ParabolicSpace) : phi43BaseFunctions N κ noise C x τ = 0 := by
  simp [phi43BaseFunctions, h1, h2]

/-- Joint continuity of every base function. -/
theorem phi43BaseFunctions_continuous (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants) (τ : Symbol) :
    Continuous (fun p : ParabolicSpace × ParabolicSpace =>
      phi43BaseFunctions N κ noise C p.1 τ p.2) := by
  by_cases h1 : τ ∈ fMinus
  · simp_rw [phi43BaseFunctions_of_mem_fMinus N κ noise C h1]
    exact (renormalisedExtensionPi_joint_smooth N κ noise C τ).continuous
  · by_cases h2 : τ = .one
    · subst h2
      simp_rw [phi43BaseFunctions_one]
      exact continuous_const
    · simp_rw [phi43BaseFunctions_other N κ noise C h1 h2]
      exact continuous_const

/-- Polynomial growth in `y` of every base function. -/
theorem phi43BaseFunctions_polyBounded (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (hf : PolyBounded noise.zeta) (C : RenormalisationConstants) (x : ParabolicSpace)
    (τ : Symbol) : PolyBounded (phi43BaseFunctions N κ noise C x τ) := by
  by_cases h1 : τ ∈ fMinus
  · rw [phi43BaseFunctions_of_mem_fMinus N κ noise C h1]
    exact renormalisedExtensionPi_growth N noise hf C x _
  · by_cases h2 : τ = .one
    · subst h2
      rw [phi43BaseFunctions_one]
      exact ⟨measurable_const, 1, 0, fun u => by simp⟩
    · rw [phi43BaseFunctions_other N κ noise C h1 h2]
      exact ⟨measurable_const, 0, 0, fun u => by simp⟩

end RegularityStructures.Phi43

end
