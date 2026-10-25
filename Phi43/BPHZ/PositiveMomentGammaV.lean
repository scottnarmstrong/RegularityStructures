/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PositiveMomentGammaPi
public import Phi43.BPHZ.PositiveMomentGammaSq
public import Phi43.BPHZ.PositiveTreeFormulasBridge
public import Phi43.BPHZ.GammaMomentWick

/-!
# The random `Γ`-entries of a Phi43 model are the recentred convolutions `v₂`, `v₃`

For a model `Z` satisfying `IsRenormalisedCanonicalModel N κ noise C Z` of the periodic lift of a
smooth noise `ξ ω` with polynomially bounded derivatives, the `1`-entries of `Γ_{yx}` on
`I(Ψ²)` and `I(Ψ³)` are the kernel-increment pairings
`∫ (K(y - w) - K(x - w)) F(w) dw`, `F = Ψ² , Ψ³ - 3 C₁ Ψ` (`gammaMap_iPsiSq_one_eq_pairing`,
`gammaMap_iPsiCube_one_eq_pairing`), i.e. `v₂(x, y)` and `v₃(x, y)` of `GammaMomentWick` when
`C₁ C` is the Wick constant (`gammaMap_iPsiSq_one_eq_gammaWickSq`, `gammaMap_iPsiCube_one_eq_gammaWickCube`).
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type*} {N : ℕ} {κ : Kappa} {ξ : Ω → SpaceTime → ℝ} {ω : Ω}
  {noise : CanonicalNoise} {C : RenormalisationConstants}
  {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}

/-- The increment pairing of `g` at `(x, w)` minus that at `(y, w)` is that at `(x, y)`. -/
theorem hairerKernelIncrementPairing_sub_sub (N : ℕ) (x y w : SpaceTime) {g : SpaceTime → ℝ}
    (hg : Continuous g) :
    hairerKernelIncrementPairing N x w g - hairerKernelIncrementPairing N y w g =
      hairerKernelIncrementPairing N x y g := by
  rw [hairerKernelIncrementPairing_eq N x w hg, hairerKernelIncrementPairing_eq N y w hg,
    hairerKernelIncrementPairing_eq N x y hg]
  ring

/-- **The `1`-entry of `Γ_{yx} I(Ψ³)` is the pairing of the kernel increment with the Wick cube.** -/
theorem gammaMap_iPsiCube_one_eq_pairing (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (hn : ∀ z, noise.zeta z = ξ ω (spaceTimeProj z)) (hξ : IsSmoothOnSpaceTime (ξ ω))
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z) (y x : ParabolicSpace) :
    Z.gammaMap y x (Pi.single Symbol.iPsiCube (1 : ℝ) : Symbol → ℝ) Symbol.one =
      hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
        (hairerTreePsiCube N ξ (C₁ C) ω) := by
  have hΨ : Continuous (hairerPsiField N ξ ω) :=
    continuous_hairerKernelTorus_convolution N (IsSmoothOnSpaceTime.continuous hξ)
  have hc : Continuous (hairerTreePsiCube N ξ (C₁ C) ω) := by
    unfold hairerTreePsiCube; fun_prop
  refine gammaMap_one_entry_eq_of_extension_sub Cg q hg hZ Symbol.psiCube Symbol.iPsiCube
    (Or.inr rfl) (Or.inr ⟨rfl, rfl⟩) (fun y x => gammaMap_single_iPsiCube Z y x) y x _ ?_
  intro w
  rw [renormalisedExtensionPi_tensor_iPsiCube, renormalisedExtensionPi_tensor_iPsiCube,
    CanonicalData.hairerCanonicalData_renormalisedPi_basis_iPsiCube_eq_treeField C x hn hξ,
    CanonicalData.hairerCanonicalData_renormalisedPi_basis_iPsiCube_eq_treeField C y hn hξ]
  exact hairerKernelIncrementPairing_sub_sub N _ _ _ hc

/-- **The `1`-entry of `Γ_{yx} I(Ψ²)` is the pairing of the kernel increment with `Ψ²`.** -/
theorem gammaMap_iPsiSq_one_eq_pairing (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (hn : ∀ z, noise.zeta z = ξ ω (spaceTimeProj z)) (hξ : IsSmoothOnSpaceTime (ξ ω))
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z) (y x : ParabolicSpace) :
    Z.gammaMap y x (Pi.single Symbol.iPsiSq (1 : ℝ) : Symbol → ℝ) Symbol.one =
      hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
        (fun w => hairerPsiField N ξ ω w * hairerPsiField N ξ ω w) := by
  have hΨ : Continuous (hairerPsiField N ξ ω) :=
    continuous_hairerKernelTorus_convolution N (IsSmoothOnSpaceTime.continuous hξ)
  have hc : Continuous (fun w => hairerPsiField N ξ ω w * hairerPsiField N ξ ω w) := by
    fun_prop
  refine gammaMap_one_entry_eq_of_extension_sub Cg q hg hZ Symbol.psiSq Symbol.iPsiSq
    (Or.inl rfl) (Or.inl ⟨rfl, rfl⟩) (fun y x => gammaMap_single_iPsiSq Z y x) y x _ ?_
  intro w
  rw [renormalisedExtensionPi_tensor_iPsiSq, renormalisedExtensionPi_tensor_iPsiSq,
    CanonicalData.hairerCanonicalData_renormalisedPi_basis_iPsiSq_eq_treeField C x hn hξ,
    CanonicalData.hairerCanonicalData_renormalisedPi_basis_iPsiSq_eq_treeField C y hn hξ]
  exact hairerKernelIncrementPairing_sub_sub N _ _ _ hc

/-- With `C₁ C` the Wick constant, the `1`-entry of `Γ_{yx} I(Ψ³)` is `v₃(x, y)`. -/
theorem gammaMap_iPsiCube_one_eq_gammaWickCube {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
    (hC : C₁ C = hairerWickConstant N ρ ε) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (hn : ∀ z, noise.zeta z = ξ ω (spaceTimeProj z)) (hξ : IsSmoothOnSpaceTime (ξ ω))
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z) (y x : ParabolicSpace) :
    Z.gammaMap y x (Pi.single Symbol.iPsiCube (1 : ℝ) : Symbol → ℝ) Symbol.one =
      gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω := by
  rw [gammaMap_iPsiCube_one_eq_pairing Cg q hg hn hξ hZ y x, hC]
  rfl

/-- With `C₁ C` the Wick constant, the `1`-entry of `Γ_{yx} I(Ψ²)` is `v₂(x, y)`. -/
theorem gammaMap_iPsiSq_one_eq_gammaWickSq {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
    (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (hn : ∀ z, noise.zeta z = ξ ω (spaceTimeProj z)) (hξ : IsSmoothOnSpaceTime (ξ ω))
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z) (y x : ParabolicSpace) :
    Z.gammaMap y x (Pi.single Symbol.iPsiSq (1 : ℝ) : Symbol → ℝ) Symbol.one =
      gammaWickSq N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω := by
  have hΨ : Continuous (hairerPsiField N ξ ω) :=
    continuous_hairerKernelTorus_convolution N (IsSmoothOnSpaceTime.continuous hξ)
  have hc : Continuous (fun w => hairerPsiField N ξ ω w * hairerPsiField N ξ ω w) := by
    fun_prop
  rw [gammaMap_iPsiSq_one_eq_pairing Cg q hg hn hξ hZ y x]
  have h := hairerKernelIncrementPairing_sub_const_mul N (spaceTimeProj x) (spaceTimeProj y)
    hc (continuous_const (y := (1 : ℝ))) (hairerWickConstant N ρ ε)
  have h1 : hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y)
      (fun _ => (1 : ℝ)) = 0 := by
    unfold hairerKernelIncrementPairing
    simpa using integral_hairerI2Psi2Kernel N (spaceTimeProj x) (spaceTimeProj y)
  rw [h1, mul_zero, sub_zero] at h
  rw [← h]
  unfold gammaWickSq hairerKernelIncrementPairing hairerPsiWickSquare
  simp only [mul_one, sq]

end RegularityStructures.Phi43

end
