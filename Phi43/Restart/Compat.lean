/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.FixedPointF.Degrees
public import Phi43.FixedPointF.Hypotheses
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.ModelNearChain

/-!
# Compatibility of an enlarged model with an old model

`EnlargedCompat κ M₁ M'`: the model `M'` of the
enlarged structure restricts to the model `M₁` of the old structure on the old symbols,
`Π'_x e_{old a} = Π_x e_a` and `Γ'_{xy} e_{old a} = e_{old} (Γ_{xy} a)`.  Below the planted symbols
(level `≤ 3/2 - 5κ`) the bounds of `M'` are therefore those of `M₁`.
-/

public section

namespace RegularityStructures.Phi43.Restart

/-- The compatibility (C) of an enlarged model with an old model. -/
structure EnlargedCompat (κ : Kappa) (M₁ : Model (phi43RegularityStructure κ) parabolicSemigroup)
    (M' : Model (phi43RegularityStructureF κ) parabolicSemigroup) : Prop where
  regPi_old : ∀ (x : ParabolicSpace) (a : Symbol → ℝ) (t : ℝ) (z : ParabolicSpace),
    M'.regPi x (phi43OldEmbF a) t z = M₁.regPi x a t z
  gammaMap_old : ∀ (x y : ParabolicSpace) (a : Symbol → ℝ),
    M'.gammaMap x y (phi43OldEmbF a) = phi43OldEmbF (M₁.gammaMap x y a)

variable {κ : Kappa} {M₁ : Model (phi43RegularityStructure κ) parabolicSemigroup}
  {M' : Model (phi43RegularityStructureF κ) parabolicSemigroup}

theorem EnlargedCompat.regPi_single (hC : EnlargedCompat κ M₁ M') (x : ParabolicSpace) (τ : Symbol)
    (t : ℝ) (z : ParabolicSpace) :
    M'.regPi x (Pi.single (.old τ) 1) t z = M₁.regPi x (Pi.single τ 1) t z := by
  rw [← phi43OldEmbF_single, hC.regPi_old]

theorem EnlargedCompat.gammaMap_single_old (hC : EnlargedCompat κ M₁ M') (x y : ParabolicSpace)
    (τ σ : Symbol) :
    M'.gammaMap x y (Pi.single (.old τ) 1) (.old σ) = M₁.gammaMap x y (Pi.single τ 1) σ := by
  rw [← phi43OldEmbF_single, hC.gammaMap_old]
  rfl

theorem EnlargedCompat.gammaMap_single_planted (hC : EnlargedCompat κ M₁ M') (x y : ParabolicSpace)
    (τ : Symbol) (p : Phi43PlantSource) :
    M'.gammaMap x y (Pi.single (.old τ) 1) (.planted p) = 0 := by
  rw [← phi43OldEmbF_single, hC.gammaMap_old]
  rfl

private theorem not_lt_planted {γ' : ℝ} (hγ : γ' ≤ 3 / 2 - 5 * κ.1) (p : Phi43PlantSource) :
    ¬ phi43DegreeF κ (.planted p) < γ' := fun h =>
  absurd (lt_of_lt_of_le h hγ) (not_lt.2 (phi43DegreeF_planted_ge κ p))

/-- Below the planted symbols the `Π`-bounds of `M'` are those of `M₁`. -/
theorem EnlargedCompat.piBoundOn (hC : EnlargedCompat κ M₁ M') {γ' C : ℝ}
    (hγ : γ' ≤ 3 / 2 - 5 * κ.1) {S : Set ParabolicSpace} (h : M₁.PiBoundOn γ' C S) :
    M'.PiBoundOn γ' C S := by
  intro j hj t ht x hx
  cases j with
  | planted p => exact absurd hj (not_lt_planted hγ p)
  | old τ =>
      rw [hC.regPi_single]
      exact h τ hj t ht x hx

/-- Below the planted symbols the near-pair `Γ`-bounds of `M'` are those of `M₁`. -/
theorem EnlargedCompat.gammaBoundNearOn (hC : EnlargedCompat κ M₁ M') {γ' C R : ℝ}
    (hγ : γ' ≤ 3 / 2 - 5 * κ.1) {S : Set ParabolicSpace} (h : M₁.GammaBoundNearOn γ' C R S) :
    M'.GammaBoundNearOn γ' C R S := by
  intro i j hi hji x hx y hy hxy
  cases i with
  | planted p => exact absurd hi (not_lt_planted hγ p)
  | old τ =>
      cases j with
      | planted p =>
          exact absurd (hji.trans hi) (not_lt_planted hγ p)
      | old σ =>
          rw [hC.gammaMap_single_old]
          exact h τ σ hi hji x hx y hy hxy

/-- Non-resonance: `deg j + 2` is not an integer for the non-polynomial symbols of degree `< κ`. -/
theorem homogeneity_add_two_ne_nat {τ : Symbol} (hτ : homogeneity κ τ < κ.1)
    (hn : τ ≠ .one) (m : ℕ) : (m : ℝ) ≠ homogeneity κ τ + 2 := by
  have hk : 0 < κ.1 := κ.2.1
  have hk' : κ.1 < 1 / 16 := κ.2.2
  intro h
  have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  cases τ <;> simp only [homogeneity] at hτ h hn <;>
    first
    | exact hn rfl
    | (exfalso; linarith)
    | skip
  all_goals
    first
    | (have h1 : (m : ℝ) < 2 := by linarith
       have h2 : (1 : ℝ) < m := by linarith
       have h3 : m < 2 := by exact_mod_cast h1
       have h4 : 1 < m := by exact_mod_cast h2
       omega)
    | (have h1 : (m : ℝ) < 1 := by linarith
       have h2 : (0 : ℝ) < m := by linarith
       have h3 : m < 1 := by exact_mod_cast h1
       have h4 : 0 < m := by exact_mod_cast h2
       omega)

end RegularityStructures.Phi43.Restart

end
