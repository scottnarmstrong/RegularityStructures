/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Model

/-!
# Near-pair `Γ`-bounds

`GammaBoundNearOn γ C R S` is the `Γ`-bound of `Model.GammaBoundOn` restricted to pairs of points
of `S` at scaled distance at most `R`:

  `|(Γ_{yx} e_i)_j| ≤ C d(y, x)^{deg i − deg j}`,  `deg j < deg i < γ`,  `x, y ∈ S`,
  `d(y, x) ≤ R`.

Hairer's model norm only uses `R = 1` ([Hai14, (2.17)]).  The far-pair version does not follow from
the near one with a polynomial constant (see `ModelNearChain`).  `GammaDiffBoundNearOn` is the
corresponding bound for the difference of two models.

Source: [Hai14] = arXiv:1303.5113v4, Definition 2.17.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

/-- The radius of the near-pair `Γ`-hypotheses of the window chain. -/
def gammaNearRadius : ℝ := 4

theorem one_le_gammaNearRadius : 1 ≤ gammaNearRadius := by
  unfold gammaNearRadius
  norm_num

theorem le_gammaNearRadius_of_le_one {d : ℝ} (h : d ≤ 1) : d ≤ gammaNearRadius :=
  h.trans one_le_gammaNearRadius

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

/-- The bound `|(Γ_{yx} e_i)_j| ≤ C d(y, x)^{deg i − deg j}` for `deg j < deg i < γ`, `x, y ∈ S`
with `d(y, x) ≤ R` (near pairs only). -/
def GammaBoundNearOn (M : Model 𝒯 K) (γ C R : ℝ) (S : Set E) : Prop :=
  ∀ i j, 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x ∈ S, ∀ y ∈ S, K.scaleDist y x ≤ R →
    |M.gammaMap y x (Pi.single i 1) j| ≤ C * K.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)

/-- The bound `|((Γ¹_{yx} − Γ²_{yx}) e_i)_j| ≤ C d(y, x)^{deg i − deg j}` for near pairs only. -/
def GammaDiffBoundNearOn (M₁ M₂ : Model 𝒯 K) (γ C R : ℝ) (S : Set E) : Prop :=
  ∀ i j, 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x ∈ S, ∀ y ∈ S, K.scaleDist y x ≤ R →
    |M₁.gammaMap y x (Pi.single i 1) j - M₂.gammaMap y x (Pi.single i 1) j| ≤
      C * K.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)

variable {M M₁ M₂ : Model 𝒯 K} {γ C R : ℝ} {S : Set E}

theorem GammaDiffBoundOn.toNear (h : M₁.GammaDiffBoundOn M₂ γ C S) (R : ℝ) :
    M₁.GammaDiffBoundNearOn M₂ γ C R S :=
  fun i j hi hj x hx y hy _ => h i j hi hj x hx y hy

theorem GammaBoundNearOn.mono_const {C' : ℝ} (h : M.GammaBoundNearOn γ C R S) (hC : C ≤ C') :
    M.GammaBoundNearOn γ C' R S := fun i j hi hj x hx y hy hd =>
  (h i j hi hj x hx y hy hd).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _))

theorem GammaDiffBoundNearOn.mono_const {C' : ℝ} (h : M₁.GammaDiffBoundNearOn M₂ γ C R S)
    (hC : C ≤ C') : M₁.GammaDiffBoundNearOn M₂ γ C' R S := fun i j hi hj x hx y hy hd =>
  (h i j hi hj x hx y hy hd).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _))

theorem GammaBoundNearOn.mono_degree {γ' : ℝ} (h : M.GammaBoundNearOn γ' C R S) (hγ : γ ≤ γ') :
    M.GammaBoundNearOn γ C R S := fun i j hi hj x hx y hy hd =>
  h i j (lt_of_lt_of_le hi hγ) hj x hx y hy hd

theorem GammaDiffBoundNearOn.mono_degree {γ' : ℝ} (h : M₁.GammaDiffBoundNearOn M₂ γ' C R S)
    (hγ : γ ≤ γ') : M₁.GammaDiffBoundNearOn M₂ γ C R S := fun i j hi hj x hx y hy hd =>
  h i j (lt_of_lt_of_le hi hγ) hj x hx y hy hd

/-- The `Γ`-bound of the window chain: near pairs of radius `gammaNearRadius`. -/
def GammaNearOn (M : Model 𝒯 K) (γ C : ℝ) (S : Set E) : Prop :=
  M.GammaBoundNearOn γ C gammaNearRadius S

/-- The `Γ`-difference bound of the window chain: near pairs of radius `gammaNearRadius`. -/
def GammaDiffNearOn (M₁ M₂ : Model 𝒯 K) (γ C : ℝ) (S : Set E) : Prop :=
  M₁.GammaDiffBoundNearOn M₂ γ C gammaNearRadius S

variable (M) in
theorem GammaNearOn.mono {γ C C' : ℝ} {S : Set E} (h : M.GammaNearOn γ C S) (hC : C ≤ C') :
    M.GammaNearOn γ C' S :=
  GammaBoundNearOn.mono_const h hC

theorem GammaDiffNearOn.mono_const {γ C C' : ℝ} {S : Set E}
    (h : M₁.GammaDiffNearOn M₂ γ C S) (hC : C ≤ C') : M₁.GammaDiffNearOn M₂ γ C' S :=
  GammaDiffBoundNearOn.mono_const h hC

end Model

end RegularityStructures

end
