/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaSplit
import Mathlib.Data.Fintype.Card

/-!
# Pathwise two-deterministic-factor Gamma channels

The finite-sector Gamma induction separates the Chen products whose two
coordinates are in `DΓ`.  This file records the corresponding pathwise
estimates, including the two-model difference formula.  These channels spend
no `κbar` reserve; their endpoint refinement is summed geometrically using
the positive degree of the fine factor.

The algebra is the coordinate form of Hairer [Hai14, (2.17)] and the
two-model expansion used in [Hai14, Theorem 10.7], arXiv:1303.5113v4.
-/

@[expose] public noncomputable section

open Set
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {𝒯 : RegularityStructure ι}

def gammaSplitLeftBadTermDiff
    (M₁ M₂ : Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (x y z : ParabolicSpace) : ℝ :=
  ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
    ((M₁.gammaMap y x (Pi.single i 1) k -
        M₂.gammaMap y x (Pi.single i 1) k) *
      M₁.gammaMap z y (Pi.single k 1) j +
      M₂.gammaMap y x (Pi.single i 1) k *
        (M₁.gammaMap z y (Pi.single k 1) j -
          M₂.gammaMap z y (Pi.single k 1) j))

def gammaSplitRightBadTermDiff
    (M₁ M₂ : Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (x y z : ParabolicSpace) : ℝ :=
  ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
    ((M₁.gammaMap y z (Pi.single i 1) k -
        M₂.gammaMap y z (Pi.single i 1) k) *
      M₁.gammaMap x y (Pi.single k 1) j +
      M₂.gammaMap y z (Pi.single i 1) k *
        (M₁.gammaMap x y (Pi.single k 1) j -
          M₂.gammaMap x y (Pi.single k 1) j))

private theorem gamma_bad_mem
    (D : Set (ι × ι)) {i j k : ι}
    (hk : k ∈ gammaBadIntermediate 𝒯 D i j) :
    𝒯.deg j < 𝒯.deg k ∧ 𝒯.deg k < 𝒯.deg i ∧
      (i, k) ∈ D ∧ (k, j) ∈ D := by
  classical
  have hbad := Finset.mem_filter.mp hk
  have hinter := Finset.mem_filter.mp hbad.1
  exact ⟨hinter.2.1, hinter.2.2, hbad.2.1, hbad.2.2⟩

private theorem enorm_le_of_abs_le {a b : ℝ} (h : |a| ≤ b) :
    ‖a‖ₑ ≤ ENNReal.ofReal b := by
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal h

theorem gammaSplitLeftBadTermDiff_enorm_le
    (M₁ M₂ : Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ C δ : ℝ) (_hC : 0 ≤ C) (_hδ : 0 ≤ δ)
    (i j : ι) (x y z : ParabolicSpace)
    (hi : 𝒯.deg i < γ) (_hij : 𝒯.deg j < 𝒯.deg i)
    (hdet₁ : ∀ a b, (a, b) ∈ D → 𝒯.deg a < γ →
      𝒯.deg b < 𝒯.deg a → ∀ u v,
      |M₁.gammaMap v u (Pi.single a 1) b| ≤
        C * parabolicSemigroup.scaleDist v u ^ (𝒯.deg a - 𝒯.deg b))
    (hdet₂ : ∀ a b, (a, b) ∈ D → 𝒯.deg a < γ →
      𝒯.deg b < 𝒯.deg a → ∀ u v,
      |M₂.gammaMap v u (Pi.single a 1) b| ≤
        C * parabolicSemigroup.scaleDist v u ^ (𝒯.deg a - 𝒯.deg b))
    (hdiff : ∀ a b, (a, b) ∈ D → 𝒯.deg a < γ →
      𝒯.deg b < 𝒯.deg a → ∀ u v,
      |M₁.gammaMap v u (Pi.single a 1) b -
        M₂.gammaMap v u (Pi.single a 1) b| ≤
        δ * parabolicSemigroup.scaleDist v u ^ (𝒯.deg a - 𝒯.deg b)) :
    ‖gammaSplitLeftBadTermDiff M₁ M₂ D i j x y z‖ₑ ≤
      ∑ k ∈ gammaBadIntermediate 𝒯 D i j, (
        ENNReal.ofReal (δ * parabolicSemigroup.scaleDist y x ^
            (𝒯.deg i - 𝒯.deg k)) *
          ENNReal.ofReal (C * parabolicSemigroup.scaleDist z y ^
            (𝒯.deg k - 𝒯.deg j)) +
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
            (𝒯.deg i - 𝒯.deg k)) *
          ENNReal.ofReal (δ * parabolicSemigroup.scaleDist z y ^
            (𝒯.deg k - 𝒯.deg j))) := by
  unfold gammaSplitLeftBadTermDiff
  calc
    _ ≤ ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
        (‖(M₁.gammaMap y x (Pi.single i 1) k -
            M₂.gammaMap y x (Pi.single i 1) k) *
            M₁.gammaMap z y (Pi.single k 1) j‖ₑ +
          ‖M₂.gammaMap y x (Pi.single i 1) k *
            (M₁.gammaMap z y (Pi.single k 1) j -
              M₂.gammaMap z y (Pi.single k 1) j)‖ₑ) := by
      exact enorm_sum_le _ _ |>.trans (Finset.sum_le_sum fun k hk =>
        enorm_add_le _ _)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      have hbad := gamma_bad_mem D hk
      rw [enorm_mul, enorm_mul]
      exact add_le_add
        (mul_le_mul
          (by
            exact enorm_le_of_abs_le (hdiff i k hbad.2.2.1 hi hbad.2.1 x y))
          (by
            exact enorm_le_of_abs_le (hdet₁ k j hbad.2.2.2
              (lt_trans hbad.2.1 hi) hbad.1 y z))
          (by positivity) (by positivity))
        (mul_le_mul
          (by
            exact enorm_le_of_abs_le (hdet₂ i k hbad.2.2.1 hi hbad.2.1 x y))
          (by
            exact enorm_le_of_abs_le (hdiff k j hbad.2.2.2
              (lt_trans hbad.2.1 hi) hbad.1 y z))
          (by positivity) (by positivity))

theorem gammaSplitRightBadTermDiff_enorm_le
    (M₁ M₂ : Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ C δ : ℝ) (_hC : 0 ≤ C) (_hδ : 0 ≤ δ)
    (i j : ι) (x y z : ParabolicSpace)
    (hi : 𝒯.deg i < γ) (_hij : 𝒯.deg j < 𝒯.deg i)
    (hdet₁ : ∀ a b, (a, b) ∈ D → 𝒯.deg a < γ →
      𝒯.deg b < 𝒯.deg a → ∀ u v,
      |M₁.gammaMap v u (Pi.single a 1) b| ≤
        C * parabolicSemigroup.scaleDist v u ^ (𝒯.deg a - 𝒯.deg b))
    (hdet₂ : ∀ a b, (a, b) ∈ D → 𝒯.deg a < γ →
      𝒯.deg b < 𝒯.deg a → ∀ u v,
      |M₂.gammaMap v u (Pi.single a 1) b| ≤
        C * parabolicSemigroup.scaleDist v u ^ (𝒯.deg a - 𝒯.deg b))
    (hdiff : ∀ a b, (a, b) ∈ D → 𝒯.deg a < γ →
      𝒯.deg b < 𝒯.deg a → ∀ u v,
      |M₁.gammaMap v u (Pi.single a 1) b -
        M₂.gammaMap v u (Pi.single a 1) b| ≤
        δ * parabolicSemigroup.scaleDist v u ^ (𝒯.deg a - 𝒯.deg b)) :
    ‖gammaSplitRightBadTermDiff M₁ M₂ D i j x y z‖ₑ ≤
      ∑ k ∈ gammaBadIntermediate 𝒯 D i j, (
        ENNReal.ofReal (δ * parabolicSemigroup.scaleDist y z ^
            (𝒯.deg i - 𝒯.deg k)) *
          ENNReal.ofReal (C * parabolicSemigroup.scaleDist x y ^
            (𝒯.deg k - 𝒯.deg j)) +
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist y z ^
            (𝒯.deg i - 𝒯.deg k)) *
          ENNReal.ofReal (δ * parabolicSemigroup.scaleDist x y ^
            (𝒯.deg k - 𝒯.deg j))) := by
  unfold gammaSplitRightBadTermDiff
  calc
    _ ≤ ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
        (‖(M₁.gammaMap y z (Pi.single i 1) k -
            M₂.gammaMap y z (Pi.single i 1) k) *
            M₁.gammaMap x y (Pi.single k 1) j‖ₑ +
          ‖M₂.gammaMap y z (Pi.single i 1) k *
            (M₁.gammaMap x y (Pi.single k 1) j -
              M₂.gammaMap x y (Pi.single k 1) j)‖ₑ) := by
      exact enorm_sum_le _ _ |>.trans (Finset.sum_le_sum fun k hk =>
        enorm_add_le _ _)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      have hbad := gamma_bad_mem D hk
      rw [enorm_mul, enorm_mul]
      exact add_le_add
        (mul_le_mul
          (by
            exact enorm_le_of_abs_le (hdiff i k hbad.2.2.1 hi hbad.2.1 z y))
          (by
            exact enorm_le_of_abs_le (hdet₁ k j hbad.2.2.2
              (lt_trans hbad.2.1 hi) hbad.1 y x))
          (by positivity) (by positivity))
        (mul_le_mul
          (by
            exact enorm_le_of_abs_le (hdet₂ i k hbad.2.2.1 hi hbad.2.1 z y))
          (by
            exact enorm_le_of_abs_le (hdiff k j hbad.2.2.2
              (lt_trans hbad.2.1 hi) hbad.1 y x))
          (by positivity) (by positivity))

end RegularityStructures

end
