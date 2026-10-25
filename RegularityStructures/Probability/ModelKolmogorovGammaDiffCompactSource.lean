/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaDiffCompactRescale
import Mathlib.Tactic.Linarith

/-!
# Affine transport of Gamma-difference source hypotheses

The compact chart rescales the parabolic distance by `L`.  These lemmas make
the finite-sector degree envelope explicit, so a unit-box theorem can be
applied with a source constant multiplied by `L^a`.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {𝒯 : RegularityStructure ι}

theorem gammaDiffCompactSource_degree_envelope
    (κbar : ℝ) (i j : ι) :
    𝒯.deg i - 𝒯.deg j + κbar ≤
      1 + κbar + 2 * ∑ k : ι, |𝒯.deg k| := by
  have hi : 𝒯.deg i ≤ |𝒯.deg i| := le_abs_self _
  have hj : -𝒯.deg j ≤ |𝒯.deg j| := neg_le_abs _
  have hi' : |𝒯.deg i| ≤ ∑ k : ι, |𝒯.deg k| :=
    Finset.single_le_sum (f := fun k : ι => |𝒯.deg k|)
      (fun k _ => abs_nonneg _) (Finset.mem_univ i)
  have hj' : |𝒯.deg j| ≤ ∑ k : ι, |𝒯.deg k| :=
    Finset.single_le_sum (f := fun k : ι => |𝒯.deg k|)
      (fun k _ => abs_nonneg _) (Finset.mem_univ j)
  linarith

private theorem gammaDiffCompactSource_scaleDist_symm
    {L : ℝ} (hL : 0 < L) (x y : ParabolicSpace) :
    parabolicSemigroup.scaleDist
        ((hsParabolicBoxHomeomorph hL.ne').symm y)
        ((hsParabolicBoxHomeomorph hL.ne').symm x) =
      L * parabolicSemigroup.scaleDist y x := by
  change parabolicNorm
      ((hsParabolicBoxHomeomorph hL.ne').symm y -
        (hsParabolicBoxHomeomorph hL.ne').symm x) = _
  exact parabolicNorm_sub_hsParabolicBoxHomeomorph_symm hL y x

private theorem gammaDiffCompactSource_rpow_scale_le
    {L C d a A : ℝ} (hL : 1 ≤ L) (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hdeg : a ≤ A) :
    C * (L * d) ^ a ≤ C * L ^ A * d ^ a := by
  rw [Real.mul_rpow (by linarith) hd]
  have hpow : L ^ a ≤ L ^ A := Real.rpow_le_rpow_of_exponent_le hL hdeg
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hd a)) hC)

omit [MeasurableSpace Ω] in
theorem gammaDiffCompactSource_det
    (L C : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (D : Set (ι × ι)) (γ : ℝ) (M : Ω → Model 𝒯 parabolicSemigroup)
    (hdet : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ ω x y,
      |(M ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j))
    (A : ℝ) (hA : ∀ i j, 𝒯.deg i - 𝒯.deg j ≤ A)
    :
    ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ ω,
      ∀ x y : ParabolicSpace,
      |(gammaDiffCompactPullbackModel (M ω) L (by linarith)).gammaMap y x
          (Pi.single i 1) j| ≤
        (C * L ^ A) * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j) := by
  intro i j hij hi hj ω x y
  have h := hdet i j hij hi hj ω
    ((hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm x)
    ((hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm y)
  have hscale := gammaDiffCompactSource_scaleDist_symm
    (show 0 < L by linarith) x y
  change |(M ω).gammaMap
      ((hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm y)
      ((hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm x)
      (Pi.single i 1) j| ≤ _
  rw [hscale] at h
  calc
    _ ≤ C * (L * parabolicSemigroup.scaleDist y x) ^
        (𝒯.deg i - 𝒯.deg j) := h
    _ ≤ _ := gammaDiffCompactSource_rpow_scale_le hL hC
      (parabolicSemigroup.scaleDist_nonneg _ _)
      (hA i j)

omit [MeasurableSpace Ω] in
theorem gammaDiffCompactSource_diff
    (L C ε θ : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (D : Set (ι × ι)) (γ : ℝ)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup)
    (hDiff : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ ω x y,
      |(M₁ ω).gammaMap y x (Pi.single i 1) j -
          (M₂ ω).gammaMap y x (Pi.single i 1) j| ≤
        C * ε ^ θ * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j))
    (A : ℝ) (hA : ∀ i j, 𝒯.deg i - 𝒯.deg j ≤ A)
    :
    ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ ω,
      ∀ x y : ParabolicSpace,
      |(gammaDiffCompactPullbackModel (M₁ ω) L (by linarith)).gammaMap y x
          (Pi.single i 1) j -
        (gammaDiffCompactPullbackModel (M₂ ω) L (by linarith)).gammaMap y x
          (Pi.single i 1) j| ≤
        (C * L ^ A) * ε ^ θ * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j) := by
  intro i j hij hi hj ω x y
  have h := hDiff i j hij hi hj ω
    ((hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm x)
    ((hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm y)
  have hscale := gammaDiffCompactSource_scaleDist_symm
    (show 0 < L by linarith) x y
  change |(M₁ ω).gammaMap
      ((hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm y)
      ((hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm x)
      (Pi.single i 1) j -
      (M₂ ω).gammaMap
      ((hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm y)
      ((hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm x)
      (Pi.single i 1) j| ≤ _
  rw [hscale] at h
  calc
    _ ≤ C * ε ^ θ * (L * parabolicSemigroup.scaleDist y x) ^
        (𝒯.deg i - 𝒯.deg j) := h
    _ = ε ^ θ * (C * (L * parabolicSemigroup.scaleDist y x) ^
        (𝒯.deg i - 𝒯.deg j)) := by ring
    _ ≤ ε ^ θ * (C * L ^ A * parabolicSemigroup.scaleDist y x ^
        (𝒯.deg i - 𝒯.deg j)) := by
      exact mul_le_mul_of_nonneg_left
        (gammaDiffCompactSource_rpow_scale_le
          (L := L) (C := C)
          (d := parabolicSemigroup.scaleDist y x)
          (a := 𝒯.deg i - 𝒯.deg j) (A := A) hL hC
          (parabolicSemigroup.scaleDist_nonneg _ _) (hA i j))
        (Real.rpow_nonneg hε θ)
    _ = _ := by ring

theorem gammaDiffCompactSource_moment
    (L κbar C : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (D : Set (ι × ι)) (γ : ℝ) (q : ℕ)
    (M : Ω → Model 𝒯 parabolicSemigroup)
    (hMoment : ∀ i j, (i, j) ∉ D → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ x y,
      ∫⁻ ω, ‖(M ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κbar)) ^ q)
    (A : ℝ) (hA : ∀ i j,
      𝒯.deg i - 𝒯.deg j + κbar ≤ A)
    :
    ∀ i j, (i, j) ∉ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x y,
      ∫⁻ ω, ‖(gammaDiffCompactPullbackModel (M ω) L (by linarith)).gammaMap y x
          (Pi.single i 1) j‖ₑ ^ q ∂P ≤
        ENNReal.ofReal ((C * L ^ A) * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κbar)) ^ q := by
  intro i j hij hi hj x y
  have h := hMoment i j hij hi hj
    ((hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm x)
    ((hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm y)
  have hscale := gammaDiffCompactSource_scaleDist_symm
    (show 0 < L by linarith) x y
  change ∫⁻ ω, ‖(M ω).gammaMap
      ((hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm y)
      ((hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm x)
      (Pi.single i 1) j‖ₑ ^ q ∂P ≤ _
  rw [hscale] at h
  exact h.trans (ENNReal.pow_le_pow_left (ENNReal.ofReal_le_ofReal
    (gammaDiffCompactSource_rpow_scale_le
      (L := L) (C := C) (d := parabolicSemigroup.scaleDist y x)
      (a := 𝒯.deg i - 𝒯.deg j + κbar) (A := A) hL hC
      (parabolicSemigroup.scaleDist_nonneg _ _) (hA i j))))

theorem gammaDiffCompactSource_diffMoment
    (L κbar C ε θ : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (D : Set (ι × ι)) (γ : ℝ) (q : ℕ)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup)
    (hMoment : ∀ i j, (i, j) ∉ D → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ x y,
      ∫⁻ ω, ‖(M₁ ω).gammaMap y x (Pi.single i 1) j -
          (M₂ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (C * ε ^ θ * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κbar)) ^ q)
    (A : ℝ) (hA : ∀ i j,
      𝒯.deg i - 𝒯.deg j + κbar ≤ A)
    :
    ∀ i j, (i, j) ∉ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x y,
      ∫⁻ ω, ‖(gammaDiffCompactPullbackModel (M₁ ω) L (by linarith)).gammaMap y x
          (Pi.single i 1) j -
        (gammaDiffCompactPullbackModel (M₂ ω) L (by linarith)).gammaMap y x
          (Pi.single i 1) j‖ₑ ^ q ∂P ≤
        ENNReal.ofReal ((C * L ^ A) * ε ^ θ *
          parabolicSemigroup.scaleDist y x ^
            (𝒯.deg i - 𝒯.deg j + κbar)) ^ q := by
  intro i j hij hi hj x y
  have h := hMoment i j hij hi hj
    ((hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm x)
    ((hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm y)
  have hscale := gammaDiffCompactSource_scaleDist_symm
    (show 0 < L by linarith) x y
  change ∫⁻ ω, ‖(M₁ ω).gammaMap
      ((hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm y)
      ((hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm x)
      (Pi.single i 1) j -
      (M₂ ω).gammaMap
      ((hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm y)
      ((hsParabolicBoxHomeomorph (by linarith : L ≠ 0)).symm x)
      (Pi.single i 1) j‖ₑ ^ q ∂P ≤ _
  rw [hscale] at h
  have hs := gammaDiffCompactSource_rpow_scale_le
    (L := L) (C := C) (d := parabolicSemigroup.scaleDist y x)
    (a := 𝒯.deg i - 𝒯.deg j + κbar) (A := A) hL hC
    (parabolicSemigroup.scaleDist_nonneg _ _) (hA i j)
  have hs' : C * ε ^ θ *
      (L * parabolicSemigroup.scaleDist y x) ^
        (𝒯.deg i - 𝒯.deg j + κbar) ≤
      C * L ^ A * ε ^ θ * parabolicSemigroup.scaleDist y x ^
        (𝒯.deg i - 𝒯.deg j + κbar) := by
    calc
      _ = ε ^ θ * (C * (L * parabolicSemigroup.scaleDist y x) ^
          (𝒯.deg i - 𝒯.deg j + κbar)) := by ring
      _ ≤ ε ^ θ * (C * L ^ A * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κbar)) :=
        mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hε θ)
      _ = _ := by ring
  exact h.trans (ENNReal.pow_le_pow_left (ENNReal.ofReal_le_ofReal hs'))

end RegularityStructures

end
