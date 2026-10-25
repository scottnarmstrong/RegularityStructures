/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaProductNet
public import Mathlib.Order.CompletePartialOrder

/-!
# Fixed-annulus two-base-point Gamma telescope

The mixed Chen estimates are applied on the annulus selected by the coarse
pair distance.  The annulus scale is therefore held fixed while the two
endpoints are refined.  This module supplies the deterministic telescope for
that arrangement; its stochastic source bounds are supplied separately.

This is the two-base-point part of Hairer [Hai14, Theorem 10.7] and
Hairer--Steele [HS23, Proposition B.3].
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The first-endpoint step restricted to the annulus at coarse scale `N`. -/
def gammaProductLeftStepSupAnnulus
    (S : Set ParabolicSpace) (F : S → S → Ω → ℝ)
    (N k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ a : gammaCell S (k + 1), ⨆ b : gammaCell S (k + 1),
    if parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
          hsParabolicCellRepresentative S (k + 1) b) ≤ 20 / (2 : ℝ) ^ N then
      ‖F (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a))
          (hsParabolicCellRepresentative S (k + 1) b) ω -
        F (hsParabolicCellRepresentative S (k + 1) a)
          (hsParabolicCellRepresentative S (k + 1) b) ω‖ₑ
    else 0

/- The parent representative is written through the existing representative
  map below; this local abbreviation keeps the two endpoint definitions
  visibly aligned. -/
def hsParabolicCellParentRepresentative (S : Set ParabolicSpace) (k : ℕ)
    (b : gammaCell S (k + 1)) : S :=
  hsParabolicCellRepresentative S k (hsParabolicCellParent S k b)

/-- The second-endpoint step restricted to the annulus at coarse scale `N`. -/
def gammaProductRightStepSupAnnulus
    (S : Set ParabolicSpace) (F : S → S → Ω → ℝ)
    (N k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ a : gammaCell S (k + 1), ⨆ b : gammaCell S (k + 1),
    if parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
          hsParabolicCellRepresentative S (k + 1) b) ≤ 20 / (2 : ℝ) ^ N then
      ‖F (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a))
          (hsParabolicCellParentRepresentative S k b) ω -
        F (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a))
          (hsParabolicCellRepresentative S (k + 1) b) ω‖ₑ
    else 0

private theorem gammaProductAnnulus_cross_distance_le
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    {N k : ℕ} (hNk : N ≤ k) (x y : S)
    (hxy : parabolicNorm ((x : ParabolicSpace) - y) ≤ 1 / (2 : ℝ) ^ N) :
    parabolicNorm
        (hsParabolicCellApprox S k x -
          hsParabolicCellApprox S (k + 1) y) ≤ 20 / (2 : ℝ) ^ N := by
  have hpair := gammaProductCellApprox_distance_le S hbox k x y
  have hyerr := hsParabolicCellApprox_error_le S hbox k y
  have hyerr' := hsParabolicCellApprox_error_le S hbox (k + 1) y
  have hscale (c : ℝ) (hc : 0 ≤ c) : c / (2 : ℝ) ^ k ≤ c / (2 : ℝ) ^ N := by
    exact div_le_div_of_nonneg_left hc
      (by positivity) (pow_le_pow_right₀ (by norm_num) hNk)
  have hpair' : parabolicNorm
      (hsParabolicCellApprox S k x - hsParabolicCellApprox S k y) ≤
        9 / (2 : ℝ) ^ N := by
    calc
      _ ≤ parabolicNorm ((x : ParabolicSpace) - y) + 8 / (2 : ℝ) ^ k := hpair
      _ ≤ 1 / (2 : ℝ) ^ N + 8 / (2 : ℝ) ^ N := by
        exact add_le_add hxy (hscale 8 (by norm_num))
      _ = 9 / (2 : ℝ) ^ N := by ring
  have hbetween : parabolicNorm
      (hsParabolicCellApprox S k y - hsParabolicCellApprox S (k + 1) y) ≤
        6 / (2 : ℝ) ^ N := by
    calc
      _ = parabolicNorm
          ((hsParabolicCellApprox S k y - (y : ParabolicSpace)) +
            ((y : ParabolicSpace) - hsParabolicCellApprox S (k + 1) y)) := by
          congr 1
          abel
      _ ≤ parabolicNorm
          (hsParabolicCellApprox S k y - (y : ParabolicSpace)) +
          parabolicNorm ((y : ParabolicSpace) -
            hsParabolicCellApprox S (k + 1) y) := by
        exact parabolicNorm_add_le _ _
      _ ≤ 4 / (2 : ℝ) ^ k + 4 / (2 : ℝ) ^ (k + 1) := by
        exact add_le_add (hyerr) (by
          rw [parabolicNorm_sub_comm]
          exact hyerr')
      _ ≤ 6 / (2 : ℝ) ^ N := by
        calc
          _ ≤ 4 / (2 : ℝ) ^ N + 2 / (2 : ℝ) ^ N := by
            exact add_le_add (hscale 4 (by norm_num)) (by
              calc
                4 / (2 : ℝ) ^ (k + 1) = 2 / (2 : ℝ) ^ k := by
                  rw [pow_succ]
                  ring
                _ ≤ 2 / (2 : ℝ) ^ N := hscale 2 (by norm_num))
          _ = 6 / (2 : ℝ) ^ N := by ring
      _ = _ := by ring
  calc
    _ = parabolicNorm
        ((hsParabolicCellApprox S k x - hsParabolicCellApprox S k y) +
          (hsParabolicCellApprox S k y -
            hsParabolicCellApprox S (k + 1) y)) := by
      congr 1
      abel
    _ ≤ parabolicNorm (hsParabolicCellApprox S k x -
          hsParabolicCellApprox S k y) +
        parabolicNorm (hsParabolicCellApprox S k y -
          hsParabolicCellApprox S (k + 1) y) := parabolicNorm_add_le _ _
    _ ≤ 15 / (2 : ℝ) ^ N := by
      calc
        _ ≤ 9 / (2 : ℝ) ^ N + 6 / (2 : ℝ) ^ N :=
          add_le_add hpair' hbetween
        _ = 15 / (2 : ℝ) ^ N := by ring
    _ ≤ 20 / (2 : ℝ) ^ N := by gcongr; norm_num

omit [MeasurableSpace Ω] in
theorem gammaProductCellApprox_step_le_of_annulus
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (F : S → S → Ω → ℝ) {N k : ℕ} (hNk : N ≤ k)
    (x y : S) (ω : Ω)
    (hxy : parabolicNorm ((x : ParabolicSpace) - y) ≤ 1 / (2 : ℝ) ^ N) :
    ‖F (hsParabolicCellApprox S k x) (hsParabolicCellApprox S k y) ω -
        F (hsParabolicCellApprox S (k + 1) x)
          (hsParabolicCellApprox S (k + 1) y) ω‖ₑ ≤
      gammaProductLeftStepSupAnnulus S F N k ω +
        gammaProductRightStepSupAnnulus S F N k ω := by
  have hx := hsParabolicCellParent_at S hbox k x
  have hy := hsParabolicCellParent_at S hbox k y
  have hcross := gammaProductAnnulus_cross_distance_le S hbox hNk x y hxy
  let xn : S := hsParabolicCellApprox S k x
  let yn : S := hsParabolicCellApprox S k y
  let xnext : S := hsParabolicCellApprox S (k + 1) x
  let ynext : S := hsParabolicCellApprox S (k + 1) y
  have hx' : hsParabolicCellRepresentative S k
      (hsParabolicCellParent S k
        ⟨hsParabolicCellIndex (k + 1) x, x, rfl⟩) = xn := by
    simpa [xn, hsParabolicCellApprox] using congrArg
      (fun i : gammaCell S k => hsParabolicCellRepresentative S k i) hx
  have hy' : hsParabolicCellRepresentative S k
      (hsParabolicCellParent S k
        ⟨hsParabolicCellIndex (k + 1) y, y, rfl⟩) = yn := by
    simpa [yn, hsParabolicCellApprox] using congrArg
      (fun i : gammaCell S k => hsParabolicCellRepresentative S k i) hy
  have hleft : ‖F xn ynext ω - F xnext ynext ω‖ₑ ≤
      gammaProductLeftStepSupAnnulus S F N k ω := by
    let i : gammaCell S (k + 1) :=
      ⟨hsParabolicCellIndex (k + 1) x, x, rfl⟩
    let j : gammaCell S (k + 1) :=
      ⟨hsParabolicCellIndex (k + 1) y, y, rfl⟩
    have hi : hsParabolicCellRepresentative S (k + 1) i = xnext := rfl
    have hj : hsParabolicCellRepresentative S (k + 1) j = ynext := rfl
    have hparent : hsParabolicCellRepresentative S k
        (hsParabolicCellParent S k i) = xn := hx'
    have hcross' : parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k i) -
          hsParabolicCellRepresentative S (k + 1) j) ≤ 20 / (2 : ℝ) ^ N := by
      calc
        _ = parabolicNorm (xn - ynext) := by rw [hparent, hj]
        _ ≤ 20 / (2 : ℝ) ^ N := by simpa [xn, ynext] using hcross
    rw [gammaProductLeftStepSupAnnulus]
    rw [← hi, ← hj, ← hparent]
    apply le_iSup_of_le i
    apply le_iSup_of_le j
    simp only [ite_eq_left hcross']
    exact le_rfl
  have hright : ‖F xn yn ω - F xn ynext ω‖ₑ ≤
      gammaProductRightStepSupAnnulus S F N k ω := by
    let i : gammaCell S (k + 1) :=
      ⟨hsParabolicCellIndex (k + 1) x, x, rfl⟩
    let j : gammaCell S (k + 1) :=
      ⟨hsParabolicCellIndex (k + 1) y, y, rfl⟩
    have hi : hsParabolicCellRepresentative S (k + 1) i = xnext := rfl
    have hj : hsParabolicCellRepresentative S (k + 1) j = ynext := rfl
    have hparentx : hsParabolicCellRepresentative S k
        (hsParabolicCellParent S k i) = xn := hx'
    have hparenty : hsParabolicCellRepresentative S k
        (hsParabolicCellParent S k j) = yn := hy'
    have hcross' : parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k i) -
          hsParabolicCellRepresentative S (k + 1) j) ≤ 20 / (2 : ℝ) ^ N := by
      calc
        _ = parabolicNorm (xn - ynext) := by rw [hparentx, hj]
        _ ≤ 20 / (2 : ℝ) ^ N := by simpa [xn, ynext] using hcross
    rw [gammaProductRightStepSupAnnulus]
    rw [← hj, ← hparentx, ← hparenty]
    apply le_iSup_of_le i
    apply le_iSup_of_le j
    simp only [ite_eq_left hcross', hsParabolicCellParentRepresentative]
    exact le_rfl
  calc
    _ ≤ ‖F xn yn ω - F xn ynext ω‖ₑ +
        ‖F xn ynext ω - F xnext ynext ω‖ₑ := by
      rw [show F xn yn ω - F xnext ynext ω =
          (F xn yn ω - F xn ynext ω) +
            (F xn ynext ω - F xnext ynext ω) by ring]
      exact enorm_add_le _ _
    _ ≤ _ := add_le_add hright hleft
    _ = _ := by rw [add_comm]

end RegularityStructures

end
