/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaSplitCompletion
public import RegularityStructures.Probability.ModelKolmogorovGammaNormConversion
public import RegularityStructures.Probability.ModelKolmogorovGlobalSourceMoments
public import RegularityStructures.Statements.Defs.IsContinuousRandomModelWithFieldsOn
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.Linarith
public import Mathlib.Order.CompletePartialOrder

/-!
# The single-model finite-sector Gamma induction

This module splits the Chen telescope as follows. A product with two `DΓ` factors is estimated
pathwise and summed in the fine endpoint scale; all other products retain the source moment reserve.
The relative fine-scale normalization is essential for the pathwise channel.

The statement is the single-model part of the Kolmogorov criterion for models. The moment order is
selected before the upper bound `Cbar`.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒯 : RegularityStructure ι}

private theorem gammaSplit_left_annulus_geometry
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (N k : ℕ) (hNk : N ≤ k) (a b : gammaCell S (k + 1))
    (hnear : parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
          hsParabolicCellRepresentative S (k + 1) b) ≤
        20 / (2 : ℝ) ^ N) :
    parabolicNorm
        (hsParabolicCellRepresentative S (k + 1) a -
          hsParabolicCellRepresentative S (k + 1) b) ≤
        24 / (2 : ℝ) ^ N ∧
      parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
          hsParabolicCellRepresentative S (k + 1) a) ≤
        4 / (2 : ℝ) ^ k := by
  have hparent := hsParabolicCellParent_radius S hbox k a
  have hparent' : parabolicNorm
      (hsParabolicCellRepresentative S (k + 1) a -
        hsParabolicCellRepresentative S k (hsParabolicCellParent S k a)) ≤
      4 / (2 : ℝ) ^ k := by
    rw [parabolicNorm_sub_comm]
    exact hparent
  constructor
  · calc
      _ = parabolicNorm
          ((hsParabolicCellRepresentative S (k + 1) a -
              hsParabolicCellRepresentative S k
                (hsParabolicCellParent S k a)) +
            (hsParabolicCellRepresentative S k
                (hsParabolicCellParent S k a) -
              hsParabolicCellRepresentative S (k + 1) b)) := by
            congr 1
            abel
      _ ≤ 4 / (2 : ℝ) ^ k + 20 / (2 : ℝ) ^ N :=
        (parabolicNorm_add_le _ _).trans (add_le_add hparent' hnear)
      _ ≤ 24 / (2 : ℝ) ^ N := by
        have hscale : 4 / (2 : ℝ) ^ k ≤ 4 / (2 : ℝ) ^ N := by
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
            (pow_le_pow_right₀ (by norm_num) hNk)
        calc
          4 / (2 : ℝ) ^ k + 20 / (2 : ℝ) ^ N ≤
              4 / (2 : ℝ) ^ N + 20 / (2 : ℝ) ^ N :=
            by simpa [add_comm] using
              (add_le_add_right hscale (20 / (2 : ℝ) ^ N))
          _ = 24 / (2 : ℝ) ^ N := by ring_nf
  · exact hparent

private theorem gammaSplit_right_annulus_geometry
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (N k : ℕ) (hNk : N ≤ k) (a b : gammaCell S (k + 1))
    (hnear : parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
          hsParabolicCellRepresentative S (k + 1) b) ≤
        20 / (2 : ℝ) ^ N) :
    parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
          hsParabolicCellRepresentative S k (hsParabolicCellParent S k b)) ≤
        24 / (2 : ℝ) ^ N ∧
      parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k b) -
          hsParabolicCellRepresentative S (k + 1) b) ≤
        4 / (2 : ℝ) ^ k := by
  have hparent := hsParabolicCellParent_radius S hbox k b
  have hparent' : parabolicNorm
      (hsParabolicCellRepresentative S (k + 1) b -
        hsParabolicCellRepresentative S k (hsParabolicCellParent S k b)) ≤
      4 / (2 : ℝ) ^ k := by
    rw [parabolicNorm_sub_comm]
    exact hparent
  constructor
  · calc
      _ = parabolicNorm
          ((hsParabolicCellRepresentative S k
              (hsParabolicCellParent S k a) -
            hsParabolicCellRepresentative S (k + 1) b) +
            (hsParabolicCellRepresentative S (k + 1) b -
              hsParabolicCellRepresentative S k
                (hsParabolicCellParent S k b))) := by
            congr 1
            abel
      _ ≤ 20 / (2 : ℝ) ^ N + 4 / (2 : ℝ) ^ k :=
        (parabolicNorm_add_le _ _).trans (add_le_add hnear hparent')
      _ ≤ 24 / (2 : ℝ) ^ N := by
        have hscale : 4 / (2 : ℝ) ^ k ≤ 4 / (2 : ℝ) ^ N := by
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
            (pow_le_pow_right₀ (by norm_num) hNk)
        calc
          20 / (2 : ℝ) ^ N + 4 / (2 : ℝ) ^ k ≤
              20 / (2 : ℝ) ^ N + 4 / (2 : ℝ) ^ N :=
            by simpa [add_comm] using
              (add_le_add_left hscale (20 / (2 : ℝ) ^ N))
          _ = 24 / (2 : ℝ) ^ N := by ring_nf
  · exact hparent

omit [MeasurableSpace Ω] in
private theorem gammaSplit_leftStepSupAnnulus_le_aux
    (S : Set ParabolicSpace)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (N k : ℕ) (ω : Ω)
    (hji : 𝒯.deg j < 𝒯.deg i) :
    gammaProductLeftStepSupAnnulus S
        (fun x y ω => (M ω).gammaMap x y (Pi.single i 1) j) N k ω ≤
      gammaSplitLeftGoodStepSupAnnulus S M D i j N k ω +
        gammaSplitLeftBadStepSupAnnulus S M D i j N k ω := by
  unfold gammaProductLeftStepSupAnnulus
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  by_cases hnear : parabolicNorm
      (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
        hsParabolicCellRepresentative S (k + 1) b) ≤ 20 / (2 : ℝ) ^ N
  · simp only [ite_eq_left hnear]
    have hsplit := gammaSplitLeftTerm_enorm_le (M ω) D i j
      (hsParabolicCellRepresentative S (k + 1) b)
      (hsParabolicCellRepresentative S (k + 1) a)
      (hsParabolicCellRepresentative S k
        (hsParabolicCellParent S k a)) hji
    calc
      _ ≤ ‖gammaSplitLeftGoodTerm (M ω) D i j
          (hsParabolicCellRepresentative S (k + 1) b)
          (hsParabolicCellRepresentative S (k + 1) a)
          (hsParabolicCellRepresentative S k
            (hsParabolicCellParent S k a))‖ₑ +
          ‖gammaSplitLeftBadTerm (M ω) D i j
          (hsParabolicCellRepresentative S (k + 1) b)
          (hsParabolicCellRepresentative S (k + 1) a)
          (hsParabolicCellRepresentative S k
            (hsParabolicCellParent S k a))‖ₑ := hsplit
      _ ≤ _ := add_le_add
        (le_iSup_of_le a (le_iSup_of_le b (by simp [hnear])))
        (le_iSup_of_le a (le_iSup_of_le b (by simp [hnear])))
  · simp only [ite_eq_right hnear]
    exact bot_le

omit [MeasurableSpace Ω] in
private theorem gammaSplit_rightStepSupAnnulus_le_aux
    (S : Set ParabolicSpace)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (N k : ℕ) (ω : Ω)
    (hji : 𝒯.deg j < 𝒯.deg i) :
    gammaProductRightStepSupAnnulus S
        (fun x y ω => (M ω).gammaMap x y (Pi.single i 1) j) N k ω ≤
      gammaSplitRightGoodStepSupAnnulus S M D i j N k ω +
        gammaSplitRightBadStepSupAnnulus S M D i j N k ω := by
  unfold gammaProductRightStepSupAnnulus
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  by_cases hnear : parabolicNorm
      (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
        hsParabolicCellRepresentative S (k + 1) b) ≤ 20 / (2 : ℝ) ^ N
  · simp only [ite_eq_left hnear]
    have hsplit := gammaSplitRightTerm_enorm_le (M ω) D i j
      (hsParabolicCellRepresentative S k
        (hsParabolicCellParent S k a))
      (hsParabolicCellRepresentative S k
        (hsParabolicCellParent S k b))
      (hsParabolicCellRepresentative S (k + 1) b) hji
    have hsplit' : ‖(M ω).gammaMap
        (hsParabolicCellRepresentative S k
          (hsParabolicCellParent S k a))
        (hsParabolicCellRepresentative S k
          (hsParabolicCellParent S k b)) (Pi.single i 1) j -
        (M ω).gammaMap
        (hsParabolicCellRepresentative S k
          (hsParabolicCellParent S k a))
        (hsParabolicCellRepresentative S (k + 1) b)
          (Pi.single i 1) j‖ₑ ≤
      ‖gammaSplitRightGoodTerm (M ω) D i j
          (hsParabolicCellRepresentative S k
            (hsParabolicCellParent S k a))
          (hsParabolicCellRepresentative S k
            (hsParabolicCellParent S k b))
          (hsParabolicCellRepresentative S (k + 1) b)‖ₑ +
        ‖gammaSplitRightBadTerm (M ω) D i j
          (hsParabolicCellRepresentative S k
            (hsParabolicCellParent S k a))
          (hsParabolicCellRepresentative S k
            (hsParabolicCellParent S k b))
          (hsParabolicCellRepresentative S (k + 1) b)‖ₑ := by
      calc
        _ = ‖-((M ω).gammaMap
            (hsParabolicCellRepresentative S k
              (hsParabolicCellParent S k a))
            (hsParabolicCellRepresentative S (k + 1) b) (Pi.single i 1) j -
          (M ω).gammaMap
            (hsParabolicCellRepresentative S k
              (hsParabolicCellParent S k a))
            (hsParabolicCellRepresentative S k
              (hsParabolicCellParent S k b)) (Pi.single i 1) j)‖ₑ := by
          rw [show (M ω).gammaMap
              (hsParabolicCellRepresentative S k
                (hsParabolicCellParent S k a))
              (hsParabolicCellRepresentative S k
                (hsParabolicCellParent S k b)) (Pi.single i 1) j -
            (M ω).gammaMap
              (hsParabolicCellRepresentative S k
                (hsParabolicCellParent S k a))
              (hsParabolicCellRepresentative S (k + 1) b)
                (Pi.single i 1) j =
            -((M ω).gammaMap
              (hsParabolicCellRepresentative S k
                (hsParabolicCellParent S k a))
              (hsParabolicCellRepresentative S (k + 1) b)
                (Pi.single i 1) j -
            (M ω).gammaMap
              (hsParabolicCellRepresentative S k
                (hsParabolicCellParent S k a))
              (hsParabolicCellRepresentative S k
                (hsParabolicCellParent S k b))
                (Pi.single i 1) j) by ring]
        _ = ‖(M ω).gammaMap
            (hsParabolicCellRepresentative S k
              (hsParabolicCellParent S k a))
            (hsParabolicCellRepresentative S (k + 1) b)
              (Pi.single i 1) j -
          (M ω).gammaMap
            (hsParabolicCellRepresentative S k
              (hsParabolicCellParent S k a))
            (hsParabolicCellRepresentative S k
              (hsParabolicCellParent S k b))
              (Pi.single i 1) j‖ₑ := by rw [enorm_neg]
        _ ≤ _ := hsplit
    calc
      _ ≤ ‖gammaSplitRightGoodTerm (M ω) D i j
          (hsParabolicCellRepresentative S k
            (hsParabolicCellParent S k a))
          (hsParabolicCellRepresentative S k
            (hsParabolicCellParent S k b))
          (hsParabolicCellRepresentative S (k + 1) b)‖ₑ +
          ‖gammaSplitRightBadTerm (M ω) D i j
          (hsParabolicCellRepresentative S k
            (hsParabolicCellParent S k a))
          (hsParabolicCellRepresentative S k
            (hsParabolicCellParent S k b))
          (hsParabolicCellRepresentative S (k + 1) b)‖ₑ := hsplit'
      _ ≤ _ := add_le_add
        (le_iSup_of_le a (le_iSup_of_le b (by simp [hnear])))
        (le_iSup_of_le a (le_iSup_of_le b (by simp [hnear])))
  · simp only [ite_eq_right hnear]
    exact bot_le

private theorem gammaSplit_ofReal_mul_rpow_scale_le
    {C A B d e : ℝ} {a b : ℝ} {r : ℕ} {N l : ℕ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B) (hd : 0 ≤ d) (he : 0 ≤ e)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdle : d ≤ A * (1 / (2 : ℝ) ^ N))
    (hele : e ≤ B * (1 / (2 : ℝ) ^ (N + l))) :
    ENNReal.ofReal (C * d ^ a * e ^ b) ^ r ≤
      ENNReal.ofReal (C * A ^ a * B ^ b) ^ r *
        dyadicBase N ^ ((r : ℝ) * (a + b)) *
        dyadicBase l ^ ((r : ℝ) * b) := by
  have hd0 : 0 ≤ (1 / (2 : ℝ) ^ N) := by positivity
  have he0 : 0 ≤ (1 / (2 : ℝ) ^ (N + l)) := by positivity
  have hda : d ^ a ≤ (A * (1 / (2 : ℝ) ^ N)) ^ a :=
    Real.rpow_le_rpow hd hdle ha
  have heb : e ^ b ≤ (B * (1 / (2 : ℝ) ^ (N + l))) ^ b :=
    Real.rpow_le_rpow he hele hb
  have hprod : C * d ^ a * e ^ b ≤
      C * (A * (1 / (2 : ℝ) ^ N)) ^ a *
        (B * (1 / (2 : ℝ) ^ (N + l))) ^ b := by
    calc
      C * d ^ a * e ^ b ≤
          C * (A * (1 / (2 : ℝ) ^ N)) ^ a * e ^ b := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hda hC)
          (Real.rpow_nonneg he b)
      _ ≤ C * (A * (1 / (2 : ℝ) ^ N)) ^ a *
          (B * (1 / (2 : ℝ) ^ (N + l))) ^ b := by
        exact mul_le_mul_of_nonneg_left heb (by positivity)
  have hmain : ENNReal.ofReal (C * d ^ a * e ^ b) ^ r ≤
      ENNReal.ofReal (C * (A * (1 / (2 : ℝ) ^ N)) ^ a *
        (B * (1 / (2 : ℝ) ^ (N + l))) ^ b) ^ r := by
    exact ENNReal.pow_le_pow_left (ENNReal.ofReal_le_ofReal hprod)
  have hrewrite :
      ENNReal.ofReal (C * (A * (1 / (2 : ℝ) ^ N)) ^ a *
        (B * (1 / (2 : ℝ) ^ (N + l))) ^ b) ^ r =
      ENNReal.ofReal (C * A ^ a * B ^ b) ^ r *
        dyadicBase N ^ ((r : ℝ) * (a + b)) *
        dyadicBase l ^ ((r : ℝ) * b) := by
    rw [Real.mul_rpow hA hd0, Real.mul_rpow hB he0]
    have hreal : C * (A ^ a * (1 / (2 : ℝ) ^ N) ^ a) *
        (B ^ b * (1 / (2 : ℝ) ^ (N + l)) ^ b) =
        (C * A ^ a * B ^ b) *
          (1 / (2 : ℝ) ^ N) ^ (a + b) *
          (1 / (2 : ℝ) ^ l) ^ b := by
      rw [show (1 / (2 : ℝ) ^ (N + l)) =
          (1 / (2 : ℝ) ^ N) * (1 / (2 : ℝ) ^ l) by
        rw [pow_add]
        ring]
      rw [Real.mul_rpow (by positivity) (by positivity)]
      calc
        C * (A ^ a * (1 / (2 : ℝ) ^ N) ^ a) *
            (B ^ b * ((1 / (2 : ℝ) ^ N) ^ b *
              (1 / (2 : ℝ) ^ l) ^ b)) =
            C * A ^ a * B ^ b *
              ((1 / (2 : ℝ) ^ N) ^ a *
                (1 / (2 : ℝ) ^ N) ^ b) *
              (1 / (2 : ℝ) ^ l) ^ b := by ring
        _ = (C * A ^ a * B ^ b) *
              (1 / (2 : ℝ) ^ N) ^ (a + b) *
              (1 / (2 : ℝ) ^ l) ^ b := by
          rw [← Real.rpow_add (by positivity :
            0 < (1 / (2 : ℝ) ^ N))]
    rw [hreal]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast]
    conv_lhs =>
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
      rw [Real.mul_rpow (by positivity) (by positivity)]
      rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    rw [← ofReal_inv_two_pow, ← ofReal_inv_two_pow]
    have hNpow :
        ENNReal.ofReal (((1 / (2 : ℝ) ^ N) ^ (a + b)) ^ (r : ℝ)) =
          ENNReal.ofReal (1 / (2 : ℝ) ^ N) ^ ((r : ℝ) * (a + b)) := by
      calc
        _ = ENNReal.ofReal ((1 / (2 : ℝ) ^ N) ^
            ((a + b) * (r : ℝ))) := by
          congr 1
          rw [Real.rpow_mul (by positivity)]
        _ = ENNReal.ofReal ((1 / (2 : ℝ) ^ N) ^
            ((r : ℝ) * (a + b))) := by
          congr 2
          ring
        _ = _ := (ENNReal.ofReal_rpow_of_nonneg (by positivity)
          (by positivity)).symm
    have hLpow :
        ENNReal.ofReal (((1 / (2 : ℝ) ^ l) ^ b) ^ (r : ℝ)) =
          ENNReal.ofReal (1 / (2 : ℝ) ^ l) ^ ((r : ℝ) * b) := by
      calc
        _ = ENNReal.ofReal ((1 / (2 : ℝ) ^ l) ^
            (b * (r : ℝ))) := by
          congr 1
          rw [Real.rpow_mul (by positivity)]
        _ = ENNReal.ofReal ((1 / (2 : ℝ) ^ l) ^
            ((r : ℝ) * b)) := by
          congr 2
          ring
        _ = _ := (ENNReal.ofReal_rpow_of_nonneg (by positivity)
          (by positivity)).symm
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    rw [hNpow, hLpow]
  exact hmain.trans_eq hrewrite

omit [MeasurableSpace Ω] in
private theorem gammaSplit_ofReal_fine_scale_le
    {C A e α : ℝ} {r N l : ℕ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (he : 0 ≤ e) (hα : 0 ≤ α)
    (hele : e ≤ A * (1 / (2 : ℝ) ^ (N + l))) :
    ENNReal.ofReal (C * e ^ α) ^ r ≤
      ENNReal.ofReal (C * A ^ α) ^ r *
        dyadicBase N ^ ((r : ℝ) * α) *
        dyadicBase l ^ ((r : ℝ) * α) := by
  have h := gammaSplit_ofReal_mul_rpow_scale_le
    (C := C) (A := 1) (B := A) (d := 1) (e := e)
    (a := 0) (b := α) (r := r) (N := 0) (l := N + l)
    hC (by norm_num) hA (by norm_num) he (by norm_num) hα
    (by norm_num) (by simpa [Nat.zero_add] using hele)
  simpa only [Real.one_rpow, Real.rpow_zero, one_mul, zero_add,
    Nat.cast_zero, zero_mul, dyadicBase_rpow_eq_geometric, pow_add,
    ENNReal.rpow_zero, pow_zero, mul_one, mul_assoc,
    Nat.cast_add, add_mul] using h

noncomputable section gammaSplitLeftGoodBound
  local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

omit [MeasurableSpace Ω] in
theorem gammaSplit_leftGoodBound_scale_le
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (𝒯 : RegularityStructure ι) (D : Set (ι × ι))
    (κ C Cbar : ℝ) (r : ℕ) (i j : ι)
    (β δ : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C) (hCbar : C ≤ Cbar)
    (hβ : β = 𝒯.deg i - 𝒯.deg j)
    (hji : 𝒯.deg j < 𝒯.deg i) (hδ : 0 < δ)
    (hδκ : 2 * δ ≤ κ)
    (hδgap : ∀ k, 𝒯.deg j < 𝒯.deg k → 𝒯.deg k < 𝒯.deg i →
      δ ≤ (𝒯.deg k - 𝒯.deg j) / 2)
    (N l : ℕ) (a b : gammaCell S (N + l + 1))
    (hnear : parabolicNorm
        (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) a) -
          hsParabolicCellRepresentative S (N + l + 1) b) ≤
        20 / (2 : ℝ) ^ N) :
    gammaSplitNearLeftGoodBound 𝒯 D κ C Cbar r i j
        (hsParabolicCellRepresentative S (N + l + 1) b)
        (hsParabolicCellRepresentative S (N + l + 1) a)
        (hsParabolicCellRepresentative S (N + l)
          (hsParabolicCellParent S (N + l) a)) ≤
      (2 : ℝ≥0∞) ^ ((r : ℝ) - 1) *
        (ENNReal.ofReal (C * 4 ^ (β + κ)) ^ r +
          ((gammaGoodIntermediate 𝒯 D i j).card : ℝ≥0∞) ^ ((r : ℝ) - 1) *
            ∑ k ∈ gammaGoodIntermediate 𝒯 D i j,
              ENNReal.ofReal (Cbar * C *
                24 ^ (𝒯.deg i - 𝒯.deg k +
                  (if (i, k) ∈ D then 0 else κ)) *
                4 ^ (𝒯.deg k - 𝒯.deg j +
                  (if (k, j) ∈ D then 0 else κ))) ^ r) *
        (dyadicBase N ^ ((r : ℝ) * (β + κ)) *
          dyadicBase l ^ ((r : ℝ) * (2 * δ))) := by
  classical
  have hCbar0 : 0 ≤ Cbar := hC.trans hCbar
  have hgeom := gammaSplit_left_annulus_geometry S hbox N (N + l)
    (Nat.le_add_right N l) a b hnear
  have hβ0 : 0 ≤ β := by rw [hβ]; linarith
  have hα0 : 0 ≤ β + κ := by linarith
  have hlead := gammaSplit_ofReal_fine_scale_le
    (C := C) (A := 4)
    (e := parabolicNorm
      (hsParabolicCellRepresentative S (N + l)
          (hsParabolicCellParent S (N + l) a) -
        hsParabolicCellRepresentative S (N + l + 1) a))
    (α := β + κ) (r := r) (N := N) (l := l)
    hC (by norm_num) (parabolicNorm_nonneg _) hα0
    (by simpa [div_eq_mul_inv] using hgeom.2)
  have hlead' : ENNReal.ofReal (C * parabolicSemigroup.scaleDist
        (hsParabolicCellRepresentative S (N + l)
          (hsParabolicCellParent S (N + l) a))
    (hsParabolicCellRepresentative S (N + l + 1) a) ^
        (𝒯.deg i - 𝒯.deg j + κ)) ^ r ≤
      ENNReal.ofReal (C * 4 ^ (β + κ)) ^ r *
        dyadicBase N ^ ((r : ℝ) * (β + κ)) *
        dyadicBase l ^ ((r : ℝ) * (2 * δ)) := by
    have hfine : 2 * δ ≤ β + κ := by
      linarith
    calc
      _ ≤ ENNReal.ofReal (C * 4 ^ (β + κ)) ^ r *
          dyadicBase N ^ ((r : ℝ) * (β + κ)) *
          dyadicBase l ^ ((r : ℝ) * (β + κ)) := by
        simpa only [hβ, show parabolicSemigroup.scaleDist
            (hsParabolicCellRepresentative S (N + l)
              (hsParabolicCellParent S (N + l) a))
            (hsParabolicCellRepresentative S (N + l + 1) a) =
            parabolicNorm
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) a) -
              hsParabolicCellRepresentative S (N + l + 1) a) by rfl] using hlead
      _ ≤ _ := by
        have hlpow : dyadicBase l ^ ((r : ℝ) * (β + κ)) ≤
            dyadicBase l ^ ((r : ℝ) * (2 * δ)) := by
          apply ENNReal.rpow_le_rpow_of_exponent_ge
          · unfold dyadicBase
            exact pow_le_one₀ (by positivity) (by norm_num)
          · exact mul_le_mul_of_nonneg_left hfine (by positivity)
        calc
          _ = (ENNReal.ofReal (C * 4 ^ (β + κ)) ^ r *
              dyadicBase N ^ ((r : ℝ) * (β + κ))) *
              dyadicBase l ^ ((r : ℝ) * (β + κ)) := by ring
          _ ≤ (ENNReal.ofReal (C * 4 ^ (β + κ)) ^ r *
              dyadicBase N ^ ((r : ℝ) * (β + κ))) *
              dyadicBase l ^ ((r : ℝ) * (2 * δ)) :=
            mul_le_mul_of_nonneg_left hlpow (by positivity)
          _ = _ := by ring
  unfold gammaSplitNearLeftGoodBound
  conv_rhs => rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_
    (by positivity : 0 ≤ (2 : ℝ≥0∞) ^ ((r : ℝ) - 1))
  have hlead'' := hlead'
  rw [mul_assoc] at hlead''
  simp only [add_mul]
  refine add_le_add hlead'' ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_
    (by positivity : 0 ≤ ((gammaGoodIntermediate 𝒯 D i j).card : ℝ≥0∞) ^ ((r : ℝ) - 1))
  conv_rhs => rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  have hmem := Finset.mem_filter.mp (Finset.mem_filter.mp hk).1
  have hjk : 𝒯.deg j < 𝒯.deg k := hmem.2.1
  have hki : 𝒯.deg k < 𝒯.deg i := hmem.2.2
  have hgood : ¬((i, k) ∈ D ∧ (k, j) ∈ D) :=
    (Finset.mem_filter.mp hk).2
  have hreserve : κ ≤ (if (i, k) ∈ D then 0 else κ) +
      (if (k, j) ∈ D then 0 else κ) := by
    by_cases hik : (i, k) ∈ D
    · have hkj : (k, j) ∉ D := by
        intro hkj
        exact hgood ⟨hik, hkj⟩
      simp [hik, hkj]
    · by_cases hkj : (k, j) ∈ D
      · simp [hik, hkj]
      · simp [hik, hkj, hκ.le]
  have hki0 : 0 ≤ 𝒯.deg i - 𝒯.deg k := by linarith
  have hjk0 : 0 ≤ 𝒯.deg k - 𝒯.deg j := by linarith
  have hai : 0 ≤ 𝒯.deg i - 𝒯.deg k +
      (if (i, k) ∈ D then 0 else κ) := by
    split
    · simp_all
    · simp_all
      linarith
  have hbj : 0 ≤ 𝒯.deg k - 𝒯.deg j +
      (if (k, j) ∈ D then 0 else κ) := by
    split
    · simp_all
    · simp_all
      linarith
  have hscale := gammaSplit_ofReal_mul_rpow_scale_le
    (C := Cbar * C) (A := 24) (B := 4)
    (d := parabolicNorm
      (hsParabolicCellRepresentative S (N + l + 1) a -
        hsParabolicCellRepresentative S (N + l + 1) b))
    (e := parabolicNorm
      (hsParabolicCellRepresentative S (N + l)
          (hsParabolicCellParent S (N + l) a) -
        hsParabolicCellRepresentative S (N + l + 1) a))
    (a := 𝒯.deg i - 𝒯.deg k +
      (if (i, k) ∈ D then 0 else κ))
    (b := 𝒯.deg k - 𝒯.deg j +
      (if (k, j) ∈ D then 0 else κ))
    (r := r) (N := N) (l := l)
    (mul_nonneg hCbar0 hC) (by norm_num) (by norm_num)
    (parabolicNorm_nonneg _) (parabolicNorm_nonneg _) hai hbj
    (by simpa [div_eq_mul_inv] using hgeom.1)
    (by simpa [div_eq_mul_inv] using hgeom.2)
  have hNexp : β + κ ≤
      (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) +
        (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ)) := by
    rw [hβ]
    linarith
  have hLexp : 2 * δ ≤ 𝒯.deg k - 𝒯.deg j +
      (if (k, j) ∈ D then 0 else κ) := by
    have hgap := hδgap k hjk hki
    by_cases hkj : (k, j) ∈ D
    · simp [hkj]
      linarith [hgap]
    · simp [hkj]
      linarith [hgap, hκ]
  calc
    _ ≤ ENNReal.ofReal (Cbar * C *
          24 ^ (𝒯.deg i - 𝒯.deg k +
            (if (i, k) ∈ D then 0 else κ)) *
          4 ^ (𝒯.deg k - 𝒯.deg j +
            (if (k, j) ∈ D then 0 else κ))) ^ r *
        dyadicBase N ^ ((r : ℝ) *
          ((𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) +
            (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ))) ) *
        dyadicBase l ^ ((r : ℝ) *
          (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ))) := by
      simpa only [show parabolicSemigroup.scaleDist
          (hsParabolicCellRepresentative S (N + l + 1) a)
          (hsParabolicCellRepresentative S (N + l + 1) b) =
          parabolicNorm
            (hsParabolicCellRepresentative S (N + l + 1) a -
              hsParabolicCellRepresentative S (N + l + 1) b) by rfl,
        show parabolicSemigroup.scaleDist
          (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) a))
          (hsParabolicCellRepresentative S (N + l + 1) a) =
          parabolicNorm
            (hsParabolicCellRepresentative S (N + l)
              (hsParabolicCellParent S (N + l) a) -
              hsParabolicCellRepresentative S (N + l + 1) a) by rfl] using hscale
    _ ≤ (ENNReal.ofReal (Cbar * C *
          24 ^ (𝒯.deg i - 𝒯.deg k +
            (if (i, k) ∈ D then 0 else κ)) *
          4 ^ (𝒯.deg k - 𝒯.deg j +
            (if (k, j) ∈ D then 0 else κ))) ^ r *
        (dyadicBase N ^ ((r : ℝ) * (β + κ)) *
          dyadicBase l ^ ((r : ℝ) * (2 * δ)))) := by
      have hNpow : dyadicBase N ^ ((r : ℝ) *
          ((𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) +
            (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ)))) ≤
          dyadicBase N ^ ((r : ℝ) * (β + κ)) := by
        apply ENNReal.rpow_le_rpow_of_exponent_ge
        · unfold dyadicBase
          exact pow_le_one₀ (by positivity) (by norm_num)
        · exact mul_le_mul_of_nonneg_left hNexp (by positivity)
      have hLpow : dyadicBase l ^ ((r : ℝ) *
          (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ))) ≤
          dyadicBase l ^ ((r : ℝ) * (2 * δ)) := by
        apply ENNReal.rpow_le_rpow_of_exponent_ge
        · unfold dyadicBase
          exact pow_le_one₀ (by positivity) (by norm_num)
        · exact mul_le_mul_of_nonneg_left hLexp (by positivity)
      calc
        _ = (ENNReal.ofReal (Cbar * C *
              24 ^ (𝒯.deg i - 𝒯.deg k +
                (if (i, k) ∈ D then 0 else κ)) *
              4 ^ (𝒯.deg k - 𝒯.deg j +
                (if (k, j) ∈ D then 0 else κ))) ^ r *
            (dyadicBase N ^ ((r : ℝ) *
              ((𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) +
                (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ)))) *
              dyadicBase l ^ ((r : ℝ) *
                (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ))))) := by ring
        _ ≤ (ENNReal.ofReal (Cbar * C *
              24 ^ (𝒯.deg i - 𝒯.deg k +
                (if (i, k) ∈ D then 0 else κ)) *
              4 ^ (𝒯.deg k - 𝒯.deg j +
                (if (k, j) ∈ D then 0 else κ))) ^ r *
            (dyadicBase N ^ ((r : ℝ) * (β + κ)) *
              dyadicBase l ^ ((r : ℝ) * (2 * δ)))) := by
          have hprod := mul_le_mul hNpow hLpow (by positivity) (by positivity)
          have hscaled := mul_le_mul_of_nonneg_left hprod
            (by positivity : 0 ≤ ENNReal.ofReal (Cbar * C *
              24 ^ (𝒯.deg i - 𝒯.deg k +
                (if (i, k) ∈ D then 0 else κ)) *
              4 ^ (𝒯.deg k - 𝒯.deg j +
                (if (k, j) ∈ D then 0 else κ))) ^ r)
          exact hscaled
end gammaSplitLeftGoodBound

noncomputable section gammaSplitRightGoodBound
  local instance propDecidableRight (p : Prop) : Decidable p := Classical.propDecidable p

omit [MeasurableSpace Ω] in
theorem gammaSplit_rightGoodBound_scale_le
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (𝒯 : RegularityStructure ι) (D : Set (ι × ι))
    (κ C Cbar : ℝ) (r : ℕ) (i j : ι)
    (β δ : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C) (hCbar : C ≤ Cbar)
    (hβ : β = 𝒯.deg i - 𝒯.deg j)
    (hji : 𝒯.deg j < 𝒯.deg i) (hδ : 0 < δ)
    (hδκ : 2 * δ ≤ κ)
    (hδgap : ∀ k, 𝒯.deg j < 𝒯.deg k → 𝒯.deg k < 𝒯.deg i →
      δ ≤ (𝒯.deg i - 𝒯.deg k) / 2)
    (N l : ℕ) (a b : gammaCell S (N + l + 1))
    (hnear : parabolicNorm
        (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) a) -
          hsParabolicCellRepresentative S (N + l + 1) b) ≤
        20 / (2 : ℝ) ^ N) :
    gammaSplitNearRightGoodBound 𝒯 D κ C Cbar r i j
        (hsParabolicCellRepresentative S (N + l)
          (hsParabolicCellParent S (N + l) a))
        (hsParabolicCellRepresentative S (N + l)
          (hsParabolicCellParent S (N + l) b))
        (hsParabolicCellRepresentative S (N + l + 1) b) ≤
      (2 : ℝ≥0∞) ^ ((r : ℝ) - 1) *
        (ENNReal.ofReal (C * 4 ^ (β + κ)) ^ r +
          ((gammaGoodIntermediate 𝒯 D i j).card : ℝ≥0∞) ^ ((r : ℝ) - 1) *
            ∑ k ∈ gammaGoodIntermediate 𝒯 D i j,
              ENNReal.ofReal (Cbar * C *
                4 ^ (𝒯.deg i - 𝒯.deg k +
                  (if (i, k) ∈ D then 0 else κ)) *
                24 ^ (𝒯.deg k - 𝒯.deg j +
                  (if (k, j) ∈ D then 0 else κ))) ^ r) *
        (dyadicBase N ^ ((r : ℝ) * (β + κ)) *
          dyadicBase l ^ ((r : ℝ) * (2 * δ))) := by
  classical
  have hCbar0 : 0 ≤ Cbar := hC.trans hCbar
  have hgeom := gammaSplit_right_annulus_geometry S hbox N (N + l)
    (Nat.le_add_right N l) a b hnear
  have hβ0 : 0 ≤ β := by rw [hβ]; linarith
  have hα0 : 0 ≤ β + κ := by linarith
  have hlead := gammaSplit_ofReal_fine_scale_le
    (C := C) (A := 4)
    (e := parabolicNorm
      (hsParabolicCellRepresentative S (N + l)
          (hsParabolicCellParent S (N + l) b) -
        hsParabolicCellRepresentative S (N + l + 1) b))
    (α := β + κ) (r := r) (N := N) (l := l)
    hC (by norm_num) (parabolicNorm_nonneg _) hα0
    (by simpa [div_eq_mul_inv] using hgeom.2)
  have hlead' : ENNReal.ofReal (C * parabolicSemigroup.scaleDist
        (hsParabolicCellRepresentative S (N + l)
          (hsParabolicCellParent S (N + l) b))
    (hsParabolicCellRepresentative S (N + l + 1) b) ^
        (𝒯.deg i - 𝒯.deg j + κ)) ^ r ≤
      ENNReal.ofReal (C * 4 ^ (β + κ)) ^ r *
        dyadicBase N ^ ((r : ℝ) * (β + κ)) *
        dyadicBase l ^ ((r : ℝ) * (2 * δ)) := by
    have hfine : 2 * δ ≤ β + κ := by
      linarith
    calc
      _ ≤ ENNReal.ofReal (C * 4 ^ (β + κ)) ^ r *
          dyadicBase N ^ ((r : ℝ) * (β + κ)) *
          dyadicBase l ^ ((r : ℝ) * (β + κ)) := by
        simpa only [hβ, show parabolicSemigroup.scaleDist
            (hsParabolicCellRepresentative S (N + l)
              (hsParabolicCellParent S (N + l) b))
            (hsParabolicCellRepresentative S (N + l + 1) b) =
            parabolicNorm
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) b) -
              hsParabolicCellRepresentative S (N + l + 1) b) by rfl] using hlead
      _ ≤ _ := by
        have hlpow : dyadicBase l ^ ((r : ℝ) * (β + κ)) ≤
            dyadicBase l ^ ((r : ℝ) * (2 * δ)) := by
          apply ENNReal.rpow_le_rpow_of_exponent_ge
          · unfold dyadicBase
            exact pow_le_one₀ (by positivity) (by norm_num)
          · exact mul_le_mul_of_nonneg_left hfine (by positivity)
        calc
          _ = (ENNReal.ofReal (C * 4 ^ (β + κ)) ^ r *
              dyadicBase N ^ ((r : ℝ) * (β + κ))) *
              dyadicBase l ^ ((r : ℝ) * (β + κ)) := by ring
          _ ≤ (ENNReal.ofReal (C * 4 ^ (β + κ)) ^ r *
              dyadicBase N ^ ((r : ℝ) * (β + κ))) *
              dyadicBase l ^ ((r : ℝ) * (2 * δ)) :=
            mul_le_mul_of_nonneg_left hlpow (by positivity)
          _ = _ := by ring
  unfold gammaSplitNearRightGoodBound
  conv_rhs => rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_
    (by positivity : 0 ≤ (2 : ℝ≥0∞) ^ ((r : ℝ) - 1))
  have hlead'' := hlead'
  rw [mul_assoc] at hlead''
  simp only [add_mul]
  refine add_le_add hlead'' ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_
    (by positivity : 0 ≤ ((gammaGoodIntermediate 𝒯 D i j).card : ℝ≥0∞) ^ ((r : ℝ) - 1))
  conv_rhs => rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  have hmem := Finset.mem_filter.mp (Finset.mem_filter.mp hk).1
  have hjk : 𝒯.deg j < 𝒯.deg k := hmem.2.1
  have hki : 𝒯.deg k < 𝒯.deg i := hmem.2.2
  have hgood : ¬((i, k) ∈ D ∧ (k, j) ∈ D) :=
    (Finset.mem_filter.mp hk).2
  have hreserve : κ ≤ (if (i, k) ∈ D then 0 else κ) +
      (if (k, j) ∈ D then 0 else κ) := by
    by_cases hik : (i, k) ∈ D
    · have hkj : (k, j) ∉ D := by
        intro hkj
        exact hgood ⟨hik, hkj⟩
      simp [hik, hkj]
    · by_cases hkj : (k, j) ∈ D
      · simp [hik, hkj]
      · simp [hik, hkj, hκ.le]
  have hki0 : 0 ≤ 𝒯.deg i - 𝒯.deg k := by linarith
  have hjk0 : 0 ≤ 𝒯.deg k - 𝒯.deg j := by linarith
  have hai : 0 ≤ 𝒯.deg i - 𝒯.deg k +
      (if (i, k) ∈ D then 0 else κ) := by
    split
    · simp_all
    · simp_all
      linarith
  have hbj : 0 ≤ 𝒯.deg k - 𝒯.deg j +
      (if (k, j) ∈ D then 0 else κ) := by
    split
    · simp_all
    · simp_all
      linarith
  have hscale := gammaSplit_ofReal_mul_rpow_scale_le
    (C := Cbar * C) (A := 24) (B := 4)
    (d := parabolicNorm
      (hsParabolicCellRepresentative S (N + l)
          (hsParabolicCellParent S (N + l) a) -
        hsParabolicCellRepresentative S (N + l)
          (hsParabolicCellParent S (N + l) b)))
    (e := parabolicNorm
      (hsParabolicCellRepresentative S (N + l)
          (hsParabolicCellParent S (N + l) b) -
        hsParabolicCellRepresentative S (N + l + 1) b))
    (a := 𝒯.deg k - 𝒯.deg j +
      (if (k, j) ∈ D then 0 else κ))
    (b := 𝒯.deg i - 𝒯.deg k +
      (if (i, k) ∈ D then 0 else κ))
    (r := r) (N := N) (l := l)
    (mul_nonneg hCbar0 hC) (by norm_num) (by norm_num)
    (parabolicNorm_nonneg _) (parabolicNorm_nonneg _) hbj hai
    (by simpa [div_eq_mul_inv] using hgeom.1)
    (by simpa [div_eq_mul_inv] using hgeom.2)
  have hNexp : β + κ ≤
      (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) +
        (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ)) := by
    rw [hβ]
    linarith
  have hLexp : 2 * δ ≤ 𝒯.deg i - 𝒯.deg k +
      (if (i, k) ∈ D then 0 else κ) := by
    have hgap := hδgap k hjk hki
    by_cases hik : (i, k) ∈ D
    · simp [hik]
      linarith [hgap]
    · simp [hik]
      linarith [hgap, hκ]
  calc
    _ ≤ ENNReal.ofReal (Cbar * C *
          4 ^ (𝒯.deg i - 𝒯.deg k +
            (if (i, k) ∈ D then 0 else κ)) *
          24 ^ (𝒯.deg k - 𝒯.deg j +
            (if (k, j) ∈ D then 0 else κ))) ^ r *
        dyadicBase N ^ ((r : ℝ) *
          ((𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) +
            (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ)))) *
        dyadicBase l ^ ((r : ℝ) *
          (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ))) := by
      have hscale' := hscale
      rw [show
          (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ)) +
              (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) =
            (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) +
              (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ)) by ring] at hscale'
      simpa [mul_comm, mul_left_comm, mul_assoc,
        show parabolicSemigroup.scaleDist
          (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) b))
          (hsParabolicCellRepresentative S (N + l + 1) b) =
          parabolicNorm
            (hsParabolicCellRepresentative S (N + l)
              (hsParabolicCellParent S (N + l) b) -
            hsParabolicCellRepresentative S (N + l + 1) b) by rfl,
        show parabolicSemigroup.scaleDist
          (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) a))
          (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) b)) =
          parabolicNorm
            (hsParabolicCellRepresentative S (N + l)
              (hsParabolicCellParent S (N + l) a) -
            hsParabolicCellRepresentative S (N + l)
              (hsParabolicCellParent S (N + l) b)) by rfl] using hscale'
    _ ≤ (ENNReal.ofReal (Cbar * C *
          4 ^ (𝒯.deg i - 𝒯.deg k +
            (if (i, k) ∈ D then 0 else κ)) *
          24 ^ (𝒯.deg k - 𝒯.deg j +
            (if (k, j) ∈ D then 0 else κ))) ^ r *
        (dyadicBase N ^ ((r : ℝ) * (β + κ)) *
          dyadicBase l ^ ((r : ℝ) * (2 * δ)))) := by
      have hNpow : dyadicBase N ^ ((r : ℝ) *
          ((𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) +
            (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ)))) ≤
          dyadicBase N ^ ((r : ℝ) * (β + κ)) := by
        apply ENNReal.rpow_le_rpow_of_exponent_ge
        · unfold dyadicBase
          exact pow_le_one₀ (by positivity) (by norm_num)
        · exact mul_le_mul_of_nonneg_left hNexp (by positivity)
      have hLpow : dyadicBase l ^ ((r : ℝ) *
          (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ))) ≤
          dyadicBase l ^ ((r : ℝ) * (2 * δ)) := by
        apply ENNReal.rpow_le_rpow_of_exponent_ge
        · unfold dyadicBase
          exact pow_le_one₀ (by positivity) (by norm_num)
        · exact mul_le_mul_of_nonneg_left hLexp (by positivity)
      calc
        _ = (ENNReal.ofReal (Cbar * C *
              4 ^ (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) *
              24 ^ (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ))) ^ r *
            (dyadicBase N ^ ((r : ℝ) *
              ((𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) +
                (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ)))) *
              dyadicBase l ^ ((r : ℝ) *
                (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ))))) := by ring
        _ ≤ (ENNReal.ofReal (Cbar * C *
              4 ^ (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) *
              24 ^ (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ))) ^ r *
            (dyadicBase N ^ ((r : ℝ) * (β + κ)) *
              dyadicBase l ^ ((r : ℝ) * (2 * δ)))) := by
          have hprod := mul_le_mul hNpow hLpow (by positivity) (by positivity)
          have hscaled := mul_le_mul_of_nonneg_left hprod
            (by positivity : 0 ≤ ENNReal.ofReal (Cbar * C *
              4 ^ (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) *
              24 ^ (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ))) ^ r)
          exact hscaled
end gammaSplitRightGoodBound

omit [MeasurableSpace Ω] in
private theorem gammaSplit_leftBadStepSupAnnulus_le_aux
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ C : ℝ) (hC : 0 ≤ C)
    (hdet : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
      ∀ ω x y, |(M ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j))
    (i j : ι) (hi : 𝒯.deg i < γ) (hji : 𝒯.deg j < 𝒯.deg i)
    (β δ : ℝ) (hβ : β = 𝒯.deg i - 𝒯.deg j) (_hδ : 0 < δ)
    (hδgap : ∀ k, 𝒯.deg j < 𝒯.deg k → 𝒯.deg k < 𝒯.deg i →
      δ ≤ (𝒯.deg k - 𝒯.deg j) / 2)
    (ω : Ω) (N l : ℕ) :
    gammaSplitLeftBadStepSupAnnulus S M D i j N (N + l) ω ≤
      ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
        ENNReal.ofReal (C ^ 2 * 24 ^ (𝒯.deg i - 𝒯.deg k) *
          4 ^ (𝒯.deg k - 𝒯.deg j)) *
          dyadicBase N ^ β * dyadicBase l ^ δ := by
  classical
  unfold gammaSplitLeftBadStepSupAnnulus
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  by_cases hnear : parabolicNorm
      (hsParabolicCellRepresentative S (N + l)
          (hsParabolicCellParent S (N + l) a) -
        hsParabolicCellRepresentative S (N + l + 1) b) ≤
      20 / (2 : ℝ) ^ N
  · simp only [ite_eq_left hnear]
    have hgeom := gammaSplit_left_annulus_geometry S hbox N (N + l)
      (Nat.le_add_right N l) a b hnear
    have hbad := gammaSplitLeftBadTerm_enorm_le_of_DGamma M D γ C hdet
      i j hi hji
      (hsParabolicCellRepresentative S (N + l + 1) b)
      (hsParabolicCellRepresentative S (N + l + 1) a)
      (hsParabolicCellRepresentative S (N + l)
        (hsParabolicCellParent S (N + l) a)) ω
    calc
      _ ≤ ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
          ENNReal.ofReal (C * parabolicSemigroup.scaleDist
            (hsParabolicCellRepresentative S (N + l + 1) a)
            (hsParabolicCellRepresentative S (N + l + 1) b) ^
              (𝒯.deg i - 𝒯.deg k)) *
            ENNReal.ofReal (C * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) a))
              (hsParabolicCellRepresentative S (N + l + 1) a) ^
                (𝒯.deg k - 𝒯.deg j)) := hbad
      _ ≤ _ := by
        refine Finset.sum_le_sum ?_
        intro k hk
        have hmem := Finset.mem_filter.mp (Finset.mem_filter.mp hk).1
        have hjk : 𝒯.deg j < 𝒯.deg k := hmem.2.1
        have hki : 𝒯.deg k < 𝒯.deg i := hmem.2.2
        have hscale := gammaSplit_ofReal_mul_rpow_scale_le
          (C := C ^ 2) (A := 24) (B := 4)
          (a := 𝒯.deg i - 𝒯.deg k)
          (b := 𝒯.deg k - 𝒯.deg j) (r := 1) (N := N) (l := l)
          (sq_nonneg C) (by norm_num) (by norm_num)
          (parabolicNorm_nonneg _) (parabolicNorm_nonneg _)
          (by linarith) (by linarith)
          (by simpa [div_eq_mul_inv] using hgeom.1)
          (by simpa [div_eq_mul_inv] using hgeom.2)
        have hdegree : 𝒯.deg i - 𝒯.deg j =
            (𝒯.deg i - 𝒯.deg k) + (𝒯.deg k - 𝒯.deg j) := by ring
        have hscale' : ENNReal.ofReal (C ^ 2 *
              parabolicNorm
                (hsParabolicCellRepresentative S (N + l + 1) a -
                  hsParabolicCellRepresentative S (N + l + 1) b) ^
                (𝒯.deg i - 𝒯.deg k) *
              parabolicNorm
                (hsParabolicCellRepresentative S (N + l)
                  (hsParabolicCellParent S (N + l) a) -
                hsParabolicCellRepresentative S (N + l + 1) a) ^
                (𝒯.deg k - 𝒯.deg j)) ≤
            ENNReal.ofReal (C ^ 2 * 24 ^ (𝒯.deg i - 𝒯.deg k) *
              4 ^ (𝒯.deg k - 𝒯.deg j)) *
              dyadicBase N ^ (𝒯.deg i - 𝒯.deg j) *
              dyadicBase l ^ (𝒯.deg k - 𝒯.deg j) := by
          have hscale'' := hscale
          simp only [pow_one, Nat.cast_one, one_mul] at hscale''
          rw [← hdegree] at hscale''
          exact hscale''
        have hfine : dyadicBase l ^ (𝒯.deg k - 𝒯.deg j) ≤
            dyadicBase l ^ δ := by
          apply ENNReal.rpow_le_rpow_of_exponent_ge
          · unfold dyadicBase
            exact pow_le_one₀ (by positivity) (by norm_num)
          · exact (hδgap k hjk hki).trans (by linarith [hjk])
        have hprod : ENNReal.ofReal (C *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l + 1) a)
                (hsParabolicCellRepresentative S (N + l + 1) b) ^
                (𝒯.deg i - 𝒯.deg k)) *
            ENNReal.ofReal (C * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) a))
              (hsParabolicCellRepresentative S (N + l + 1) a) ^
                (𝒯.deg k - 𝒯.deg j)) =
            ENNReal.ofReal (C ^ 2 *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l + 1) a)
                (hsParabolicCellRepresentative S (N + l + 1) b) ^
                (𝒯.deg i - 𝒯.deg k) *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l)
                  (hsParabolicCellParent S (N + l) a))
                (hsParabolicCellRepresentative S (N + l + 1) a) ^
                (𝒯.deg k - 𝒯.deg j)) := by
          have hfirst : 0 ≤ C * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l + 1) a)
              (hsParabolicCellRepresentative S (N + l + 1) b) ^
                (𝒯.deg i - 𝒯.deg k) :=
            mul_nonneg hC (Real.rpow_nonneg
              (parabolicSemigroup.scaleDist_nonneg _ _) _)
          rw [← ENNReal.ofReal_mul hfirst]
          congr 1
          ring
        rw [hprod]
        calc
          _ ≤ ENNReal.ofReal (C ^ 2 * 24 ^ (𝒯.deg i - 𝒯.deg k) *
              4 ^ (𝒯.deg k - 𝒯.deg j)) *
              dyadicBase N ^ (𝒯.deg i - 𝒯.deg j) *
              dyadicBase l ^ (𝒯.deg k - 𝒯.deg j) := hscale'
          _ ≤ ENNReal.ofReal (C ^ 2 * 24 ^ (𝒯.deg i - 𝒯.deg k) *
              4 ^ (𝒯.deg k - 𝒯.deg j)) *
              dyadicBase N ^ (𝒯.deg i - 𝒯.deg j) *
              dyadicBase l ^ δ := by gcongr
          _ = _ := by rw [hβ, show 𝒯.deg i - 𝒯.deg j =
              (𝒯.deg i - 𝒯.deg k) + (𝒯.deg k - 𝒯.deg j) by ring]
  · simp [hnear]

omit [MeasurableSpace Ω] in
private theorem gammaSplit_rightBadStepSupAnnulus_le_aux
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ C : ℝ) (hC : 0 ≤ C)
    (hdet : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
      ∀ ω x y, |(M ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j))
    (i j : ι) (hi : 𝒯.deg i < γ) (hji : 𝒯.deg j < 𝒯.deg i)
    (β δ : ℝ) (hβ : β = 𝒯.deg i - 𝒯.deg j) (_hδ : 0 < δ)
    (hδgap : ∀ k, 𝒯.deg j < 𝒯.deg k → 𝒯.deg k < 𝒯.deg i →
      δ ≤ (𝒯.deg i - 𝒯.deg k) / 2)
    (ω : Ω) (N l : ℕ) :
    gammaSplitRightBadStepSupAnnulus S M D i j N (N + l) ω ≤
      ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
        ENNReal.ofReal (C ^ 2 * 24 ^ (𝒯.deg k - 𝒯.deg j) *
          4 ^ (𝒯.deg i - 𝒯.deg k)) *
          dyadicBase N ^ β * dyadicBase l ^ δ := by
  classical
  unfold gammaSplitRightBadStepSupAnnulus
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  by_cases hnear : parabolicNorm
      (hsParabolicCellRepresentative S (N + l)
          (hsParabolicCellParent S (N + l) a) -
        hsParabolicCellRepresentative S (N + l + 1) b) ≤
      20 / (2 : ℝ) ^ N
  · simp only [ite_eq_left hnear]
    have hgeom := gammaSplit_right_annulus_geometry S hbox N (N + l)
      (Nat.le_add_right N l) a b hnear
    have hbad := gammaSplitRightBadTerm_enorm_le_of_DGamma M D γ C hdet
      i j hi hji
      (hsParabolicCellRepresentative S (N + l)
        (hsParabolicCellParent S (N + l) a))
      (hsParabolicCellRepresentative S (N + l)
        (hsParabolicCellParent S (N + l) b))
      (hsParabolicCellRepresentative S (N + l + 1) b) ω
    calc
      _ ≤ ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
          ENNReal.ofReal (C * parabolicSemigroup.scaleDist
            (hsParabolicCellRepresentative S (N + l)
              (hsParabolicCellParent S (N + l) b))
            (hsParabolicCellRepresentative S (N + l + 1) b) ^
              (𝒯.deg i - 𝒯.deg k)) *
            ENNReal.ofReal (C * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) a))
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) b)) ^
                (𝒯.deg k - 𝒯.deg j)) := hbad
      _ ≤ _ := by
        refine Finset.sum_le_sum ?_
        intro k hk
        have hmem := Finset.mem_filter.mp (Finset.mem_filter.mp hk).1
        have hjk : 𝒯.deg j < 𝒯.deg k := hmem.2.1
        have hki : 𝒯.deg k < 𝒯.deg i := hmem.2.2
        have hscale := gammaSplit_ofReal_mul_rpow_scale_le
          (C := C ^ 2) (A := 24) (B := 4)
          (a := 𝒯.deg k - 𝒯.deg j)
          (b := 𝒯.deg i - 𝒯.deg k) (r := 1) (N := N) (l := l)
          (d := parabolicNorm
            (hsParabolicCellRepresentative S (N + l)
              (hsParabolicCellParent S (N + l) a) -
            hsParabolicCellRepresentative S (N + l)
              (hsParabolicCellParent S (N + l) b)))
          (e := parabolicNorm
            (hsParabolicCellRepresentative S (N + l)
              (hsParabolicCellParent S (N + l) b) -
            hsParabolicCellRepresentative S (N + l + 1) b))
          (sq_nonneg C) (by norm_num) (by norm_num)
          (parabolicNorm_nonneg _) (parabolicNorm_nonneg _)
          (by linarith) (by linarith)
          (by simpa [div_eq_mul_inv] using hgeom.1)
          (by simpa [div_eq_mul_inv] using hgeom.2)
        have hdegree : 𝒯.deg i - 𝒯.deg j =
            (𝒯.deg i - 𝒯.deg k) + (𝒯.deg k - 𝒯.deg j) := by ring
        have hdegreeRight : 𝒯.deg i - 𝒯.deg j =
            (𝒯.deg k - 𝒯.deg j) + (𝒯.deg i - 𝒯.deg k) := by ring
        have hscale' : ENNReal.ofReal (C ^ 2 *
              parabolicNorm
                (hsParabolicCellRepresentative S (N + l)
                  (hsParabolicCellParent S (N + l) a) -
                hsParabolicCellRepresentative S (N + l)
                  (hsParabolicCellParent S (N + l) b)) ^
                (𝒯.deg k - 𝒯.deg j) *
              parabolicNorm
                (hsParabolicCellRepresentative S (N + l)
                  (hsParabolicCellParent S (N + l) b) -
                hsParabolicCellRepresentative S (N + l + 1) b) ^
                (𝒯.deg i - 𝒯.deg k)) ≤
            ENNReal.ofReal (C ^ 2 * 24 ^ (𝒯.deg k - 𝒯.deg j) *
              4 ^ (𝒯.deg i - 𝒯.deg k)) *
              dyadicBase N ^ (𝒯.deg i - 𝒯.deg j) *
              dyadicBase l ^ (𝒯.deg i - 𝒯.deg k) := by
          have hscale'' := hscale
          simp only [pow_one, Nat.cast_one, one_mul] at hscale''
          rw [← hdegreeRight] at hscale''
          exact hscale''
        have hfine : dyadicBase l ^ (𝒯.deg i - 𝒯.deg k) ≤
            dyadicBase l ^ δ := by
          apply ENNReal.rpow_le_rpow_of_exponent_ge
          · unfold dyadicBase
            exact pow_le_one₀ (by positivity) (by norm_num)
          · exact (hδgap k hjk hki).trans (by linarith [hki])
        have hprod : ENNReal.ofReal (C * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) b))
              (hsParabolicCellRepresentative S (N + l + 1) b) ^
                (𝒯.deg i - 𝒯.deg k)) *
            ENNReal.ofReal (C * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) a))
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) b)) ^
                (𝒯.deg k - 𝒯.deg j)) =
            ENNReal.ofReal (C ^ 2 *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l)
                  (hsParabolicCellParent S (N + l) a))
                (hsParabolicCellRepresentative S (N + l)
                  (hsParabolicCellParent S (N + l) b)) ^
                (𝒯.deg k - 𝒯.deg j) *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l)
                  (hsParabolicCellParent S (N + l) b))
                (hsParabolicCellRepresentative S (N + l + 1) b) ^
                (𝒯.deg i - 𝒯.deg k)) := by
          have hfirst : 0 ≤ C * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) b))
              (hsParabolicCellRepresentative S (N + l + 1) b) ^
                (𝒯.deg i - 𝒯.deg k) :=
            mul_nonneg hC (Real.rpow_nonneg
              (parabolicSemigroup.scaleDist_nonneg _ _) _)
          rw [← ENNReal.ofReal_mul hfirst]
          congr 1
          ring
        rw [hprod]
        calc
          _ ≤ ENNReal.ofReal (C ^ 2 * 24 ^ (𝒯.deg k - 𝒯.deg j) *
              4 ^ (𝒯.deg i - 𝒯.deg k)) *
              dyadicBase N ^ (𝒯.deg i - 𝒯.deg j) *
              dyadicBase l ^ (𝒯.deg i - 𝒯.deg k) := hscale'
          _ ≤ ENNReal.ofReal (C ^ 2 * 24 ^ (𝒯.deg k - 𝒯.deg j) *
              4 ^ (𝒯.deg i - 𝒯.deg k)) *
              dyadicBase N ^ (𝒯.deg i - 𝒯.deg j) *
              dyadicBase l ^ δ := by gcongr
          _ = _ := by rw [hβ]
  · simp only [ite_eq_right hnear]
    exact bot_le

omit [MeasurableSpace Ω] in
/-- The annular left-step split exposed to the final finite-sector assembly. -/
theorem gammaSplit_leftStepSupAnnulus_le
    (S : Set ParabolicSpace)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (N k : ℕ) (ω : Ω)
    (hji : 𝒯.deg j < 𝒯.deg i) :
    gammaProductLeftStepSupAnnulus S
        (fun x y ω => (M ω).gammaMap x y (Pi.single i 1) j) N k ω ≤
      gammaSplitLeftGoodStepSupAnnulus S M D i j N k ω +
        gammaSplitLeftBadStepSupAnnulus S M D i j N k ω := by
  exact gammaSplit_leftStepSupAnnulus_le_aux S M D i j N k ω hji

omit [MeasurableSpace Ω] in
/-- The annular right-step split exposed to the final finite-sector assembly. -/
theorem gammaSplit_rightStepSupAnnulus_le
    (S : Set ParabolicSpace)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (N k : ℕ) (ω : Ω)
    (hji : 𝒯.deg j < 𝒯.deg i) :
    gammaProductRightStepSupAnnulus S
        (fun x y ω => (M ω).gammaMap x y (Pi.single i 1) j) N k ω ≤
      gammaSplitRightGoodStepSupAnnulus S M D i j N k ω +
        gammaSplitRightBadStepSupAnnulus S M D i j N k ω := by
  exact gammaSplit_rightStepSupAnnulus_le_aux S M D i j N k ω hji

omit [MeasurableSpace Ω] in
/-- The pathwise left bad channel exposed to the final finite-sector assembly. -/
theorem gammaSplit_leftBadStepSupAnnulus_le
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ C : ℝ) (hC : 0 ≤ C)
    (hdet : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
      ∀ ω x y, |(M ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j))
    (i j : ι) (hi : 𝒯.deg i < γ) (hji : 𝒯.deg j < 𝒯.deg i)
    (β δ : ℝ) (hβ : β = 𝒯.deg i - 𝒯.deg j) (_hδ : 0 < δ)
    (hδgap : ∀ k, 𝒯.deg j < 𝒯.deg k → 𝒯.deg k < 𝒯.deg i →
      δ ≤ (𝒯.deg k - 𝒯.deg j) / 2) (ω : Ω) (N l : ℕ) :
    gammaSplitLeftBadStepSupAnnulus S M D i j N (N + l) ω ≤
      ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
        ENNReal.ofReal (C ^ 2 * 24 ^ (𝒯.deg i - 𝒯.deg k) *
          4 ^ (𝒯.deg k - 𝒯.deg j)) *
          dyadicBase N ^ β * dyadicBase l ^ δ := by
  exact gammaSplit_leftBadStepSupAnnulus_le_aux S hbox M D γ C hC hdet i j hi hji
    β δ hβ _hδ hδgap ω N l

omit [MeasurableSpace Ω] in
/-- The pathwise right bad channel exposed to the final finite-sector assembly. -/
theorem gammaSplit_rightBadStepSupAnnulus_le
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ C : ℝ) (hC : 0 ≤ C)
    (hdet : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
      ∀ ω x y, |(M ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j))
    (i j : ι) (hi : 𝒯.deg i < γ) (hji : 𝒯.deg j < 𝒯.deg i)
    (β δ : ℝ) (hβ : β = 𝒯.deg i - 𝒯.deg j) (_hδ : 0 < δ)
    (hδgap : ∀ k, 𝒯.deg j < 𝒯.deg k → 𝒯.deg k < 𝒯.deg i →
      δ ≤ (𝒯.deg i - 𝒯.deg k) / 2) (ω : Ω) (N l : ℕ) :
    gammaSplitRightBadStepSupAnnulus S M D i j N (N + l) ω ≤
      ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
        ENNReal.ofReal (C ^ 2 * 24 ^ (𝒯.deg k - 𝒯.deg j) *
          4 ^ (𝒯.deg i - 𝒯.deg k)) *
          dyadicBase N ^ β * dyadicBase l ^ δ := by
  exact gammaSplit_rightBadStepSupAnnulus_le_aux S hbox M D γ C hC hdet i j hi hji
    β δ hβ _hδ hδgap ω N l

end RegularityStructures

end
