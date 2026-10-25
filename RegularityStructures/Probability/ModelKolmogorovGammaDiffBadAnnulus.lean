/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaDiffRelativeSource
import Mathlib.Tactic.Linarith
public import Mathlib.Order.CompletePartialOrder

/-!
# Pathwise annular bounds for the difference `DΓ × DΓ` channel

The difference of two Chen products is a sum of two terms.  When both
coordinates belong to `DΓ`, one factor is controlled pathwise by the
deterministic model estimate and the other by the pathwise difference
estimate.  The positive degree of the fine factor gives the geometric
endpoint reserve.  This is the difference analogue of the pathwise part of
Hairer [Hai14, (2.17)].
-/

@[expose] public noncomputable section

open Set
open scoped ENNReal

namespace RegularityStructures

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  {𝒯 : RegularityStructure ι}

private theorem gammaDiffBad_left_geometry
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

private theorem gammaDiffBad_right_geometry
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

private theorem gammaDiffBad_ofReal_mul_rpow_scale_le
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

theorem gammaDiffBadLeftStepSupAnnulus_le
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ C d r : ℝ) (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hdet₁ : ∀ a b, (a, b) ∈ D → 𝒯.deg a < γ →
      𝒯.deg b < 𝒯.deg a → ∀ ω u v,
      |(M₁ ω).gammaMap v u (Pi.single a 1) b| ≤
        C * parabolicSemigroup.scaleDist v u ^ (𝒯.deg a - 𝒯.deg b))
    (hdet₂ : ∀ a b, (a, b) ∈ D → 𝒯.deg a < γ →
      𝒯.deg b < 𝒯.deg a → ∀ ω u v,
      |(M₂ ω).gammaMap v u (Pi.single a 1) b| ≤
        C * parabolicSemigroup.scaleDist v u ^ (𝒯.deg a - 𝒯.deg b))
    (hdiff : ∀ a b, (a, b) ∈ D → 𝒯.deg a < γ →
      𝒯.deg b < 𝒯.deg a → ∀ ω u v,
      |(M₁ ω).gammaMap v u (Pi.single a 1) b -
        (M₂ ω).gammaMap v u (Pi.single a 1) b| ≤
        d * parabolicSemigroup.scaleDist v u ^ (𝒯.deg a - 𝒯.deg b))
    (i j : ι) (hi : 𝒯.deg i < γ) (hij : 𝒯.deg j < 𝒯.deg i)
    (β : ℝ) (hβ : β = 𝒯.deg i - 𝒯.deg j) (_hr : 0 < r)
    (hgap : ∀ k, 𝒯.deg j < 𝒯.deg k → 𝒯.deg k < 𝒯.deg i →
      r ≤ 𝒯.deg k - 𝒯.deg j)
    (ω : Ω) (N l : ℕ) :
    gammaDiffBadLeftAnnulusStepSup S M₁ M₂ D i j N (N + l) ω ≤
      ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
        2 * ENNReal.ofReal (C * d * 24 ^ (𝒯.deg i - 𝒯.deg k) *
          4 ^ (𝒯.deg k - 𝒯.deg j)) *
          dyadicBase N ^ β * dyadicBase l ^ r := by
  classical
  unfold gammaDiffBadLeftAnnulusStepSup
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
    have hgeom := gammaDiffBad_left_geometry S hbox N (N + l)
      (Nat.le_add_right N l) a b hnear
    have hbad := gammaSplitLeftBadTermDiff_enorm_le
      (M₁ ω) (M₂ ω) D γ C d hC hd i j
      (hsParabolicCellRepresentative S (N + l + 1) b)
      (hsParabolicCellRepresentative S (N + l + 1) a)
      (hsParabolicCellRepresentative S (N + l)
        (hsParabolicCellParent S (N + l) a)) hi hij
      (fun c e hde hci hej u v => hdet₁ c e hde hci hej ω u v)
      (fun c e hde hci hej u v => hdet₂ c e hde hci hej ω u v)
      (fun c e hde hci hej u v => hdiff c e hde hci hej ω u v)
    calc
      _ ≤ ∑ k ∈ gammaBadIntermediate 𝒯 D i j, (
          ENNReal.ofReal (d * parabolicSemigroup.scaleDist
            (hsParabolicCellRepresentative S (N + l + 1) a)
            (hsParabolicCellRepresentative S (N + l + 1) b) ^
              (𝒯.deg i - 𝒯.deg k)) *
            ENNReal.ofReal (C * parabolicSemigroup.scaleDist
            (hsParabolicCellRepresentative S (N + l)
              (hsParabolicCellParent S (N + l) a))
            (hsParabolicCellRepresentative S (N + l + 1) a) ^
              (𝒯.deg k - 𝒯.deg j)) +
          ENNReal.ofReal (C * parabolicSemigroup.scaleDist
            (hsParabolicCellRepresentative S (N + l + 1) a)
            (hsParabolicCellRepresentative S (N + l + 1) b) ^
              (𝒯.deg i - 𝒯.deg k)) *
            ENNReal.ofReal (d * parabolicSemigroup.scaleDist
            (hsParabolicCellRepresentative S (N + l)
              (hsParabolicCellParent S (N + l) a))
            (hsParabolicCellRepresentative S (N + l + 1) a) ^
              (𝒯.deg k - 𝒯.deg j))) := hbad
      _ ≤ ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
          2 * ENNReal.ofReal (C * d * 24 ^ (𝒯.deg i - 𝒯.deg k) *
            4 ^ (𝒯.deg k - 𝒯.deg j)) *
            dyadicBase N ^ β * dyadicBase l ^ r := by
        refine Finset.sum_le_sum ?_
        intro k hk
        have hmem := Finset.mem_filter.mp (Finset.mem_filter.mp hk).1
        have hjk : 𝒯.deg j < 𝒯.deg k := hmem.2.1
        have hki : 𝒯.deg k < 𝒯.deg i := hmem.2.2
        have hscale := gammaDiffBad_ofReal_mul_rpow_scale_le
          (C := C * d) (A := 24) (B := 4)
          (a := 𝒯.deg i - 𝒯.deg k)
          (b := 𝒯.deg k - 𝒯.deg j) (r := 1) (N := N) (l := l)
          (mul_nonneg hC hd) (by norm_num) (by norm_num)
          (parabolicNorm_nonneg _) (parabolicNorm_nonneg _)
          (by linarith) (by linarith)
          (by simpa [div_eq_mul_inv] using hgeom.1)
          (by simpa [div_eq_mul_inv] using hgeom.2)
        have hscale'' := hscale
        simp only [pow_one, Nat.cast_one, one_mul] at hscale''
        have hdegree : β = (𝒯.deg i - 𝒯.deg k) +
            (𝒯.deg k - 𝒯.deg j) := by rw [hβ]; ring
        have hfine : dyadicBase l ^ (𝒯.deg k - 𝒯.deg j) ≤
            dyadicBase l ^ r := by
          apply ENNReal.rpow_le_rpow_of_exponent_ge
          · unfold dyadicBase
            exact pow_le_one₀ (by positivity) (by norm_num)
          · exact hgap k hjk hki
        have hbase :
            ENNReal.ofReal (C * d * 24 ^ (𝒯.deg i - 𝒯.deg k) *
              4 ^ (𝒯.deg k - 𝒯.deg j)) *
              dyadicBase N ^ β * dyadicBase l ^
                (𝒯.deg k - 𝒯.deg j) =
            ENNReal.ofReal (C * d * 24 ^ (𝒯.deg i - 𝒯.deg k) *
              4 ^ (𝒯.deg k - 𝒯.deg j)) *
              dyadicBase N ^ ((𝒯.deg i - 𝒯.deg k) +
                (𝒯.deg k - 𝒯.deg j)) * dyadicBase l ^
                (𝒯.deg k - 𝒯.deg j) := by rw [hdegree]
        have hprod₁ :
            ENNReal.ofReal (d * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l + 1) a)
              (hsParabolicCellRepresentative S (N + l + 1) b) ^
                (𝒯.deg i - 𝒯.deg k)) *
              ENNReal.ofReal (C * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) a))
              (hsParabolicCellRepresentative S (N + l + 1) a) ^
                (𝒯.deg k - 𝒯.deg j)) =
            ENNReal.ofReal (C * d *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l + 1) a)
                (hsParabolicCellRepresentative S (N + l + 1) b) ^
                  (𝒯.deg i - 𝒯.deg k) *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l)
                  (hsParabolicCellParent S (N + l) a))
                (hsParabolicCellRepresentative S (N + l + 1) a) ^
                  (𝒯.deg k - 𝒯.deg j)) := by
          have hfirst : 0 ≤ d * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l + 1) a)
              (hsParabolicCellRepresentative S (N + l + 1) b) ^
                (𝒯.deg i - 𝒯.deg k) :=
            mul_nonneg hd (Real.rpow_nonneg
              (parabolicSemigroup.scaleDist_nonneg _ _) _)
          rw [← ENNReal.ofReal_mul hfirst]
          congr 1
          ring_nf
        have hprod₂ :
            ENNReal.ofReal (C * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l + 1) a)
              (hsParabolicCellRepresentative S (N + l + 1) b) ^
                (𝒯.deg i - 𝒯.deg k)) *
              ENNReal.ofReal (d * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) a))
              (hsParabolicCellRepresentative S (N + l + 1) a) ^
                (𝒯.deg k - 𝒯.deg j)) =
            ENNReal.ofReal (C * d *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l + 1) a)
                (hsParabolicCellRepresentative S (N + l + 1) b) ^
                  (𝒯.deg i - 𝒯.deg k) *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l)
                  (hsParabolicCellParent S (N + l) a))
                (hsParabolicCellRepresentative S (N + l + 1) a) ^
                  (𝒯.deg k - 𝒯.deg j)) := by
          rw [← ENNReal.ofReal_mul]
          · congr 1
            ring
          · exact mul_nonneg hC (Real.rpow_nonneg
              (parabolicSemigroup.scaleDist_nonneg _ _) _)
        have hone :
            ENNReal.ofReal (C * d *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l + 1) a)
                (hsParabolicCellRepresentative S (N + l + 1) b) ^
                  (𝒯.deg i - 𝒯.deg k) *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l)
                  (hsParabolicCellParent S (N + l) a))
                (hsParabolicCellRepresentative S (N + l + 1) a) ^
                  (𝒯.deg k - 𝒯.deg j)) ≤
            ENNReal.ofReal (C * d * 24 ^ (𝒯.deg i - 𝒯.deg k) *
              4 ^ (𝒯.deg k - 𝒯.deg j)) *
              dyadicBase N ^ ((𝒯.deg i - 𝒯.deg k) +
                (𝒯.deg k - 𝒯.deg j)) * dyadicBase l ^
                (𝒯.deg k - 𝒯.deg j) := hscale''
        have hone' :
            ENNReal.ofReal (C * d *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l + 1) a)
                (hsParabolicCellRepresentative S (N + l + 1) b) ^
                  (𝒯.deg i - 𝒯.deg k) *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l)
                  (hsParabolicCellParent S (N + l) a))
                (hsParabolicCellRepresentative S (N + l + 1) a) ^
                  (𝒯.deg k - 𝒯.deg j)) ≤
            ENNReal.ofReal (C * d * 24 ^ (𝒯.deg i - 𝒯.deg k) *
              4 ^ (𝒯.deg k - 𝒯.deg j)) *
              dyadicBase N ^ β * dyadicBase l ^ r := by
          calc
            _ ≤ ENNReal.ofReal (C * d * 24 ^ (𝒯.deg i - 𝒯.deg k) *
                4 ^ (𝒯.deg k - 𝒯.deg j)) *
                dyadicBase N ^ ((𝒯.deg i - 𝒯.deg k) +
                  (𝒯.deg k - 𝒯.deg j)) * dyadicBase l ^
                  (𝒯.deg k - 𝒯.deg j) := hone
            _ = ENNReal.ofReal (C * d * 24 ^ (𝒯.deg i - 𝒯.deg k) *
                4 ^ (𝒯.deg k - 𝒯.deg j)) * dyadicBase N ^ β *
                dyadicBase l ^ (𝒯.deg k - 𝒯.deg j) := hbase.symm
            _ ≤ _ := by gcongr
        calc
          _ ≤ (ENNReal.ofReal (C * d * 24 ^ (𝒯.deg i - 𝒯.deg k) *
                4 ^ (𝒯.deg k - 𝒯.deg j)) * dyadicBase N ^ β *
                dyadicBase l ^ r) +
              (ENNReal.ofReal (C * d * 24 ^ (𝒯.deg i - 𝒯.deg k) *
                4 ^ (𝒯.deg k - 𝒯.deg j)) * dyadicBase N ^ β *
                dyadicBase l ^ r) := add_le_add
            (hprod₁ ▸ (hone' : _)) (hprod₂ ▸ (hone' : _))
          _ = 2 * ENNReal.ofReal (C * d * 24 ^ (𝒯.deg i - 𝒯.deg k) *
                4 ^ (𝒯.deg k - 𝒯.deg j)) * dyadicBase N ^ β *
                dyadicBase l ^ r := by ring
  · simp only [ite_eq_right hnear]
    exact bot_le

theorem gammaDiffBadRightStepSupAnnulus_le
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ C d r : ℝ) (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hdet₁ : ∀ a b, (a, b) ∈ D → 𝒯.deg a < γ →
      𝒯.deg b < 𝒯.deg a → ∀ ω u v,
      |(M₁ ω).gammaMap v u (Pi.single a 1) b| ≤
        C * parabolicSemigroup.scaleDist v u ^ (𝒯.deg a - 𝒯.deg b))
    (hdet₂ : ∀ a b, (a, b) ∈ D → 𝒯.deg a < γ →
      𝒯.deg b < 𝒯.deg a → ∀ ω u v,
      |(M₂ ω).gammaMap v u (Pi.single a 1) b| ≤
        C * parabolicSemigroup.scaleDist v u ^ (𝒯.deg a - 𝒯.deg b))
    (hdiff : ∀ a b, (a, b) ∈ D → 𝒯.deg a < γ →
      𝒯.deg b < 𝒯.deg a → ∀ ω u v,
      |(M₁ ω).gammaMap v u (Pi.single a 1) b -
        (M₂ ω).gammaMap v u (Pi.single a 1) b| ≤
        d * parabolicSemigroup.scaleDist v u ^ (𝒯.deg a - 𝒯.deg b))
    (i j : ι) (hi : 𝒯.deg i < γ) (hij : 𝒯.deg j < 𝒯.deg i)
    (β : ℝ) (hβ : β = 𝒯.deg i - 𝒯.deg j) (_hr : 0 < r)
    (hgap : ∀ k, 𝒯.deg j < 𝒯.deg k → 𝒯.deg k < 𝒯.deg i →
      r ≤ 𝒯.deg i - 𝒯.deg k)
    (ω : Ω) (N l : ℕ) :
    gammaDiffBadRightAnnulusStepSup S M₁ M₂ D i j N (N + l) ω ≤
      ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
        2 * ENNReal.ofReal (C * d * 24 ^ (𝒯.deg k - 𝒯.deg j) *
          4 ^ (𝒯.deg i - 𝒯.deg k)) *
          dyadicBase N ^ β * dyadicBase l ^ r := by
  classical
  unfold gammaDiffBadRightAnnulusStepSup
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
    have hgeom := gammaDiffBad_right_geometry S hbox N (N + l)
      (Nat.le_add_right N l) a b hnear
    have hbad := gammaSplitRightBadTermDiff_enorm_le
      (M₁ ω) (M₂ ω) D γ C d hC hd i j
      (hsParabolicCellRepresentative S (N + l)
        (hsParabolicCellParent S (N + l) a))
      (hsParabolicCellRepresentative S (N + l + 1) b)
      (hsParabolicCellRepresentative S (N + l)
        (hsParabolicCellParent S (N + l) b)) hi hij
      (fun c e hde hci hej u v => hdet₁ c e hde hci hej ω u v)
      (fun c e hde hci hej u v => hdet₂ c e hde hci hej ω u v)
      (fun c e hde hci hej u v => hdiff c e hde hci hej ω u v)
    calc
      _ ≤ ∑ k ∈ gammaBadIntermediate 𝒯 D i j, (
          ENNReal.ofReal (d * parabolicSemigroup.scaleDist
            (hsParabolicCellRepresentative S (N + l + 1) b)
            (hsParabolicCellRepresentative S (N + l)
              (hsParabolicCellParent S (N + l) b)) ^
              (𝒯.deg i - 𝒯.deg k)) *
            ENNReal.ofReal (C * parabolicSemigroup.scaleDist
            (hsParabolicCellRepresentative S (N + l)
              (hsParabolicCellParent S (N + l) a))
            (hsParabolicCellRepresentative S (N + l + 1) b) ^
              (𝒯.deg k - 𝒯.deg j)) +
          ENNReal.ofReal (C * parabolicSemigroup.scaleDist
            (hsParabolicCellRepresentative S (N + l + 1) b)
            (hsParabolicCellRepresentative S (N + l)
              (hsParabolicCellParent S (N + l) b)) ^
              (𝒯.deg i - 𝒯.deg k)) *
            ENNReal.ofReal (d * parabolicSemigroup.scaleDist
            (hsParabolicCellRepresentative S (N + l)
              (hsParabolicCellParent S (N + l) a))
            (hsParabolicCellRepresentative S (N + l + 1) b) ^
              (𝒯.deg k - 𝒯.deg j))) := hbad
      _ ≤ ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
          2 * ENNReal.ofReal (C * d * 24 ^ (𝒯.deg k - 𝒯.deg j) *
            4 ^ (𝒯.deg i - 𝒯.deg k)) *
            dyadicBase N ^ β * dyadicBase l ^ r := by
        refine Finset.sum_le_sum ?_
        intro k hk
        have hmem := Finset.mem_filter.mp (Finset.mem_filter.mp hk).1
        have hjk : 𝒯.deg j < 𝒯.deg k := hmem.2.1
        have hki : 𝒯.deg k < 𝒯.deg i := hmem.2.2
        have hscale := gammaDiffBad_ofReal_mul_rpow_scale_le
          (C := C * d) (A := 24) (B := 4)
          (d := parabolicNorm
            (hsParabolicCellRepresentative S (N + l)
              (hsParabolicCellParent S (N + l) a) -
            hsParabolicCellRepresentative S (N + l + 1) b))
          (e := parabolicNorm
            (hsParabolicCellRepresentative S (N + l + 1) b -
            hsParabolicCellRepresentative S (N + l)
              (hsParabolicCellParent S (N + l) b)))
          (a := 𝒯.deg k - 𝒯.deg j)
          (b := 𝒯.deg i - 𝒯.deg k) (r := 1) (N := N) (l := l)
          (mul_nonneg hC hd) (by norm_num) (by norm_num)
          (parabolicNorm_nonneg _) (parabolicNorm_nonneg _)
          (by linarith) (by linarith)
          (by
            have hc : parabolicNorm
                (hsParabolicCellRepresentative S (N + l)
                  (hsParabolicCellParent S (N + l) a) -
                hsParabolicCellRepresentative S (N + l + 1) b) ≤
                24 / (2 : ℝ) ^ N := by
              exact hnear.trans (by gcongr; norm_num)
            simpa [div_eq_mul_inv] using hc)
          (by
            simpa [parabolicNorm_sub_comm, div_eq_mul_inv] using hgeom.2)
        simp only [pow_one, Nat.cast_one, one_mul] at hscale
        have hdegree : β = (𝒯.deg k - 𝒯.deg j) +
            (𝒯.deg i - 𝒯.deg k) := by rw [hβ]; ring
        rw [← hdegree] at hscale
        have hfine : dyadicBase l ^ (𝒯.deg i - 𝒯.deg k) ≤
            dyadicBase l ^ r := by
          apply ENNReal.rpow_le_rpow_of_exponent_ge
          · unfold dyadicBase
            exact pow_le_one₀ (by positivity) (by norm_num)
          · exact hgap k hjk hki
        have hscale' := hscale.trans (by gcongr)
        have hprod₁ :
            ENNReal.ofReal (d * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l + 1) b)
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) b)) ^
                (𝒯.deg i - 𝒯.deg k)) *
              ENNReal.ofReal (C * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) a))
              (hsParabolicCellRepresentative S (N + l + 1) b) ^
                (𝒯.deg k - 𝒯.deg j)) =
            ENNReal.ofReal (C * d *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l)
                  (hsParabolicCellParent S (N + l) a))
                (hsParabolicCellRepresentative S (N + l + 1) b) ^
                  (𝒯.deg k - 𝒯.deg j) *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l + 1) b)
                (hsParabolicCellRepresentative S (N + l)
                  (hsParabolicCellParent S (N + l) b)) ^
                  (𝒯.deg i - 𝒯.deg k)) := by
          have hfirst : 0 ≤ d * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l + 1) b)
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) b)) ^
                (𝒯.deg i - 𝒯.deg k) :=
            mul_nonneg hd (Real.rpow_nonneg
              (parabolicSemigroup.scaleDist_nonneg _ _) _)
          rw [← ENNReal.ofReal_mul hfirst]
          congr 1
          ring
        have hprod₂ :
            ENNReal.ofReal (C * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l + 1) b)
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) b)) ^
                (𝒯.deg i - 𝒯.deg k)) *
              ENNReal.ofReal (d * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) a))
              (hsParabolicCellRepresentative S (N + l + 1) b) ^
                (𝒯.deg k - 𝒯.deg j)) =
            ENNReal.ofReal (C * d *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l)
                  (hsParabolicCellParent S (N + l) a))
                (hsParabolicCellRepresentative S (N + l + 1) b) ^
                  (𝒯.deg k - 𝒯.deg j) *
              parabolicSemigroup.scaleDist
                (hsParabolicCellRepresentative S (N + l + 1) b)
                (hsParabolicCellRepresentative S (N + l)
                  (hsParabolicCellParent S (N + l) b)) ^
                  (𝒯.deg i - 𝒯.deg k)) := by
          rw [← ENNReal.ofReal_mul]
          · congr 1
            ring_nf
          · exact mul_nonneg hC (Real.rpow_nonneg
              (parabolicSemigroup.scaleDist_nonneg _ _) _)
        have hterm₁ :
            ENNReal.ofReal (d * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l + 1) b)
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) b)) ^
                (𝒯.deg i - 𝒯.deg k)) *
              ENNReal.ofReal (C * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) a))
              (hsParabolicCellRepresentative S (N + l + 1) b) ^
                (𝒯.deg k - 𝒯.deg j)) ≤
            ENNReal.ofReal (C * d * 24 ^ (𝒯.deg k - 𝒯.deg j) *
              4 ^ (𝒯.deg i - 𝒯.deg k)) * dyadicBase N ^ β *
              dyadicBase l ^ r := by
          calc
            _ = ENNReal.ofReal (C * d *
                parabolicSemigroup.scaleDist
                  (hsParabolicCellRepresentative S (N + l)
                    (hsParabolicCellParent S (N + l) a))
                  (hsParabolicCellRepresentative S (N + l + 1) b) ^
                    (𝒯.deg k - 𝒯.deg j) *
                parabolicSemigroup.scaleDist
                  (hsParabolicCellRepresentative S (N + l + 1) b)
                  (hsParabolicCellRepresentative S (N + l)
                    (hsParabolicCellParent S (N + l) b)) ^
                    (𝒯.deg i - 𝒯.deg k)) := hprod₁
            _ ≤ ENNReal.ofReal (C * d * 24 ^ (𝒯.deg k - 𝒯.deg j) *
                4 ^ (𝒯.deg i - 𝒯.deg k)) * dyadicBase N ^ β *
                dyadicBase l ^ (𝒯.deg i - 𝒯.deg k) := by
              simpa [parabolicSemigroup] using hscale'
            _ ≤ _ := by gcongr
        have hterm₂ :
            ENNReal.ofReal (C * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l + 1) b)
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) b)) ^
                (𝒯.deg i - 𝒯.deg k)) *
              ENNReal.ofReal (d * parabolicSemigroup.scaleDist
              (hsParabolicCellRepresentative S (N + l)
                (hsParabolicCellParent S (N + l) a))
              (hsParabolicCellRepresentative S (N + l + 1) b) ^
                (𝒯.deg k - 𝒯.deg j)) ≤
            ENNReal.ofReal (C * d * 24 ^ (𝒯.deg k - 𝒯.deg j) *
              4 ^ (𝒯.deg i - 𝒯.deg k)) * dyadicBase N ^ β *
              dyadicBase l ^ r := by
          calc
            _ = ENNReal.ofReal (C * d *
                parabolicSemigroup.scaleDist
                  (hsParabolicCellRepresentative S (N + l)
                    (hsParabolicCellParent S (N + l) a))
                  (hsParabolicCellRepresentative S (N + l + 1) b) ^
                    (𝒯.deg k - 𝒯.deg j) *
                parabolicSemigroup.scaleDist
                  (hsParabolicCellRepresentative S (N + l + 1) b)
                  (hsParabolicCellRepresentative S (N + l)
                    (hsParabolicCellParent S (N + l) b)) ^
                    (𝒯.deg i - 𝒯.deg k)) := hprod₂
            _ ≤ ENNReal.ofReal (C * d * 24 ^ (𝒯.deg k - 𝒯.deg j) *
                4 ^ (𝒯.deg i - 𝒯.deg k)) * dyadicBase N ^ β *
                dyadicBase l ^ (𝒯.deg i - 𝒯.deg k) := by
              simpa [parabolicSemigroup] using hscale'
            _ ≤ _ := by gcongr
        calc
          _ ≤ (ENNReal.ofReal (C * d * 24 ^ (𝒯.deg k - 𝒯.deg j) *
                4 ^ (𝒯.deg i - 𝒯.deg k)) * dyadicBase N ^ β *
                dyadicBase l ^ r) +
              (ENNReal.ofReal (C * d * 24 ^ (𝒯.deg k - 𝒯.deg j) *
                4 ^ (𝒯.deg i - 𝒯.deg k)) * dyadicBase N ^ β *
                dyadicBase l ^ r) := add_le_add
            hterm₁ hterm₂
          _ = 2 * ENNReal.ofReal (C * d * 24 ^ (𝒯.deg k - 𝒯.deg j) *
                4 ^ (𝒯.deg i - 𝒯.deg k)) * dyadicBase N ^ β *
                dyadicBase l ^ r := by ring
  · simp only [ite_eq_right hnear]
    exact bot_le

end RegularityStructures

end
