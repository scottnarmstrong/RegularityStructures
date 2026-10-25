/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovHSCompactParent
public import RegularityStructures.Probability.ModelKolmogorovHSFiniteMoment
public import RegularityStructures.Probability.ModelKolmogorovHSCompactTopology
public import RegularityStructures.Probability.KolmogorovChentsovSupremum
import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Order.CompletePartialOrder

/-!
# Product-net increments for Gamma chaining

At a fixed parabolic scale the two base points are selected independently from
the occupied cells of the compact.  The definitions below retain that product
net explicitly.  Their moment lemmas are the finite, source-facing part of the
annular argument: no model norm or random bound is used as a premise.
-/

@[expose] public noncomputable section

open MeasureTheory
open Filter
open scoped ENNReal NNReal Topology

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

abbrev gammaCell (S : Set ParabolicSpace) (n : ℕ) :=
  HSParabolicOccupiedCell S n

/-- The supremum of the field on the product of two occupied cell nets. -/
def gammaProductCellSup (S : Set ParabolicSpace)
    (F : S → S → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
    ⨆ i : gammaCell S n, ⨆ j : gammaCell S n,
    if parabolicNorm ((hsParabolicCellRepresentative S n i : ParabolicSpace) -
        hsParabolicCellRepresentative S n j) ≤ 20 / (2 : ℝ) ^ n then
      ‖F (hsParabolicCellRepresentative S n i)
        (hsParabolicCellRepresentative S n j) ω‖ₑ
    else 0

/-- The first-base-point parent increment on the product net. -/
def gammaProductLeftStepSup (S : Set ParabolicSpace)
    (F : S → S → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ i : gammaCell S (n + 1), ⨆ j : gammaCell S (n + 1),
    ‖F (hsParabolicCellRepresentative S n (hsParabolicCellParent S n i))
        (hsParabolicCellRepresentative S (n + 1) j) ω -
      F (hsParabolicCellRepresentative S (n + 1) i)
        (hsParabolicCellRepresentative S (n + 1) j) ω‖ₑ

/-- The second-base-point parent increment on the product net. -/
def gammaProductRightStepSup (S : Set ParabolicSpace)
    (F : S → S → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ i : gammaCell S (n + 1), ⨆ j : gammaCell S (n + 1),
    ‖F (hsParabolicCellRepresentative S n (hsParabolicCellParent S n i))
        (hsParabolicCellRepresentative S n (hsParabolicCellParent S n j)) ω -
      F (hsParabolicCellRepresentative S n (hsParabolicCellParent S n i))
        (hsParabolicCellRepresentative S (n + 1) j) ω‖ₑ

private theorem gammaProduct_cellSup_aemeasurable
    (S : Set ParabolicSpace) (F : S → S → Ω → ℝ)
    (hmeas : ∀ x y, AEMeasurable (F x y) P) (n : ℕ) :
    AEMeasurable (gammaProductCellSup S F n) P := by
  unfold gammaProductCellSup
  apply AEMeasurable.iSup
  intro i
  apply AEMeasurable.iSup
  intro j
  split_ifs
  · exact (hmeas _ _).enorm
  · exact aemeasurable_const

theorem gammaProduct_card_le (S : Set ParabolicSpace) (n : ℕ) :
    (Fintype.card (gammaCell S (n + 1)) : ℝ≥0∞) ^ 2 ≤
      (512 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞) ^ (10 * n) := by
  have h := card_hsParabolicOccupiedCell_le S (n + 1)
  have h' : Fintype.card (gammaCell S (n + 1)) ≤ 512 * 2 ^ (5 * n) := by
    rw [show 16 * 2 ^ (5 * (n + 1)) = 512 * 2 ^ (5 * n) by
      rw [Nat.mul_add, pow_add]
      ring] at h
    exact h
  have h'' : (Fintype.card (gammaCell S (n + 1)) : ℝ≥0∞) ≤
      (512 : ℝ≥0∞) * 2 ^ (5 * n) := by exact_mod_cast h'
  calc
    _ ≤ ((512 : ℝ≥0∞) * 2 ^ (5 * n)) ^ 2 := pow_le_pow_left' h'' 2
    _ = (512 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞) ^ (10 * n) := by
      rw [mul_pow, ← pow_mul]
      congr 2
      omega

/-!
The next three lemmas use the source estimates at exactly the representative
pairs selected by the net.  The endpoint estimates are kept separate because
the later telescoping proof must preserve both Chen channels.
-/

theorem gammaProductCellSup_moment_le
    (S : Set ParabolicSpace)
    (F : S → S → Ω → ℝ)
    (hmeas : ∀ x y, AEMeasurable (F x y) P)
    {p : ℕ} (hp : p ≠ 0) {q ε : ℝ} (hq : 0 ≤ q) {M : ℝ≥0∞}
    (hpair : ∀ x y : S, parabolicNorm ((x : ParabolicSpace) - y) ≤ ε →
      ∫⁻ ω, ‖F x y ω‖ₑ ^ p ∂P ≤
        M * ENNReal.ofReal (parabolicNorm ((x : ParabolicSpace) - y)) ^ q)
    (n : ℕ) (hn : 20 / (2 : ℝ) ^ n ≤ ε) :
    ∫⁻ ω, gammaProductCellSup S F n ω ^ p ∂P ≤
      (Fintype.card (gammaCell S n) : ℝ≥0∞) ^ 2 *
        (M * ENNReal.ofReal (20 / (2 : ℝ) ^ n) ^ q) := by
  classical
  have hm (z : gammaCell S n × gammaCell S n) :
      ∫⁻ ω, (if parabolicNorm
          ((hsParabolicCellRepresentative S n z.1 : ParabolicSpace) -
            hsParabolicCellRepresentative S n z.2) ≤ 20 / (2 : ℝ) ^ n then
          ‖F (hsParabolicCellRepresentative S n z.1)
            (hsParabolicCellRepresentative S n z.2) ω‖ₑ else 0) ^ p ∂P ≤
        M * ENNReal.ofReal (20 / (2 : ℝ) ^ n) ^ q := by
    split_ifs with hd
    · exact (hpair _ _ (hd.trans hn)).trans (by gcongr)
    · simp [hp]
  have hmeas' (z : gammaCell S n × gammaCell S n) :
      AEMeasurable (fun ω =>
        if parabolicNorm
            ((hsParabolicCellRepresentative S n z.1 : ParabolicSpace) -
              hsParabolicCellRepresentative S n z.2) ≤ 20 / (2 : ℝ) ^ n then
          ‖F (hsParabolicCellRepresentative S n z.1)
            (hsParabolicCellRepresentative S n z.2) ω‖ₑ else 0) P := by
    split_ifs
    · exact (hmeas _ _).enorm
    · exact aemeasurable_const
  have hsup := finiteSup_lintegral_pow_le_card_mul hp hmeas' hm
  calc
    _ ≤ (Fintype.card (gammaCell S n) : ℝ≥0∞) *
        Fintype.card (gammaCell S n) *
          (M * ENNReal.ofReal (20 / (2 : ℝ) ^ n) ^ q) := by
      simpa only [gammaProductCellSup, iSup_prod, Fintype.card_prod,
        Nat.cast_mul, ENNReal.coe_mul, ENNReal.coe_pow] using hsup
    _ = _ := by rw [pow_two]

/-!
The parent-child decomposition is the deterministic telescope used to pass from
the finite product nets to a genuine two-base-point field.  The orientation of
the right-step definition is chosen so that the intermediate value has the
fine first endpoint and the fine second endpoint.
-/

omit [MeasurableSpace Ω] in
theorem gammaProductCellApprox_step_le
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Set.Icc (0 : ℝ) 1)
    (F : S → S → Ω → ℝ) (n : ℕ) (x y : S) (ω : Ω) :
    ‖F (hsParabolicCellApprox S n x) (hsParabolicCellApprox S n y) ω -
        F (hsParabolicCellApprox S (n + 1) x)
          (hsParabolicCellApprox S (n + 1) y) ω‖ₑ ≤
      gammaProductLeftStepSup S F n ω +
        gammaProductRightStepSup S F n ω := by
  have hx := hsParabolicCellParent_at S hbox n x
  have hy := hsParabolicCellParent_at S hbox n y
  let xn : S := hsParabolicCellApprox S n x
  let yn : S := hsParabolicCellApprox S n y
  let xnext : S := hsParabolicCellApprox S (n + 1) x
  let ynext : S := hsParabolicCellApprox S (n + 1) y
  have hx' : hsParabolicCellRepresentative S n
      (hsParabolicCellParent S n
        ⟨hsParabolicCellIndex (n + 1) x, x, rfl⟩) = xn := by
    simpa [xn, hsParabolicCellApprox] using congrArg
      (fun i : gammaCell S n => hsParabolicCellRepresentative S n i) hx
  have hy' : hsParabolicCellRepresentative S n
      (hsParabolicCellParent S n
        ⟨hsParabolicCellIndex (n + 1) y, y, rfl⟩) = yn := by
    simpa [yn, hsParabolicCellApprox] using congrArg
      (fun i : gammaCell S n => hsParabolicCellRepresentative S n i) hy
  have hleft : ‖F xn ynext ω - F xnext ynext ω‖ₑ ≤
      gammaProductLeftStepSup S F n ω := by
    let i : gammaCell S (n + 1) :=
      ⟨hsParabolicCellIndex (n + 1) x, x, rfl⟩
    let j : gammaCell S (n + 1) :=
      ⟨hsParabolicCellIndex (n + 1) y, y, rfl⟩
    have hi : hsParabolicCellRepresentative S (n + 1) i = xnext := rfl
    have hj : hsParabolicCellRepresentative S (n + 1) j = ynext := rfl
    have hparent : hsParabolicCellRepresentative S n (hsParabolicCellParent S n i) = xn := by
      exact hx'
    rw [gammaProductLeftStepSup]
    rw [← hi, ← hj, ← hparent]
    exact le_iSup_of_le i (le_iSup_of_le j le_rfl)
  have hright : ‖F xn yn ω - F xn ynext ω‖ₑ ≤
      gammaProductRightStepSup S F n ω := by
    let i : gammaCell S (n + 1) :=
      ⟨hsParabolicCellIndex (n + 1) x, x, rfl⟩
    let j : gammaCell S (n + 1) :=
      ⟨hsParabolicCellIndex (n + 1) y, y, rfl⟩
    have hi : hsParabolicCellRepresentative S (n + 1) i = xnext := rfl
    have hj : hsParabolicCellRepresentative S (n + 1) j = ynext := rfl
    have hparentx : hsParabolicCellRepresentative S n (hsParabolicCellParent S n i) = xn := by
      exact hx'
    have hparenty : hsParabolicCellRepresentative S n (hsParabolicCellParent S n j) = yn := by
      exact hy'
    rw [gammaProductRightStepSup]
    rw [← hj, ← hparentx, ← hparenty]
    exact le_iSup_of_le i (le_iSup_of_le j le_rfl)
  calc
    _ ≤ ‖F xn yn ω - F xn ynext ω‖ₑ +
        ‖F xn ynext ω - F xnext ynext ω‖ₑ := by
      rw [show F xn yn ω - F xnext ynext ω =
          (F xn yn ω - F xn ynext ω) +
            (F xn ynext ω - F xnext ynext ω) by ring]
      exact enorm_add_le _ _
    _ ≤ _ := add_le_add hright hleft
    _ = _ := by rw [add_comm]

theorem gammaProductCellApprox_distance_le
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (x y : S) :
    parabolicNorm ((hsParabolicCellApprox S n x : ParabolicSpace) -
        hsParabolicCellApprox S n y) ≤
      parabolicNorm ((x : ParabolicSpace) - y) + 8 / (2 : ℝ) ^ n := by
  have hx := hsParabolicCellApprox_error_le S hbox n x
  have hy := hsParabolicCellApprox_error_le S hbox n y
  calc
    _ = parabolicNorm (((hsParabolicCellApprox S n x : ParabolicSpace) - x) +
        ((x : ParabolicSpace) - y) + (y - hsParabolicCellApprox S n y)) := by
      congr 1
      abel
    _ ≤ parabolicNorm (((hsParabolicCellApprox S n x : ParabolicSpace) - x) +
        ((x : ParabolicSpace) - y)) +
        parabolicNorm (y - hsParabolicCellApprox S n y) := by
      exact parabolicNorm_add_le _ _
    _ ≤ parabolicNorm ((hsParabolicCellApprox S n x : ParabolicSpace) - x) +
        parabolicNorm ((x : ParabolicSpace) - y) +
          parabolicNorm (y - hsParabolicCellApprox S n y) := by
      gcongr
      exact parabolicNorm_add_le _ _
    _ ≤ _ := by
      have hy' : parabolicNorm (y -
          (hsParabolicCellApprox S n y : ParabolicSpace)) ≤ 4 / (2 : ℝ) ^ n := by
        rw [parabolicNorm_sub_comm]
        exact hy
      calc
        _ ≤ 4 / (2 : ℝ) ^ n + parabolicNorm ((x : ParabolicSpace) - y) +
            4 / (2 : ℝ) ^ n := by
          gcongr
        _ = parabolicNorm ((x : ParabolicSpace) - y) + 8 / (2 : ℝ) ^ n := by ring

theorem gammaProductCellApprox_distance_le_of_scale
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (x y : S)
    (hxy : parabolicNorm ((x : ParabolicSpace) - y) ≤ 1 / (2 : ℝ) ^ n) :
    parabolicNorm ((hsParabolicCellApprox S n x : ParabolicSpace) -
        hsParabolicCellApprox S n y) ≤ 20 / (2 : ℝ) ^ n := by
  have h := gammaProductCellApprox_distance_le S hbox n x y
  calc
    _ ≤ 1 / (2 : ℝ) ^ n + 8 / (2 : ℝ) ^ n :=
      h.trans (add_le_add hxy le_rfl)
    _ = 9 / (2 : ℝ) ^ n := by ring
    _ ≤ 20 / (2 : ℝ) ^ n := by gcongr; norm_num

omit [MeasurableSpace Ω] in
theorem gammaProductCellApprox_value_le
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Set.Icc (0 : ℝ) 1)
    (F : S → S → Ω → ℝ) (n : ℕ) (x y : S) (ω : Ω)
    (hxy : parabolicNorm ((x : ParabolicSpace) - y) ≤ 1 / (2 : ℝ) ^ n) :
    ‖F (hsParabolicCellApprox S n x)
        (hsParabolicCellApprox S n y) ω‖ₑ ≤
      gammaProductCellSup S F n ω := by
  let i : gammaCell S n := ⟨hsParabolicCellIndex n x, x, rfl⟩
  let j : gammaCell S n := ⟨hsParabolicCellIndex n y, y, rfl⟩
  have hi : hsParabolicCellRepresentative S n i = hsParabolicCellApprox S n x := rfl
  have hj : hsParabolicCellRepresentative S n j = hsParabolicCellApprox S n y := rfl
  have hd := gammaProductCellApprox_distance_le_of_scale S hbox n x y hxy
  rw [gammaProductCellSup]
  apply le_iSup_of_le i
  apply le_iSup_of_le j
  have hd' : parabolicNorm
      ((hsParabolicCellRepresentative S n i : ParabolicSpace) -
        hsParabolicCellRepresentative S n j) ≤ 20 / (2 : ℝ) ^ n := by
    simpa only [hi, hj] using hd
  rw [ite_eq_left hd']
  simpa only [hi, hj] using
    (le_refl (‖F (hsParabolicCellApprox S n x)
      (hsParabolicCellApprox S n y) ω‖ₑ))

private theorem gammaProduct_scale_product (n : ℕ) (q r : ℝ) (p : ℕ) :
    (2 : ℝ≥0∞) ^ (10 * n) * ENNReal.ofReal (20 / (2 : ℝ) ^ n) ^ q *
        dyadicBase n ^ (-r * p) =
      (20 : ℝ≥0∞) ^ q * dyadicBase n ^ (q - (p : ℝ) * r - 10) := by
  have hrad : ENNReal.ofReal (20 / (2 : ℝ) ^ n) = 20 * dyadicBase n := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by positivity),
      ENNReal.inv_pow]
    norm_num [dyadicBase]
  have hcard : (2 : ℝ≥0∞) ^ (10 * n) = dyadicBase n ^ (-(10 : ℝ)) := by
    rw [ENNReal.rpow_neg]
    change (2 : ℝ≥0∞) ^ (10 * n) = (dyadicBase n ^ ((10 : ℕ) : ℝ))⁻¹
    rw [ENNReal.rpow_natCast]
    simp [dyadicBase, ← pow_mul, mul_comm, ← ENNReal.inv_pow]
  rw [hrad, hcard,
    ENNReal.mul_rpow_of_ne_zero (by norm_num) (dyadicBase_pos n).ne' q]
  calc
    _ = (20 : ℝ≥0∞) ^ q *
        ((dyadicBase n ^ (-(10 : ℝ)) * dyadicBase n ^ q) *
          dyadicBase n ^ (-r * p)) := by ac_rfl
    _ = _ := by
      rw [← ENNReal.rpow_add _ _ (dyadicBase_pos n).ne' (dyadicBase_ne_top n),
        ← ENNReal.rpow_add _ _ (dyadicBase_pos n).ne' (dyadicBase_ne_top n)]
      congr 2
      ring

/-- The normalized value envelope on the product nets. -/
def gammaProductCellNormalisedSup (S : Set ParabolicSpace)
    (F : S → S → Ω → ℝ) (r : ℝ) (N : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ n : ℕ,
    gammaProductCellSup S F (N + n) ω * dyadicBase (N + n) ^ (-r)

theorem gammaProductCellNormalisedSup_aemeasurable
    (S : Set ParabolicSpace)
    (F : S → S → Ω → ℝ)
    (r : ℝ) (N : ℕ)
    (hmeas : ∀ x y, AEMeasurable (F x y) P) :
    AEMeasurable (gammaProductCellNormalisedSup S F r N) P := by
  unfold gammaProductCellNormalisedSup
  apply AEMeasurable.iSup
  intro n
  exact (gammaProduct_cellSup_aemeasurable S F hmeas (N + n)).mul_const _

omit [MeasurableSpace Ω] in
/-- Each product-net value is bounded by the normalized value envelope. -/
theorem gammaProductCellSup_le_normalisedSup
    (S : Set ParabolicSpace) (F : S → S → Ω → ℝ)
    (r : ℝ) (N n : ℕ) (ω : Ω) :
    gammaProductCellSup S F (N + n) ω ≤
      gammaProductCellNormalisedSup S F r N ω * dyadicBase (N + n) ^ r := by
  have hc : dyadicBase (N + n) ^ (-r) * dyadicBase (N + n) ^ r = 1 := by
    rw [← ENNReal.rpow_add _ _ (dyadicBase_pos _).ne' (dyadicBase_ne_top _)]
    simp
  calc
    _ = (gammaProductCellSup S F (N + n) ω * dyadicBase (N + n) ^ (-r)) *
        dyadicBase (N + n) ^ r := by rw [mul_assoc, hc, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (le_iSup (fun k : ℕ =>
        gammaProductCellSup S F (N + k) ω * dyadicBase (N + k) ^ (-r)) n) zero_le

private theorem gammaProductCellNormalised_moment
    (S : Set ParabolicSpace)
    (F : S → S → Ω → ℝ)
    (hmeas : ∀ x y, AEMeasurable (F x y) P)
    {p : ℕ} (hp : 1 ≤ p) {q ε : ℝ} (hq : 0 ≤ q) {M : ℝ≥0∞}
    (hpair : ∀ x y : S, parabolicNorm ((x : ParabolicSpace) - y) ≤ ε →
      ∫⁻ ω, ‖F x y ω‖ₑ ^ p ∂P ≤
        M * ENNReal.ofReal (parabolicNorm ((x : ParabolicSpace) - y)) ^ q)
    (r : ℝ) (n : ℕ) (hn : 20 / (2 : ℝ) ^ n ≤ ε) :
    ∫⁻ ω, (gammaProductCellSup S F n ω * dyadicBase n ^ (-r)) ^ p ∂P ≤
      (512 : ℝ≥0∞) ^ 2 * M * (20 : ℝ≥0∞) ^ q *
        dyadicBase n ^ (q - (p : ℝ) * r - 10) := by
  have hpow (z : ℝ≥0∞) :
      (z * dyadicBase n ^ (-r)) ^ p =
        z ^ p * dyadicBase n ^ (-r * p) := by
    rw [mul_pow, ← ENNReal.rpow_natCast (dyadicBase n ^ (-r)), ← ENNReal.rpow_mul]
  calc
    _ = (∫⁻ ω, gammaProductCellSup S F n ω ^ p ∂P) *
        dyadicBase n ^ (-r * p) := by
      simp_rw [hpow]
      exact lintegral_mul_const'' _
        ((gammaProduct_cellSup_aemeasurable S F hmeas n).pow_const p)
    _ ≤ ((Fintype.card (gammaCell S n) : ℝ≥0∞) ^ 2 *
        (M * ENNReal.ofReal (20 / (2 : ℝ) ^ n) ^ q)) *
        dyadicBase n ^ (-r * p) := by
      gcongr
      exact gammaProductCellSup_moment_le S F hmeas (p := p) (hp := by omega)
        hq hpair n hn
    _ ≤ ((512 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞) ^ (10 * n) *
        (M * ENNReal.ofReal (20 / (2 : ℝ) ^ n) ^ q)) *
        dyadicBase n ^ (-r * p) := by
      have hcard := card_hsParabolicOccupiedCell_le S n
      have hcard' : Fintype.card (gammaCell S n) ≤ 512 * 2 ^ (5 * n) := by
        calc
          Fintype.card (gammaCell S n) ≤ 16 * 2 ^ (5 * n) := hcard
          _ ≤ 512 * 2 ^ (5 * n) := by gcongr; norm_num
      have hcard'' : (Fintype.card (gammaCell S n) : ℝ≥0∞) ≤
          (512 : ℝ≥0∞) * 2 ^ (5 * n) := by exact_mod_cast hcard'
      have hsquare : (Fintype.card (gammaCell S n) : ℝ≥0∞) ^ 2 ≤
          (512 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞) ^ (10 * n) := by
        calc
          _ ≤ ((512 : ℝ≥0∞) * 2 ^ (5 * n)) ^ 2 := pow_le_pow_left' hcard'' 2
          _ = _ := by rw [mul_pow, ← pow_mul]; congr 2; omega
      gcongr
    _ = (512 : ℝ≥0∞) ^ 2 * M * (20 : ℝ≥0∞) ^ q *
        dyadicBase n ^ (q - (p : ℝ) * r - 10) := by
      calc
        _ = (512 : ℝ≥0∞) ^ 2 * M *
            ((2 : ℝ≥0∞) ^ (10 * n) *
              ENNReal.ofReal (20 / (2 : ℝ) ^ n) ^ q *
              dyadicBase n ^ (-r * p)) := by ring
        _ = _ := by rw [gammaProduct_scale_product]; ring

/-- The normalized product-net value envelope has a geometric moment bound. -/
theorem gammaProductCellNormalisedSup_moment_le
    (S : Set ParabolicSpace)
    (F : S → S → Ω → ℝ)
    (hmeas : ∀ x y, AEMeasurable (F x y) P)
    {p : ℕ} (hp : 1 ≤ p) {q ε : ℝ} (hq : 0 ≤ q) {M : ℝ≥0∞}
    (hpair : ∀ x y : S, parabolicNorm ((x : ParabolicSpace) - y) ≤ ε →
      ∫⁻ ω, ‖F x y ω‖ₑ ^ p ∂P ≤
        M * ENNReal.ofReal (parabolicNorm ((x : ParabolicSpace) - y)) ^ q)
    (r : ℝ) (_hgap : (p : ℝ) * r < q - 10)
    (N : ℕ) (hN : 20 / (2 : ℝ) ^ N ≤ ε) :
    ∫⁻ ω, gammaProductCellNormalisedSup S F r N ω ^ p ∂P ≤
      (512 : ℝ≥0∞) ^ 2 * M * (20 : ℝ≥0∞) ^ q *
        dyadicBase N ^ (q - (p : ℝ) * r - 10) *
        (1 - ((2 : ℝ≥0∞)⁻¹) ^ (q - (p : ℝ) * r - 10))⁻¹ := by
  have hterm (k : ℕ) := gammaProductCellNormalised_moment S F hmeas hp hq hpair r
    (N + k)
      (show 20 / (2 : ℝ) ^ (N + k) ≤ ε from
        (div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (pow_le_pow_right₀ (by norm_num) (Nat.le_add_right N k))).trans hN)
  calc
    _ ≤ ∑' k : ℕ, ∫⁻ ω,
        (gammaProductCellSup S F (N + k) ω *
          dyadicBase (N + k) ^ (-r)) ^ p ∂P := by
      apply lintegral_iSup_pow_le_tsum_lintegral_pow hp
      intro k
      exact (gammaProduct_cellSup_aemeasurable S F hmeas (N + k)).mul_const _
    _ ≤ ∑' k : ℕ, (512 : ℝ≥0∞) ^ 2 * M * (20 : ℝ≥0∞) ^ q *
        dyadicBase (N + k) ^ (q - (p : ℝ) * r - 10) :=
      ENNReal.tsum_le_tsum hterm
    _ = _ := by
      simp_rw [dyadicBase_rpow_eq_geometric, pow_add]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      ring

end RegularityStructures

end
