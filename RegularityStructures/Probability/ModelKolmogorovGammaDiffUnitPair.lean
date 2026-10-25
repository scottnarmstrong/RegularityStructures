/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaDiffUnitEnvelope
public import RegularityStructures.Probability.ModelKolmogorovGammaDiffUnitScale
public import RegularityStructures.Probability.ModelKolmogorovGammaDiffBadAnnulus
public import RegularityStructures.Probability.ModelKolmogorovMomentOrder
import Mathlib.Tactic.Linarith

/-!
# One coordinate of the unit-box Gamma difference

For a moment-controlled pair `(i, j) ∉ DΓ`, the coordinate
`(x, y) ↦ Γ¹_{xy} e_i |_j - Γ²_{xy} e_i |_j` on the unit box has a pointwise Hölder envelope `E` of
order `deg i - deg j` with `∫ E^m ≤ K₀ (C δ)^m`, where `K₀` depends only on the structure, the
exponents and the upper bound `C̄` of `C`, and not on the probability space or on `C, δ`.

The Chen increments are split as in
`RegularityStructures.Probability.ModelKolmogorovGammaDiffRelativeSource`:

* the products of two `DΓ` factors are pathwise, bounded by `C · Cδ ≤ C̄' · Cδ`, and summed
  geometrically over the fine scale using the positive degree gaps (no `κ̄` is needed);
* the remaining (good) products are moment-controlled, with step moments
  `card² (Cδ)^m L (2^{-N})^{m(β+ρ)} (2^{-l})^{mρ}`; the reserve `κ̄ > ρ` pays for the union bound
  over the `card² ≲ 2^{10(N+l)}` pairs;
* the cell values are bounded by the normalised cell supremum, again through the reserve.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

universe u

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

private theorem gammaDiffUnitPair_ofReal_pow_eq {c d e : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (m : ℕ) :
    ENNReal.ofReal (c * d ^ e) ^ m =
      ENNReal.ofReal c ^ m * ENNReal.ofReal d ^ ((m : ℝ) * e) := by
  have hpow : (ENNReal.ofReal d ^ e) ^ m = ENNReal.ofReal d ^ ((m : ℝ) * e) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_comm]
  rw [ENNReal.ofReal_mul hc, mul_pow, ← ENNReal.ofReal_rpow_of_nonneg hd he, hpow]

/-- **Cell moment of the Gamma difference.**  The normalised cell supremum of a
moment-controlled coordinate of `Γ¹ - Γ²` has `m`-th moment at most `(C δ)^m` times an explicit
constant. -/
theorem gammaDiffUnitCell_moment_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (S : Set ParabolicSpace)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ κ C δ : ℝ) {m q : ℕ} (hm : 1 ≤ m) (hmq : m ≤ q) (hκ0 : 0 < κ)
    (hκ : 10 < (m : ℝ) * κ) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hm₁ : ∀ x y i j, AEMeasurable
      (fun ω => ((M₁ ω).gammaMap y x (Pi.single i 1) j)) P)
    (hm₂ : ∀ x y i j, AEMeasurable
      (fun ω => ((M₂ ω).gammaMap y x (Pi.single i 1) j)) P)
    (hdiffN : ∀ i j, (i, j) ∉ D → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ x y,
      (∫⁻ ω, ‖(M₁ ω).gammaMap y x (Pi.single i 1) j -
        (M₂ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P) ≤
        ENNReal.ofReal (C * δ * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ q)
    (i j : ι) (hi : 𝒯.deg i < γ) (hj : 𝒯.deg j < 𝒯.deg i) (hij : (i, j) ∉ D) :
    ∫⁻ ω, gammaProductCellNormalisedSup S
        (fun x y ω => (M₁ ω).gammaMap (x : ParabolicSpace) y (Pi.single i 1) j -
          (M₂ ω).gammaMap (x : ParabolicSpace) y (Pi.single i 1) j)
        (𝒯.deg i - 𝒯.deg j) 0 ω ^ m ∂P ≤
      ENNReal.ofReal (C * δ) ^ m * ((512 : ℝ≥0∞) ^ 2 *
        (20 : ℝ≥0∞) ^ ((m : ℝ) * (𝒯.deg i - 𝒯.deg j + κ)) *
        dyadicBase 0 ^ ((m : ℝ) * (𝒯.deg i - 𝒯.deg j + κ) -
          (m : ℝ) * (𝒯.deg i - 𝒯.deg j) - 10) *
        (1 - ((2 : ℝ≥0∞)⁻¹) ^ ((m : ℝ) * (𝒯.deg i - 𝒯.deg j + κ) -
          (m : ℝ) * (𝒯.deg i - 𝒯.deg j) - 10))⁻¹) := by
  have he : 0 ≤ 𝒯.deg i - 𝒯.deg j + κ := by linarith
  have hpair : ∀ x y : S, parabolicNorm ((x : ParabolicSpace) - y) ≤ 20 →
      ∫⁻ ω, ‖(M₁ ω).gammaMap (x : ParabolicSpace) y (Pi.single i 1) j -
          (M₂ ω).gammaMap (x : ParabolicSpace) y (Pi.single i 1) j‖ₑ ^ m ∂P ≤
        ENNReal.ofReal (C * δ) ^ m * ENNReal.ofReal
          (parabolicNorm ((x : ParabolicSpace) - y)) ^ ((m : ℝ) * (𝒯.deg i - 𝒯.deg j + κ)) := by
    intro x y _
    have h := lintegral_enorm_pow_le_of_nat_le ((hm₁ y x i j).sub (hm₂ y x i j)) hm hmq
      (hdiffN i j hij hi hj y x)
    rw [gammaDiffUnitPair_ofReal_pow_eq (mul_nonneg hC hδ)
      (parabolicSemigroup.scaleDist_nonneg _ _) he] at h
    exact h
  have hgap : (m : ℝ) * (𝒯.deg i - 𝒯.deg j) <
      (m : ℝ) * (𝒯.deg i - 𝒯.deg j + κ) - 10 := by
    rw [mul_add]
    linarith
  have h := gammaProductCellNormalisedSup_moment_le S
    (fun x y ω => (M₁ ω).gammaMap (x : ParabolicSpace) y (Pi.single i 1) j -
      (M₂ ω).gammaMap (x : ParabolicSpace) y (Pi.single i 1) j)
    (fun x y => (hm₁ y x i j).sub (hm₂ y x i j)) hm
    (mul_nonneg (Nat.cast_nonneg m) he) hpair (𝒯.deg i - 𝒯.deg j) hgap 0 (by norm_num)
  exact h.trans_eq (by ring)

omit [Fintype ι] [DecidableEq ι] in
private theorem gammaDiffUnitPair_bad_sum_le (s : Finset ι) (f g : ι → ℝ)
    {C Cbar d : ℝ} (hCbar : C ≤ Cbar) (hd : 0 ≤ d) (a b : ℝ≥0∞) :
    ∑ k ∈ s, 2 * ENNReal.ofReal (C * d * (24 : ℝ) ^ f k * 4 ^ g k) * a * b ≤
      ENNReal.ofReal d *
        (∑ k ∈ s, 2 * ENNReal.ofReal (Cbar * (24 : ℝ) ^ f k * 4 ^ g k)) * a * b := by
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  have hX : 0 ≤ (24 : ℝ) ^ f k * 4 ^ g k :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _)
  have h : ENNReal.ofReal (C * d * (24 : ℝ) ^ f k * 4 ^ g k) ≤
      ENNReal.ofReal d * ENNReal.ofReal (Cbar * (24 : ℝ) ^ f k * 4 ^ g k) := by
    rw [← ENNReal.ofReal_mul hd]
    apply ENNReal.ofReal_le_ofReal
    calc
      C * d * (24 : ℝ) ^ f k * 4 ^ g k = d * (C * ((24 : ℝ) ^ f k * 4 ^ g k)) := by ring
      _ ≤ d * (Cbar * ((24 : ℝ) ^ f k * 4 ^ g k)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCbar hX) hd
      _ = d * (Cbar * (24 : ℝ) ^ f k * 4 ^ g k) := by ring
  calc
    2 * ENNReal.ofReal (C * d * (24 : ℝ) ^ f k * 4 ^ g k) * a * b ≤
        2 * (ENNReal.ofReal d * ENNReal.ofReal (Cbar * (24 : ℝ) ^ f k * 4 ^ g k)) * a * b := by
      gcongr
    _ = _ := by ring

private theorem gammaDiffUnitPair_inv_ne_top {t : ℝ} (ht : 0 < t) :
    (1 - ((2 : ℝ≥0∞)⁻¹) ^ t)⁻¹ ≠ ∞ :=
  ENNReal.inv_ne_top.2 (ne_of_gt (tsub_pos_iff_lt.2 (ENNReal.rpow_lt_one (by norm_num) ht)))

private theorem gammaDiffUnitPair_envelope_core
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧ ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (D : Set (ι × ι)) (γ κ ρ Cbar : ℝ) (i j : ι) {m q : ℕ}
    (hm : 1 ≤ m) (hmq : 2 * m ≤ q) (hκ : 0 < κ) (hρ : 0 < ρ) (hρκ : ρ < κ)
    (hρgap : ∀ a b : ι, 𝒯.deg b < 𝒯.deg a → ρ < 𝒯.deg a - 𝒯.deg b)
    (hreserve : 20 < (m : ℝ) * ρ)
    (hi : 𝒯.deg i < γ) (hj : 𝒯.deg j < 𝒯.deg i) (hij : (i, j) ∉ D) :
    ∃ K₀ : ℝ≥0∞, K₀ ≠ ∞ ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (C δ : ℝ), 0 ≤ C → C ≤ Cbar → 0 ≤ δ →
      (∀ x y a b, AEMeasurable
        (fun ω => ((M₁ ω).gammaMap y x (Pi.single a 1) b)) P) →
      (∀ x y a b, AEMeasurable
        (fun ω => ((M₂ ω).gammaMap y x (Pi.single a 1) b)) P) →
      (∀ ω, Continuous (fun z : S × S =>
        (M₁ ω).gammaMap (z.1 : ParabolicSpace) z.2 (Pi.single i 1) j -
          (M₂ ω).gammaMap (z.1 : ParabolicSpace) z.2 (Pi.single i 1) j)) →
      (∀ a b, (a, b) ∈ D → 𝒯.deg a < γ → 𝒯.deg b < 𝒯.deg a → ∀ ω x y,
        |(M₁ ω).gammaMap y x (Pi.single a 1) b| ≤
          C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg a - 𝒯.deg b)) →
      (∀ a b, (a, b) ∈ D → 𝒯.deg a < γ → 𝒯.deg b < 𝒯.deg a → ∀ ω x y,
        |(M₂ ω).gammaMap y x (Pi.single a 1) b| ≤
          C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg a - 𝒯.deg b)) →
      (∀ a b, (a, b) ∉ D → 𝒯.deg a < γ → 𝒯.deg b < 𝒯.deg a → ∀ x y,
        (∫⁻ ω, ‖(M₁ ω).gammaMap y x (Pi.single a 1) b‖ₑ ^ q ∂P) ≤
          ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
            (𝒯.deg a - 𝒯.deg b + κ)) ^ q) →
      (∀ a b, (a, b) ∉ D → 𝒯.deg a < γ → 𝒯.deg b < 𝒯.deg a → ∀ x y,
        (∫⁻ ω, ‖(M₂ ω).gammaMap y x (Pi.single a 1) b‖ₑ ^ q ∂P) ≤
          ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
            (𝒯.deg a - 𝒯.deg b + κ)) ^ q) →
      (∀ a b, (a, b) ∈ D → 𝒯.deg a < γ → 𝒯.deg b < 𝒯.deg a → ∀ ω x y,
        |(M₁ ω).gammaMap y x (Pi.single a 1) b - (M₂ ω).gammaMap y x (Pi.single a 1) b| ≤
          C * δ * parabolicSemigroup.scaleDist y x ^ (𝒯.deg a - 𝒯.deg b)) →
      (∀ a b, (a, b) ∉ D → 𝒯.deg a < γ → 𝒯.deg b < 𝒯.deg a → ∀ x y,
        (∫⁻ ω, ‖(M₁ ω).gammaMap y x (Pi.single a 1) b -
          (M₂ ω).gammaMap y x (Pi.single a 1) b‖ₑ ^ q ∂P) ≤
          ENNReal.ofReal (C * δ * parabolicSemigroup.scaleDist y x ^
            (𝒯.deg a - 𝒯.deg b + κ)) ^ q) →
      ∃ E : Ω → ℝ≥0∞, AEMeasurable E P ∧
        (∫⁻ ω, E ω ^ m ∂P ≤ K₀ * ENNReal.ofReal (C * δ) ^ m) ∧
        ∀ᵐ ω ∂P, ∀ x y : S, 0 < parabolicNorm ((x : ParabolicSpace) - y) →
          ‖(M₁ ω).gammaMap (x : ParabolicSpace) y (Pi.single i 1) j -
              (M₂ ω).gammaMap (x : ParabolicSpace) y (Pi.single i 1) j‖ₑ ≤
            E ω * ENNReal.ofReal (parabolicNorm ((x : ParabolicSpace) - y)) ^
              (𝒯.deg i - 𝒯.deg j) := by
  classical
  have hβ : 0 < 𝒯.deg i - 𝒯.deg j := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hκm : 10 < (m : ℝ) * κ := by nlinarith
  have hCbar1 : (0 : ℝ) ≤ max Cbar 1 := le_max_of_le_right zero_le_one
  obtain ⟨Lleft, hLleft, hLl⟩ := gammaDiffNearLeftGoodBound_finite_scale 𝒯 D κ
    (max Cbar 1) ρ i j hm hCbar1 hκ hρκ hρgap hj hij
  obtain ⟨Lright, hLright, hLr⟩ := gammaDiffNearRightGoodBound_finite_scale 𝒯 D κ
    (max Cbar 1) ρ i j hm hCbar1 hκ hρκ hρgap hj hij
  set e : ℝ := (m : ℝ) * (𝒯.deg i - 𝒯.deg j + κ) - (m : ℝ) * (𝒯.deg i - 𝒯.deg j) - 10
    with hedef
  have he0 : 0 < e := by rw [hedef, mul_add]; linarith
  have hη0 : 0 < (m : ℝ) * ρ / 2 - 10 := by linarith
  set KA0 : ℝ≥0∞ := (512 : ℝ≥0∞) ^ 2 * (20 : ℝ≥0∞) ^ ((m : ℝ) * (𝒯.deg i - 𝒯.deg j + κ)) *
    dyadicBase 0 ^ e * (1 - ((2 : ℝ≥0∞)⁻¹) ^ e)⁻¹ with hKA0def
  set KG0 : ℝ≥0∞ := (2 : ℝ≥0∞) ^ ((m : ℝ) - 1) * (512 : ℝ≥0∞) ^ 2 * (Lleft + Lright) *
    (1 - ((2 : ℝ≥0∞)⁻¹) ^ ((m : ℝ) * ρ / 2 - 10))⁻¹ *
    (1 - ((2 : ℝ≥0∞)⁻¹) ^ ((m : ℝ) * ρ / 2 - 10))⁻¹ with hKG0def
  set B0 : ℝ≥0∞ := (∑ k ∈ gammaBadIntermediate 𝒯 D i j,
      2 * ENNReal.ofReal (max Cbar 1 * (24 : ℝ) ^ (𝒯.deg i - 𝒯.deg k) *
        4 ^ (𝒯.deg k - 𝒯.deg j))) +
    (∑ k ∈ gammaBadIntermediate 𝒯 D i j,
      2 * ENNReal.ofReal (max Cbar 1 * (24 : ℝ) ^ (𝒯.deg k - 𝒯.deg j) *
        4 ^ (𝒯.deg i - 𝒯.deg k))) with hB0def
  set dd : ℝ≥0∞ := 1 - ((2 : ℝ≥0∞)⁻¹) ^ (ρ / 2) with hdddef
  have hKA0 : KA0 ≠ ∞ := by
    have h1 : dyadicBase 0 ^ e ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg he0.le (dyadicBase_ne_top 0)
    have h2 := gammaDiffUnitPair_inv_ne_top he0
    rw [hKA0def]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by finiteness) h1) h2
  have hKG0 : KG0 ≠ ∞ := by
    have h2 := gammaDiffUnitPair_inv_ne_top hη0
    rw [hKG0def]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by finiteness)
      (ENNReal.add_ne_top.2 ⟨hLleft, hLright⟩)) h2) h2
  have hB0 : B0 ≠ ∞ := by
    rw [hB0def]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun k _ => by finiteness,
      ENNReal.sum_ne_top.2 fun k _ => by finiteness⟩
  have hdd : dd⁻¹ ≠ ∞ := gammaDiffUnitPair_inv_ne_top (half_pos hρ)
  refine ⟨((2 : ℝ≥0∞) ^ (𝒯.deg i - 𝒯.deg j)) ^ m * (3 : ℝ≥0∞) ^ ((m : ℝ) - 1) *
      (KA0 + dd⁻¹ ^ m * KG0 + dd⁻¹ ^ m * B0 ^ m), ?_, ?_⟩
  · have h1 : ((2 : ℝ≥0∞) ^ (𝒯.deg i - 𝒯.deg j)) ^ m ≠ ∞ :=
      ENNReal.pow_ne_top (ENNReal.rpow_ne_top_of_nonneg hβ.le (by norm_num))
    have h2 : (3 : ℝ≥0∞) ^ ((m : ℝ) - 1) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by linarith [show (1 : ℝ) ≤ m by exact_mod_cast hm])
        (by norm_num)
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top h1 h2) (ENNReal.add_ne_top.2
      ⟨ENNReal.add_ne_top.2 ⟨hKA0, ENNReal.mul_ne_top (ENNReal.pow_ne_top hdd) hKG0⟩,
        ENNReal.mul_ne_top (ENNReal.pow_ne_top hdd) (ENNReal.pow_ne_top hB0)⟩)
  intro Ω _ P _ M₁ M₂ C δ hC hCbar hδ hm₁ hm₂ hcont hdet₁ hdet₂ hann₁ hann₂ hdiff hdiffN
  have hCbarmax : Cbar ≤ max Cbar 1 := le_max_left _ _
  have hCmax : C ≤ max Cbar 1 := hCbar.trans hCbarmax
  have hCδ : 0 ≤ C * δ := mul_nonneg hC hδ
  let F : S → S → Ω → ℝ := fun x y ω =>
    (M₁ ω).gammaMap (x : ParabolicSpace) y (Pi.single i 1) j -
      (M₂ ω).gammaMap (x : ParabolicSpace) y (Pi.single i 1) j
  have hFmeas : ∀ x y, AEMeasurable (F x y) P := fun x y => (hm₁ y x i j).sub (hm₂ y x i j)
  -- the cell envelope
  have hA0moment := gammaDiffUnitCell_moment_le S M₁ M₂ D γ κ C δ hm
    (by omega : m ≤ q) hκ hκm hC hδ hm₁ hm₂ hdiffN i j hi hj hij
  -- the good envelope
  have hleft := fun N l => gammaDiffGoodLeftAnnulusStepSup_moment_source_le S hbox M₁ M₂ D
    γ κ C Cbar (max Cbar 1) δ ρ hm hmq hC hCbar hCbarmax hδ hm₁ hm₂ hdet₁ hdet₂ hann₁ hann₂
    hdiff hdiffN i j hi hj hij Lleft hLl N l
  have hright := fun N l => gammaDiffGoodRightAnnulusStepSup_moment_source_le S hbox M₁ M₂ D
    γ κ C Cbar (max Cbar 1) δ ρ hm hmq hC hCbar hCbarmax hδ hm₁ hm₂ hdet₁ hdet₂ hann₁ hann₂
    hdiff hdiffN i j hi hj hij Lright hLr N l
  have hGmoment := gammaDiffGoodGlobalEnvelope_moment_le S M₁ M₂ D hm₁ hm₂ i j
    (𝒯.deg i - 𝒯.deg j) ρ hm hreserve hleft hright
  set G := gammaDiffGoodGlobalEnvelope S M₁ M₂ D i j (𝒯.deg i - 𝒯.deg j) (ρ / 2) with hG
  have hGmeas : AEMeasurable G P :=
    gammaDiffGoodGlobalEnvelope_aemeasurable S M₁ M₂ D hm₁ hm₂ i j _ _
  -- the deterministic bad constant
  set Bbad : ℝ≥0∞ := ENNReal.ofReal (C * δ) * B0 with hBbaddef
  have hBbadtop : Bbad ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB0
  have hbad : ∀ (ω : Ω) (N l : ℕ),
      gammaDiffBadLeftAnnulusStepSup S M₁ M₂ D i j N (N + l) ω +
          gammaDiffBadRightAnnulusStepSup S M₁ M₂ D i j N (N + l) ω ≤
        Bbad * dyadicBase N ^ (𝒯.deg i - 𝒯.deg j) * dyadicBase l ^ (ρ / 2) := by
    intro ω N l
    have hl := gammaDiffBadLeftStepSupAnnulus_le S hbox M₁ M₂ D γ C (C * δ) (ρ / 2) hC hCδ
      hdet₁ hdet₂ hdiff i j hi hj (𝒯.deg i - 𝒯.deg j) rfl (half_pos hρ)
      (fun k hjk _ => by linarith [hρgap k j hjk]) ω N l
    have hr := gammaDiffBadRightStepSupAnnulus_le S hbox M₁ M₂ D γ C (C * δ) (ρ / 2) hC hCδ
      hdet₁ hdet₂ hdiff i j hi hj (𝒯.deg i - 𝒯.deg j) rfl (half_pos hρ)
      (fun k _ hki => by linarith [hρgap i k hki]) ω N l
    have hl' := hl.trans (gammaDiffUnitPair_bad_sum_le _ (fun k => 𝒯.deg i - 𝒯.deg k)
      (fun k => 𝒯.deg k - 𝒯.deg j) hCmax hCδ _ _)
    have hr' := hr.trans (gammaDiffUnitPair_bad_sum_le _ (fun k => 𝒯.deg k - 𝒯.deg j)
      (fun k => 𝒯.deg i - 𝒯.deg k) hCmax hCδ _ _)
    calc
      _ ≤ _ := add_le_add hl' hr'
      _ = _ := by rw [hBbaddef, hB0def]; ring
  -- the full annular steps
  have hGfull : ∀ (ω : Ω) (N l : ℕ),
      gammaProductLeftStepSupAnnulus S F N (N + l) ω +
          gammaProductRightStepSupAnnulus S F N (N + l) ω ≤
        (G ω + Bbad) * dyadicBase N ^ (𝒯.deg i - 𝒯.deg j) * dyadicBase l ^ (ρ / 2) := by
    intro ω N l
    have hl := gammaDiffAnnulusSplitLeftStep_le S M₁ M₂ D i j N (N + l) ω hj
    have hr := gammaDiffAnnulusSplitRightStep_le S M₁ M₂ D i j N (N + l) ω hj
    have hg := gammaDiffGoodGlobalTerm_le_envelope_mul_scale S M₁ M₂ D i j
      (𝒯.deg i - 𝒯.deg j) (ρ / 2) N l ω
    calc
      _ ≤ (gammaDiffGoodLeftAnnulusStepSup S M₁ M₂ D i j N (N + l) ω +
            gammaDiffBadLeftAnnulusStepSup S M₁ M₂ D i j N (N + l) ω) +
          (gammaDiffGoodRightAnnulusStepSup S M₁ M₂ D i j N (N + l) ω +
            gammaDiffBadRightAnnulusStepSup S M₁ M₂ D i j N (N + l) ω) := add_le_add hl hr
      _ = (gammaDiffGoodLeftAnnulusStepSup S M₁ M₂ D i j N (N + l) ω +
            gammaDiffGoodRightAnnulusStepSup S M₁ M₂ D i j N (N + l) ω) +
          (gammaDiffBadLeftAnnulusStepSup S M₁ M₂ D i j N (N + l) ω +
            gammaDiffBadRightAnnulusStepSup S M₁ M₂ D i j N (N + l) ω) := by ring
      _ ≤ G ω * dyadicBase N ^ (𝒯.deg i - 𝒯.deg j) * dyadicBase l ^ (ρ / 2) +
          Bbad * dyadicBase N ^ (𝒯.deg i - 𝒯.deg j) * dyadicBase l ^ (ρ / 2) :=
        add_le_add hg (hbad ω N l)
      _ = _ := by ring
  have hσ : ENNReal.ofReal (C * δ) ^ m ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  obtain ⟨E, hEmeas, hEmoment, hEpoint⟩ := gammaDiffUnitEnvelope_moment_of_split S hbox F
    (𝒯.deg i - 𝒯.deg j) (ρ / 2) m hm G Bbad hFmeas hGmeas hA0moment hGmoment
    (ENNReal.mul_ne_top hσ hKG0) hBbadtop hGfull hcont hβ.le (half_pos hρ)
  refine ⟨E, hEmeas, hEmoment.trans_eq ?_, hEpoint⟩
  rw [hBbaddef, mul_pow, hKA0def, hKG0def, hdddef, hedef]
  ring

/-- **Hölder envelope of one moment-controlled coordinate of the Gamma difference.**  The
constant `K₀` is chosen before the pair conditions, the probability space, `C ≤ C̄` and `δ`. -/
theorem gammaDiffUnitPair_envelope
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧ ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (D : Set (ι × ι)) (γ κ ρ Cbar : ℝ) (i j : ι) {m q : ℕ}
    (hm : 1 ≤ m) (hmq : 2 * m ≤ q) (hκ : 0 < κ) (hρ : 0 < ρ) (hρκ : ρ < κ)
    (hρgap : ∀ a b : ι, 𝒯.deg b < 𝒯.deg a → ρ < 𝒯.deg a - 𝒯.deg b)
    (hreserve : 20 < (m : ℝ) * ρ) :
    ∃ K₀ : ℝ≥0∞, K₀ ≠ ∞ ∧ ((i, j) ∉ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (C δ : ℝ), 0 ≤ C → C ≤ Cbar → 0 ≤ δ →
      (∀ x y a b, AEMeasurable
        (fun ω => ((M₁ ω).gammaMap y x (Pi.single a 1) b)) P) →
      (∀ x y a b, AEMeasurable
        (fun ω => ((M₂ ω).gammaMap y x (Pi.single a 1) b)) P) →
      (∀ ω, Continuous (fun z : S × S =>
        (M₁ ω).gammaMap (z.1 : ParabolicSpace) z.2 (Pi.single i 1) j -
          (M₂ ω).gammaMap (z.1 : ParabolicSpace) z.2 (Pi.single i 1) j)) →
      (∀ a b, (a, b) ∈ D → 𝒯.deg a < γ → 𝒯.deg b < 𝒯.deg a → ∀ ω x y,
        |(M₁ ω).gammaMap y x (Pi.single a 1) b| ≤
          C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg a - 𝒯.deg b)) →
      (∀ a b, (a, b) ∈ D → 𝒯.deg a < γ → 𝒯.deg b < 𝒯.deg a → ∀ ω x y,
        |(M₂ ω).gammaMap y x (Pi.single a 1) b| ≤
          C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg a - 𝒯.deg b)) →
      (∀ a b, (a, b) ∉ D → 𝒯.deg a < γ → 𝒯.deg b < 𝒯.deg a → ∀ x y,
        (∫⁻ ω, ‖(M₁ ω).gammaMap y x (Pi.single a 1) b‖ₑ ^ q ∂P) ≤
          ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
            (𝒯.deg a - 𝒯.deg b + κ)) ^ q) →
      (∀ a b, (a, b) ∉ D → 𝒯.deg a < γ → 𝒯.deg b < 𝒯.deg a → ∀ x y,
        (∫⁻ ω, ‖(M₂ ω).gammaMap y x (Pi.single a 1) b‖ₑ ^ q ∂P) ≤
          ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
            (𝒯.deg a - 𝒯.deg b + κ)) ^ q) →
      (∀ a b, (a, b) ∈ D → 𝒯.deg a < γ → 𝒯.deg b < 𝒯.deg a → ∀ ω x y,
        |(M₁ ω).gammaMap y x (Pi.single a 1) b - (M₂ ω).gammaMap y x (Pi.single a 1) b| ≤
          C * δ * parabolicSemigroup.scaleDist y x ^ (𝒯.deg a - 𝒯.deg b)) →
      (∀ a b, (a, b) ∉ D → 𝒯.deg a < γ → 𝒯.deg b < 𝒯.deg a → ∀ x y,
        (∫⁻ ω, ‖(M₁ ω).gammaMap y x (Pi.single a 1) b -
          (M₂ ω).gammaMap y x (Pi.single a 1) b‖ₑ ^ q ∂P) ≤
          ENNReal.ofReal (C * δ * parabolicSemigroup.scaleDist y x ^
            (𝒯.deg a - 𝒯.deg b + κ)) ^ q) →
      ∃ E : Ω → ℝ≥0∞, AEMeasurable E P ∧
        (∫⁻ ω, E ω ^ m ∂P ≤ K₀ * ENNReal.ofReal (C * δ) ^ m) ∧
        ∀ᵐ ω ∂P, ∀ x y : S, 0 < parabolicNorm ((x : ParabolicSpace) - y) →
          ‖(M₁ ω).gammaMap (x : ParabolicSpace) y (Pi.single i 1) j -
              (M₂ ω).gammaMap (x : ParabolicSpace) y (Pi.single i 1) j‖ₑ ≤
            E ω * ENNReal.ofReal (parabolicNorm ((x : ParabolicSpace) - y)) ^
              (𝒯.deg i - 𝒯.deg j)) := by
  by_cases h : (i, j) ∉ D ∧ 𝒯.deg i < γ ∧ 𝒯.deg j < 𝒯.deg i
  · obtain ⟨K₀, hK₀, hmain⟩ := gammaDiffUnitPair_envelope_core S hbox D γ κ ρ Cbar i j hm hmq
      hκ hρ hρκ hρgap hreserve h.2.1 h.2.2 h.1
    exact ⟨K₀, hK₀, fun _ _ _ => hmain⟩
  · exact ⟨0, ENNReal.zero_ne_top, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩

end RegularityStructures

end
