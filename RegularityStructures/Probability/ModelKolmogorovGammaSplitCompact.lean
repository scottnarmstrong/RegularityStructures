/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaMeasurability
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.Linarith
public import RegularityStructures.Probability.ModelKolmogorovAnnealed
public import RegularityStructures.Probability.ModelKolmogorovGammaSplitHalf

/-!
# Compact assembly for the Gamma half

This module assembles the deterministic/moment split on a normalized compact parabolic set and then
returns the compact `gammaNormOn` moment required by the Kolmogorov criterion for models.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒯 : RegularityStructure ι}

private noncomputable def gammaSplitCompact_pullbackModel
    (M : Model 𝒯 parabolicSemigroup)
    (e : ParabolicSpace ≃ₜ ParabolicSpace) :
    Model 𝒯 parabolicSemigroup where
  pi := fun _ => 0
  gamma := fun x y => M.gamma (e.symm x) (e.symm y)
  pi_gamma := by simp
  gamma_self := fun x => M.gamma_self (e.symm x)
  gamma_mul := fun x y z => M.gamma_mul (e.symm x) (e.symm y) (e.symm z)
  measurable_diag := by
    intro i t ht
    exact measurable_const
  measurable_pi := by
    intro x i t ht
    exact measurable_const

private theorem gammaSplitCompact_pullbackModel_gammaMap
    (M : Model 𝒯 parabolicSemigroup)
    (e : ParabolicSpace ≃ₜ ParabolicSpace) (x y : ParabolicSpace)
    (τ : ι → ℝ) :
    (gammaSplitCompact_pullbackModel M e).gammaMap x y τ =
      M.gammaMap (e.symm x) (e.symm y) τ := rfl

private theorem gammaSplitCompact_pullback_continuous
    (M : Model 𝒯 parabolicSemigroup)
    (e : ParabolicSpace ≃ₜ ParabolicSpace)
    {S T : Set ParabolicSpace} (f : S ≃ₜ T)
    (hf : ∀ z : T, ((f.symm z : S) : ParabolicSpace) = e.symm z)
    (τ : ι → ℝ) (j : ι)
    (hM : ContinuousOn
      (fun w : ParabolicSpace × ParabolicSpace =>
        M.gammaMap w.2 w.1 τ j)
      (S ×ˢ S)) :
    Continuous (fun z : T × T =>
      (gammaSplitCompact_pullbackModel M e).gammaMap z.1 z.2 τ j) := by
  let g : T × T → ParabolicSpace × ParabolicSpace := fun z =>
    (((f.symm z.2 : S) : ParabolicSpace),
      ((f.symm z.1 : S) : ParabolicSpace))
  have hg : Continuous g := by
    exact
      ((continuous_subtype_val.comp (f.symm.continuous.comp continuous_snd)).prodMk
        (continuous_subtype_val.comp (f.symm.continuous.comp continuous_fst)))
  have hmaps : Set.MapsTo g Set.univ (S ×ˢ S) := by
    intro z hz
    exact ⟨(f.symm z.2).property, (f.symm z.1).property⟩
  have hc : ContinuousOn (fun z => M.gammaMap (g z).2 (g z).1 τ j) Set.univ :=
    hM.comp' hg.continuousOn hmaps
  rw [continuousOn_univ] at hc
  simpa only [g, gammaSplitCompact_pullbackModel_gammaMap, hf] using hc

private theorem gammaSplitCompact_parabolicNorm_pos {x y : ParabolicSpace}
    (hxy : x ≠ y) : 0 < parabolicNorm (y - x) := by
  have hnonneg : 0 ≤ parabolicNorm (y - x) := parabolicNorm_nonneg _
  by_contra hnot
  have hz : parabolicNorm (y - x) = 0 :=
    le_antisymm (le_of_not_gt hnot) hnonneg
  have hsum_nonneg : 0 ≤ ∑ k, |y.2 k - x.2 k| :=
    Finset.sum_nonneg (fun k _ => abs_nonneg (y.2 k - x.2 k))
  have hsqrt_nonneg : 0 ≤ Real.sqrt |y.1 - x.1| := Real.sqrt_nonneg _
  have hsqrt : Real.sqrt |y.1 - x.1| = 0 := by
    dsimp [parabolicNorm] at hz
    linarith
  have htime : |y.1 - x.1| = 0 := by
    nlinarith [Real.sq_sqrt (abs_nonneg (y.1 - x.1))]
  have hsum : (∑ k, |y.2 k - x.2 k|) = 0 := by
    dsimp [parabolicNorm] at hz
    linarith
  have hspace : ∀ k, |y.2 k - x.2 k| = 0 := by
    intro k
    have hle : |y.2 k - x.2 k| ≤ ∑ l, |y.2 l - x.2 l| :=
      Finset.single_le_sum (fun l _ => abs_nonneg (y.2 l - x.2 l))
        (Finset.mem_univ k)
    exact le_antisymm (by simpa [hsum] using hle) (abs_nonneg _)
  apply hxy
  apply Prod.ext
  · have htime' : |x.1 - y.1| = 0 := by simpa [abs_sub_comm] using htime
    exact sub_eq_zero.mp (abs_eq_zero.mp htime')
  · funext k
    have hspace' : |x.2 k - y.2 k| = 0 := by
      simpa [abs_sub_comm] using hspace k
    exact sub_eq_zero.mp (abs_eq_zero.mp hspace')

private theorem gammaSplitCompact_lower_ennreal_moment
    (f : Ω → ℝ≥0∞) (hf : AEMeasurable f P) {p q : ℕ}
    (hp : 1 ≤ p) (hpq : p ≤ q) {A : ℝ≥0∞}
    (hA : ∫⁻ ω, f ω ^ q ∂P ≤ A ^ q) :
    ∫⁻ ω, f ω ^ p ∂P ≤ A ^ p := by
  have hA' : ∫⁻ ω, f ω ^ (q : ℝ) ∂P ≤ A ^ (q : ℝ) := by
    simpa only [ENNReal.rpow_natCast] using hA
  by_cases hAtop : A = ∞
  · rw [hAtop]
    simp [Nat.ne_of_gt hp]
  have hAqtop : A ^ (q : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hAtop
  have htop : ∀ᵐ ω ∂P, f ω ≠ ∞ := by
    filter_upwards [ae_lt_top' (hf.pow_const (q : ℝ))
      (ne_top_of_le_ne_top hAqtop hA')] with ω hω
    by_contra hfn
    rw [hfn] at hω
    simp at hω
    omega
  let g : Ω → ℝ := fun ω => (f ω).toReal
  have hg : AEMeasurable g P := hf.ennreal_toReal
  have hgeq : ∀ᵐ ω ∂P, ‖g ω‖ₑ = f ω := by
    filter_upwards [htop] with ω hω
    simp [g, Real.enorm_of_nonneg, ENNReal.toReal_nonneg, hω]
  have hpow (n : ℕ) : ∀ᵐ ω ∂P, f ω ^ n = ‖g ω‖ₑ ^ n :=
    hgeq.mono fun ω hω => congrArg (fun z : ℝ≥0∞ => z ^ n) hω.symm
  have hpowRev (n : ℕ) : ∀ᵐ ω ∂P, ‖g ω‖ₑ ^ n = f ω ^ n :=
    hpow n |>.mono fun ω hω => hω.symm
  have hreal : ∫⁻ ω, ‖g ω‖ₑ ^ q ∂P ≤ A ^ q := by
    calc
      _ = ∫⁻ ω, f ω ^ q ∂P := lintegral_congr_ae (hpowRev q)
      _ ≤ _ := hA
  have hlow := lintegral_enorm_pow_le_of_nat_le hg hp hpq hreal
  calc
    _ = ∫⁻ ω, ‖g ω‖ₑ ^ p ∂P := lintegral_congr_ae (hpow p)
    _ ≤ _ := hlow

private theorem gammaSplitCompact_degree_envelope
    (𝒯 : RegularityStructure ι) (a b : ι) :
    𝒯.deg a - 𝒯.deg b ≤
      1 + 2 * ∑ k : ι, |𝒯.deg k| := by
  have ha : 𝒯.deg a ≤ |𝒯.deg a| := le_abs_self _
  have hb : -𝒯.deg b ≤ |𝒯.deg b| := neg_le_abs _
  have ha' : |𝒯.deg a| ≤ ∑ k : ι, |𝒯.deg k| := by
    exact Finset.single_le_sum (f := fun k : ι => |𝒯.deg k|)
      (fun k _ => abs_nonneg _) (Finset.mem_univ a)
  have hb' : |𝒯.deg b| ≤ ∑ k : ι, |𝒯.deg k| := by
    exact Finset.single_le_sum (f := fun k : ι => |𝒯.deg k|)
      (fun k _ => abs_nonneg _) (Finset.mem_univ b)
  linarith

private theorem gammaSplitCompact_scale_source
    (L C A β d : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hβ : β ≤ A) (hd : 0 ≤ d) :
    C * (L * d) ^ β ≤ C * L ^ A * d ^ β := by
  rw [Real.mul_rpow (by linarith) hd]
  have hpow : L ^ β ≤ L ^ A := Real.rpow_le_rpow_of_exponent_le hL hβ
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hd β)) hC)

private theorem gammaSplitCompact_profile_ne_top
    (𝒯 : RegularityStructure ι) (D : Set (ι × ι)) (i j : ι)
    (κ Dbar δ : ℝ) (r : ℕ) (_hκ : 0 < κ) (hδ : 0 < δ)
    (hreserveκ : 10 < (r : ℝ) * κ)
    (hreserveδ : 10 < (r : ℝ) * δ) :
    gammaSplitUnitProfile 𝒯 D i j κ Dbar δ r ≠ ∞ := by
  have hη : 0 < min ((r : ℝ) * κ - 10) ((r : ℝ) * δ - 10) := by
    exact lt_min (by linarith) (by linarith)
  have hr : 1 ≤ r := by
    by_contra h
    have : r = 0 := by omega
    subst this
    norm_num at hreserveκ
  have hrreal : 1 ≤ (r : ℝ) := by exact_mod_cast hr
  have hdenκ : 1 - ((2 : ℝ≥0∞)⁻¹) ^ ((r : ℝ) * κ - 10) ≠ 0 := by
    exact ne_of_gt (tsub_pos_iff_lt.2
      (ENNReal.rpow_lt_one (by norm_num) (by linarith)))
  have hdenδ : 1 - ((2 : ℝ≥0∞)⁻¹) ^ δ ≠ 0 := by
    exact ne_of_gt (tsub_pos_iff_lt.2 (ENNReal.rpow_lt_one (by norm_num) hδ))
  have hdenη : 1 - ((2 : ℝ≥0∞)⁻¹) ^
      (min ((r : ℝ) * κ - 10) ((r : ℝ) * δ - 10)) ≠ 0 := by
    exact ne_of_gt (tsub_pos_iff_lt.2 (ENNReal.rpow_lt_one (by norm_num) hη))
  have hcell : gammaSplitCellConstant 𝒯 i j κ 1 r ≠ ∞ := by
    dsimp [gammaSplitCellConstant]
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top
          · finiteness
          · exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
        · exact ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
      · exact ENNReal.rpow_ne_top_of_nonneg (by positivity)
          (dyadicBase_ne_top 0)
    · exact ENNReal.inv_ne_top.mpr hdenκ
  have hleft : gammaSplitLeftConstant 𝒯 D i j κ 1 Dbar r ≠ ∞ := by
    dsimp [gammaSplitLeftConstant]
    apply ENNReal.mul_ne_top
    · finiteness
    · apply ENNReal.add_ne_top.mpr
      refine ⟨ENNReal.pow_ne_top ENNReal.ofReal_ne_top, ?_⟩
      apply ENNReal.mul_ne_top
      · exact ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.coe_ne_top
      · apply ENNReal.sum_ne_top.mpr
        intro k hk
        exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hright : gammaSplitRightConstant 𝒯 D i j κ 1 Dbar r ≠ ∞ := by
    dsimp [gammaSplitRightConstant]
    apply ENNReal.mul_ne_top
    · finiteness
    · apply ENNReal.add_ne_top.mpr
      refine ⟨ENNReal.pow_ne_top ENNReal.ofReal_ne_top, ?_⟩
      apply ENNReal.mul_ne_top
      · exact ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.coe_ne_top
      · apply ENNReal.sum_ne_top.mpr
        intro k hk
        exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hbad : gammaSplitBadConstant 𝒯 D i j 1 r ≠ ∞ := by
    dsimp [gammaSplitBadConstant]
    apply ENNReal.add_ne_top.mpr
    exact ⟨ENNReal.sum_ne_top.mpr (fun k hk => ENNReal.ofReal_ne_top),
      ENNReal.sum_ne_top.mpr (fun k hk => ENNReal.ofReal_ne_top)⟩
  have hglobal : gammaSplitGlobalConstant 𝒯 D i j κ 1 Dbar δ r ≠ ∞ := by
    dsimp [gammaSplitGlobalConstant]
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · finiteness
        · exact ENNReal.add_ne_top.mpr ⟨hleft, hright⟩
      · exact ENNReal.inv_ne_top.mpr hdenη
    · exact ENNReal.inv_ne_top.mpr hdenη
  dsimp [gammaSplitUnitProfile]
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · finiteness
    · exact ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.coe_ne_top
  · apply ENNReal.add_ne_top.mpr
    refine ⟨?_, ?_⟩
    · apply ENNReal.add_ne_top.mpr
      refine ⟨hcell, ?_⟩
      apply ENNReal.mul_ne_top
      · exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hdenδ)
      · exact hglobal
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hdenδ)
        · exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
      · exact ENNReal.pow_ne_top hbad

private theorem gammaSplitCompact_coordinate_envelope
    (S : Set ParabolicSpace) (L : ℝ) (hL : 2 ≤ L)
    (hbound : ∀ x ∈ S, ‖x‖ ≤ L / 2)
    (hdist_bound : ∀ x y, x ∈ S → y ∈ S →
      parabolicNorm (x - y) ≤ 20 * L)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ κ C Cbar δ : ℝ) (i j : ι) {q r : ℕ} (hr : 1 ≤ r)
    (hrq : 2 * r ≤ q) (hκ : 0 < κ) (hC : 0 ≤ C) (hCbar : C ≤ Cbar)
    (hreserveκ : 10 < (r : ℝ) * κ)
    (hδ : 0 < δ) (hreserveδ : 10 < (r : ℝ) * δ)
    (hδκ : 2 * δ ≤ κ)
    (hδleft : ∀ k, 𝒯.deg j < 𝒯.deg k → 𝒯.deg k < 𝒯.deg i →
      δ ≤ (𝒯.deg k - 𝒯.deg j) / 2)
    (hδright : ∀ k, 𝒯.deg j < 𝒯.deg k → 𝒯.deg k < 𝒯.deg i →
      δ ≤ (𝒯.deg i - 𝒯.deg k) / 2)
    (hm : ∀ x y a b, AEMeasurable
      (fun ω => (M ω).gammaMap x y (Pi.single a 1) b) P)
    (hdet : ∀ a b, (a, b) ∈ D → 𝒯.deg a < γ → 𝒯.deg b < 𝒯.deg a →
      ∀ ω x y, |(M ω).gammaMap y x (Pi.single a 1) b| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg a - 𝒯.deg b))
    (hann : ∀ a b, (a, b) ∉ D → 𝒯.deg a < γ → 𝒯.deg b < 𝒯.deg a →
      ∀ x y, ∫⁻ ω, ‖(M ω).gammaMap y x (Pi.single a 1) b‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg a - 𝒯.deg b + κ)) ^ q)
    (hcont : ∀ ω, ContinuousOn
      (fun w : ParabolicSpace × ParabolicSpace =>
        (M ω).gammaMap w.2 w.1 (Pi.single i 1) j) (S ×ˢ S))
    (hi : 𝒯.deg i < γ) (hj : 𝒯.deg j < 𝒯.deg i) :
    ∃ B : Ω → ℝ≥0∞, AEMeasurable B P ∧
      ∃ KB : ℝ≥0∞, KB ≠ ∞ ∧
        (∫⁻ ω, B ω ^ r ∂P ≤ KB) ∧
        KB ≤ (1 + gammaSplitUnitProfile 𝒯 D i j κ
          (max 1 (Cbar * L ^ (1 + κ + 2 * ∑ k : ι, |𝒯.deg k|))) δ r) *
            (ENNReal.ofReal (C * L ^
              (1 + κ + 2 * ∑ k : ι, |𝒯.deg k|))) ^ r ∧
        (∀ᵐ ω ∂P, ∀ x y : S, 0 < parabolicNorm
          ((x : ParabolicSpace) - y) →
          ‖(M ω).gammaMap (y : ParabolicSpace) (x : ParabolicSpace)
              (Pi.single i 1) j‖ₑ ≤
            B ω * ENNReal.ofReal (parabolicNorm
              ((x : ParabolicSpace) - y)) ^ (𝒯.deg i - 𝒯.deg j)) := by
  classical
  have hLpos : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  let e := hsParabolicBoxHomeomorph hLpos.ne'
  let T : Set ParabolicSpace := e '' S
  let f : S ≃ₜ T := e.image S
  have hf (z : T) : ((f.symm z : S) : ParabolicSpace) = e.symm z := by
    rfl
  have hbox : ∀ x ∈ T, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ k, x.2 k ∈ Icc (0 : ℝ) 1 := by
    rintro y ⟨x, hx, rfl⟩
    exact hsParabolicBoxHomeomorph_mem_unitBox hL (hbound x hx)
  let M' : Ω → Model 𝒯 parabolicSemigroup := fun ω =>
    gammaSplitCompact_pullbackModel (M ω) e
  let A : ℝ := 1 + κ + 2 * ∑ k : ι, |𝒯.deg k|
  let C₀ : ℝ := C * L ^ A
  let Cbar₀ : ℝ := Cbar * L ^ A
  have hAβ (a b : ι) (hab : 𝒯.deg b < 𝒯.deg a) :
      𝒯.deg a - 𝒯.deg b ≤ A := by
    dsimp [A]
    have h := gammaSplitCompact_degree_envelope 𝒯 a b
    linarith
  have hAβκ (a b : ι) (hab : 𝒯.deg b < 𝒯.deg a) :
      𝒯.deg a - 𝒯.deg b + κ ≤ A := by
    dsimp [A]
    have h := gammaSplitCompact_degree_envelope 𝒯 a b
    linarith
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    exact mul_nonneg hC (Real.rpow_nonneg (by linarith) _)
  have hCbar₀ : 0 ≤ Cbar₀ := by
    dsimp [Cbar₀]
    exact mul_nonneg (le_trans hC hCbar) (Real.rpow_nonneg (by linarith) _)
  have hC₀bar : C₀ ≤ Cbar₀ := by
    dsimp [C₀, Cbar₀]
    exact mul_le_mul_of_nonneg_right hCbar (Real.rpow_nonneg (by linarith) _)
  have hscale (x y : ParabolicSpace) :
      parabolicSemigroup.scaleDist (e.symm y) (e.symm x) =
        L * parabolicSemigroup.scaleDist y x := by
    change parabolicNorm (e.symm y - e.symm x) =
      L * parabolicNorm (y - x)
    exact parabolicNorm_sub_hsParabolicBoxHomeomorph_symm hLpos y x
  have hm' : ∀ x y a b, AEMeasurable
      (fun ω => (M' ω).gammaMap x y (Pi.single a 1) b) P := by
    intro x y a b
    simpa only [M', gammaSplitCompact_pullbackModel_gammaMap] using
      hm (e.symm x) (e.symm y) a b
  have hdet' : ∀ a b, (a, b) ∈ D → 𝒯.deg a < γ →
      𝒯.deg b < 𝒯.deg a → ∀ ω x y,
      |(M' ω).gammaMap y x (Pi.single a 1) b| ≤
        C₀ * parabolicSemigroup.scaleDist y x ^ (𝒯.deg a - 𝒯.deg b) := by
    intro a b hab ha hb ω x y
    have hs := hdet a b hab ha hb ω (e.symm x) (e.symm y)
    rw [hscale] at hs
    have hscaled := gammaSplitCompact_scale_source L C A
      (𝒯.deg a - 𝒯.deg b) (parabolicSemigroup.scaleDist y x)
      hLone hC (hAβ a b hb) (parabolicSemigroup.scaleDist_nonneg _ _)
    simpa only [M', gammaSplitCompact_pullbackModel_gammaMap, C₀] using
      hs.trans hscaled
  have hann' : ∀ a b, (a, b) ∉ D → 𝒯.deg a < γ →
      𝒯.deg b < 𝒯.deg a → ∀ x y,
      ∫⁻ ω, ‖(M' ω).gammaMap y x (Pi.single a 1) b‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (C₀ * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg a - 𝒯.deg b + κ)) ^ q := by
    intro a b hab ha hb x y
    have hs := hann a b hab ha hb (e.symm x) (e.symm y)
    rw [hscale] at hs
    have hscaled := gammaSplitCompact_scale_source L C A
      (𝒯.deg a - 𝒯.deg b + κ) (parabolicSemigroup.scaleDist y x)
      hLone hC (hAβκ a b hb) (parabolicSemigroup.scaleDist_nonneg _ _)
    have hpow := pow_le_pow_left'
      (ENNReal.ofReal_le_ofReal hscaled) q
    simpa only [M', gammaSplitCompact_pullbackModel_gammaMap, C₀] using
      hs.trans hpow
  have hcont' : ∀ ω, Continuous (fun z : T × T =>
      (M' ω).gammaMap z.1 z.2 (Pi.single i 1) j) := by
    intro ω
    exact gammaSplitCompact_pullback_continuous (M ω) e f hf
      (Pi.single i 1) j (hcont ω)
  obtain ⟨B, hBmeas, KB, hKBtop, hBmoment, hKBbound, hBpoint⟩ :=
    gammaSplit_unit_coordinate_envelope_full (P := P) T hbox M' D γ κ C₀ Cbar₀ δ i j
      hr hrq hκ hC₀ hC₀bar hreserveκ hδ hreserveδ hδκ hδleft hδright hm' hdet' hann'
      hcont' hi hj
  let β : ℝ := 𝒯.deg i - 𝒯.deg j
  let aScale : ℝ≥0∞ := ENNReal.ofReal L⁻¹ ^ β
  let B' : Ω → ℝ≥0∞ := fun ω => B ω * aScale
  have hB'meas : AEMeasurable B' P := by
    exact hBmeas.mul_const aScale
  have hB'moment : ∫⁻ ω, B' ω ^ r ∂P ≤
      aScale ^ r * KB := by
    dsimp [B']
    rw [show (fun ω => (B ω * aScale) ^ r) =
      (fun ω => aScale ^ r * B ω ^ r) by
        funext ω; rw [mul_pow, mul_comm]]
    rw [lintegral_const_mul'' _ (hBmeas.pow_const r)]
    exact mul_le_mul_of_nonneg_left hBmoment (by positivity)
  have hB'point : ∀ᵐ ω ∂P, ∀ x y : S, 0 < parabolicNorm
      ((x : ParabolicSpace) - y) →
      ‖(M ω).gammaMap (y : ParabolicSpace) (x : ParabolicSpace)
          (Pi.single i 1) j‖ₑ ≤
        B' ω * ENNReal.ofReal (parabolicNorm
          ((x : ParabolicSpace) - y)) ^ β := by
    filter_upwards [hBpoint] with ω hω
    intro x y hxy
    have hdist' : parabolicNorm
        ((f x : ParabolicSpace) - f y) =
        L⁻¹ * parabolicNorm ((x : ParabolicSpace) - y) := by
      exact parabolicNorm_sub_hsParabolicBoxHomeomorph hLpos
        (x : ParabolicSpace) (y : ParabolicSpace)
    have hdist'0 : 0 < parabolicNorm
        ((f x : ParabolicSpace) - f y) := by
      rw [hdist']
      exact mul_pos (inv_pos.2 hLpos) hxy
    have hdist'20 : parabolicNorm
        ((f x : ParabolicSpace) - f y) ≤ 20 := by
      rw [hdist', inv_mul_eq_div]
      apply (div_le_iff₀ hLpos).2
      exact hdist_bound (x : ParabolicSpace) (y : ParabolicSpace)
        x.property y.property
    have hunit := hω (f x) (f y) hdist'0 hdist'20
    have hrewrite : ENNReal.ofReal
        (parabolicNorm ((f x : ParabolicSpace) - f y)) ^ β =
        aScale * ENNReal.ofReal (parabolicNorm
          ((x : ParabolicSpace) - y)) ^ β := by
      rw [hdist', ENNReal.ofReal_mul (by positivity),
        ENNReal.mul_rpow_of_nonneg _ _ (by dsimp [β]; linarith)]
    have hfx : e.symm (f x) = (x : ParabolicSpace) := by
      simpa using (hf (f x)).symm
    have hfy : e.symm (f y) = (y : ParabolicSpace) := by
      simpa using (hf (f y)).symm
    rw [gammaSplitCompact_pullbackModel_gammaMap] at hunit
    rw [hfx, hfy, hrewrite] at hunit
    simpa [B', aScale, mul_assoc] using hunit
  refine ⟨B', hB'meas, KB * aScale ^ r,
    ENNReal.mul_ne_top hKBtop (by finiteness), ?_, ?_, hB'point⟩
  · simpa only [mul_comm] using hB'moment
  · have hβ : 0 ≤ β := by
      dsimp [β]
      linarith
    have hscale : aScale ≤ 1 := by
      dsimp [aScale]
      apply ENNReal.rpow_le_one
      · exact ENNReal.ofReal_le_one.mpr (by
          rw [inv_le_one₀ hLpos]
          exact hLone)
      exact hβ
    have hscale_pow : aScale ^ r ≤ 1 := by
      exact pow_le_one₀ (by positivity) hscale
    calc
      KB * aScale ^ r ≤ KB := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hscale_pow (by positivity : 0 ≤ KB))
      _ ≤ (1 + gammaSplitUnitProfile 𝒯 D i j κ
          (max 1 Cbar₀) δ r) * (ENNReal.ofReal C₀) ^ r := hKBbound

private theorem gammaSplitCompact_gammaNormOn_moment_le_of_ae_coordinate_envelopes
    (M : Ω → Model 𝒯 parabolicSemigroup) (γ : ℝ) (S : Set ParabolicSpace)
    (p : ℕ) (hp : 1 ≤ p) (A : Ω → ι → ι → ℝ≥0)
    (a : ι → ι → ℝ≥0∞)
    (hAmeas : ∀ i j, AEMeasurable
      (fun ω => (A ω i j : ℝ≥0∞)) P)
    (hAmoment : ∀ i j, ∫⁻ ω, (A ω i j : ℝ≥0∞) ^ p ∂P ≤ a i j)
    (hApoint : ∀ᵐ ω ∂P, ∀ i j, 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
      ∀ x ∈ S, ∀ y ∈ S,
        |(M ω).gammaMap y x (Pi.single i 1) j| ≤
          (A ω i j : ℝ) * parabolicSemigroup.scaleDist y x ^
            (𝒯.deg i - 𝒯.deg j)) :
    ∫⁻ ω, (M ω).gammaNormOn γ S ^ p ∂P ≤
      (Fintype.card (ι × ι) : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        ∑ ij : ι × ι, a ij.1 ij.2 := by
  let A_sum : Ω → ℝ≥0 := fun ω => ∑ ij : ι × ι, A ω ij.1 ij.2
  have hAij : ∀ ω i j, A ω i j ≤ A_sum ω := by
    intro ω i j
    dsimp [A_sum]
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun ij : ι × ι => A ω ij.1 ij.2)
      (fun ij _ => (zero_le : 0 ≤ A ω ij.1 ij.2))
      (Finset.mem_univ (i, j))
  have hGamma : ∀ᵐ ω ∂P, (M ω).GammaBoundOn γ (A_sum ω : ℝ) S := by
    filter_upwards [hApoint] with ω hω
    intro i j hi hj x hx y hy
    calc
      |(M ω).gammaMap y x (Pi.single i 1) j| ≤
          (A ω i j : ℝ) * parabolicSemigroup.scaleDist y x ^
            (𝒯.deg i - 𝒯.deg j) := hω i j hi hj x hx y hy
      _ ≤ (A_sum ω : ℝ) * parabolicSemigroup.scaleDist y x ^
            (𝒯.deg i - 𝒯.deg j) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hAij ω i j)
          (Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg _ _) _)
  have hA_sum_meas : AEMeasurable
      (fun ω => (A_sum ω : ℝ≥0∞)) P := by
    simpa [A_sum] using
      (Finset.aemeasurable_fun_sum (μ := P) (s := Finset.univ)
        (fun ij _ => hAmeas ij.1 ij.2))
  have hA_sum_moment : ∫⁻ ω, (A_sum ω : ℝ≥0∞) ^ p ∂P ≤
      (Fintype.card (ι × ι) : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        ∑ ij : ι × ι, a ij.1 ij.2 := by
    have h := finiteFamilyEnvelope_moment_le_of_pointwise (P := P)
      (ι := ι × ι) (V := fun ω (ij : ι × ι) =>
        (A ω ij.1 ij.2 : ℝ≥0∞)) hp
      (fun ij => hAmeas ij.1 ij.2)
      (fun ij => hAmoment ij.1 ij.2)
    simp only [finiteFamilyEnvelope] at h
    have hsum : ∀ ω, (∑ ij : ι × ι,
        (A ω ij.1 ij.2 : ℝ≥0∞)) = (A_sum ω : ℝ≥0∞) := by
      intro ω
      simp [A_sum]
    calc
      ∫⁻ ω, (A_sum ω : ℝ≥0∞) ^ p ∂P =
          ∫⁻ ω, (∑ ij : ι × ι,
            (A ω ij.1 ij.2 : ℝ≥0∞)) ^ p ∂P := by
        apply lintegral_congr
        intro ω
        rw [hsum]
      _ ≤ (Fintype.card (ι × ι) : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          ∑ ij : ι × ι, a ij.1 ij.2 := h
  exact randomModel_gammaNormOn_moment_le_of_gammaBound M γ S p
    (B := fun ω => (A_sum ω : ℝ≥0∞))
    (A := (Fintype.card (ι × ι) : ℝ≥0∞) ^ ((p : ℝ) - 1) *
      ∑ ij : ι × ι, a ij.1 ij.2)
    hGamma (Filter.Eventually.of_forall fun ω => ENNReal.coe_ne_top)
    hA_sum_moment

theorem randomModel_gammaNormOn_moment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒯 : RegularityStructure ι) (γ κbar θ : ℝ)
    (hκbar : 0 < κbar) (hθ : 0 ≤ θ)
    (DΓ : Set (ι × ι)) (S : Set ParabolicSpace)
    (hS : IsCompact S) (p : ℕ) (hp : 1 ≤ p) :
    ∃ q : ℕ, p ≤ q ∧ ∀ Cbar : ℝ, ∃ K : ℝ, 0 ≤ K ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (Z : Ω → Model 𝒯 parabolicSemigroup) (C : ℝ),
      0 ≤ C → C ≤ Cbar →
      IsContinuousRandomModelWithFieldsOn Z S →
      (∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ ω,
        ∀ x y : ParabolicSpace,
        |(Z ω).gammaMap y x (Pi.single i 1) j| ≤
          C * parabolicSemigroup.scaleDist y x ^
            (𝒯.deg i - 𝒯.deg j)) →
      (∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
        ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖(Z ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
            (𝒯.deg i - 𝒯.deg j + κbar)) ^ q) →
      AEMeasurable (fun ω => (Z ω).gammaNormOn γ S) P ∧
      ∫⁻ ω, (Z ω).gammaNormOn γ S ^ p ∂P ≤
        ENNReal.ofReal (K * C ^ p) := by
  have _hθ : 0 ≤ θ := hθ
  obtain ⟨δ, hδ, hδκ, hδall⟩ :=
    gammaSplit_uniform_delta 𝒯 κbar hκbar
  obtain ⟨r, hpr, hr, hreserveκ, hreserveδ⟩ :=
    gammaSplit_exists_reserve p κbar δ hκbar hδ
  let q : ℕ := 2 * r
  have hpq : p ≤ q := by
    dsimp [q]
    omega
  have hrq : 2 * r ≤ q := by rfl
  refine ⟨q, hpq, ?_⟩
  intro Cbar
  obtain ⟨R, hRpos, hR⟩ := hS.isBounded.exists_pos_norm_le
  let distFun : ParabolicSpace × ParabolicSpace → ℝ :=
    fun z => parabolicNorm (z.1 - z.2)
  have hdistCont : Continuous distFun :=
    continuous_parabolicNorm.comp (continuous_fst.sub continuous_snd)
  have hcompactProd : IsCompact (S ×ˢ S) := hS.prod hS
  have hcompactDist : IsCompact ((S ×ˢ S).image distFun) :=
    hcompactProd.image hdistCont
  obtain ⟨Rdist, hRdistpos, hRdist⟩ :=
    hcompactDist.isBounded.exists_pos_norm_le
  let L : ℝ := max (2 * max 1 R) (Rdist / 20)
  have hL : 2 ≤ L := by
    dsimp [L]
    exact le_max_of_le_left (by
      have : 1 ≤ max 1 R := le_max_left _ _
      linarith)
  have hLpos : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hbound : ∀ x ∈ S, ‖x‖ ≤ L / 2 := by
    intro x hx
    have hxR := hR x hx
    have hmax : 2 * max 1 R ≤ L := le_max_left _ _
    have hRle : R ≤ L / 2 := by
      have hRmax : R ≤ max 1 R := le_max_right _ _
      linarith
    exact hxR.trans hRle
  have hdist_bound : ∀ x y, x ∈ S → y ∈ S →
      parabolicNorm (x - y) ≤ 20 * L := by
    intro x y hx hy
    have hmem : distFun (x, y) ∈ (S ×ˢ S).image distFun := by
      exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
    have hd := hRdist (distFun (x, y)) hmem
    have hd' : parabolicNorm (x - y) ≤ Rdist := by
      change |parabolicNorm (x - y)| ≤ Rdist at hd
      rw [abs_of_nonneg (parabolicNorm_nonneg _)] at hd
      exact hd
    have hmax : Rdist / 20 ≤ L := le_max_right _ _
    linarith
  let Aexp : ℝ := 1 + κbar + 2 * ∑ k : ι, |𝒯.deg k|
  let Lpow : ℝ := L ^ Aexp
  have hLpow : 0 ≤ Lpow := by
    dsimp [Lpow]
    positivity
  have hLpowtop : ENNReal.ofReal Lpow ≠ ∞ := ENNReal.ofReal_ne_top
  let Profile : ι → ι → ℝ≥0∞ := fun i j =>
    1 + gammaSplitUnitProfile 𝒯 DΓ i j κbar
      (max 1 (Cbar * Lpow)) δ r
  let V : ι → ι → ℝ≥0∞ := fun i j =>
    if h : 𝒯.deg i < γ ∧ 𝒯.deg j < 𝒯.deg i then
      Profile i j * ENNReal.ofReal Lpow
    else 0
  have hProfileTop : ∀ i j, Profile i j ≠ ∞ := by
    intro i j
    dsimp [Profile]
    apply ENNReal.add_ne_top.mpr
    refine ⟨ENNReal.one_ne_top, ?_⟩
    exact gammaSplitCompact_profile_ne_top 𝒯 DΓ i j κbar
      (max 1 (Cbar * Lpow)) δ r hκbar hδ hreserveκ hreserveδ
  have hVtop : ∀ i j, V i j ≠ ∞ := by
    intro i j
    dsimp [V]
    split_ifs
    · exact ENNReal.mul_ne_top (hProfileTop i j) hLpowtop
    · exact ENNReal.zero_ne_top
  have hProfilePow (i j : ι) : Profile i j ≤ Profile i j ^ r := by
    have hone : 1 ≤ Profile i j := by
      change 1 ≤ 1 + gammaSplitUnitProfile 𝒯 DΓ i j κbar
        (max 1 (Cbar * Lpow)) δ r
      exact le_add_of_nonneg_right (by positivity)
    simpa only [pow_one] using (pow_le_pow_right' hone hr)
  let KENN : ℝ≥0∞ :=
    (Fintype.card (ι × ι) : ℝ≥0∞) ^ ((p : ℝ) - 1) *
      ∑ ij : ι × ι, V ij.1 ij.2 ^ p
  have hKENNtop : KENN ≠ ∞ := by
    dsimp [KENN]
    apply ENNReal.mul_ne_top
    · have hpReal : 0 ≤ (p : ℝ) - 1 := by
        have : (1 : ℝ) ≤ p := by exact_mod_cast hp
        linarith
      exact ENNReal.rpow_lt_top_of_nonneg hpReal ENNReal.coe_ne_top |>.ne
    · apply ENNReal.sum_ne_top.mpr
      intro ij hij
      exact ENNReal.pow_ne_top (hVtop ij.1 ij.2)
  refine ⟨KENN.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro Ω _ P _ Z C hC hCbar hZ hdet hann
  let U : ι → ι → ℝ≥0∞ := fun i j => V i j * ENNReal.ofReal C
  let a : ι → ι → ℝ≥0∞ := fun i j => U i j ^ p
  have hm : ∀ x y a b, AEMeasurable
      (fun ω => (Z ω).gammaMap x y (Pi.single a 1) b) P := by
    intro x y a b
    exact (hZ.1.2.1 a b y x).aemeasurable
  have hcoordData : ∀ i j, 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
      ∃ (B : Ω → ℝ≥0∞) (KB : ℝ≥0∞), AEMeasurable B P ∧ KB ≠ ∞ ∧
        (∫⁻ ω, B ω ^ r ∂P ≤ KB) ∧
        KB ≤ Profile i j * (ENNReal.ofReal (C * Lpow)) ^ r ∧
        (∀ᵐ ω ∂P, ∀ x y : S, 0 < parabolicNorm
          ((x : ParabolicSpace) - y) →
          ‖(Z ω).gammaMap (y : ParabolicSpace) (x : ParabolicSpace)
              (Pi.single i 1) j‖ₑ ≤
            B ω * ENNReal.ofReal (parabolicNorm
              ((x : ParabolicSpace) - y)) ^ (𝒯.deg i - 𝒯.deg j)) := by
    intro i j hi hj
    obtain ⟨B, hBm, KB, hKBtop, hBmoment, hKBbound, hBpoint⟩ :=
      gammaSplitCompact_coordinate_envelope S L hL hbound hdist_bound Z DΓ
        γ κbar C Cbar δ i j hr hrq hκbar hC hCbar hreserveκ hδ hreserveδ
        (by linarith [hδκ])
        (fun k hjk hik => (hδall i j hj k hjk hik).1)
        (fun k hjk hik => (hδall i j hj k hjk hik).2)
        hm hdet hann (fun ω => hZ.1.2.2.2 ω i j) hi hj
    refine ⟨B, KB, hBm, hKBtop, hBmoment, ?_, hBpoint⟩
    have hKBbound' : KB ≤ Profile i j * (ENNReal.ofReal (C * Lpow)) ^ r := by
      simpa [Profile, Lpow, Aexp] using hKBbound
    exact hKBbound'
  let Bcoord : ι → ι → Ω → ℝ≥0∞ := fun i j =>
    if h : 𝒯.deg i < γ ∧ 𝒯.deg j < 𝒯.deg i then
      Classical.choose (hcoordData i j h.1 h.2)
    else fun _ => 0
  let Acoord : Ω → ι → ι → ℝ≥0 := fun ω i j =>
    (Bcoord i j ω).toNNReal
  have hcoordSpec : ∀ i j (hi : 𝒯.deg i < γ) (hj : 𝒯.deg j < 𝒯.deg i),
      AEMeasurable (Bcoord i j) P ∧
      (∫⁻ ω, Bcoord i j ω ^ r ∂P ≤ U i j ^ r) ∧
      (∀ᵐ ω ∂P, ∀ x y : S, 0 < parabolicNorm
        ((x : ParabolicSpace) - y) →
        ‖(Z ω).gammaMap (y : ParabolicSpace) (x : ParabolicSpace)
            (Pi.single i 1) j‖ₑ ≤
          Bcoord i j ω * ENNReal.ofReal (parabolicNorm
            ((x : ParabolicSpace) - y)) ^ (𝒯.deg i - 𝒯.deg j)) := by
    intro i j hi hj
    let H := hcoordData i j hi hj
    obtain ⟨KB, hBm, hKBtop, hBmoment, hKBbound, hBpoint⟩ :=
      Classical.choose_spec H
    have hBcoord : Bcoord i j = Classical.choose H := by
      simp [Bcoord, hi, hj]
    have hBm' : AEMeasurable (Bcoord i j) P := by
      rw [hBcoord]
      exact hBm
    have hBmoment' : ∫⁻ ω, Bcoord i j ω ^ r ∂P ≤ U i j ^ r := by
      have hKBbound' : KB ≤ U i j ^ r := by
        have hsource : Profile i j * (ENNReal.ofReal (C * Lpow)) ^ r ≤
            U i j ^ r := by
          dsimp [U, V]
          simp [hi, hj]
          rw [ENNReal.ofReal_mul hC, mul_pow]
          calc
            Profile i j *
                  ((ENNReal.ofReal C) ^ r * (ENNReal.ofReal Lpow) ^ r) =
                (ENNReal.ofReal C) ^ r * (ENNReal.ofReal Lpow) ^ r *
                  Profile i j := by ac_rfl
            _ ≤ (ENNReal.ofReal C) ^ r * (ENNReal.ofReal Lpow) ^ r *
                  Profile i j ^ r := by
              exact mul_le_mul_of_nonneg_left (hProfilePow i j) (by positivity)
            _ = (Profile i j * ENNReal.ofReal Lpow * ENNReal.ofReal C) ^ r := by
              rw [mul_pow, mul_pow]
              ac_rfl
        have hKBbound' : KB ≤ Profile i j *
            (ENNReal.ofReal (C * Lpow)) ^ r := by
          simpa [Profile, Lpow, Aexp] using hKBbound
        exact hKBbound'.trans hsource
      rw [hBcoord]
      exact hBmoment.trans hKBbound'
    have hBpoint' : ∀ᵐ ω ∂P, ∀ x y : S, 0 < parabolicNorm
        ((x : ParabolicSpace) - y) →
        ‖(Z ω).gammaMap (y : ParabolicSpace) (x : ParabolicSpace)
            (Pi.single i 1) j‖ₑ ≤
          Bcoord i j ω * ENNReal.ofReal (parabolicNorm
            ((x : ParabolicSpace) - y)) ^ (𝒯.deg i - 𝒯.deg j) := by
      rw [hBcoord]
      exact hBpoint
    exact ⟨hBm', hBmoment', hBpoint'⟩
  have hBmeas : ∀ i j, AEMeasurable (Bcoord i j) P := by
    intro i j
    by_cases hij : 𝒯.deg i < γ ∧ 𝒯.deg j < 𝒯.deg i
    · exact (hcoordSpec i j hij.1 hij.2).1
    ·
      have hzero : Bcoord i j = fun _ => 0 := by simp [Bcoord, hij]
      rw [hzero]
      exact aemeasurable_const
  have hBmoment : ∀ i j, ∫⁻ ω, Bcoord i j ω ^ r ∂P ≤ U i j ^ r := by
    intro i j
    by_cases hij : 𝒯.deg i < γ ∧ 𝒯.deg j < 𝒯.deg i
    · exact (hcoordSpec i j hij.1 hij.2).2.1
    · dsimp [Bcoord, U, V]
      simp [hij]
  have hAmeas : ∀ i j, AEMeasurable
      (fun ω => (Acoord ω i j : ℝ≥0∞)) P := by
    intro i j
    simpa [Acoord] using (hBmeas i j).ennreal_toNNReal.coe_nnreal_ennreal
  have hBtop : ∀ i j, ∀ᵐ ω ∂P, Bcoord i j ω ≠ ∞ := by
    intro i j
    have hUtop : U i j ^ r ≠ ∞ := by
      exact ENNReal.pow_ne_top (ENNReal.mul_ne_top (hVtop i j)
        ENNReal.ofReal_ne_top)
    filter_upwards [ae_lt_top' ((hBmeas i j).pow_const r)
      (ne_top_of_le_ne_top hUtop (hBmoment i j))] with ω hω
    by_contra htop
    rw [htop] at hω
    simp [Nat.ne_of_gt hr] at hω
  have hAmoment : ∀ i j, ∫⁻ ω, (Acoord ω i j : ℝ≥0∞) ^ p ∂P ≤ a i j := by
    intro i j
    have hlow : ∫⁻ ω, Bcoord i j ω ^ p ∂P ≤ U i j ^ p :=
      gammaSplitCompact_lower_ennreal_moment (Bcoord i j) (hBmeas i j)
        hp hpr (hBmoment i j)
    have heq : ∀ᵐ ω ∂P, (Acoord ω i j : ℝ≥0∞) = Bcoord i j ω := by
      filter_upwards [hBtop i j] with ω hω
      simp [Acoord, hω]
    calc
      ∫⁻ ω, (Acoord ω i j : ℝ≥0∞) ^ p ∂P =
          ∫⁻ ω, Bcoord i j ω ^ p ∂P := by
            apply lintegral_congr_ae
            exact heq.mono fun ω hω => congrArg (fun z : ℝ≥0∞ => z ^ p) hω
      _ ≤ U i j ^ p := hlow
  have hApoint : ∀ᵐ ω ∂P, ∀ i j, 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
      ∀ x ∈ S, ∀ y ∈ S,
        |(Z ω).gammaMap y x (Pi.single i 1) j| ≤
          (Acoord ω i j : ℝ) * parabolicSemigroup.scaleDist y x ^
            (𝒯.deg i - 𝒯.deg j) := by
    refine ae_all_iff.2 (fun i => ae_all_iff.2 (fun j => ?_))
    by_cases hij : 𝒯.deg i < γ ∧ 𝒯.deg j < 𝒯.deg i
    · have hspec := hcoordSpec i j hij.1 hij.2
      filter_upwards [hspec.2.2, hBtop i j] with ω hω htop
      intro hi hj x hx y hy
      have hβ : 0 ≤ 𝒯.deg i - 𝒯.deg j := by linarith
      change |(Z ω).gammaMap y x (Pi.single i 1) j| ≤
        (Bcoord i j ω).toNNReal * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j)
      by_cases hxy : x = y
      · subst y
        have hji : j ≠ i := by
          intro hji
          subst j
          linarith
        rw [(Z ω).gammaMap_self x]
        have hβpos : 0 < 𝒯.deg i - 𝒯.deg j := sub_pos.mpr hj
        have hij' : i ≠ j := Ne.symm hji
        have hzero :
            ((LinearMap.id : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (Pi.single i 1)) j = 0 := by
          simp [hij']
        rw [hzero]
        have hscale : parabolicSemigroup.scaleDist x x = 0 := by
          simp [parabolicSemigroup]
        rw [hscale]
        simp [hβpos.ne']
      · have hdist : 0 < parabolicNorm (y - x) :=
          gammaSplitCompact_parabolicNorm_pos hxy
        have hdist' : 0 < parabolicNorm (x - y) := by
          rw [parabolicNorm_sub_comm]
          exact hdist
        have hreal :
            ENNReal.ofReal ‖(Z ω).gammaMap y x (Pi.single i 1) j‖ ≤
              ENNReal.ofReal ((Bcoord i j ω).toNNReal *
                parabolicSemigroup.scaleDist y x ^
                  (𝒯.deg i - 𝒯.deg j)) := by
          change ENNReal.ofReal ‖(Z ω).gammaMap y x (Pi.single i 1) j‖ ≤
            ENNReal.ofReal ((Bcoord i j ω).toNNReal *
              parabolicNorm (y - x) ^ (𝒯.deg i - 𝒯.deg j))
          rw [ENNReal.ofReal_mul (Bcoord i j ω).toNNReal.coe_nonneg,
            ← ENNReal.ofReal_rpow_of_nonneg
              (parabolicNorm_nonneg _) hβ,
            ENNReal.ofReal_coe_nnreal, ENNReal.coe_toNNReal htop]
          have hω' := hω (⟨x, hx⟩ : S) (⟨y, hy⟩ : S) hdist'
          calc
            ENNReal.ofReal ‖(Z ω).gammaMap y x (Pi.single i 1) j‖ =
                ‖(Z ω).gammaMap y x (Pi.single i 1) j‖ₑ :=
              ofReal_norm ((Z ω).gammaMap y x (Pi.single i 1) j)
            _ ≤ Bcoord i j ω * ENNReal.ofReal (parabolicNorm (x - y)) ^
                (𝒯.deg i - 𝒯.deg j) := by simpa only using hω'
            _ = Bcoord i j ω * ENNReal.ofReal (parabolicNorm (y - x)) ^
                (𝒯.deg i - 𝒯.deg j) := by rw [parabolicNorm_sub_comm]
        have hq : 0 ≤ (Bcoord i j ω).toNNReal *
            parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j) := by
          exact mul_nonneg (Bcoord i j ω).toNNReal.coe_nonneg
            (Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg _ _) _)
        have hnorm := (ENNReal.ofReal_le_ofReal_iff hq).mp hreal
        simpa only [Real.norm_eq_abs] using hnorm
    · filter_upwards with ω
      intro hi hj
      exact (hij ⟨hi, hj⟩).elim
  have hgamma := gammaSplitCompact_gammaNormOn_moment_le_of_ae_coordinate_envelopes
    (P := P) Z γ S p hp Acoord a hAmeas hAmoment hApoint
  have hsum : (∑ ij : ι × ι, U ij.1 ij.2 ^ p) =
      (∑ ij : ι × ι, V ij.1 ij.2 ^ p) * (ENNReal.ofReal C) ^ p := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    dsimp [U]
    rw [mul_pow]
  have hrewrite :
      (Fintype.card (ι × ι) : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        ∑ ij : ι × ι, U ij.1 ij.2 ^ p =
      KENN * (ENNReal.ofReal C) ^ p := by
    dsimp [KENN]
    rw [hsum]
    ac_rfl
  have hfinalENN : ∫⁻ ω, (Z ω).gammaNormOn γ S ^ p ∂P ≤
      KENN * (ENNReal.ofReal C) ^ p := by
    exact hgamma.trans_eq hrewrite
  have hCpow : (ENNReal.ofReal C) ^ p = ENNReal.ofReal (C ^ p) := by
    exact (ENNReal.ofReal_pow hC p).symm
  constructor
  · exact randomModel_gammaNormOn_aemeasurable_of_continuousWithFields hZ γ
  · calc
      ∫⁻ ω, (Z ω).gammaNormOn γ S ^ p ∂P ≤
          KENN * ENNReal.ofReal (C ^ p) := by simpa [hCpow] using hfinalENN
      _ = ENNReal.ofReal (KENN.toReal * C ^ p) := by
        rw [ENNReal.ofReal_mul (ENNReal.toReal_nonneg)]
        rw [ENNReal.ofReal_toReal hKENNtop]

end RegularityStructures

end
