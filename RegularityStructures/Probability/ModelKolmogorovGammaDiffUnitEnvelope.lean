/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaDiffUnitGood
public import RegularityStructures.Probability.ModelKolmogorovGammaSplitCompletion
public import RegularityStructures.Probability.ModelKolmogorovAnnealed
public import RegularityStructures.Probability.KolmogorovChentsovSupMoment
import Mathlib.Tactic.Linarith
public import Mathlib.Order.CompletePartialOrder

/-!
# Envelopes for the unit-box Gamma difference

Two source-independent pieces of the unit-box Gamma-difference estimate in the Kolmogorov criterion
for models:

* the global good envelope `gammaDiffGoodGlobalEnvelope`, the supremum over all coarse
  annuli `N` and fine refinements `l` of the good Chen channels of `Γ¹ - Γ²`, normalised by
  `2^{-Nβ} 2^{-lρ/2}`; its `m`-th moment is the source factor `σ` times an explicit constant
  whenever the step moments are (`gammaDiffGoodGlobalEnvelope_moment_le`);
* the fixed-coarse-scale completion `gammaDiffUnitEnvelope_moment_of_split`: a cell envelope,
  a good envelope and a deterministic bad constant give a pointwise Hölder envelope of any
  continuous two-point field on the unit box, with an explicit moment bound.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RegularityStructures

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒯 : RegularityStructure ι}

/-- The good Chen channels of `Γ¹ - Γ²` on the annulus `(N, N + l)`, normalised at the coarse
scale with exponent `β` and at the fine scale with exponent `ϑ`. -/
def gammaDiffGoodGlobalTerm (S : Set ParabolicSpace)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (β ϑ : ℝ) (N l : ℕ) (ω : Ω) : ℝ≥0∞ :=
  (gammaDiffGoodLeftAnnulusStepSup S M₁ M₂ D i j N (N + l) ω +
      gammaDiffGoodRightAnnulusStepSup S M₁ M₂ D i j N (N + l) ω) *
    dyadicBase N ^ (-β) * dyadicBase l ^ (-ϑ)

/-- The global good envelope: the supremum over all coarse annuli and fine refinements. -/
def gammaDiffGoodGlobalEnvelope (S : Set ParabolicSpace)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (β ϑ : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ N : ℕ, ⨆ l : ℕ, gammaDiffGoodGlobalTerm S M₁ M₂ D i j β ϑ N l ω

omit [IsProbabilityMeasure P] in
theorem gammaDiffGoodGlobalTerm_aemeasurable (S : Set ParabolicSpace)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (hm₁ : ∀ x y i j, AEMeasurable
      (fun ω => ((M₁ ω).gammaMap y x (Pi.single i 1) j)) P)
    (hm₂ : ∀ x y i j, AEMeasurable
      (fun ω => ((M₂ ω).gammaMap y x (Pi.single i 1) j)) P)
    (i j : ι) (β ϑ : ℝ) (N l : ℕ) :
    AEMeasurable (gammaDiffGoodGlobalTerm S M₁ M₂ D i j β ϑ N l) P := by
  unfold gammaDiffGoodGlobalTerm
  exact (((gammaDiffGoodLeftAnnulusStepSup_aemeasurable S M₁ M₂ D hm₁ hm₂ i j N
    (N + l)).add (gammaDiffGoodRightAnnulusStepSup_aemeasurable S M₁ M₂ D hm₁ hm₂ i j N
      (N + l))).mul_const _).mul_const _

omit [IsProbabilityMeasure P] in
theorem gammaDiffGoodGlobalEnvelope_aemeasurable (S : Set ParabolicSpace)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (hm₁ : ∀ x y i j, AEMeasurable
      (fun ω => ((M₁ ω).gammaMap y x (Pi.single i 1) j)) P)
    (hm₂ : ∀ x y i j, AEMeasurable
      (fun ω => ((M₂ ω).gammaMap y x (Pi.single i 1) j)) P)
    (i j : ι) (β ϑ : ℝ) :
    AEMeasurable (gammaDiffGoodGlobalEnvelope S M₁ M₂ D i j β ϑ) P :=
  AEMeasurable.iSup fun N => AEMeasurable.iSup fun l =>
    gammaDiffGoodGlobalTerm_aemeasurable S M₁ M₂ D hm₁ hm₂ i j β ϑ N l

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem gammaDiffGoodGlobalTerm_le_envelope_mul_scale (S : Set ParabolicSpace)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (β ϑ : ℝ) (N l : ℕ) (ω : Ω) :
    gammaDiffGoodLeftAnnulusStepSup S M₁ M₂ D i j N (N + l) ω +
        gammaDiffGoodRightAnnulusStepSup S M₁ M₂ D i j N (N + l) ω ≤
      gammaDiffGoodGlobalEnvelope S M₁ M₂ D i j β ϑ ω *
        dyadicBase N ^ β * dyadicBase l ^ ϑ := by
  have hterm : gammaDiffGoodGlobalTerm S M₁ M₂ D i j β ϑ N l ω ≤
      gammaDiffGoodGlobalEnvelope S M₁ M₂ D i j β ϑ ω :=
    le_iSup_of_le N (le_iSup_of_le l le_rfl)
  have hcancelN : dyadicBase N ^ (-β) * dyadicBase N ^ β = 1 := by
    rw [← ENNReal.rpow_add _ _ (dyadicBase_pos _).ne' (dyadicBase_ne_top _)]
    simp
  have hcancelL : dyadicBase l ^ (-ϑ) * dyadicBase l ^ ϑ = 1 := by
    rw [← ENNReal.rpow_add _ _ (dyadicBase_pos _).ne' (dyadicBase_ne_top _)]
    simp
  calc
    _ = gammaDiffGoodGlobalTerm S M₁ M₂ D i j β ϑ N l ω *
        (dyadicBase N ^ β * dyadicBase l ^ ϑ) := by
      unfold gammaDiffGoodGlobalTerm
      calc
        _ = (gammaDiffGoodLeftAnnulusStepSup S M₁ M₂ D i j N (N + l) ω +
            gammaDiffGoodRightAnnulusStepSup S M₁ M₂ D i j N (N + l) ω) *
            (dyadicBase N ^ (-β) * dyadicBase N ^ β) *
            (dyadicBase l ^ (-ϑ) * dyadicBase l ^ ϑ) := by
          rw [hcancelN, hcancelL, mul_one, mul_one]
        _ = _ := by ring
    _ ≤ gammaDiffGoodGlobalEnvelope S M₁ M₂ D i j β ϑ ω *
        (dyadicBase N ^ β * dyadicBase l ^ ϑ) :=
      mul_le_mul_of_nonneg_right hterm (by positivity)
    _ = _ := by ring

private theorem gammaDiffUnitEnvelope_two_pow_eq (N l : ℕ) :
    (2 : ℝ≥0∞) ^ (10 * (N + l)) = dyadicBase N ^ (-10 : ℝ) * dyadicBase l ^ (-10 : ℝ) := by
  have hbase (n : ℕ) : (2 : ℝ≥0∞) ^ (10 * n) = dyadicBase n ^ (-10 : ℝ) := by
    rw [ENNReal.rpow_neg, dyadicBase_rpow_eq_geometric]
    simp [← pow_mul, mul_comm, ← ENNReal.inv_pow]
  rw [hbase, dyadicBase_rpow_eq_geometric, pow_add, ← dyadicBase_rpow_eq_geometric,
    ← dyadicBase_rpow_eq_geometric]

private theorem gammaDiffUnitEnvelope_scale_eq (β ρ : ℝ) (m N l : ℕ) :
    (2 : ℝ≥0∞) ^ (10 * (N + l)) *
        (dyadicBase N ^ ((m : ℝ) * (β + ρ)) * dyadicBase l ^ ((m : ℝ) * ρ)) *
        dyadicBase N ^ (-(m : ℝ) * β) * dyadicBase l ^ (-(m : ℝ) * (ρ / 2)) =
      dyadicBase N ^ ((m : ℝ) * ρ - 10) * dyadicBase l ^ ((m : ℝ) * ρ / 2 - 10) := by
  rw [gammaDiffUnitEnvelope_two_pow_eq]
  calc
    _ = (dyadicBase N ^ (-10 : ℝ) * dyadicBase N ^ ((m : ℝ) * (β + ρ)) *
          dyadicBase N ^ (-(m : ℝ) * β)) *
        (dyadicBase l ^ (-10 : ℝ) * dyadicBase l ^ ((m : ℝ) * ρ) *
          dyadicBase l ^ (-(m : ℝ) * (ρ / 2))) := by ring
    _ = dyadicBase N ^ ((-10 : ℝ) + (m : ℝ) * (β + ρ) + -(m : ℝ) * β) *
        dyadicBase l ^ ((-10 : ℝ) + (m : ℝ) * ρ + -(m : ℝ) * (ρ / 2)) := by
      rw [← ENNReal.rpow_add _ _ (dyadicBase_pos N).ne' (dyadicBase_ne_top N),
        ← ENNReal.rpow_add _ _ (dyadicBase_pos N).ne' (dyadicBase_ne_top N),
        ← ENNReal.rpow_add _ _ (dyadicBase_pos l).ne' (dyadicBase_ne_top l),
        ← ENNReal.rpow_add _ _ (dyadicBase_pos l).ne' (dyadicBase_ne_top l)]
    _ = _ := by
      congr 2 <;> ring

private theorem gammaDiffUnitEnvelope_dyadic_rpow_le {a b : ℝ} (hab : b ≤ a) (n : ℕ) :
    dyadicBase n ^ a ≤ dyadicBase n ^ b := by
  apply ENNReal.rpow_le_rpow_of_exponent_ge _ hab
  unfold dyadicBase
  exact pow_le_one₀ (by positivity) (by norm_num)

omit [IsProbabilityMeasure P] in
/-- **Moment of the global good envelope.**  If the good step moments are
`card² σ L (2^{-N})^{m(β+ρ)} (2^{-l})^{mρ}`, then the envelope normalised with the fine
exponent `ρ / 2` has `m`-th moment at most `σ` times an explicit constant. -/
theorem gammaDiffGoodGlobalEnvelope_moment_le (S : Set ParabolicSpace)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (hm₁ : ∀ x y i j, AEMeasurable
      (fun ω => ((M₁ ω).gammaMap y x (Pi.single i 1) j)) P)
    (hm₂ : ∀ x y i j, AEMeasurable
      (fun ω => ((M₂ ω).gammaMap y x (Pi.single i 1) j)) P)
    (i j : ι) (β ρ : ℝ) {m : ℕ} (hm : 1 ≤ m) (hreserve : 20 < (m : ℝ) * ρ)
    {σ Lleft Lright : ℝ≥0∞}
    (hleft : ∀ N l : ℕ,
      ∫⁻ ω, gammaDiffGoodLeftAnnulusStepSup S M₁ M₂ D i j N (N + l) ω ^ m ∂P ≤
        (Fintype.card (gammaCell S (N + l + 1)) : ℝ≥0∞) ^ 2 *
          (σ * (Lleft * dyadicBase N ^ ((m : ℝ) * (β + ρ)) *
            dyadicBase l ^ ((m : ℝ) * ρ))))
    (hright : ∀ N l : ℕ,
      ∫⁻ ω, gammaDiffGoodRightAnnulusStepSup S M₁ M₂ D i j N (N + l) ω ^ m ∂P ≤
        (Fintype.card (gammaCell S (N + l + 1)) : ℝ≥0∞) ^ 2 *
          (σ * (Lright * dyadicBase N ^ ((m : ℝ) * (β + ρ)) *
            dyadicBase l ^ ((m : ℝ) * ρ)))) :
    ∫⁻ ω, gammaDiffGoodGlobalEnvelope S M₁ M₂ D i j β (ρ / 2) ω ^ m ∂P ≤
      σ * ((2 : ℝ≥0∞) ^ ((m : ℝ) - 1) * (512 : ℝ≥0∞) ^ 2 * (Lleft + Lright) *
        (1 - ((2 : ℝ≥0∞)⁻¹) ^ ((m : ℝ) * ρ / 2 - 10))⁻¹ *
        (1 - ((2 : ℝ≥0∞)⁻¹) ^ ((m : ℝ) * ρ / 2 - 10))⁻¹) := by
  set η : ℝ := (m : ℝ) * ρ / 2 - 10 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  set A : ℝ≥0∞ := (2 : ℝ≥0∞) ^ ((m : ℝ) - 1) * (512 : ℝ≥0∞) ^ 2 * σ * (Lleft + Lright)
    with hA
  have hmeas : ∀ N l, AEMeasurable (gammaDiffGoodGlobalTerm S M₁ M₂ D i j β (ρ / 2) N l) P :=
    fun N l => gammaDiffGoodGlobalTerm_aemeasurable S M₁ M₂ D hm₁ hm₂ i j β (ρ / 2) N l
  have hterm : ∀ N l : ℕ,
      ∫⁻ ω, gammaDiffGoodGlobalTerm S M₁ M₂ D i j β (ρ / 2) N l ω ^ m ∂P ≤
        A * dyadicBase N ^ η * dyadicBase l ^ η := by
    intro N l
    set gL := gammaDiffGoodLeftAnnulusStepSup S M₁ M₂ D i j N (N + l) with hgL
    set gR := gammaDiffGoodRightAnnulusStepSup S M₁ M₂ D i j N (N + l) with hgR
    have hml : AEMeasurable gL P :=
      gammaDiffGoodLeftAnnulusStepSup_aemeasurable S M₁ M₂ D hm₁ hm₂ i j N (N + l)
    have hmr : AEMeasurable gR P :=
      gammaDiffGoodRightAnnulusStepSup_aemeasurable S M₁ M₂ D hm₁ hm₂ i j N (N + l)
    set c : ℝ≥0∞ := (Fintype.card (gammaCell S (N + l + 1)) : ℝ≥0∞) ^ 2 with hc
    set X : ℝ≥0∞ := dyadicBase N ^ ((m : ℝ) * (β + ρ)) * dyadicBase l ^ ((m : ℝ) * ρ)
      with hX
    have hsum : ∫⁻ ω, (gL ω + gR ω) ^ m ∂P ≤
        (2 : ℝ≥0∞) ^ ((m : ℝ) - 1) * c * σ * (Lleft + Lright) * X := by
      have hpoint (ω : Ω) : (gL ω + gR ω) ^ m ≤
          (2 : ℝ≥0∞) ^ ((m : ℝ) - 1) * (gL ω ^ m + gR ω ^ m) := by
        simpa only [ENNReal.rpow_natCast] using
          ENNReal.rpow_add_le_mul_rpow_add_rpow (gL ω) (gR ω)
            (show (1 : ℝ) ≤ m by exact_mod_cast hm)
      calc
        _ ≤ ∫⁻ ω, (2 : ℝ≥0∞) ^ ((m : ℝ) - 1) * (gL ω ^ m + gR ω ^ m) ∂P :=
          lintegral_mono hpoint
        _ = (2 : ℝ≥0∞) ^ ((m : ℝ) - 1) *
            (∫⁻ ω, gL ω ^ m ∂P + ∫⁻ ω, gR ω ^ m ∂P) := by
          rw [lintegral_const_mul'' (f := fun ω => gL ω ^ m + gR ω ^ m) _
              ((hml.pow_const m).add (hmr.pow_const m)),
            lintegral_add_left' (f := fun ω => gL ω ^ m) (hml.pow_const m)]
        _ ≤ (2 : ℝ≥0∞) ^ ((m : ℝ) - 1) *
            (c * (σ * (Lleft * dyadicBase N ^ ((m : ℝ) * (β + ρ)) *
              dyadicBase l ^ ((m : ℝ) * ρ))) +
            c * (σ * (Lright * dyadicBase N ^ ((m : ℝ) * (β + ρ)) *
              dyadicBase l ^ ((m : ℝ) * ρ)))) := by
          gcongr
          · exact hleft N l
          · exact hright N l
        _ = _ := by rw [hX]; ring
    have hpow : ∀ ω, gammaDiffGoodGlobalTerm S M₁ M₂ D i j β (ρ / 2) N l ω ^ m =
        (gL ω + gR ω) ^ m * dyadicBase N ^ (-(m : ℝ) * β) *
          dyadicBase l ^ (-(m : ℝ) * (ρ / 2)) := by
      intro ω
      have hNpow : (dyadicBase N ^ (-β)) ^ m = dyadicBase N ^ (-(m : ℝ) * β) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        congr 1
        ring
      have hLpow : (dyadicBase l ^ (-(ρ / 2))) ^ m = dyadicBase l ^ (-(m : ℝ) * (ρ / 2)) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        congr 1
        ring
      unfold gammaDiffGoodGlobalTerm
      rw [mul_pow, mul_pow, hNpow, hLpow]
    have hnormeq : ∫⁻ ω, gammaDiffGoodGlobalTerm S M₁ M₂ D i j β (ρ / 2) N l ω ^ m ∂P =
        (∫⁻ ω, (gL ω + gR ω) ^ m ∂P) * dyadicBase N ^ (-(m : ℝ) * β) *
          dyadicBase l ^ (-(m : ℝ) * (ρ / 2)) := by
      simp_rw [hpow]
      rw [lintegral_mul_const''
          (f := fun ω => (gL ω + gR ω) ^ m * dyadicBase N ^ (-(m : ℝ) * β)) _
          (((hml.add hmr).pow_const m).mul_const _),
        lintegral_mul_const'' (f := fun ω => (gL ω + gR ω) ^ m) _
          ((hml.add hmr).pow_const m)]
    rw [hnormeq]
    have hcard : c ≤ (512 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞) ^ (10 * (N + l)) :=
      gammaProduct_card_le S (N + l)
    calc
      _ ≤ ((2 : ℝ≥0∞) ^ ((m : ℝ) - 1) * c * σ * (Lleft + Lright) * X) *
          dyadicBase N ^ (-(m : ℝ) * β) * dyadicBase l ^ (-(m : ℝ) * (ρ / 2)) := by
        gcongr
      _ ≤ ((2 : ℝ≥0∞) ^ ((m : ℝ) - 1) *
            ((512 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞) ^ (10 * (N + l))) * σ * (Lleft + Lright) * X) *
          dyadicBase N ^ (-(m : ℝ) * β) * dyadicBase l ^ (-(m : ℝ) * (ρ / 2)) := by
        gcongr
      _ = A * ((2 : ℝ≥0∞) ^ (10 * (N + l)) * X * dyadicBase N ^ (-(m : ℝ) * β) *
          dyadicBase l ^ (-(m : ℝ) * (ρ / 2))) := by rw [hA]; ring
      _ = A * (dyadicBase N ^ ((m : ℝ) * ρ - 10) * dyadicBase l ^ η) := by
        rw [hX, gammaDiffUnitEnvelope_scale_eq]
      _ ≤ A * (dyadicBase N ^ η * dyadicBase l ^ η) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (by positivity))
          (by positivity)
        exact gammaDiffUnitEnvelope_dyadic_rpow_le (by rw [hηdef]; linarith) N
      _ = _ := by ring
  have hinner : ∀ N : ℕ,
      ∫⁻ ω, (⨆ l : ℕ, gammaDiffGoodGlobalTerm S M₁ M₂ D i j β (ρ / 2) N l ω) ^ m ∂P ≤
        ∑' l : ℕ, ∫⁻ ω, gammaDiffGoodGlobalTerm S M₁ M₂ D i j β (ρ / 2) N l ω ^ m ∂P :=
    fun N => lintegral_iSup_pow_le_tsum_lintegral_pow hm (hmeas N)
  have hsup0 : ∫⁻ ω, gammaDiffGoodGlobalEnvelope S M₁ M₂ D i j β (ρ / 2) ω ^ m ∂P ≤
      ∑' N : ℕ, ∫⁻ ω, (⨆ l : ℕ,
        gammaDiffGoodGlobalTerm S M₁ M₂ D i j β (ρ / 2) N l ω) ^ m ∂P :=
    lintegral_iSup_pow_le_tsum_lintegral_pow hm fun N => AEMeasurable.iSup fun l => hmeas N l
  set b : ℝ≥0∞ := ((2 : ℝ≥0∞)⁻¹) ^ η with hb
  have hterm' (N l : ℕ) : A * dyadicBase N ^ η * dyadicBase l ^ η = (A * b ^ N) * b ^ l := by
    simp only [hb, dyadicBase_rpow_eq_geometric]
  calc
    _ ≤ ∑' N : ℕ, ∑' l : ℕ,
        ∫⁻ ω, gammaDiffGoodGlobalTerm S M₁ M₂ D i j β (ρ / 2) N l ω ^ m ∂P :=
      hsup0.trans (ENNReal.tsum_le_tsum hinner)
    _ ≤ ∑' N : ℕ, ∑' l : ℕ, A * dyadicBase N ^ η * dyadicBase l ^ η := by
      gcongr with N l
      exact hterm N l
    _ = ∑' N : ℕ, (A * b ^ N) * ∑' l : ℕ, b ^ l := by
      simp_rw [hterm']
      exact tsum_congr fun N => ENNReal.tsum_mul_left
    _ = A * (1 - b)⁻¹ * (1 - b)⁻¹ := by
      rw [ENNReal.tsum_geometric, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left,
        ENNReal.tsum_geometric]
    _ = _ := by rw [hA, hb]; ring

/-- **Fixed-coarse-scale completion with explicit moments.**  A cell envelope `A0` (the
normalised cell supremum), a good envelope `G` and a deterministic bad constant `Bbad` controlling
the annular steps give a pointwise Hölder envelope of a continuous two-point field on the unit
box. -/
theorem gammaDiffUnitEnvelope_moment_of_split
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (F : S → S → Ω → ℝ) (β ϑ : ℝ) (p : ℕ) (hp : 1 ≤ p)
    (G : Ω → ℝ≥0∞) (Bbad : ℝ≥0∞)
    (hFmeas : ∀ x y, AEMeasurable (F x y) P) (hGmeas : AEMeasurable G P)
    {KA KG : ℝ≥0∞}
    (hA0moment : ∫⁻ ω, gammaProductCellNormalisedSup S F β 0 ω ^ p ∂P ≤ KA)
    (hGmoment : ∫⁻ ω, G ω ^ p ∂P ≤ KG) (hKG : KG ≠ ∞) (hBbad : Bbad ≠ ∞)
    (hG : ∀ (ω : Ω) (N l : ℕ),
      gammaProductLeftStepSupAnnulus S F N (N + l) ω +
          gammaProductRightStepSupAnnulus S F N (N + l) ω ≤
        (G ω + Bbad) * dyadicBase N ^ β * dyadicBase l ^ ϑ)
    (hcont : ∀ ω, Continuous (fun z : S × S => F z.1 z.2 ω))
    (hβ : 0 ≤ β) (hϑ : 0 < ϑ) :
    ∃ B : Ω → ℝ≥0∞, AEMeasurable B P ∧
      (∫⁻ ω, B ω ^ p ∂P ≤
        ((2 : ℝ≥0∞) ^ β) ^ p * (3 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          (KA + (1 - ((2 : ℝ≥0∞)⁻¹) ^ ϑ)⁻¹ ^ p * KG +
            (1 - ((2 : ℝ≥0∞)⁻¹) ^ ϑ)⁻¹ ^ p * Bbad ^ p)) ∧
      (∀ᵐ ω ∂P, ∀ x y : S, 0 < parabolicNorm ((x : ParabolicSpace) - y) →
        ‖F x y ω‖ₑ ≤ B ω * ENNReal.ofReal
          (parabolicNorm ((x : ParabolicSpace) - y)) ^ β) := by
  set A0 : Ω → ℝ≥0∞ := gammaProductCellNormalisedSup S F β 0 with hA0
  set d : ℝ≥0∞ := 1 - ((2 : ℝ≥0∞)⁻¹) ^ ϑ with hd
  set c : ℝ≥0∞ := (2 : ℝ≥0∞) ^ β with hc
  have hA0meas : AEMeasurable A0 P := gammaProductCellNormalisedSup_aemeasurable S F β 0 hFmeas
  let V : Ω → Fin 3 → ℝ≥0∞ := fun ω n =>
    if n = 0 then A0 ω else if n = 1 then d⁻¹ * G ω else d⁻¹ * Bbad
  have hVmeas : ∀ n : Fin 3, AEMeasurable (V · n) P := by
    intro n
    fin_cases n
    · simpa [V] using hA0meas
    · simpa [V] using hGmeas.const_mul d⁻¹
    · exact aemeasurable_const
  let b : Fin 3 → ℝ≥0∞ := fun n =>
    if n = 0 then KA else if n = 1 then d⁻¹ ^ p * KG else d⁻¹ ^ p * Bbad ^ p
  have hb : ∀ n : Fin 3, ∫⁻ ω, V ω n ^ p ∂P ≤ b n := by
    intro n
    fin_cases n
    · simpa [V, b] using hA0moment
    · have heq : (fun ω => V ω (1 : Fin 3) ^ p) = fun ω => d⁻¹ ^ p * G ω ^ p := by
        funext ω
        simp [V, mul_pow]
      change ∫⁻ ω, V ω (1 : Fin 3) ^ p ∂P ≤ d⁻¹ ^ p * KG
      rw [heq, lintegral_const_mul'' _ (hGmeas.pow_const p)]
      gcongr
    · have heq : (fun ω => V ω (2 : Fin 3) ^ p) = fun _ => d⁻¹ ^ p * Bbad ^ p := by
        funext ω
        simp [V, mul_pow]
      change ∫⁻ ω, V ω (2 : Fin 3) ^ p ∂P ≤ d⁻¹ ^ p * Bbad ^ p
      rw [heq]
      simp [MeasureTheory.lintegral_const]
  let H : Ω → ℝ≥0∞ := finiteFamilyEnvelope V
  have hHmeas : AEMeasurable H P := finiteFamilyEnvelope_aemeasurable hVmeas
  have hHmoment : ∫⁻ ω, H ω ^ p ∂P ≤
      (Fintype.card (Fin 3) : ℝ≥0∞) ^ ((p : ℝ) - 1) * ∑ n, b n :=
    finiteFamilyEnvelope_moment_le_of_pointwise hp hVmeas hb
  have hsum : ∑ n : Fin 3, b n = KA + d⁻¹ ^ p * KG + d⁻¹ ^ p * Bbad ^ p := by
    simp [b, Fin.sum_univ_succ, add_assoc]
  refine ⟨fun ω => c * H ω, hHmeas.const_mul c, ?_, ?_⟩
  · calc
      _ = c ^ p * ∫⁻ ω, H ω ^ p ∂P := by
        simp only [mul_pow]
        rw [lintegral_const_mul'' _ (hHmeas.pow_const p)]
      _ ≤ c ^ p * ((Fintype.card (Fin 3) : ℝ≥0∞) ^ ((p : ℝ) - 1) * ∑ n, b n) := by
        gcongr
      _ = _ := by
        rw [hsum, Fintype.card_fin]
        push_cast
        ring
  have hGtop : ∀ᵐ ω ∂P, G ω ≠ ∞ := by
    filter_upwards [ae_lt_top' (hGmeas.pow_const p)
      (ne_top_of_le_ne_top hKG hGmoment)] with ω hω
    intro htop
    rw [htop, ENNReal.top_pow (by omega)] at hω
    exact lt_irrefl _ hω
  filter_upwards [hGtop] with ω hGω
  intro x y hxy0
  have hGB : G ω + Bbad ≠ ∞ := ENNReal.add_ne_top.2 ⟨hGω, hBbad⟩
  have hvalueN (N : ℕ) (x' y' : S)
      (hxy : parabolicNorm ((x' : ParabolicSpace) - y') ≤ 1 / (2 : ℝ) ^ N) :
      ‖F (hsParabolicCellApprox S N x') (hsParabolicCellApprox S N y') ω‖ₑ ≤
        A0 ω * dyadicBase N ^ β := by
    have hcell := gammaProductCellApprox_value_le S hbox F N x' y' ω hxy
    have hnorm := gammaProductCellSup_le_normalisedSup S F β 0 N ω
    simp only [Nat.zero_add] at hnorm
    exact hcell.trans hnorm
  have hvalue (x' y' : S) :
      ‖F (hsParabolicCellApprox S 0 x') (hsParabolicCellApprox S 0 y') ω‖ₑ ≤ A0 ω := by
    have hv := gammaProductCellApprox_value_le_of_box S hbox F x' y' ω
      (gammaSplit_box_distance_le_four S hbox x' y')
    have hn := gammaProductCellSup_le_normalisedSup S F β 0 0 ω
    simpa [dyadicBase] using hv.trans hn
  have hstep (x' y' : S) (l : ℕ) :
      ‖F (hsParabolicCellApprox S l x') (hsParabolicCellApprox S l y') ω -
        F (hsParabolicCellApprox S (l + 1) x') (hsParabolicCellApprox S (l + 1) y') ω‖ₑ ≤
      (G ω + Bbad) * dyadicBase 0 ^ β * dyadicBase l ^ ϑ := by
    have hs := gammaProductCellApprox_step_le_of_box S hbox F l x' y' ω
    have hg := hG ω 0 l
    simp only [Nat.zero_add] at hg
    exact hs.trans hg
  have hstepN (N l : ℕ) (x' y' : S)
      (hxy : parabolicNorm ((x' : ParabolicSpace) - y') ≤ 1 / (2 : ℝ) ^ N) :
      ‖F (hsParabolicCellApprox S (N + l) x') (hsParabolicCellApprox S (N + l) y') ω -
        F (hsParabolicCellApprox S (N + l + 1) x')
          (hsParabolicCellApprox S (N + l + 1) y') ω‖ₑ ≤
        (G ω + Bbad) * dyadicBase N ^ β * dyadicBase l ^ ϑ :=
    (gammaProductCellApprox_step_le_of_annulus S hbox F (Nat.le_add_right N l) x' y' ω
      hxy).trans (hG ω N l)
  have h := gammaSplit_pointwise_bound_of_envelopes_global S hbox F β ϑ ω
    (A0 ω) (G ω) Bbad hGB hβ hϑ (hcont ω) hvalueN hstepN hvalue hstep x y hxy0
  have hH : H ω = A0 ω + d⁻¹ * G ω + d⁻¹ * Bbad := by
    simp [H, V, finiteFamilyEnvelope, Fin.sum_univ_succ, add_assoc]
  calc
    ‖F x y ω‖ₑ ≤ (A0 ω + (G ω + Bbad) / d) * c * ENNReal.ofReal
        (parabolicNorm ((x : ParabolicSpace) - y)) ^ β := h
    _ = c * H ω * ENNReal.ofReal (parabolicNorm ((x : ParabolicSpace) - y)) ^ β := by
      rw [hH, div_eq_mul_inv]
      ring

end RegularityStructures

end
