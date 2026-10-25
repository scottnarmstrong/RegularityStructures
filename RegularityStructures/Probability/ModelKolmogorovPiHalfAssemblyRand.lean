/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyConcreteDiff
public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyUniformDiffRand
public import RegularityStructures.Probability.ModelKolmogorovPiHalfMomentTools
public import RegularityStructures.Probability.ModelKolmogorovPiHalfCellWeight

/-!
# Measurability and moments of the concrete random parts

* `measurable_piHalfCellRandPartA_omega`, `measurable_piHalfCellDiffRandPartA_omega`: the random
  parts of the cell weights are measurable in `ω` when the off-diagonal field is jointly measurable.
* `lintegral_sum_pow_le_card_mul`: `E (∑_{k ∈ F} g_k)^q ≤ (|F| B)^q` if `E g_k^q ≤ B^q`.
* `lintegral_piHalfCellRand_pow_le`, `lintegral_piHalfCellDiffRand_pow_le`: the moment bounds
  `E R_{j,i,c}^q ≤ (K C s_j^{(deg i + κ)/ℓ})^q` required by the skeleton.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem measurable_piHalfCellRandPartA_omega {𝒯 : RegularityStructure ι} (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (n : ℕ) (C s : ℝ) (x₀ : ParabolicSpace) (k : ι) {Ω : Type*}
    [MeasurableSpace Ω] {Z : Ω → Model 𝒯 parabolicSemigroup}
    (hmOff : Measurable (fun z : Ω × ParabolicSpace => (Z z.1).regPi x₀ (Pi.single k 1) s z.2)) :
    Measurable (fun ω => piHalfCellRandPartA 𝒯 Dπ DΓ n C s x₀ k (Z ω)) := by
  have h1 : Measurable (fun z : Ω × ParabolicSpace =>
      ‖(Z z.1).regPi x₀ (Pi.single k 1) s z.2‖ₑ) := hmOff.enorm
  have h2 : Measurable (fun z : Ω × ParabolicSpace =>
      ENNReal.ofReal (piHalfCellDetFunA 𝒯 Dπ DΓ k C s x₀ z.2)) :=
    (measurable_piHalfCellDetFunA 𝒯 Dπ DΓ k C s x₀).ennreal_ofReal.comp measurable_snd
  have hE : Measurable (fun z : Ω × ParabolicSpace =>
      ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - z.2))) :=
    ((measurable_kernelBlockEnvelope n s).comp (measurable_const.sub measurable_snd)).ennreal_ofReal
  exact (hE.mul (h1.sub h2)).lintegral_prod_right'

theorem measurable_piHalfCellDiffRandPartA_omega {𝒯 : RegularityStructure ι} (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (n : ℕ) (C ε θ s : ℝ) (x₀ : ParabolicSpace) (k : ι) {Ω : Type*}
    [MeasurableSpace Ω] {Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup}
    (hmOff : Measurable (fun z : Ω × ParabolicSpace =>
      (Z₁ z.1).regPi x₀ (Pi.single k 1) s z.2 - (Z₂ z.1).regPi x₀ (Pi.single k 1) s z.2)) :
    Measurable (fun ω => piHalfCellDiffRandPartA 𝒯 Dπ DΓ n C ε θ s x₀ k (Z₁ ω) (Z₂ ω)) := by
  have h1 : Measurable (fun z : Ω × ParabolicSpace =>
      ‖(Z₁ z.1).regPi x₀ (Pi.single k 1) s z.2 - (Z₂ z.1).regPi x₀ (Pi.single k 1) s z.2‖ₑ) :=
    hmOff.enorm
  have h2 : Measurable (fun z : Ω × ParabolicSpace =>
      ENNReal.ofReal (piHalfCellDiffDetFunA 𝒯 Dπ DΓ k C ε θ s x₀ z.2)) :=
    (measurable_piHalfCellDetFunCoeffA 𝒯 Dπ DΓ k _ s x₀).ennreal_ofReal.comp measurable_snd
  have hE : Measurable (fun z : Ω × ParabolicSpace =>
      ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - z.2))) :=
    ((measurable_kernelBlockEnvelope n s).comp (measurable_const.sub measurable_snd)).ennreal_ofReal
  exact (hE.mul (h1.sub h2)).lintegral_prod_right'

/-- Minkowski-type bound for a finite sum. -/
theorem lintegral_sum_pow_le_card_mul {κ Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (F : Finset κ) (g : κ → Ω → ℝ≥0∞) (q : ℕ) (hq : 1 ≤ q) {B : ℝ}
    (hg : ∀ k ∈ F, AEMeasurable (g k) P)
    (h : ∀ k ∈ F, ∫⁻ ω, g k ω ^ q ∂P ≤ ENNReal.ofReal B ^ q) :
    ∫⁻ ω, (∑ k ∈ F, g k ω) ^ q ∂P ≤ ENNReal.ofReal (F.card * B) ^ q := by
  calc ∫⁻ ω, (∑ k ∈ F, g k ω) ^ q ∂P
      ≤ ∫⁻ ω, (F.card : ℝ≥0∞) ^ (q - 1) * ∑ k ∈ F, g k ω ^ q ∂P :=
        lintegral_mono fun ω => piHalf_finset_sum_pow_le F (fun k => g k ω) hq
    _ = (F.card : ℝ≥0∞) ^ (q - 1) * ∑ k ∈ F, ∫⁻ ω, g k ω ^ q ∂P := by
        rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)),
          lintegral_finsetSum' _ fun k hk => (hg k hk).pow_const q]
    _ ≤ (F.card : ℝ≥0∞) ^ (q - 1) * ∑ _k ∈ F, ENNReal.ofReal B ^ q := by
        gcongr with k hk
        exact h k hk
    _ = ENNReal.ofReal (F.card * B) ^ q := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast, mul_pow, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hq]

/-- Moment of the rescaled random part: `∫⁻ (ofReal a * R)^q ≤ ofReal (a b)^q` from `∫⁻ R^q ≤ ofReal b ^ q`. -/
theorem lintegral_ofReal_mul_pow_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {R : Ω → ℝ≥0∞} {a b : ℝ} (ha : 0 ≤ a) (q : ℕ)
    (h : ∫⁻ ω, R ω ^ q ∂P ≤ ENNReal.ofReal b ^ q) :
    ∫⁻ ω, (ENNReal.ofReal a * R ω) ^ q ∂P ≤ ENNReal.ofReal (a * b) ^ q := by
  simp only [mul_pow]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  refine (mul_le_mul' le_rfl h).trans (le_of_eq ?_)
  rw [← mul_pow, ← ENNReal.ofReal_mul ha]

/-- Moment bound for the concrete random part. -/
theorem lintegral_piHalfCellRand_pow_le (𝒯 : RegularityStructure ι) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (nEnv : ℕ) (T : Set ParabolicSpace) (κ C c₀ : ℝ) (q : ℕ) (hq : 1 ≤ q)
    (KR : ι → ℝ) (hKR : ∀ k, 0 ≤ KR k) (hc₀ : 0 ≤ c₀) (hC : 0 ≤ C) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (Z : Ω → Model 𝒯 parabolicSemigroup) (j : ℕ) (i : ι)
    (c : ℕ)
    (hmeas : ∀ k, AEMeasurable (fun ω => piHalfCellRandPartA 𝒯 Dπ DΓ nEnv C (piHalfScale j)
      (piHalfCellRep T j c) k (Z ω)) P)
    (hmom : ∀ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i),
      ∫⁻ ω, piHalfCellRandPartA 𝒯 Dπ DΓ nEnv C (piHalfScale j) (piHalfCellRep T j c) k (Z ω) ^ q ∂P ≤
        ENNReal.ofReal (KR k * max 1 C * C * piHalfScale j ^ ((𝒯.deg k + κ) / 4)) ^ q) :
    AEMeasurable (fun ω => piHalfCellRand 𝒯 Dπ DΓ nEnv T C c₀ (Z ω) j i c) P ∧
      ∫⁻ ω, piHalfCellRand 𝒯 Dπ DΓ nEnv T C c₀ (Z ω) j i c ^ q ∂P ≤
        ENNReal.ofReal (c₀ * ((Fintype.card ι : ℝ) * ∑ k, KR k) * max 1 C * C *
          piHalfScale j ^ ((𝒯.deg i + κ) / 4)) ^ q := by
  have hs := piHalfScale_pos j
  have hm0 : 0 ≤ max 1 C := le_trans zero_le_one (le_max_left _ _)
  set F := Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i) with hF
  set g : ι → Ω → ℝ≥0∞ := fun k ω => ENNReal.ofReal (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
    piHalfCellRandPartA 𝒯 Dπ DΓ nEnv C (piHalfScale j) (piHalfCellRep T j c) k (Z ω) with hg
  have hgm : ∀ k, AEMeasurable (g k) P := fun k => (hmeas k).const_mul _
  have hsum : AEMeasurable (fun ω => ∑ k ∈ F, g k ω) P :=
    by
    convert Finset.aemeasurable_sum F (fun k _ => hgm k) using 1
    ext ω; simp [Finset.sum_apply]
  refine ⟨(hsum.const_mul _), ?_⟩
  set Kf : ℝ := ∑ k, KR k with hKf
  have hKfk : ∀ k, KR k ≤ Kf := fun k =>
    Finset.single_le_sum (f := KR) (fun k _ => hKR k) (Finset.mem_univ k)
  have hKf0 : 0 ≤ Kf := Finset.sum_nonneg fun k _ => hKR k
  set B : ℝ := Kf * max 1 C * C * piHalfScale j ^ ((𝒯.deg i + κ) / 4) with hB
  have hB0 : 0 ≤ B := by
    rw [hB]; exact mul_nonneg (mul_nonneg (mul_nonneg hKf0 hm0) hC) (Real.rpow_nonneg hs.le _)
  have hterm : ∀ k ∈ F, ∫⁻ ω, g k ω ^ q ∂P ≤ ENNReal.ofReal B ^ q := by
    intro k hk
    have h1 := lintegral_ofReal_mul_pow_le (P := P) (Real.rpow_nonneg hs.le
      ((𝒯.deg i - 𝒯.deg k) / 4)) q (hmom k hk)
    refine h1.trans ?_
    have hexp : piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4) *
        (KR k * max 1 C * C * piHalfScale j ^ ((𝒯.deg k + κ) / 4)) =
        KR k * max 1 C * C * piHalfScale j ^ ((𝒯.deg i + κ) / 4) := by
      have : piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4) * piHalfScale j ^ ((𝒯.deg k + κ) / 4) =
          piHalfScale j ^ ((𝒯.deg i + κ) / 4) := by
        rw [← Real.rpow_add hs]; congr 1; ring
      calc _ = KR k * max 1 C * C * (piHalfScale j ^ ((𝒯.deg i - 𝒯.deg k) / 4) *
            piHalfScale j ^ ((𝒯.deg k + κ) / 4)) := by ring
        _ = _ := by rw [this]
    rw [hexp]
    refine pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hKfk k) hm0) hC) (Real.rpow_nonneg hs.le _)
  have hMink := lintegral_sum_pow_le_card_mul (P := P) F g q hq (B := B) (fun k _ => hgm k) hterm
  have hcard : (F.card : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Finset.card_le_univ F
  calc ∫⁻ ω, piHalfCellRand 𝒯 Dπ DΓ nEnv T C c₀ (Z ω) j i c ^ q ∂P
      = ∫⁻ ω, ENNReal.ofReal c₀ ^ q * (∑ k ∈ F, g k ω) ^ q ∂P := by
        refine lintegral_congr fun ω => ?_
        simp only [piHalfCellRand, hg, hF]
        rw [mul_pow]
    _ = ENNReal.ofReal c₀ ^ q * ∫⁻ ω, (∑ k ∈ F, g k ω) ^ q ∂P :=
        lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    _ ≤ ENNReal.ofReal c₀ ^ q * ENNReal.ofReal (F.card * B) ^ q := by gcongr
    _ ≤ ENNReal.ofReal c₀ ^ q * ENNReal.ofReal ((Fintype.card ι : ℝ) * B) ^ q := by
        gcongr
    _ = ENNReal.ofReal (c₀ * ((Fintype.card ι : ℝ) * Kf) * max 1 C * C *
          piHalfScale j ^ ((𝒯.deg i + κ) / 4)) ^ q := by
        rw [← mul_pow, ← ENNReal.ofReal_mul hc₀]
        congr 2
        rw [hB]; ring

end RegularityStructures

end
