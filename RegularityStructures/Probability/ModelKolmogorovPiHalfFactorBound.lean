/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfCellWeightARand

/-!
# Factor bounds for the difference version

`PiHalfFactorBoundA P q f A` says that the random variable `f` is either bounded by `A` surely or
has `q`-th moment at most `A^q`. `piHalf_lintegral_mul_pow_le_of_factorBound` bounds the `p`-th
moment of a product of two such factors by `(A B)^p` (`2 p ≤ q`). The four lemmas
`piHalf_factorBound_*` produce the factor bounds from the hypotheses of `hPiHalf`: for the `Γ`
coefficient `max 1 C * d^α`, for the diagonal `Π` coefficient `C s^β`, and for their differences
`C ε^θ * ...`, with the unified exponents `piHalfRandAlphaA`, `piHalfRandBetaA`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `f` is either surely bounded by `A` or has `q`-th moment at most `A^q`. -/
def PiHalfFactorBoundA {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (q : ℕ) (f : Ω → ℝ)
    (A : ℝ) : Prop :=
  (∀ ω, ‖f ω‖ₑ ≤ ENNReal.ofReal A) ∨ ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal A ^ q

/-- The hypotheses of `hPiHalf` on the difference of two models, for one model pair. -/
structure PiHalfDiffMomentHypsA (𝒯 : RegularityStructure ι) (γ κbar θ : ℝ) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (q : ℕ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup) (C ε : ℝ) : Prop where
  piDet : ∀ i ∈ Dπ, 𝒯.deg i < γ → ∀ ω, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
    |(Z₁ ω).regPi x (Pi.single i 1) t x - (Z₂ ω).regPi x (Pi.single i 1) t x| ≤
      C * ε ^ θ * t ^ (𝒯.deg i / parabolicSemigroup.order)
  gammaDet : ∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ ω,
    ∀ x y : ParabolicSpace, |(Z₁ ω).gammaMap y x (Pi.single i 1) j -
        (Z₂ ω).gammaMap y x (Pi.single i 1) j| ≤
      C * ε ^ θ * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)
  piAnn : ∀ i, i ∉ Dπ → 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
    ∫⁻ ω, ‖(Z₁ ω).regPi x (Pi.single i 1) t x - (Z₂ ω).regPi x (Pi.single i 1) t x‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (C * ε ^ θ *
        t ^ ((𝒯.deg i + κbar) / parabolicSemigroup.order)) ^ q
  gammaAnn : ∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
    ∀ x y : ParabolicSpace, ∫⁻ ω, ‖(Z₁ ω).gammaMap y x (Pi.single i 1) j -
        (Z₂ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (C * ε ^ θ * parabolicSemigroup.scaleDist y x ^
        (𝒯.deg i - 𝒯.deg j + κbar)) ^ q

end RegularityStructures

end

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem PiHalfFactorBoundA.mono {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {q : ℕ}
    {f : Ω → ℝ} {A A' : ℝ} (h : PiHalfFactorBoundA P q f A) (hA : A ≤ A') :
    PiHalfFactorBoundA P q f A' := by
  rcases h with h | h
  · exact Or.inl fun ω => (h ω).trans (ENNReal.ofReal_le_ofReal hA)
  · exact Or.inr (h.trans (piHalf_ofReal_pow_le hA q))

/-- A factor bound gives all integer moments `m ≤ q`. -/
theorem PiHalfFactorBoundA.moment_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {q : ℕ} {f : Ω → ℝ} {A : ℝ} (h : PiHalfFactorBoundA P q f A)
    (hf : Measurable f) {m : ℕ} (hm : 1 ≤ m) (hmq : m ≤ q) :
    ∫⁻ ω, ‖f ω‖ₑ ^ m ∂P ≤ ENNReal.ofReal A ^ m := by
  rcases h with h | h
  · calc ∫⁻ ω, ‖f ω‖ₑ ^ m ∂P ≤ ∫⁻ _ω, ENNReal.ofReal A ^ m ∂P :=
          lintegral_mono fun ω => pow_le_pow_left' (h ω) m
      _ = ENNReal.ofReal A ^ m := by simp
  · exact piHalf_lintegral_pow_le_of_le hf.aestronglyMeasurable hm hmq h

/-- The `p`-th moment of a product of two factors with factor bounds. -/
theorem piHalf_lintegral_mul_pow_le_of_factorBound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {q p : ℕ} (hp : 1 ≤ p) (hpq : 2 * p ≤ q)
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) {A B : ℝ} (hA0 : 0 ≤ A)
    (hA : PiHalfFactorBoundA P q f A) (hB : PiHalfFactorBoundA P q g B) :
    ∫⁻ ω, (‖f ω‖ₑ * ‖g ω‖ₑ) ^ p ∂P ≤ ENNReal.ofReal (A * B) ^ p := by
  have h1 := hA.moment_le hf (by omega : 1 ≤ 2 * p) hpq
  have h2 := hB.moment_le hg (by omega : 1 ≤ 2 * p) hpq
  have h := piHalf_lintegral_mul_pow_le (P := P) (a := fun ω => ‖f ω‖ₑ)
    (b := fun ω => ‖g ω‖ₑ) hf.enorm.aemeasurable hg.enorm.aemeasurable h1 h2
  rwa [← mul_pow, ← ENNReal.ofReal_mul hA0] at h

/-- Factor bound for the `Γ` coefficient. -/
theorem piHalf_factorBound_gamma {𝒯 : RegularityStructure ι} {γ κbar C : ℝ}
    {Dπ : Set ι} {DΓ : Set (ι × ι)} {q : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : Ω → Model 𝒯 parabolicSemigroup} (hH : PiHalfMomentHypsA 𝒯 γ κbar Dπ DΓ q P Z C)
    {k : ι} (hkγ : 𝒯.deg k < γ) {j : ι} (hjk : 𝒯.deg j ≤ 𝒯.deg k) (x₀ w : ParabolicSpace) :
    PiHalfFactorBoundA P q (fun ω => (Z ω).gammaMap w x₀ (Pi.single k 1) j)
      (max 1 C * parabolicNorm (x₀ - w) ^ piHalfRandAlphaA 𝒯 κbar DΓ k j) := by
  classical
  by_cases hG : 𝒯.deg j = 𝒯.deg k ∨ (k, j) ∈ DΓ
  · have hα : piHalfRandAlphaA 𝒯 κbar DΓ k j = 𝒯.deg k - 𝒯.deg j := by
      simp [piHalfRandAlphaA, hG]
    rw [hα]
    exact Or.inl fun ω => piHalf_gamma_enorm_le_of_det hkγ (Z ω)
      (fun i j' h1 h2 h3 x y => hH.gammaDet i j' h1 h2 h3 ω x y) hjk hG x₀ w
  · have hjlt : 𝒯.deg j < 𝒯.deg k := lt_of_le_of_ne hjk fun h => hG (Or.inl h)
    have hnot : (k, j) ∉ DΓ := fun h => hG (Or.inr h)
    have hα : piHalfRandAlphaA 𝒯 κbar DΓ k j = (𝒯.deg k - 𝒯.deg j) + κbar := by
      simp [piHalfRandAlphaA, hG]
    rw [hα]
    have h := hH.gammaAnn k j hnot hkγ hjlt x₀ w
    rw [piHalf_scaleDist_eq] at h
    exact Or.inr (h.trans (piHalf_ofReal_pow_le
      (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg (parabolicNorm_nonneg _) _)) q))

/-- Factor bound for the diagonal `Π` coefficient. -/
theorem piHalf_factorBound_pi {𝒯 : RegularityStructure ι} {γ κbar C : ℝ}
    {Dπ : Set ι} {DΓ : Set (ι × ι)} {q : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : Ω → Model 𝒯 parabolicSemigroup} (hH : PiHalfMomentHypsA 𝒯 γ κbar Dπ DΓ q P Z C)
    {k : ι} (hkγ : 𝒯.deg k < γ) {j : ι} (hjk : 𝒯.deg j ≤ 𝒯.deg k) {s : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) (w : ParabolicSpace) :
    PiHalfFactorBoundA P q (fun ω => (Z ω).regPi w (Pi.single j 1) s w)
      (C * s ^ piHalfRandBetaA 𝒯 κbar Dπ j) := by
  classical
  have hord : parabolicSemigroup.order = 4 := rfl
  have hjγ : 𝒯.deg j < γ := lt_of_le_of_lt hjk hkγ
  by_cases hP : j ∈ Dπ
  · have hβ : piHalfRandBetaA 𝒯 κbar Dπ j = 𝒯.deg j / 4 := by simp [piHalfRandBetaA, hP]
    rw [hβ]
    refine Or.inl fun ω => ?_
    rw [Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hH.piDet j hP hjγ ω s hs w
    rwa [hord] at this
  · have hβ : piHalfRandBetaA 𝒯 κbar Dπ j = (𝒯.deg j + κbar) / 4 := by
      simp [piHalfRandBetaA, hP]
    rw [hβ]
    have h := hH.piAnn j hP hjγ s hs w
    rw [hord] at h
    exact Or.inr h
    
/-- Deterministic bound for the difference of the `Γ` coefficients. -/
theorem piHalf_gammaDiff_enorm_le_of_det {𝒯 : RegularityStructure ι}
    {γ κbar θ C ε : ℝ} {Dπ : Set ι} {DΓ : Set (ι × ι)} {q : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup}
    (hD : PiHalfDiffMomentHypsA 𝒯 γ κbar θ Dπ DΓ q P Z₁ Z₂ C ε)
    {k : ι} (hkγ : 𝒯.deg k < γ) {j : ι} (hjk : 𝒯.deg j ≤ 𝒯.deg k) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hG : 𝒯.deg j = 𝒯.deg k ∨ (k, j) ∈ DΓ) (ω : Ω) (x₀ w : ParabolicSpace) :
    ‖(Z₁ ω).gammaMap w x₀ (Pi.single k 1) j - (Z₂ ω).gammaMap w x₀ (Pi.single k 1) j‖ₑ ≤
      ENNReal.ofReal (C * ε ^ θ * parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j)) := by
  have hd : 0 ≤ C * ε ^ θ * parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j) :=
    mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hε _)) (Real.rpow_nonneg (parabolicNorm_nonneg _) _)
  have hU1 := (Z₁ ω).isGradedUnipotent_gammaMap w x₀
  have hU2 := (Z₂ ω).isGradedUnipotent_gammaMap w x₀
  rw [Real.enorm_eq_ofReal_abs]
  refine ENNReal.ofReal_le_ofReal ?_
  have hzero : 𝒯.deg j = 𝒯.deg k →
      (Z₁ ω).gammaMap w x₀ (Pi.single k 1) j - (Z₂ ω).gammaMap w x₀ (Pi.single k 1) j = 0 := by
    intro hdeg
    by_cases hjkeq : j = k
    · subst hjkeq
      rw [hU1.apply_single_self, hU2.apply_single_self, sub_self]
    · rw [hU1.apply_single_of_le hjkeq (le_of_eq hdeg.symm),
        hU2.apply_single_of_le hjkeq (le_of_eq hdeg.symm), sub_self]
  rcases hjk.lt_or_eq with hlt | heq
  · rcases hG with hdeg | hDΓ
    · exact absurd hdeg hlt.ne
    · have := hD.gammaDet k j hDΓ hkγ hlt ω x₀ w
      rwa [piHalf_scaleDist_eq] at this
  · rw [hzero heq, abs_zero]; exact hd

/-- Factor bound for the difference of the `Γ` coefficients. -/
theorem piHalf_factorBound_gammaDiff {𝒯 : RegularityStructure ι} {γ κbar θ C ε : ℝ}
    {Dπ : Set ι} {DΓ : Set (ι × ι)} {q : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup}
    (hD : PiHalfDiffMomentHypsA 𝒯 γ κbar θ Dπ DΓ q P Z₁ Z₂ C ε)
    {k : ι} (hkγ : 𝒯.deg k < γ) {j : ι} (hjk : 𝒯.deg j ≤ 𝒯.deg k) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (x₀ w : ParabolicSpace) :
    PiHalfFactorBoundA P q
      (fun ω => (Z₁ ω).gammaMap w x₀ (Pi.single k 1) j - (Z₂ ω).gammaMap w x₀ (Pi.single k 1) j)
      (C * ε ^ θ * parabolicNorm (x₀ - w) ^ piHalfRandAlphaA 𝒯 κbar DΓ k j) := by
  classical
  by_cases hG : 𝒯.deg j = 𝒯.deg k ∨ (k, j) ∈ DΓ
  · have hα : piHalfRandAlphaA 𝒯 κbar DΓ k j = 𝒯.deg k - 𝒯.deg j := by
      simp [piHalfRandAlphaA, hG]
    rw [hα]
    exact Or.inl fun ω => piHalf_gammaDiff_enorm_le_of_det hD hkγ hjk hC hε hG ω x₀ w
  · have hjlt : 𝒯.deg j < 𝒯.deg k := lt_of_le_of_ne hjk fun h => hG (Or.inl h)
    have hnot : (k, j) ∉ DΓ := fun h => hG (Or.inr h)
    have hα : piHalfRandAlphaA 𝒯 κbar DΓ k j = (𝒯.deg k - 𝒯.deg j) + κbar := by
      simp [piHalfRandAlphaA, hG]
    rw [hα]
    have h := hD.gammaAnn k j hnot hkγ hjlt x₀ w
    rw [piHalf_scaleDist_eq] at h
    exact Or.inr h

/-- Factor bound for the difference of the diagonal `Π` coefficients. -/
theorem piHalf_factorBound_piDiff {𝒯 : RegularityStructure ι} {γ κbar θ C ε : ℝ}
    {Dπ : Set ι} {DΓ : Set (ι × ι)} {q : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup}
    (hD : PiHalfDiffMomentHypsA 𝒯 γ κbar θ Dπ DΓ q P Z₁ Z₂ C ε)
    {k : ι} (hkγ : 𝒯.deg k < γ) {j : ι} (hjk : 𝒯.deg j ≤ 𝒯.deg k) {s : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) (w : ParabolicSpace) :
    PiHalfFactorBoundA P q
      (fun ω => (Z₁ ω).regPi w (Pi.single j 1) s w - (Z₂ ω).regPi w (Pi.single j 1) s w)
      (C * ε ^ θ * s ^ piHalfRandBetaA 𝒯 κbar Dπ j) := by
  classical
  have hord : parabolicSemigroup.order = 4 := rfl
  have hjγ : 𝒯.deg j < γ := lt_of_le_of_lt hjk hkγ
  by_cases hP : j ∈ Dπ
  · have hβ : piHalfRandBetaA 𝒯 κbar Dπ j = 𝒯.deg j / 4 := by simp [piHalfRandBetaA, hP]
    rw [hβ]
    refine Or.inl fun ω => ?_
    rw [Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hD.piDet j hP hjγ ω s hs w
    rwa [hord] at this
  · have hβ : piHalfRandBetaA 𝒯 κbar Dπ j = (𝒯.deg j + κbar) / 4 := by
      simp [piHalfRandBetaA, hP]
    rw [hβ]
    have h := hD.piAnn j hP hjγ s hs w
    rw [hord] at h
    exact Or.inr h

end RegularityStructures

end
