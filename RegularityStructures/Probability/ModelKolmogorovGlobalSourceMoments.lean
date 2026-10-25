/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Model
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Global source moments with deterministic exemptions

Ingredients of the Kolmogorov criterion for models [Hai14, Theorem 10.7]. A single sufficiently high
source moment controls the lower moment orders used in chaining. Deterministic components receive no
reserve gain; non-exempt components receive exactly the source's kappa reserve. These are coordinate
bounds, not assumptions on or conclusions about an unknown pathwise model norm.

Sources: [Hai14, Theorem 10.7]; [HS23, Theorem B.1 and Proposition B.3].
-/

public section

open MeasureTheory Set Classical
open scoped ENNReal NNReal

namespace RegularityStructures

/-- A normalised higher moment bound implies the same bound at every smaller positive
natural moment order on a probability space. -/
theorem probability_natMoment_le_of_higher
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf : AEMeasurable f P)
    {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) (B : ℝ≥0∞)
    (hq : (∫⁻ ω, ‖f ω‖ₑ ^ q ∂P) ≤ B ^ q) :
    (∫⁻ ω, ‖f ω‖ₑ ^ p ∂P) ≤ B ^ p := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hp
  have hqR : 0 < (q : ℝ) := hpR.trans_le (by exact_mod_cast hpq)
  have hqroot : eLpNorm' f (q : ℝ) P ≤ B := by
    rw [eLpNorm'_eq_lintegral_enorm]
    simp_rw [ENNReal.rpow_natCast]
    have h := ENNReal.rpow_le_rpow hq (one_div_nonneg.mpr hqR.le)
    have he : (B ^ q) ^ (1 / (q : ℝ)) = B := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, one_div,
        mul_inv_cancel₀ hqR.ne', ENNReal.rpow_one]
    exact h.trans_eq he
  have hroot : eLpNorm' f (p : ℝ) P ≤ B :=
    (eLpNorm'_le_eLpNorm'_of_exponent_le hpR (by exact_mod_cast hpq) P
      hf.aestronglyMeasurable).trans hqroot
  calc
    _ = eLpNorm' f (p : ℝ) P ^ p := by
      simpa only [ENNReal.rpow_natCast] using
        (lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := f) (μ := P) hpR)
    _ ≤ _ := ENNReal.pow_le_pow_left hroot

private theorem global_source_deterministic_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℝ} {B : ℝ} (h : ∀ ω, |f ω| ≤ B) (p : ℕ) :
    (∫⁻ ω, ‖f ω‖ₑ ^ p ∂P) ≤ ENNReal.ofReal B ^ p := by
  have he (ω : Ω) : ‖f ω‖ₑ ≤ ENNReal.ofReal B := by
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (h ω)
  simpa only [lintegral_const, measure_univ, mul_one] using
    lintegral_mono (μ := P) (fun ω => ENNReal.pow_le_pow_left (he ω) (n := p))

variable {ι E Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace E] [MeasurableSpace Ω] {μ : Measure E} {P : Measure Ω}
  [IsProbabilityMeasure P] {𝒯 : RegularityStructure ι} {Q : RegularisingSemigroup E μ}

/-- The global Gamma source hypotheses give every lower moment order, with the correct
zero reserve on deterministic pairs. -/
theorem randomModel_gamma_coordinate_moment_le_global_source
    (Z : Ω → Model 𝒯 Q) (D : Set (ι × ι)) (γ κ C : ℝ)
    {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hm : ∀ x y i j, AEMeasurable (fun ω => (Z ω).gammaMap y x (Pi.single i 1) j) P)
    (hdet : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
      ∀ ω x y, |(Z ω).gammaMap y x (Pi.single i 1) j| ≤
        C * Q.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j))
    (hann : ∀ i j, (i, j) ∉ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
      ∀ x y, (∫⁻ ω, ‖(Z ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P) ≤
        ENNReal.ofReal (C * Q.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j + κ)) ^ q)
    (x y : E) {i j : ι} (hi : 𝒯.deg i < γ) (hj : 𝒯.deg j < 𝒯.deg i) :
    (∫⁻ ω, ‖(Z ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ p ∂P) ≤
      ENNReal.ofReal (C * Q.scaleDist y x ^
        (𝒯.deg i - 𝒯.deg j + (if (i, j) ∈ D then 0 else κ))) ^ p := by
  classical
  by_cases hd : (i, j) ∈ D
  · simp only [hd, ite_true, add_zero]
    exact global_source_deterministic_moment (fun ω => hdet i j hd hi hj ω x y) p
  · simp only [hd, ite_false]
    exact probability_natMoment_le_of_higher (hm x y i j) hp hpq _
      (hann i j hd hi hj x y)

/-- Global difference Gamma moments retain the exact C*eps^theta prefactor and assign
no reserve to deterministic pairs. -/
theorem randomModel_gamma_diff_coordinate_moment_le_global_source
    (Z Zbar : Ω → Model 𝒯 Q) (D : Set (ι × ι)) (γ κ C ε θ : ℝ)
    {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hm : ∀ x y i j, AEMeasurable (fun ω =>
      (Z ω).gammaMap y x (Pi.single i 1) j -
        (Zbar ω).gammaMap y x (Pi.single i 1) j) P)
    (hdet : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
      ∀ ω x y, |(Z ω).gammaMap y x (Pi.single i 1) j -
        (Zbar ω).gammaMap y x (Pi.single i 1) j| ≤
          C * ε ^ θ * Q.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j))
    (hann : ∀ i j, (i, j) ∉ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
      ∀ x y, (∫⁻ ω, ‖(Z ω).gammaMap y x (Pi.single i 1) j -
        (Zbar ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P) ≤
          ENNReal.ofReal (C * ε ^ θ * Q.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j + κ)) ^ q)
    (x y : E) {i j : ι} (hi : 𝒯.deg i < γ) (hj : 𝒯.deg j < 𝒯.deg i) :
    (∫⁻ ω, ‖(Z ω).gammaMap y x (Pi.single i 1) j -
      (Zbar ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ p ∂P) ≤
      ENNReal.ofReal (C * ε ^ θ * Q.scaleDist y x ^
        (𝒯.deg i - 𝒯.deg j + (if (i, j) ∈ D then 0 else κ))) ^ p := by
  classical
  by_cases hd : (i, j) ∈ D
  · simp only [hd, ite_true, add_zero]
    exact global_source_deterministic_moment (fun ω => hdet i j hd hi hj ω x y) p
  · simp only [hd, ite_false]
    exact probability_natMoment_le_of_higher (hm x y i j) hp hpq _
      (hann i j hd hi hj x y)

end RegularityStructures

end

