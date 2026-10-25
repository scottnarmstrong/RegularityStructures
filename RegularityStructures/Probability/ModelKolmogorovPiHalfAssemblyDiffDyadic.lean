/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyDyadic
public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyMoments

/-!
# Dyadic blocks for the `Π` difference norm, and moment helpers

`piDiffNormOn_le_of_dyadic_blocks` is the difference analogue of `piNormOn_le_of_dyadic_blocks`.
The remaining lemmas are small `ℝ≥0∞` moment helpers shared by the skeletons.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

theorem piDiffNormOn_le_of_dyadic_blocks (M M₂ : Model 𝒯 parabolicSemigroup) (γ : ℝ)
    (S : Set ParabolicSpace) (Dπ : Set ι) (C : ℝ) (B : ℝ≥0∞)
    (hdet : ∀ i ∈ Dπ, 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x ∈ S,
      |M.regPi x (Pi.single i 1) t x - M₂.regPi x (Pi.single i 1) t x| ≤
        C * t ^ (𝒯.deg i / parabolicSemigroup.order))
    (hdy : ∀ i, i ∉ Dπ → 𝒯.deg i < γ → ∀ j : ℕ,
      ∀ u ∈ Icc ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j), ∀ x ∈ S,
        ‖M.regPi x (Pi.single i 1) u x - M₂.regPi x (Pi.single i 1) u x‖ₑ ≤
          B * ENNReal.ofReal (piHalfScale j ^ (𝒯.deg i / parabolicSemigroup.order))) :
    M.piDiffNormOn M₂ γ S ≤ ENNReal.ofReal C + ENNReal.ofReal (piHalfBlockConst 𝒯) * B := by
  set c : ℝ≥0∞ := ENNReal.ofReal C + ENNReal.ofReal (piHalfBlockConst 𝒯) * B with hc
  by_cases htop : c = ⊤
  · rw [htop]; exact le_top
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ≥0, (c' : ℝ≥0∞) = c := ⟨_, ENNReal.coe_toNNReal htop⟩
  rw [← hc', Model.piDiffNormOn_le_iff]
  intro i hi t ht x hx
  have hcC : C ≤ c' := by
    have : ENNReal.ofReal C ≤ c' := hc' ▸ le_self_add
    exact (ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top).1 this |>.trans (by simp)
  by_cases hD : i ∈ Dπ
  · exact (hdet i hD hi t ht x hx).trans
      (mul_le_mul_of_nonneg_right hcC (Real.rpow_nonneg ht.1.le _))
  · obtain ⟨j, hj⟩ := exists_dyadic_block ht
    have hblock : t ∈ Icc (2 * piHalfScale j) (4 * piHalfScale j) := by
      rw [two_mul_piHalfScale, four_mul_piHalfScale]; exact hj
    have h1 := hdy i hD hi j t hj x hx
    have h2 : ENNReal.ofReal (piHalfScale j ^ (𝒯.deg i / parabolicSemigroup.order)) ≤
        ENNReal.ofReal (piHalfBlockConst 𝒯) *
          ENNReal.ofReal (t ^ (𝒯.deg i / parabolicSemigroup.order)) := by
      rw [← ENNReal.ofReal_mul (piHalfBlockConst_nonneg 𝒯)]
      exact ENNReal.ofReal_le_ofReal (rpow_piHalfScale_le i hblock)
    have h3 : ‖M.regPi x (Pi.single i 1) t x - M₂.regPi x (Pi.single i 1) t x‖ₑ ≤
        (c' : ℝ≥0∞) * ENNReal.ofReal (t ^ (𝒯.deg i / parabolicSemigroup.order)) := by
      calc _ ≤ B * ENNReal.ofReal (piHalfScale j ^ (𝒯.deg i / parabolicSemigroup.order)) := h1
        _ ≤ B * (ENNReal.ofReal (piHalfBlockConst 𝒯) *
            ENNReal.ofReal (t ^ (𝒯.deg i / parabolicSemigroup.order))) := by gcongr
        _ = (ENNReal.ofReal (piHalfBlockConst 𝒯) * B) *
            ENNReal.ofReal (t ^ (𝒯.deg i / parabolicSemigroup.order)) := by ring
        _ ≤ (c' : ℝ≥0∞) * ENNReal.ofReal (t ^ (𝒯.deg i / parabolicSemigroup.order)) := by
            gcongr
            rw [hc']; exact le_add_self
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul c'.coe_nonneg,
      ENNReal.ofReal_le_ofReal_iff (mul_nonneg c'.coe_nonneg (Real.rpow_nonneg ht.1.le _))] at h3
    exact h3

/-- `E (ofReal a + Y)^m ≤ 2^m (a^m + b^m)` if `E Y^m ≤ b^m`. -/
theorem lintegral_ofReal_add_pow_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ≥0∞} (m : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∫⁻ ω, Y ω ^ m ∂P ≤ ENNReal.ofReal b ^ m) :
    ∫⁻ ω, (ENNReal.ofReal a + Y ω) ^ m ∂P ≤ ENNReal.ofReal (2 ^ m * (a ^ m + b ^ m)) := by
  calc ∫⁻ ω, (ENNReal.ofReal a + Y ω) ^ m ∂P
      ≤ ∫⁻ ω, 2 ^ m * (ENNReal.ofReal a ^ m + Y ω ^ m) ∂P :=
        lintegral_mono fun ω => ennreal_add_pow_le _ _ _
    _ = 2 ^ m * (ENNReal.ofReal a ^ m + ∫⁻ ω, Y ω ^ m ∂P) := by
        rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
          lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ 2 ^ m * (ENNReal.ofReal a ^ m + ENNReal.ofReal b ^ m) := by gcongr
    _ = ENNReal.ofReal (2 ^ m * (a ^ m + b ^ m)) := by
        have h2 : (2 : ℝ≥0∞) ^ m = ENNReal.ofReal ((2 : ℝ) ^ m) := by
          rw [ENNReal.ofReal_pow (by norm_num)]; simp
        rw [h2, ← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_pow hb,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]

/-- `E (G V)^p ≤ √a √b` from `E G^{2p} ≤ a`, `E V^{2p} ≤ b`. -/
theorem lintegral_mul_pow_le_sqrt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {G V : Ω → ℝ≥0∞} (hG : AEMeasurable G P) (hV : AEMeasurable V P) (p : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hGa : ∫⁻ ω, G ω ^ (2 * p) ∂P ≤ ENNReal.ofReal a)
    (hVb : ∫⁻ ω, V ω ^ (2 * p) ∂P ≤ ENNReal.ofReal b) :
    ∫⁻ ω, (G ω * V ω) ^ p ∂P ≤ ENNReal.ofReal (Real.sqrt a * Real.sqrt b) := by
  have := lintegral_mul_le_sqrt_mul_sqrt (P := P) (f := fun ω => G ω ^ p)
    (g := fun ω => V ω ^ p) (hG.pow_const p) (hV.pow_const p) ha hb
    (by simpa only [← pow_mul, mul_comm p 2] using hGa)
    (by simpa only [← pow_mul, mul_comm p 2] using hVb)
  simpa only [mul_pow] using this

end RegularityStructures

end
