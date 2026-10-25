/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.Linearity

/-!
# Finite linear combinations of white-noise evaluations

The finite-dimensional covariance clause forces a white-noise family to respect scalar
multiplication almost surely.  Together with `whiteNoise_add_ae`, this gives the finite-sum
identity used by Fourier partial sums.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace RegularityStructures.Phi43

theorem whiteNoise_smul_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {h : SpaceTime → ℝ} (hh : MemLp h 2 (volume : Measure SpaceTime)) (a : ℝ) :
    (fun w => W (a • h) w) =ᵐ[P] fun w => a * W h w := by
  let f : Fin 2 → SpaceTime → ℝ := fun i => if i = 0 then a • h else h
  let b : Fin 2 → ℝ := fun i => if i = 0 then 1 else -a
  have hf : ∀ i, MemLp (f i) 2 (volume : Measure SpaceTime) := by
    intro i
    fin_cases i <;> simp [f, hh, hh.const_smul]
  have hcent := hW.2 2 f hf
  have hzero : ∫ w, (∑ i, b i * W (f i) w) ^ (2 : ℕ) ∂P = 0 := by
    calc
      ∫ w, (∑ i, b i * W (f i) w) ^ (2 : ℕ) ∂P =
          ∑ i, ∑ j, b i * b j * ∫ z, f i z * f j z :=
        hcent.integral_linear_sq (σ := id) b
      _ = 0 := by
        have hsq : Integrable (fun z : SpaceTime => h z * h z) :=
          hh.integrable_mul hh
        have h00 : (∫ z, (a • h) z * (a • h) z) =
            a ^ 2 * ∫ z, h z * h z := by
          calc
            (∫ z, (a • h) z * (a • h) z) =
                ∫ z, a ^ 2 * (h z * h z) := by
                  apply integral_congr_ae
                  filter_upwards [] with z
                  simp only [Pi.smul_apply]
                  ring
            _ = a ^ 2 * ∫ z, h z * h z := integral_const_mul _ _
        have h01 : (∫ z, (a • h) z * h z) = a * ∫ z, h z * h z := by
          calc
            (∫ z, (a • h) z * h z) = ∫ z, a * (h z * h z) := by
              apply integral_congr_ae
              filter_upwards [] with z
              simp only [Pi.smul_apply]
              ring
            _ = a * ∫ z, h z * h z := integral_const_mul _ _
        have h10 : (∫ z, h z * (a • h) z) = a * ∫ z, h z * h z := by
          calc
            (∫ z, h z * (a • h) z) = ∫ z, a * (h z * h z) := by
              apply integral_congr_ae
              filter_upwards [] with z
              simp only [Pi.smul_apply]
              ring
            _ = a * ∫ z, h z * h z := integral_const_mul _ _
        have h00' : (∫ z, a * h z * (a * h z)) =
            a ^ 2 * ∫ z, h z * h z := by
          simpa [Pi.smul_apply] using h00
        have h01' : (∫ z, a * h z * h z) =
            a * ∫ z, h z * h z := by
          simpa [Pi.smul_apply] using h01
        have h10' : (∫ z, h z * (a * h z)) =
            a * ∫ z, h z * h z := by
          simpa [Pi.smul_apply] using h10
        simp [f, b, Fin.sum_univ_two]
        rw [h00', h01', h10']
        ring
  have hint : Integrable (fun w => (∑ i, b i * W (f i) w) ^ (2 : ℕ)) P :=
    hcent.integrable_linear_pow (σ := id) b 2
  have hnonneg : 0 ≤ᵐ[P] (fun w => (∑ i, b i * W (f i) w) ^ (2 : ℕ)) :=
    ae_of_all _ fun w => sq_nonneg _
  have hsumzero : (fun w => ∑ i, b i * W (f i) w) =ᵐ[P] 0 := by
    have hpow := (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hzero
    filter_upwards [hpow] with w hw
    exact sq_eq_zero_iff.mp hw
  filter_upwards [hsumzero] with w hw
  have hw' : W (a • h) w - a * W h w = 0 := by
    simpa [f, b, Fin.sum_univ_two, sub_eq_add_neg] using hw
  exact sub_eq_zero.mp hw'

theorem whiteNoise_finset_sum_ae {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (s : Finset ι) (a : ι → ℝ) (h : ι → SpaceTime → ℝ)
    (hh : ∀ i ∈ s, MemLp (h i) 2 (volume : Measure SpaceTime)) :
    (fun w => W (∑ i ∈ s, a i • h i) w) =ᵐ[P]
      fun w => ∑ i ∈ s, a i * W (h i) w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hzero := whiteNoise_smul_ae hW (MemLp.zero : MemLp (0 : SpaceTime → ℝ) 2 volume) 0
      simpa using hzero
  | @insert i s hi ih =>
      have hsum : MemLp (∑ j ∈ s, a j • h j) 2 (volume : Measure SpaceTime) := by
        convert memLp_finsetSum s (fun j hj =>
          (hh j (Finset.mem_insert_of_mem hj)).const_smul (a j)) using 1
        ext z
        simp [Pi.smul_apply]
      have hadd := whiteNoise_add_ae hW
        ((hh i (Finset.mem_insert_self i s)).const_smul (a i)) hsum
      have hsmul := whiteNoise_smul_ae hW (hh i (Finset.mem_insert_self i s)) (a i)
      have htail := ih (fun j hj => hh j (Finset.mem_insert_of_mem hj))
      filter_upwards [hadd, hsmul, htail] with w hwadd hwsmul hwtail
      calc
        W (∑ j ∈ insert i s, a j • h j) w =
            W (a i • h i) w + W (∑ j ∈ s, a j • h j) w := by
              simpa [Finset.sum_insert, hi] using hwadd
        _ = a i * W (h i) w + W (∑ j ∈ s, a j • h j) w := by rw [hwsmul]
        _ = a i * W (h i) w + ∑ j ∈ s, a j * W (h j) w := by rw [hwtail]
        _ = ∑ j ∈ insert i s, a j * W (h j) w := by simp [Finset.sum_insert, hi]

end RegularityStructures.Phi43

end
