/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.WhiteNoise

/-!
# Almost-sure linearity of a white-noise family

The finite-dimensional Gaussian clause forces the evaluations of an arbitrary white-noise family to
be linear almost surely.  This is the algebraic bridge used by a Fourier-series modification.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace RegularityStructures.Phi43

theorem whiteNoise_add_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    {h g : SpaceTime → ℝ} (hh : MemLp h 2 (volume : Measure SpaceTime))
    (hg : MemLp g 2 (volume : Measure SpaceTime)) :
    (fun w => W (h + g) w) =ᵐ[P] fun w => W h w + W g w := by
  let f : Fin 3 → SpaceTime → ℝ :=
    fun i => if i = 0 then h + g else if i = 1 then h else g
  let a : Fin 3 → ℝ := fun i => if i = 0 then 1 else -1
  have hf : ∀ i, MemLp (f i) 2 (volume : Measure SpaceTime) := by
    intro i
    fin_cases i <;> simp [f, hh, hg, hh.add hg]
  have hhh : Integrable (fun z : SpaceTime => h z * h z) := hh.integrable_mul hh
  have hhg : Integrable (fun z : SpaceTime => h z * g z) := hh.integrable_mul hg
  have hgh : Integrable (fun z : SpaceTime => g z * h z) := hg.integrable_mul hh
  have hgg : Integrable (fun z : SpaceTime => g z * g z) := hg.integrable_mul hg
  have hpp : Integrable (fun z : SpaceTime => (h + g) z * (h + g) z) :=
    (hh.add hg).integrable_mul (hh.add hg)
  have hpg : Integrable (fun z : SpaceTime => (h + g) z * g z) :=
    (hh.add hg).integrable_mul hg
  have hph : Integrable (fun z : SpaceTime => (h + g) z * h z) :=
    (hh.add hg).integrable_mul hh
  have hpp_eq :
      (∫ z, (h + g) z * (h + g) z) =
        (∫ z, h z * h z) + (∫ z, h z * g z) +
          ((∫ z, g z * h z) + (∫ z, g z * g z)) := by
    calc
      (∫ z, (h + g) z * (h + g) z) =
          ∫ z, (h z * h z + h z * g z) + (g z * h z + g z * g z) := by
            congr 1
            funext z
            simp only [Pi.add_apply]
            ring
      _ = (∫ z, (h z * h z + h z * g z)) +
          (∫ z, (g z * h z + g z * g z)) := by
            apply integral_add
            · exact hhh.add hhg
            · exact hgh.add hgg
      _ = (∫ z, h z * h z) + (∫ z, h z * g z) +
          ((∫ z, g z * h z) + (∫ z, g z * g z)) := by
            rw [integral_add hhh hhg, integral_add hgh hgg]
  have hpg_eq :
      (∫ z, (h + g) z * g z) = (∫ z, h z * g z) + (∫ z, g z * g z) := by
    calc
      (∫ z, (h + g) z * g z) = ∫ z, h z * g z + g z * g z := by
        congr 1
        funext z
        simp only [Pi.add_apply]
        ring
      _ = (∫ z, h z * g z) + ∫ z, g z * g z :=
        integral_add hhg hgg
  have hph_eq :
      (∫ z, (h + g) z * h z) = (∫ z, h z * h z) + (∫ z, g z * h z) := by
    calc
      (∫ z, (h + g) z * h z) = ∫ z, h z * h z + g z * h z := by
        congr 1
        funext z
        simp only [Pi.add_apply]
        ring
      _ = (∫ z, h z * h z) + ∫ z, g z * h z :=
        integral_add hhh hgh
  have hgp_eq :
      (∫ z, g z * (h + g) z) = (∫ z, g z * h z) + (∫ z, g z * g z) := by
    calc
      (∫ z, g z * (h + g) z) = ∫ z, g z * h z + g z * g z := by
        congr 1
        funext z
        simp only [Pi.add_apply]
        ring
      _ = (∫ z, g z * h z) + ∫ z, g z * g z :=
        integral_add hgh hgg
  have hghp_eq :
      (∫ z, h z * (h + g) z) = (∫ z, h z * h z) + (∫ z, h z * g z) := by
    calc
      (∫ z, h z * (h + g) z) = ∫ z, h z * h z + h z * g z := by
        congr 1
        funext z
        simp only [Pi.add_apply]
        ring
      _ = (∫ z, h z * h z) + ∫ z, h z * g z :=
        integral_add hhh hhg
  have hcent := hW.2 3 f hf
  have hpp_eq' :
      (∫ z, (h z + g z) * (h z + g z)) =
        (∫ z, h z * h z) + (∫ z, h z * g z) +
          ((∫ z, g z * h z) + (∫ z, g z * g z)) := by
    simpa only [Pi.add_apply] using hpp_eq
  have hpg_eq' :
      (∫ z, (h z + g z) * g z) = (∫ z, h z * g z) + (∫ z, g z * g z) := by
    simpa only [Pi.add_apply] using hpg_eq
  have hph_eq' :
      (∫ z, (h z + g z) * h z) = (∫ z, h z * h z) + (∫ z, g z * h z) := by
    simpa only [Pi.add_apply] using hph_eq
  have hgp_eq' :
      (∫ z, g z * (h z + g z)) = (∫ z, g z * h z) + (∫ z, g z * g z) := by
    simpa only [Pi.add_apply] using hgp_eq
  have hghp_eq' :
      (∫ z, h z * (h z + g z)) = (∫ z, h z * h z) + (∫ z, h z * g z) := by
    simpa only [Pi.add_apply] using hghp_eq
  have hzero : ∫ ω, (∑ m, a m * W (f m) ω) ^ (2 : ℕ) ∂P = 0 := by
    calc
      ∫ ω, (∑ m, a m * W (f m) ω) ^ (2 : ℕ) ∂P =
          ∑ m, ∑ m', a m * a m' * ∫ z, f m z * f m' z := by
            convert hcent.integral_linear_sq (σ := id) a using 1 <;> simp
      _ = 0 := by
        simp [f, a, Fin.sum_univ_succ]
        linarith [hpp_eq', hpg_eq', hph_eq', hgp_eq', hghp_eq']
  have hint : Integrable (fun w => (∑ m, a m * W (f m) w) ^ (2 : ℕ)) P :=
    hcent.integrable_linear_pow (σ := id) a 2
  have hnonneg : 0 ≤ᵐ[P] (fun w => (∑ m, a m * W (f m) w) ^ (2 : ℕ)) :=
    ae_of_all _ fun w => sq_nonneg _
  have hsumzero : (fun w => ∑ m, a m * W (f m) w) =ᵐ[P] 0 := by
    have hpow := (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hzero
    filter_upwards [hpow] with w hw
    exact sq_eq_zero_iff.mp hw
  filter_upwards [hsumzero] with w hw
  have hw' : W (h + g) w + (-W g w + -W h w) = 0 := by
    simpa [f, a, Fin.sum_univ_succ, add_sub, sub_eq_add_neg] using hw
  linarith

end RegularityStructures.Phi43

end
