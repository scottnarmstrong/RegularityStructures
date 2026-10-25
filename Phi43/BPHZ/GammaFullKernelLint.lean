/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramMultiSq
public import Phi43.BPHZ.TreeI2Psi2DiagramBounded
import Mathlib.Tactic

/-!
# A single translated kernel of singularity `s⁻ᵃ` against a singular weight

For a measurable kernel `K` supported in `|t| ≤ 1` with `|K| ≤ B s⁻ᵃ`, the double integral
`∬ |K(x - w)| |K(x - w')| s(w' - w)^(-p) dw dw'` is bounded by `C B²` with `C = C(a, p)`
independent of `x` and `K`, whenever `5 < a + p`, `a < 5`, `p < 5` and `2a + p < 10`
(`gammaFull_lintBound_kernel_shift_sq`). `Phi43.BPHZ.KernelSingularWeight` has the case `a = 3`.
With `a = 4` (the spatial gradient of the Hairer kernel) the admissible range is `1 < p < 2`. On the
time slab `|t| ≤ 4` one has `s ≤ 3`, so smaller exponents `p₀ ≤ p` follow
(`gammaFull_lintBound_kernel_shift_sq_of_le`).
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- **Double integral of a single translated kernel of singularity `s⁻ᵃ`.** -/
theorem gammaFull_lintBound_kernel_shift_sq {a p : ℝ} (ha : 0 < a) (ha5 : a < 5) (hp : 0 < p)
    (hp5 : p < 5) (hap : 5 < a + p) (h2a : 2 * a + p < 10) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B → Measurable K →
      (∀ u : SpaceTime, 1 < |u.1| → K u = 0) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u → |K u| ≤ B * torusParabolicSize u ^ (-a)) →
      ∀ x : SpaceTime,
      i2Psi2LintBound (volume.prod volume) (fun q : SpaceTime × SpaceTime =>
        |K (x - q.1)| * |K (x - q.2)| * torusParabolicSize (q.2 - q.1) ^ (-p)) (C * B ^ 2) := by
  obtain ⟨C1, hC1, h1⟩ := i2Psi2LintBound_rpow_mul_rpow_of_gt (a := a) (b := p) ha ha5 hp hp5 hap
  obtain ⟨C2, hC2, h2⟩ := i2Psi2LintBound_slab_rpow (e := 2 * a + p - 5) (by linarith)
    (by linarith)
  refine ⟨C1 * C2, mul_nonneg hC1 hC2, ?_⟩
  intro K B hB hKm hKs hKb x
  have mK : Measurable fun w : SpaceTime => |K (x - w)| :=
    continuous_abs.measurable.comp (hKm.comp (measurable_const.sub measurable_id))
  have hs0 : ∀ u : SpaceTime, 0 ≤ torusParabolicSize u ^ (-p) :=
    fun u => Real.rpow_nonneg (torusParabolicSize_nonneg u) _
  refine i2Psi2LintBound.of_prod_symm
    (G := fun b => |K (x - b)| * (B * C1 * torusParabolicSize (x - b) ^ (5 - a - p))) ?_ ?_ ?_
  · exact ((mK.comp measurable_fst).mul (mK.comp measurable_snd)).mul
      ((Phi43.measurable_torusParabolicSize.comp (measurable_snd.sub measurable_fst)).pow_const _)
  · filter_upwards [ae_torusParabolicSize_sub_pos x] with b hb
    have key := (h1 x b hb).const_mul (c := |K (x - b)| * B)
      (mul_nonneg (abs_nonneg _) hB)
    refine key.mono_ae ?_ (le_of_eq (by ring))
    filter_upwards [ae_torusParabolicSize_sub_pos x] with a' ha'
    have hKa := hKb (x - a') ha'
    calc |K (x - a')| * |K (x - b)| * torusParabolicSize (b - a') ^ (-p)
        ≤ (B * torusParabolicSize (x - a') ^ (-a)) * |K (x - b)| *
            torusParabolicSize (b - a') ^ (-p) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKa (abs_nonneg _)) (hs0 _)
      _ = _ := by ring
  · have key := (h2 x.1 x (by simp)).const_mul (c := B * C1 * B)
      (mul_nonneg (mul_nonneg hB hC1) hB)
    refine key.mono_ae ?_ (le_of_eq (by ring))
    filter_upwards [ae_torusParabolicSize_sub_pos x] with b hb
    have hsn : 0 ≤ torusParabolicSize (x - b) ^ (-(2 * a + p - 5)) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    by_cases hb1 : |(x - b).1| ≤ 1
    · have hsl : i2Psi2Slab x.1 b = 1 := by
        refine i2Psi2Slab_of_le ?_
        rw [Prod.fst_sub] at hb1
        rw [abs_sub_comm]
        linarith
      have hKb' := hKb (x - b) hb
      have hexp : torusParabolicSize (x - b) ^ (-a) *
          torusParabolicSize (x - b) ^ (5 - a - p) = torusParabolicSize (x - b) ^
            (-(2 * a + p - 5)) := by
        rw [← Real.rpow_add hb]
        congr 1
        ring
      have hnn : 0 ≤ B * C1 * torusParabolicSize (x - b) ^ (5 - a - p) :=
        mul_nonneg (mul_nonneg hB hC1) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      calc |K (x - b)| * (B * C1 * torusParabolicSize (x - b) ^ (5 - a - p))
          ≤ (B * torusParabolicSize (x - b) ^ (-a)) *
              (B * C1 * torusParabolicSize (x - b) ^ (5 - a - p)) :=
            mul_le_mul_of_nonneg_right hKb' hnn
        _ = B * C1 * B * (i2Psi2Slab x.1 b * torusParabolicSize (x - b) ^
              (-(2 * a + p - 5))) := by
            rw [hsl, one_mul, ← hexp]
            ring
    · have h0 : K (x - b) = 0 := hKs _ (lt_of_not_ge hb1)
      rw [h0, abs_zero, zero_mul]
      exact mul_nonneg (mul_nonneg (mul_nonneg hB hC1) hB)
        (mul_nonneg (i2Psi2Slab_nonneg _ _) hsn)

/-- **The same with a smaller exponent `p₀ ≤ p`** (the pairs lie in a time slab of width `4`,
where `s ≤ 3`). -/
theorem gammaFull_lintBound_kernel_shift_sq_of_le {a p p₀ : ℝ} (ha : 0 < a) (ha5 : a < 5)
    (hp5 : p < 5) (hap : 5 < a + p) (h2a : 2 * a + p < 10) (hp₀ : 0 < p₀) (hpp : p₀ ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B → Measurable K →
      (∀ u : SpaceTime, 1 < |u.1| → K u = 0) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u → |K u| ≤ B * torusParabolicSize u ^ (-a)) →
      ∀ x : SpaceTime,
      i2Psi2LintBound (volume.prod volume) (fun q : SpaceTime × SpaceTime =>
        |K (x - q.1)| * |K (x - q.2)| * torusParabolicSize (q.2 - q.1) ^ (-p₀)) (C * B ^ 2) := by
  obtain ⟨C0, hC0, h⟩ := gammaFull_lintBound_kernel_shift_sq ha ha5 (by linarith) hp5 hap h2a
  have h3 : (0 : ℝ) ≤ 3 ^ (p - p₀) := Real.rpow_nonneg (by norm_num) _
  refine ⟨3 ^ (p - p₀) * C0, mul_nonneg h3 hC0, ?_⟩
  intro K B hB hKm hKs hKb x
  have key := (h hB hKm hKs hKb x).const_mul (c := 3 ^ (p - p₀)) h3
  refine key.mono (fun q => ?_) (le_of_eq (by ring))
  have hs0 : 0 ≤ torusParabolicSize (q.2 - q.1) ^ (-p) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  by_cases hz : K (x - q.1) = 0 ∨ K (x - q.2) = 0
  · rcases hz with hz | hz <;> simp [hz]
  · push Not at hz
    have h1 : |(x - q.1).1| ≤ 1 := by
      by_contra hc
      exact hz.1 (hKs _ (lt_of_not_ge hc))
    have h2 : |(x - q.2).1| ≤ 1 := by
      by_contra hc
      exact hz.2 (hKs _ (lt_of_not_ge hc))
    have hd : |(q.2 - q.1).1| ≤ 4 := by
      have : (q.2 - q.1).1 = (x - q.1).1 - (x - q.2).1 := by
        simp only [Prod.fst_sub]; ring
      rw [this]
      calc |(x - q.1).1 - (x - q.2).1| ≤ |(x - q.1).1| + |(x - q.2).1| := abs_sub _ _
        _ ≤ 4 := by linarith
    have hs3 := torusParabolicSize_le_three_of_abs_le hd
    rcases (torusParabolicSize_nonneg (q.2 - q.1)).eq_or_lt with h0 | h0
    · have e1 : (0 : ℝ) ^ (-p₀) = 0 := Real.zero_rpow (by linarith)
      have e2 : (0 : ℝ) ^ (-p) = 0 := Real.zero_rpow (by linarith)
      rw [← h0, e1, e2]
      simp
    · have hsplit : torusParabolicSize (q.2 - q.1) ^ (-p₀) =
          torusParabolicSize (q.2 - q.1) ^ (-p) *
            torusParabolicSize (q.2 - q.1) ^ (p - p₀) := by
        rw [← Real.rpow_add h0]
        congr 1
        ring
      have hle : torusParabolicSize (q.2 - q.1) ^ (p - p₀) ≤ 3 ^ (p - p₀) :=
        Real.rpow_le_rpow h0.le hs3 (by linarith)
      rw [hsplit]
      have hk : 0 ≤ |K (x - q.1)| * |K (x - q.2)| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
      calc |K (x - q.1)| * |K (x - q.2)| * (torusParabolicSize (q.2 - q.1) ^ (-p) *
            torusParabolicSize (q.2 - q.1) ^ (p - p₀))
          ≤ |K (x - q.1)| * |K (x - q.2)| * (torusParabolicSize (q.2 - q.1) ^ (-p) *
            3 ^ (p - p₀)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hs0) hk
        _ = _ := by ring

end RegularityStructures

end
