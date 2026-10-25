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
# A single translated kernel against a singular weight

For a kernel `K` with `i2Psi2KernelHyp K B` (support in `|t| ≤ 1`, `|K| ≤ B s⁻³`), the double
integral
`∬ |K(x - w)| |K(x - w')| s(w' - w)^(-p) dw dw'`
is bounded by `C B²` for `2 < p < 4`, with `C = C(p)` independent of `x` and `K`
(`i2Psi2LintBound_kernel_shift_sq`).  This is the diagonal term of the second moment of a kernel
test `∫ K(x - w) Y(w) dw` of a field with covariance `≲ s⁻ᵖ`; it is used for the uniform bound
of the structure-group entries `v₂`, `v₃` at large distances.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- **Double integral of a single translated kernel**, `2 < p < 4`. -/
theorem i2Psi2LintBound_kernel_shift_sq {p : ℝ} (hp2 : 2 < p) (hp4 : p < 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B → ∀ x : SpaceTime,
      i2Psi2LintBound (volume.prod volume) (fun q : SpaceTime × SpaceTime =>
        |K (x - q.1)| * |K (x - q.2)| * torusParabolicSize (q.2 - q.1) ^ (-p)) (C * B ^ 2) := by
  obtain ⟨C1, hC1, h1⟩ := i2Psi2LintBound_rpow_mul_rpow_of_gt (a := 3) (b := p)
    (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith)
  obtain ⟨C2, hC2, h2⟩ := i2Psi2LintBound_slab_rpow (e := 1 + p) (by linarith) (by linarith)
  refine ⟨C1 * C2, mul_nonneg hC1 hC2, ?_⟩
  intro K B hK x
  obtain ⟨hB, hKm, hKs, hKb, -⟩ := hK
  have mK : Measurable fun w : SpaceTime => |K (x - w)| :=
    continuous_abs.measurable.comp (hKm.comp (measurable_const.sub measurable_id))
  have hs0 : ∀ u : SpaceTime, 0 ≤ torusParabolicSize u ^ (-p) :=
    fun u => Real.rpow_nonneg (torusParabolicSize_nonneg u) _
  refine i2Psi2LintBound.of_prod_symm
    (G := fun b => |K (x - b)| * (B * C1 * torusParabolicSize (x - b) ^ (5 - 3 - p))) ?_ ?_ ?_
  · exact ((mK.comp measurable_fst).mul (mK.comp measurable_snd)).mul
      ((Phi43.measurable_torusParabolicSize.comp (measurable_snd.sub measurable_fst)).pow_const _)
  · filter_upwards [ae_torusParabolicSize_sub_pos x] with b hb
    have key := (h1 x b hb).const_mul (c := |K (x - b)| * B)
      (mul_nonneg (abs_nonneg _) hB)
    refine key.mono_ae ?_ (le_of_eq (by ring))
    filter_upwards [ae_torusParabolicSize_sub_pos x] with a ha
    have hKa := hKb (x - a) ha
    calc |K (x - a)| * |K (x - b)| * torusParabolicSize (b - a) ^ (-p)
        ≤ (B * torusParabolicSize (x - a) ^ (-(3 : ℝ))) * |K (x - b)| *
            torusParabolicSize (b - a) ^ (-p) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKa (abs_nonneg _)) (hs0 _)
      _ = _ := by ring
  · have key := (h2 x.1 x (by simp)).const_mul (c := B * C1 * B)
      (mul_nonneg (mul_nonneg hB hC1) hB)
    refine key.mono_ae ?_ (le_of_eq (by ring))
    filter_upwards [ae_torusParabolicSize_sub_pos x] with b hb
    have hsn : 0 ≤ torusParabolicSize (x - b) ^ (-(1 + p)) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    by_cases hb1 : |(x - b).1| ≤ 1
    · have hsl : i2Psi2Slab x.1 b = 1 := by
        refine i2Psi2Slab_of_le ?_
        rw [Prod.fst_sub] at hb1
        rw [abs_sub_comm]
        linarith
      have hKb' := hKb (x - b) hb
      have hexp : torusParabolicSize (x - b) ^ (-(3 : ℝ)) *
          torusParabolicSize (x - b) ^ (5 - 3 - p) = torusParabolicSize (x - b) ^ (-(1 + p)) := by
        rw [← Real.rpow_add hb]
        congr 1
        ring
      have hnn : 0 ≤ B * C1 * torusParabolicSize (x - b) ^ (5 - 3 - p) :=
        mul_nonneg (mul_nonneg hB hC1) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      calc |K (x - b)| * (B * C1 * torusParabolicSize (x - b) ^ (5 - 3 - p))
          ≤ (B * torusParabolicSize (x - b) ^ (-(3 : ℝ))) *
              (B * C1 * torusParabolicSize (x - b) ^ (5 - 3 - p)) :=
            mul_le_mul_of_nonneg_right hKb' hnn
        _ = B * C1 * B * (i2Psi2Slab x.1 b * torusParabolicSize (x - b) ^ (-(1 + p))) := by
            rw [hsl, one_mul, ← hexp]
            ring
    · have h0 : K (x - b) = 0 := hKs _ (lt_of_not_ge hb1)
      rw [h0, abs_zero, zero_mul]
      exact mul_nonneg (mul_nonneg (mul_nonneg hB hC1) hB)
        (mul_nonneg (i2Psi2Slab_nonneg _ _) hsn)

/-- **Double integral of a single translated kernel**, `2 ≤ p ≤ 7/2` (the borderline `p = 2` is
reached by the bounded time slab, on which `s ≤ 3`). -/
theorem i2Psi2LintBound_kernel_shift_sq_of_le {p : ℝ} (hp2 : 2 ≤ p) (hp7 : p ≤ 7 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B → ∀ x : SpaceTime,
      i2Psi2LintBound (volume.prod volume) (fun q : SpaceTime × SpaceTime =>
        |K (x - q.1)| * |K (x - q.2)| * torusParabolicSize (q.2 - q.1) ^ (-p)) (C * B ^ 2) := by
  obtain ⟨C0, hC0, h⟩ := i2Psi2LintBound_kernel_shift_sq (p := p + 1 / 4) (by linarith)
    (by linarith)
  have h3 : (0 : ℝ) ≤ 3 ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by norm_num) _
  refine ⟨3 ^ (1 / 4 : ℝ) * C0, mul_nonneg h3 hC0, ?_⟩
  intro K B hK x
  have hKs : ∀ u : SpaceTime, 1 < |u.1| → K u = 0 := hK.2.2.1
  have key := (h hK x).const_mul (c := 3 ^ (1 / 4 : ℝ)) h3
  refine key.mono (fun q => ?_) (le_of_eq (by ring))
  have hs0 : 0 ≤ torusParabolicSize (q.2 - q.1) ^ (-(p + 1 / 4)) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hnn : 0 ≤ 3 ^ (1 / 4 : ℝ) * (|K (x - q.1)| * |K (x - q.2)| *
      torusParabolicSize (q.2 - q.1) ^ (-(p + 1 / 4))) :=
    mul_nonneg h3 (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hs0)
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
    · have e1 : (0 : ℝ) ^ (-p) = 0 := Real.zero_rpow (by linarith)
      have e2 : (0 : ℝ) ^ (-(p + 1 / 4)) = 0 := Real.zero_rpow (by linarith)
      rw [← h0, e1, e2]
      simp
    · have hsplit : torusParabolicSize (q.2 - q.1) ^ (-p) =
          torusParabolicSize (q.2 - q.1) ^ (-(p + 1 / 4)) *
            torusParabolicSize (q.2 - q.1) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_add h0]
        congr 1
        ring
      have hle : torusParabolicSize (q.2 - q.1) ^ (1 / 4 : ℝ) ≤ 3 ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow h0.le hs3 (by norm_num)
      rw [hsplit]
      have hk : 0 ≤ |K (x - q.1)| * |K (x - q.2)| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
      calc |K (x - q.1)| * |K (x - q.2)| * (torusParabolicSize (q.2 - q.1) ^ (-(p + 1 / 4)) *
            torusParabolicSize (q.2 - q.1) ^ (1 / 4 : ℝ))
          ≤ |K (x - q.1)| * |K (x - q.2)| * (torusParabolicSize (q.2 - q.1) ^ (-(p + 1 / 4)) *
            3 ^ (1 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hs0) hk
        _ = _ := by ring

end RegularityStructures

end
