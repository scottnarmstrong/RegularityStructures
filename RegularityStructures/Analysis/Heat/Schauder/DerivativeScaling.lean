/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Annihilating.Scaled
public import RegularityStructures.Analysis.Heat.Schauder.Shell

/-!
# Scaling of derivatives of dyadic rescalings

For `h` smooth and supported in the unit parabolic ball and a multi-index `k`:
`D^k (scaledShell h n) = (2^n)^{|k|_𝔰} · scaledShell (D^k h) n` (`lineIter_multiDirs_scaledShell`),
and the `L¹` norms of `scaledShell F n` and of its generator scale exactly
(`integral_abs_scaledShell`, `integral_abs_parabolicGenerator_scaledShell`).
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

/-- Locality: if `f` vanishes on an open set `U`, so do all its `lineIter`s. -/
theorem lineIter_eq_zero_of_isOpen {U : Set ParabolicSpace} (hU : IsOpen U) :
    ∀ (L : List ParabolicSpace) (f : ParabolicSpace → ℝ), (∀ w ∈ U, f w = 0) →
      ∀ w ∈ U, lineIter L f w = 0
  | [], f, hf, w, hw => hf w hw
  | d :: L, f, hf, w, hw => by
    have h0 := lineIter_eq_zero_of_isOpen hU L f hf
    have hev : lineIter L f =ᶠ[nhds w] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (hU.mem_nhds hw) h0
    simp [lineIter_cons, dirDeriv, hev.fderiv_eq]

theorem lineIter_eq_zero_of_lt {h : ParabolicSpace → ℝ}
    (hs : ∀ z, 1 < parabolicNorm z → h z = 0) (L : List ParabolicSpace) {w : ParabolicSpace}
    (hw : 1 < parabolicNorm w) : lineIter L h w = 0 :=
  lineIter_eq_zero_of_isOpen (isOpen_lt continuous_const continuous_parabolicNorm) L h
    (fun z hz => hs z hz) w hw

theorem lineIter_multiDirs_scaledShell {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h)
    (k : Fin 4 →₀ ℕ) (n : ℕ) :
    lineIter (multiDirs k) (scaledShell h n) =
      fun w => ((2 : ℝ) ^ n) ^ multiDeg k *
        scaledShell (lineIter (multiDirs k) h) n w := by
  funext w
  have := lineIter_coordDir_scaledShell h0 n (Finsupp.toMultiset k).toList w
  rw [← multiDirs_eq_map, indexWeight_toList] at this
  rw [this]
  simp only [scaledShell, pow_add]
  ring

theorem integral_abs_scaledShell (F : ParabolicSpace → ℝ) (n : ℕ) :
    ∫ w, |scaledShell F n w| = ((2 : ℝ) ^ n)⁻¹ ^ 2 * ∫ w, |F w| := by
  have hN : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have e : ∀ w, |scaledShell F n w| = ((2 : ℝ) ^ n) ^ 3 * |F (parabolicDilate (2 ^ n) w)| := by
    intro w
    rw [scaledShell, abs_mul, abs_of_pos (by positivity)]
  simp_rw [e]
  rw [integral_const_mul, integral_comp_parabolicDilate (fun u => |F u|) hN]
  field_simp

theorem parabolicGenerator_scaledShell {F : ParabolicSpace → ℝ} (hF : ContDiff ℝ ∞ F) (n : ℕ)
    (w : ParabolicSpace) :
    parabolicGenerator (scaledShell F n) w =
      ((2 : ℝ) ^ n) ^ 7 * parabolicGenerator F (parabolicDilate (2 ^ n) w) := by
  have h2 : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hc : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := inv_pos.2 h2
  have hfun : scaledShell F n = fun w => ((2 : ℝ) ^ n)⁻¹ ^ 2 *
      rescaledTestFunction F (((2 : ℝ) ^ n)⁻¹) 0 w := by
    funext w
    simp only [scaledShell, rescaledTestFunction, sub_zero, inv_inv]
    field_simp
  have hsm := contDiff_rescaledTestFunction hF (((2 : ℝ) ^ n)⁻¹) 0
  rw [hfun, parabolicGenerator_const_mul hsm]
  beta_reduce
  rw [parabolicGenerator_rescaledTestFunction hF hc]
  unfold rescaledTestFunction
  simp only [sub_zero, inv_inv]
  field_simp

theorem integral_abs_parabolicGenerator_scaledShell {F : ParabolicSpace → ℝ}
    (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ∫ w, |parabolicGenerator (scaledShell F n) w| =
      ((2 : ℝ) ^ n) ^ 2 * ∫ w, |parabolicGenerator F w| := by
  have hN : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have e : ∀ w, |parabolicGenerator (scaledShell F n) w| =
      ((2 : ℝ) ^ n) ^ 7 * |parabolicGenerator F (parabolicDilate (2 ^ n) w)| := by
    intro w
    rw [parabolicGenerator_scaledShell hF, abs_mul, abs_of_pos (by positivity)]
  simp_rw [e]
  rw [integral_const_mul, integral_comp_parabolicDilate (fun u => |parabolicGenerator F u|) hN]
  field_simp

end RegularityStructures

end
