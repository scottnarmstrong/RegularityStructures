/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.ScaledTest
public import RegularityStructures.Abstract.Singular.ModelPairing.Single

/-!
# Doubling the radius of a scaled test function

If `g` is scaled at `y` with radius `R` and constant `A`, and vanishes outside `B(z, 2R)` with
`2R ≤ 1`, then `g` is scaled at `z` with radius `2R` and constant `256 A`.
-/

public section

open scoped ContDiff

namespace RegularityStructures

private theorem dilate_add_eq (c : ℝ) (z w : ParabolicSpace) :
    parabolicDilate c (z + w) = parabolicDilate c z + parabolicDilate c w := by
  ext <;> simp [parabolicDilate, mul_add]

theorem IsScaledTest.double {g : ParabolicSpace → ℝ} {y z : ParabolicSpace} {R A : ℝ}
    (hg : IsScaledTest g y R A) (hR2 : 2 * R ≤ 1)
    (hsupp : ∀ w, 2 * R < parabolicNorm (w - z) → g w = 0) :
    IsScaledTest g z (2 * R) (256 * A) := by
  have hR := hg.radius_pos
  set h : ParabolicSpace → ℝ := fun u => g (y + parabolicDilate R u) with hh_def
  have hh : ContDiff ℝ ∞ h :=
    hg.contDiff.comp (contDiff_const.add (parabolicDilateCLM R).contDiff)
  set a : ParabolicSpace := parabolicDilate R⁻¹ (z - y) with ha
  have e : (fun v => g (z + parabolicDilate (2 * R) v)) =
      (fun u => h (a + u)) ∘ (parabolicDilateCLM 2) := by
    funext v
    simp only [Function.comp_apply, parabolicDilateCLM_apply, hh_def, dilate_add_eq, ha]
    rw [parabolicDilate_parabolicDilate_inv hR.ne', ← parabolicDilate_mul, mul_comm R 2]
    congr 1
    abel
  refine ⟨hg.contDiff, by positivity, hR2, by have := hg.const_pos; positivity, hsupp,
    fun k hk v => ?_⟩
  rw [e]
  have hh' : ContDiff ℝ ∞ (fun u => h (a + u)) := hh.comp (contDiff_const.add contDiff_id)
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (n := k) _
    (hh'.of_le (by exact_mod_cast le_top)) v (by exact_mod_cast le_refl k)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hn : ‖parabolicDilateCLM 2‖ ≤ 4 := by
    have := norm_parabolicDilateCLM_le (d := 2) (by norm_num)
    norm_num at this ⊢
    linarith
  have hp : ∏ _i : Fin k, ‖parabolicDilateCLM 2‖ ≤ 256 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc ‖parabolicDilateCLM 2‖ ^ k ≤ 4 ^ k := pow_le_pow_left₀ (norm_nonneg _) hn k
      _ ≤ 4 ^ 4 := pow_le_pow_right₀ (by norm_num) hk
      _ = 256 := by norm_num
  have hd : ‖iteratedFDeriv ℝ k (fun u => h (a + u)) (parabolicDilateCLM 2 v)‖ ≤ A := by
    rw [iteratedFDeriv_comp_add_left]
    exact hg.deriv k hk _
  calc _ ≤ A * 256 := mul_le_mul hd hp (Finset.prod_nonneg fun _ _ => norm_nonneg _)
        ((norm_nonneg _).trans hd)
    _ = _ := by ring

end RegularityStructures

end
