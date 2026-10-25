/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Mollifier
public import RegularityStructures.Analysis.Parabolic.TestFunction

/-!
# Parabolic scaling of the mollifier

The rescaled mollifier has scale-independent total variation on Euclidean space.  This is the
Euclidean half of the uniform `L¹` estimate for its spatial periodisation.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures

namespace Phi43

theorem integrable_abs_rescale (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) : Integrable (fun z => |rescale ρ ε z|) := by
  have hc : Continuous (rescale ρ ε) := by
    unfold rescale
    apply Continuous.const_mul
    exact hρ.contDiff.continuous.comp (by fun_prop)
  have hs : HasCompactSupport (rescale ρ ε) := by
    let a : ℝ := ε ^ (-2 : ℤ)
    let b : ℝ := ε⁻¹
    let e : (ℝ × (Fin 3 → ℝ)) ≃ₜ (ℝ × (Fin 3 → ℝ)) :=
      Homeomorph.prodCongr (Homeomorph.mulRight₀ a (by
        dsimp [a]
        exact zpow_ne_zero _ (ne_of_gt hε)))
        (Homeomorph.smulOfNeZero b (by
          dsimp [b]
          exact inv_ne_zero (ne_of_gt hε)))
    have he := hρ.hasCompactSupport.comp_homeomorph e
    have hm := he.mul_left (f := fun _ : ℝ × (Fin 3 → ℝ) => ε ^ (-5 : ℤ))
    convert hm using 1
    funext q
    simp [e, a, b, rescale, Function.comp_def, zpow_neg, Prod.map, ne_of_gt hε]
    ring_nf
  exact hc.norm.integrable_of_hasCompactSupport hs.norm

theorem integral_abs_rescale (ρ : ℝ × (Fin 3 → ℝ) → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ z, |rescale ρ ε z| = ∫ z, |ρ z| := by
  have hscale : ∀ z : ℝ × (Fin 3 → ℝ),
      |rescale ρ ε z| = ε ^ (-5 : ℤ) *
        |ρ (RegularityStructures.parabolicDilate ε⁻¹ z)| := by
    intro z
    unfold rescale RegularityStructures.parabolicDilate
    rw [abs_mul, abs_of_pos (zpow_pos hε _)]
    congr 2
    · norm_num
  simp_rw [hscale]
  rw [integral_const_mul,
    integral_comp_parabolicDilate (fun z => |ρ z|) (inv_pos.mpr hε)]
  have hpow : ε ^ (-5 : ℤ) * (ε⁻¹ ^ 5)⁻¹ = 1 := by
    rw [inv_pow, inv_inv]
    rw [show ε ^ 5 = ε ^ (5 : ℤ) by norm_num]
    rw [← zpow_add₀ (ne_of_gt hε)]
    norm_num
  calc
    ε ^ (-5 : ℤ) * ((ε⁻¹ ^ 5)⁻¹ * ∫ (w : ParabolicSpace), |ρ w|) =
        (ε ^ (-5 : ℤ) * (ε⁻¹ ^ 5)⁻¹) * ∫ (w : ParabolicSpace), |ρ w| := by ring
    _ = ∫ (w : ParabolicSpace), |ρ w| := by rw [hpow, one_mul]

end Phi43

end RegularityStructures

end
