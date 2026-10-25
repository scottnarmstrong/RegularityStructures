/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.QFamilyModelBound
public import RegularityStructures.Analysis.Kernel.BlockEnvelope.Envelope

/-!
# Cell weights for the varying-base Pi estimate

Definition of the cell weight `W_{s,k}(x₀)` and the deterministic algebra behind the cell-block
reduction: the structure-group composition `Γ_{wx} = Γ_{wx₀} Γ_{x₀x}` expands
`(Γ_{wx} e_i)_j` over the symbols `k` of degree `≤ deg i`, with coefficients
`(Γ_{x₀x} e_i)_k` bounded through `GammaBoundOn`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

theorem measurable_kernelBlockEnvelope (n : ℕ) (s : ℝ) :
    Measurable (kernelBlockEnvelope n s) := by
  unfold kernelBlockEnvelope
  fun_prop

namespace Model

variable (M : Model 𝒯 parabolicSemigroup)

theorem gammaMap_single_apply_eq_zero_of_lt (y x : ParabolicSpace) {k j : ι}
    (h : 𝒯.deg k < 𝒯.deg j) : M.gammaMap y x (Pi.single k 1) j = 0 :=
  (M.isGradedUnipotent_gammaMap y x).apply_single_of_le (fun e => by
    rw [e] at h; exact lt_irrefl _ h) h.le

end Model

/-- The coefficient bound `|(Γ_{x₀x} e_i)_k| ≤ (1 + G) s^{(deg i - deg k)/4}` for
`deg k ≤ deg i`, when `d(x₀,x) ≤ s^{1/4}`. -/
theorem enorm_gammaMap_coeff_le (M : Model 𝒯 parabolicSemigroup) {γ G : ℝ} (hG : 0 ≤ G)
    {S : Set ParabolicSpace} (hΓ : M.GammaBoundOn γ G S) {i k : ι} (hi : 𝒯.deg i < γ)
    (hk : 𝒯.deg k ≤ 𝒯.deg i) {s : ℝ} (hs : 0 < s) {x x₀ : ParabolicSpace} (hx : x ∈ S)
    (hx₀ : x₀ ∈ S) (hd : parabolicNorm (x - x₀) ≤ s ^ (1 / 4 : ℝ)) :
    ‖M.gammaMap x₀ x (Pi.single i 1) k‖ₑ ≤
      ENNReal.ofReal (1 + G) * ENNReal.ofReal (s ^ ((𝒯.deg i - 𝒯.deg k) / 4)) := by
  by_cases hki : k = i
  · subst hki
    rw [M.gammaMap_single_apply_self, sub_self, zero_div, Real.rpow_zero, enorm_one,
      ENNReal.ofReal_one, mul_one]
    exact_mod_cast ENNReal.one_le_ofReal.2 (by linarith)
  rcases hk.lt_or_eq with hlt | heq
  · have hb := hΓ i k hi hlt x hx x₀ hx₀
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (by linarith)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hscale : parabolicSemigroup.scaleDist x₀ x ^ (𝒯.deg i - 𝒯.deg k) ≤
        s ^ ((𝒯.deg i - 𝒯.deg k) / 4) := by
      have h0 : parabolicSemigroup.scaleDist x₀ x ≤ s ^ (1 / 4 : ℝ) := by
        change parabolicNorm (x₀ - x) ≤ _
        rwa [parabolicNorm_sub_comm]
      calc _ ≤ (s ^ (1 / 4 : ℝ)) ^ (𝒯.deg i - 𝒯.deg k) :=
            Real.rpow_le_rpow (parabolicSemigroup.scaleDist_nonneg _ _) h0 (by linarith)
        _ = _ := by
            rw [← Real.rpow_mul hs.le]
            congr 1
            ring
    have hpos : 0 ≤ s ^ ((𝒯.deg i - 𝒯.deg k) / 4) := Real.rpow_nonneg hs.le _
    calc |M.gammaMap x₀ x (Pi.single i 1) k|
        ≤ G * parabolicSemigroup.scaleDist x₀ x ^ (𝒯.deg i - 𝒯.deg k) := hb
      _ ≤ G * s ^ ((𝒯.deg i - 𝒯.deg k) / 4) := mul_le_mul_of_nonneg_left hscale hG
      _ ≤ (1 + G) * s ^ ((𝒯.deg i - 𝒯.deg k) / 4) :=
          mul_le_mul_of_nonneg_right (by linarith) hpos
  · have : M.gammaMap x₀ x (Pi.single i 1) k = 0 :=
      (M.isGradedUnipotent_gammaMap x₀ x).apply_single_of_le hki heq.ge
    rw [this, enorm_zero]
    exact bot_le

end RegularityStructures

end
