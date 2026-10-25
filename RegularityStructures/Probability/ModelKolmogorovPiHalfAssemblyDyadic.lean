/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyBox

/-!
# Dyadic blocks for the `Π` norm

The blocks `u ∈ [2 s_j, 4 s_j] = [2^{-(j+1)}, 2^{-j}]`, `s_j = 2^{-(j+2)}`, cover `(0, 1]`.
`piNormOn_le_of_dyadic_blocks` bounds `‖Π‖_{γ;S}` by the deterministic constant for the symbols in
`Dπ` plus a dyadic block bound for all other symbols.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RegularityStructures

/-- The dyadic scale `s_j = 2^{-(j+2)}`, so that the block `[2 s_j, 4 s_j]` is `[2^{-(j+1)}, 2^{-j}]`. -/
@[expose] noncomputable def piHalfScale (j : ℕ) : ℝ := (1 / 2 : ℝ) ^ (j + 2)

theorem piHalfScale_pos (j : ℕ) : 0 < piHalfScale j := by
  unfold piHalfScale; positivity

theorem two_mul_piHalfScale (j : ℕ) : 2 * piHalfScale j = (1 / 2 : ℝ) ^ (j + 1) := by
  unfold piHalfScale; rw [pow_succ _ (j + 1)]; ring

theorem four_mul_piHalfScale (j : ℕ) : 4 * piHalfScale j = (1 / 2 : ℝ) ^ j := by
  unfold piHalfScale
  rw [pow_succ _ (j + 1), pow_succ _ j]; ring

/-- Every `t ∈ (0, 1]` lies in some dyadic block `[2^{-(j+1)}, 2^{-j}]`. -/
theorem exists_dyadic_block {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    ∃ j : ℕ, t ∈ Icc ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j) := by
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near (x := 1 / t) (y := (2 : ℝ))
    (by rw [le_div_iff₀ ht.1]; simpa using ht.2) one_lt_two
  refine ⟨n, ?_, ?_⟩
  · rw [one_div_pow, div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ ht.1] at h2
    nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) (n + 1)]
  · rw [one_div_pow, le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ ht.1] at h1
    linarith

/-- `s^e ≤ 4^{|e|} t^e` for `t ∈ [2 s, 4 s]`. -/
theorem rpow_scale_le_of_mem_block {s t : ℝ} (hs : 0 < s) (ht : t ∈ Icc (2 * s) (4 * s))
    (e : ℝ) : s ^ e ≤ (4 : ℝ) ^ |e| * t ^ e := by
  have ht0 : 0 < t := by linarith [ht.1]
  rcases le_or_gt 0 e with he | he
  · calc s ^ e ≤ t ^ e := Real.rpow_le_rpow hs.le (by linarith [ht.1]) he
      _ ≤ (4 : ℝ) ^ |e| * t ^ e :=
        le_mul_of_one_le_left (Real.rpow_nonneg ht0.le _)
          (Real.one_le_rpow (by norm_num) (abs_nonneg e))
  · have h1 : s ^ e ≤ (t / 4) ^ e :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [ht.2]) he.le
    rw [Real.div_rpow ht0.le (by norm_num), abs_of_neg he] at *
    rw [Real.rpow_neg (by norm_num)]
    calc s ^ e ≤ t ^ e / 4 ^ e := h1
      _ = ((4 : ℝ) ^ e)⁻¹ * t ^ e := by rw [div_eq_inv_mul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- The block-to-continuum constant `W = ∑_i 4^{|deg i / ℓ|}`. -/
noncomputable def piHalfBlockConst (𝒯 : RegularityStructure ι) : ℝ :=
  ∑ i, (4 : ℝ) ^ |𝒯.deg i / parabolicSemigroup.order|

theorem piHalfBlockConst_nonneg (𝒯 : RegularityStructure ι) : 0 ≤ piHalfBlockConst 𝒯 :=
  Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (by norm_num) _

theorem rpow_piHalfScale_le (i : ι) {j : ℕ} {t : ℝ}
    (ht : t ∈ Icc (2 * piHalfScale j) (4 * piHalfScale j)) :
    piHalfScale j ^ (𝒯.deg i / parabolicSemigroup.order) ≤
      piHalfBlockConst 𝒯 * t ^ (𝒯.deg i / parabolicSemigroup.order) := by
  have hle : (4 : ℝ) ^ |𝒯.deg i / parabolicSemigroup.order| ≤ piHalfBlockConst 𝒯 :=
    Finset.single_le_sum (f := fun i => (4 : ℝ) ^ |𝒯.deg i / parabolicSemigroup.order|)
      (fun _ _ => Real.rpow_nonneg (by norm_num) _) (Finset.mem_univ i)
  have ht0 : 0 < t := by linarith [ht.1, piHalfScale_pos j]
  exact (rpow_scale_le_of_mem_block (piHalfScale_pos j) ht _).trans
    (mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg ht0.le _))

/-- Deterministic reduction of the `Π` norm to dyadic blocks: symbols in `Dπ` are bounded by `C`
directly, all other symbols by a block bound `B · s_j^{deg i/ℓ}` on `u ∈ [2^{-(j+1)}, 2^{-j}]`. -/
theorem piNormOn_le_of_dyadic_blocks (M : Model 𝒯 parabolicSemigroup) (γ : ℝ)
    (S : Set ParabolicSpace) (Dπ : Set ι) (C : ℝ) (B : ℝ≥0∞)
    (hdet : ∀ i ∈ Dπ, 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x ∈ S,
      |M.regPi x (Pi.single i 1) t x| ≤ C * t ^ (𝒯.deg i / parabolicSemigroup.order))
    (hdy : ∀ i, i ∉ Dπ → 𝒯.deg i < γ → ∀ j : ℕ,
      ∀ u ∈ Icc ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j), ∀ x ∈ S,
        ‖M.regPi x (Pi.single i 1) u x‖ₑ ≤
          B * ENNReal.ofReal (piHalfScale j ^ (𝒯.deg i / parabolicSemigroup.order))) :
    M.piNormOn γ S ≤ ENNReal.ofReal C + ENNReal.ofReal (piHalfBlockConst 𝒯) * B := by
  set c : ℝ≥0∞ := ENNReal.ofReal C + ENNReal.ofReal (piHalfBlockConst 𝒯) * B with hc
  by_cases htop : c = ⊤
  · rw [htop]; exact le_top
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ≥0, (c' : ℝ≥0∞) = c := ⟨_, ENNReal.coe_toNNReal htop⟩
  rw [← hc', Model.piNormOn_le_iff]
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
    have h3 : ‖M.regPi x (Pi.single i 1) t x‖ₑ ≤
        (c' : ℝ≥0∞) * ENNReal.ofReal (t ^ (𝒯.deg i / parabolicSemigroup.order)) := by
      calc ‖M.regPi x (Pi.single i 1) t x‖ₑ
          ≤ B * ENNReal.ofReal (piHalfScale j ^ (𝒯.deg i / parabolicSemigroup.order)) := by
            have := h1; rwa [show t = t from rfl] at this
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

end RegularityStructures

end
