/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.BlockEnvelope.Bracket
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# The block envelope of the parabolic kernel

`kernelBlockEnvelope n s z = s^{-5/4} (1 + |z₀|/s^{1/2})^{-n} ∏ᵢ (1 + |zᵢ|/s^{1/4})^{-n}`.

* `exists_abs_parabolicKernel_le_blockEnvelope`: `|q_r(z)| ≤ C E^n_s(z)` for `r ∈ [s, 3s]`;
* `kernelBlockEnvelope_shift_le`: Peetre comparison under a shift of parabolic size `≤ s^{1/4}`;
* `exists_enorm_apply_le_blockEnvelope_lintegral`: block splitting for `Q`-distributions.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The block envelope `E^n_s(z) = s^{-5/4} (1 + |z₀|/s^{1/2})^{-n} ∏ᵢ (1 + |zᵢ|/s^{1/4})^{-n}`. -/
def kernelBlockEnvelope (n : ℕ) (s : ℝ) (z : ParabolicSpace) : ℝ :=
  s ^ (-(5 / 4 : ℝ)) * (1 + |z.1| / s ^ (1 / 2 : ℝ)) ^ (-(n : ℝ)) *
    ∏ i, (1 + |z.2 i| / s ^ (1 / 4 : ℝ)) ^ (-(n : ℝ))

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

/-- The envelope as a product of one-dimensional factors. -/
theorem kernelBlockEnvelope_eq_prod (n : ℕ) {s : ℝ} (hs : 0 < s) (z : ParabolicSpace) :
    kernelBlockEnvelope n s z = (s ^ (-(1 / 2 : ℝ)) * blockBracket n (s ^ (1 / 2 : ℝ)) z.1) *
      ∏ i, (s ^ (-(1 / 4 : ℝ)) * blockBracket n (s ^ (1 / 4 : ℝ)) (z.2 i)) := by
  have hprod : s ^ (-(5 / 4 : ℝ)) = s ^ (-(1 / 2 : ℝ)) * (s ^ (-(1 / 4 : ℝ))) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le, ← Real.rpow_add hs]
    norm_num
  unfold kernelBlockEnvelope
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hprod]
  simp only [blockBracket]
  ring

theorem kernelBlockEnvelope_nonneg (n : ℕ) {s : ℝ} (hs : 0 < s) (z : ParabolicSpace) :
    0 ≤ kernelBlockEnvelope n s z := by
  rw [kernelBlockEnvelope_eq_prod n hs]
  have h1 : ∀ θ : ℝ, 0 ≤ s ^ θ := fun θ => (Real.rpow_pos_of_pos hs θ).le
  have hb : ∀ (θ : ℝ) (u : ℝ), 0 ≤ blockBracket n (s ^ θ) u := fun θ u =>
    blockBracket_nonneg n (Real.rpow_pos_of_pos hs θ) u
  exact mul_nonneg (mul_nonneg (h1 _) (hb _ _))
    (Finset.prod_nonneg fun i _ => mul_nonneg (h1 _) (hb _ _))

theorem exists_abs_heatKernel1D_le_blockBracket (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → ∀ r ∈ Set.Icc s (3 * s), ∀ b : ℝ,
      |heatKernel1D r b| ≤ C * (s ^ (-(1 / 2 : ℝ)) * blockBracket n (s ^ (1 / 2 : ℝ)) b) := by
  obtain ⟨C, hC⟩ := heatKernel1D_one_decay n
  have hC0 : 0 ≤ C := by simpa using (abs_nonneg _).trans (hC 0)
  refine ⟨C * (3 ^ (1 / 2 : ℝ)) ^ n, by positivity, fun s hs r hr b => ?_⟩
  rw [heatKernel1D_eq_scale (hs.trans_le hr.1)]
  have := abs_scaled_profile_le n hC0 hC (θ := 1 / 2) (by norm_num) hs hr.1 hr.2 b
  exact this

theorem exists_abs_quarticKernel_le_blockBracket (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → ∀ r ∈ Set.Icc s (3 * s), ∀ b : ℝ,
      |quarticKernel r b| ≤ C * (s ^ (-(1 / 4 : ℝ)) * blockBracket n (s ^ (1 / 4 : ℝ)) b) := by
  obtain ⟨C, hC⟩ := symKernel_one_decay (j := 2) (by norm_num) n
  have hC0 : 0 ≤ C := by simpa using (abs_nonneg _).trans (hC 0)
  refine ⟨C * (3 ^ (1 / 4 : ℝ)) ^ n, by positivity, fun s hs r hr b => ?_⟩
  rw [quarticKernel_eq_scale (hs.trans_le hr.1)]
  have := abs_scaled_profile_le n hC0 (f := quarticKernel 1) hC (θ := 1 / 4) (by norm_num) hs
    hr.1 hr.2 b
  exact this

/-- Block domination of the parabolic kernel by the envelope, uniformly for `r ∈ [s, 3s]`. -/
theorem exists_abs_parabolicKernel_le_blockEnvelope (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → ∀ r ∈ Set.Icc s (3 * s), ∀ z : ParabolicSpace,
      |parabolicKernel r z| ≤ C * kernelBlockEnvelope n s z := by
  obtain ⟨C₁, h₁, H₁⟩ := exists_abs_heatKernel1D_le_blockBracket n
  obtain ⟨C₂, h₂, H₂⟩ := exists_abs_quarticKernel_le_blockBracket n
  refine ⟨C₁ * C₂ ^ 3, by positivity, fun s hs r hr z => ?_⟩
  rw [kernelBlockEnvelope_eq_prod n hs, parabolicKernel, abs_mul, Finset.abs_prod]
  have hprod : ∏ i, |quarticKernel r (z.2 i)| ≤
      ∏ i, (C₂ * (s ^ (-(1 / 4 : ℝ)) * blockBracket n (s ^ (1 / 4 : ℝ)) (z.2 i))) :=
    Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => H₂ s hs r hr _
  calc |heatKernel1D r z.1| * ∏ i, |quarticKernel r (z.2 i)|
      ≤ (C₁ * (s ^ (-(1 / 2 : ℝ)) * blockBracket n (s ^ (1 / 2 : ℝ)) z.1)) *
        ∏ i, (C₂ * (s ^ (-(1 / 4 : ℝ)) * blockBracket n (s ^ (1 / 4 : ℝ)) (z.2 i))) :=
        mul_le_mul (H₁ s hs r hr _) hprod (Finset.prod_nonneg fun i _ => abs_nonneg _)
          (mul_nonneg h₁ (mul_nonneg (Real.rpow_pos_of_pos hs _).le
            (blockBracket_nonneg _ (Real.rpow_pos_of_pos hs _) _)))
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring

/-- Coordinates of a displacement of parabolic size `≤ s^{1/4}`. -/
theorem abs_fst_le_of_parabolicNorm_le {h : ParabolicSpace} {s : ℝ} (hs : 0 < s)
    (hh : parabolicNorm h ≤ s ^ (1 / 4 : ℝ)) : |h.1| ≤ s ^ (1 / 2 : ℝ) := by
  have h1 : Real.sqrt |h.1| ≤ s ^ (1 / 4 : ℝ) := by
    refine le_trans ?_ hh
    unfold parabolicNorm
    have : 0 ≤ ∑ i, |h.2 i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  have h2 : |h.1| = Real.sqrt |h.1| ^ 2 := (Real.sq_sqrt (abs_nonneg _)).symm
  have h3 : (s ^ (1 / 4 : ℝ)) ^ 2 = s ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    norm_num
  rw [h2, ← h3]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2

theorem abs_snd_le_of_parabolicNorm_le {h : ParabolicSpace} {s : ℝ}
    (hh : parabolicNorm h ≤ s ^ (1 / 4 : ℝ)) (i : Fin 3) : |h.2 i| ≤ s ^ (1 / 4 : ℝ) := by
  refine le_trans ?_ hh
  unfold parabolicNorm
  have : 0 ≤ Real.sqrt |h.1| := Real.sqrt_nonneg _
  have h2 : |h.2 i| ≤ ∑ j, |h.2 j| :=
    Finset.single_le_sum (f := fun j => |h.2 j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  linarith

/-- Shift comparison (Peetre): base points moved by at most the block scale. -/
theorem kernelBlockEnvelope_shift_le (n : ℕ) {s : ℝ} (hs : 0 < s) {x x₀ y : ParabolicSpace}
    (hx : parabolicNorm (x - x₀) ≤ s ^ (1 / 4 : ℝ)) :
    kernelBlockEnvelope n s (x - y) ≤ 2 ^ (4 * n) * kernelBlockEnvelope n s (x₀ - y) := by
  rw [kernelBlockEnvelope_eq_prod n hs, kernelBlockEnvelope_eq_prod n hs]
  have h0 : blockBracket n (s ^ (1 / 2 : ℝ)) (x - y).1 ≤
      2 ^ n * blockBracket n (s ^ (1 / 2 : ℝ)) (x₀ - y).1 := by
    refine blockBracket_le_two_pow_mul n (Real.rpow_pos_of_pos hs _) ?_
    have := abs_fst_le_of_parabolicNorm_le hs hx
    simpa [abs_sub_comm] using this
  have hi : ∀ i : Fin 3, blockBracket n (s ^ (1 / 4 : ℝ)) ((x - y).2 i) ≤
      2 ^ n * blockBracket n (s ^ (1 / 4 : ℝ)) ((x₀ - y).2 i) := fun i => by
    refine blockBracket_le_two_pow_mul n (Real.rpow_pos_of_pos hs _) ?_
    have := abs_snd_le_of_parabolicNorm_le hx i
    simpa [abs_sub_comm] using this
  have hs1 : 0 ≤ s ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos hs _).le
  have hs2 : 0 ≤ s ^ (-(1 / 4 : ℝ)) := (Real.rpow_pos_of_pos hs _).le
  have hb : ∀ (θ : ℝ) (u : ℝ), 0 ≤ blockBracket n (s ^ θ) u := fun θ u =>
    blockBracket_nonneg n (Real.rpow_pos_of_pos hs θ) u
  have hprod : ∏ i, (s ^ (-(1 / 4 : ℝ)) * blockBracket n (s ^ (1 / 4 : ℝ)) ((x - y).2 i)) ≤
      ∏ i, (2 ^ n * (s ^ (-(1 / 4 : ℝ)) *
        blockBracket n (s ^ (1 / 4 : ℝ)) ((x₀ - y).2 i))) :=
    Finset.prod_le_prod₀ (fun i _ => mul_nonneg hs2 (hb _ _)) fun i _ => by
      have := mul_le_mul_of_nonneg_left (hi i) hs2
      calc _ ≤ s ^ (-(1 / 4 : ℝ)) * (2 ^ n * blockBracket n (s ^ (1 / 4 : ℝ)) ((x₀ - y).2 i)) := this
        _ = _ := by ring
  have hfst : s ^ (-(1 / 2 : ℝ)) * blockBracket n (s ^ (1 / 2 : ℝ)) (x - y).1 ≤
      2 ^ n * (s ^ (-(1 / 2 : ℝ)) * blockBracket n (s ^ (1 / 2 : ℝ)) (x₀ - y).1) := by
    calc _ ≤ s ^ (-(1 / 2 : ℝ)) * (2 ^ n * blockBracket n (s ^ (1 / 2 : ℝ)) (x₀ - y).1) :=
          mul_le_mul_of_nonneg_left h0 hs1
      _ = _ := by ring
  calc _ ≤ (2 ^ n * (s ^ (-(1 / 2 : ℝ)) * blockBracket n (s ^ (1 / 2 : ℝ)) (x₀ - y).1)) *
        ∏ i, (2 ^ n * (s ^ (-(1 / 4 : ℝ)) * blockBracket n (s ^ (1 / 4 : ℝ)) ((x₀ - y).2 i))) :=
        mul_le_mul hfst hprod (Finset.prod_nonneg fun i _ => mul_nonneg hs2 (hb _ _))
          (mul_nonneg (pow_nonneg (by norm_num) n) (mul_nonneg hs1 (hb _ _)))
    _ = _ := by
        have h4 : (2 : ℝ) ^ (4 * n) = 2 ^ n * (2 ^ n) ^ 3 := by
          rw [← pow_mul, ← pow_add]
          congr 1
          ring
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, h4]
        ring

/-- Block splitting for `Q`-distributions of the parabolic semigroup, for `t ∈ [2s, 4s]`. -/
theorem exists_enorm_apply_le_blockEnvelope_lintegral (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Λ : ℝ → ParabolicSpace → ℝ}, Λ ∈ parabolicSemigroup.distributions →
      ∀ s : ℝ, 0 < s → ∀ t ∈ Set.Icc (2 * s) (4 * s), ∀ z : ParabolicSpace,
        ‖Λ t z‖ₑ ≤ ENNReal.ofReal C *
          ∫⁻ w, ENNReal.ofReal (kernelBlockEnvelope n s (z - w)) * ‖Λ s w‖ₑ := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_parabolicKernel_le_blockEnvelope n
  refine ⟨C, hC0, fun {Λ} hΛ s hs t ht z => ?_⟩
  have hts : 0 < t - s := by linarith [ht.1]
  have hblock : t - s ∈ Set.Icc s (3 * s) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h1 := parabolicSemigroup.apply_eq hΛ hts hs z
  rw [sub_add_cancel] at h1
  rw [← h1]
  have h2 : parabolicSemigroup.apply (t - s) (Λ s) z =
      ∫ w, parabolicKernel (t - s) (z - w) * Λ s w := rfl
  rw [h2]
  calc ‖∫ w, parabolicKernel (t - s) (z - w) * Λ s w‖ₑ
      ≤ ∫⁻ w, ‖parabolicKernel (t - s) (z - w) * Λ s w‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ w, ENNReal.ofReal C *
          (ENNReal.ofReal (kernelBlockEnvelope n s (z - w)) * ‖Λ s w‖ₑ) := by
        refine lintegral_mono fun w => ?_
        rw [enorm_mul, Real.enorm_eq_ofReal_abs, ← mul_assoc, ← ENNReal.ofReal_mul hC0]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hC s hs _ hblock _)) le_rfl
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end RegularityStructures

end
