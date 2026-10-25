/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.SymbolDeriv
public import RegularityStructures.Analysis.Kernel.Parabolic

/-!
# The time-derivative bound for the parabolic kernel

[Hos25, Definition 2.6 (iv)] (arXiv:2310.07396v2) asks for
`|∂_t Q_t(x, y)| ≤ C t⁻¹ t^{-5/4} G(t^{-1/2} z₀, t^{-1/4} z')` with a rapidly decaying `G`.
For `parabolicKernel` this follows from exact scaling and the decay of `k_1, k_1', g_1, g_1'`:
`parabolicKernel` is differentiable in `t` with derivative `parabolicTimeDeriv t z`
(`hasDerivAt_parabolicKernel_time`), and
`|parabolicTimeDeriv t z| ≤ t⁻¹ t^{-5/4} parabolicTimeProfile (S^{t^{-1/4}} z)`
(`abs_parabolicTimeDeriv_le`), where `parabolicTimeProfile` is an explicit profile built from
`|k_1|, |g_1|` and `|k_1 + u k_1'|, |g_1 + u g_1'|`, with rapid decay in every coordinate
(`parabolicTimeProfile_decay`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The time derivative of `s ↦ parabolicKernel s z` at `t`. -/
def parabolicTimeDeriv (t : ℝ) (z : ParabolicSpace) : ℝ :=
  symKernelTimeDeriv 1 t z.1 *
      (quarticKernel t (z.2 0) * quarticKernel t (z.2 1) * quarticKernel t (z.2 2)) +
    heatKernel1D t z.1 *
      (symKernelTimeDeriv 2 t (z.2 0) * quarticKernel t (z.2 1) * quarticKernel t (z.2 2) +
        quarticKernel t (z.2 0) * symKernelTimeDeriv 2 t (z.2 1) * quarticKernel t (z.2 2) +
        quarticKernel t (z.2 0) * quarticKernel t (z.2 1) * symKernelTimeDeriv 2 t (z.2 2))

/-- The profile `G` bounding the time derivative: with `κ = |k_1|`, `Φ = |k_1 + u k_1'|`,
`B = |g_1|`, `A = |g_1 + u g_1'|`,
`G(w) = ½ A(w₀) κ(w₁) κ(w₂) κ(w₃) + ¼ B(w₀) (Φ(w₁) κ(w₂) κ(w₃) + κ(w₁) Φ(w₂) κ(w₃) +
κ(w₁) κ(w₂) Φ(w₃))`. -/
def parabolicTimeProfile (w : ParabolicSpace) : ℝ :=
  (1 / 2) * |symProfile 1 w.1| * (|quarticKernel 1 (w.2 0)| * |quarticKernel 1 (w.2 1)| *
      |quarticKernel 1 (w.2 2)|) +
    (1 / 4) * |heatKernel1D 1 w.1| *
      (|symProfile 2 (w.2 0)| * |quarticKernel 1 (w.2 1)| * |quarticKernel 1 (w.2 2)| +
        |quarticKernel 1 (w.2 0)| * |symProfile 2 (w.2 1)| * |quarticKernel 1 (w.2 2)| +
        |quarticKernel 1 (w.2 0)| * |quarticKernel 1 (w.2 1)| * |symProfile 2 (w.2 2)|)

end RegularityStructures

end

public section

open Real

namespace RegularityStructures

theorem hasDerivAt_parabolicKernel_time {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    HasDerivAt (fun s => parabolicKernel s z) (parabolicTimeDeriv t z) t := by
  have hg := hasDerivAt_symKernel_time (j := 1) (by norm_num) ht z.1
  have hk := fun i : Fin 3 => hasDerivAt_symKernel_time (j := 2) (by norm_num) ht (z.2 i)
  have hprod := ((hk 0).mul (hk 1)).mul (hk 2)
  have h := hg.mul hprod
  have e : (fun s => parabolicKernel s z) =
      fun s => symKernel 1 s z.1 * (symKernel 2 s (z.2 0) * symKernel 2 s (z.2 1) *
        symKernel 2 s (z.2 2)) := by
    funext s
    simp only [parabolicKernel, Fin.prod_univ_three]
    rfl
  rw [e]
  refine h.congr_deriv ?_
  simp only [parabolicTimeDeriv, Pi.mul_apply, quarticKernel, heatKernel1D]
  ring

/-- Algebraic core of the time-derivative bound. -/
theorem abs_time_deriv_aux {g g' k₀ k₁ k₂ k₀' k₁' k₂' lg lk T A B κ₀ κ₁ κ₂ Φ₀ Φ₁ Φ₂ : ℝ}
    (hlk : 0 ≤ lk) (hlg : 0 ≤ lg) (hB : 0 ≤ B) (h₀ : 0 ≤ κ₀) (h₁ : 0 ≤ κ₁) (h₂ : 0 ≤ κ₂)
    (hg' : |g'| ≤ (1 / 2) * T * lg * A) (hg : |g| = lg * B)
    (hk₀ : |k₀| = lk * κ₀) (hk₁ : |k₁| = lk * κ₁) (hk₂ : |k₂| = lk * κ₂)
    (hk₀' : |k₀'| ≤ (1 / 4) * T * lk * Φ₀) (hk₁' : |k₁'| ≤ (1 / 4) * T * lk * Φ₁)
    (hk₂' : |k₂'| ≤ (1 / 4) * T * lk * Φ₂) :
    |g' * (k₀ * k₁ * k₂) + g * (k₀' * k₁ * k₂ + k₀ * k₁' * k₂ + k₀ * k₁ * k₂')| ≤
      T * lg * lk ^ 3 *
        ((1 / 2) * A * (κ₀ * κ₁ * κ₂) + (1 / 4) * B * (Φ₀ * κ₁ * κ₂ + κ₀ * Φ₁ * κ₂ +
          κ₀ * κ₁ * Φ₂)) := by
  have step1 : |g' * (k₀ * k₁ * k₂) + g * (k₀' * k₁ * k₂ + k₀ * k₁' * k₂ + k₀ * k₁ * k₂')| ≤
      |g'| * (|k₀| * |k₁| * |k₂|) + |g| * (|k₀'| * |k₁| * |k₂| + |k₀| * |k₁'| * |k₂| +
        |k₀| * |k₁| * |k₂'|) := by
    refine (abs_add_le _ _).trans ?_
    simp only [abs_mul]
    gcongr
    exact abs_add_three _ _ _ |>.trans (by simp only [abs_mul]; exact le_rfl)
  refine step1.trans ?_
  rw [hg, hk₀, hk₁, hk₂]
  have : |g'| * (lk * κ₀ * (lk * κ₁) * (lk * κ₂)) +
      lg * B * (|k₀'| * (lk * κ₁) * (lk * κ₂) + lk * κ₀ * |k₁'| * (lk * κ₂) +
        lk * κ₀ * (lk * κ₁) * |k₂'|) ≤
      ((1 / 2) * T * lg * A) * (lk * κ₀ * (lk * κ₁) * (lk * κ₂)) +
      lg * B * (((1 / 4) * T * lk * Φ₀) * (lk * κ₁) * (lk * κ₂) +
        lk * κ₀ * ((1 / 4) * T * lk * Φ₁) * (lk * κ₂) +
        lk * κ₀ * (lk * κ₁) * ((1 / 4) * T * lk * Φ₂)) := by
    gcongr
  refine this.trans (le_of_eq ?_)
  ring

theorem symScale_two_sq {t : ℝ} (ht : 0 < t) : symScale 2 t ^ 2 = symScale 1 t := by
  unfold symScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  norm_num

theorem symScale_mul_pow {t : ℝ} (ht : 0 < t) :
    symScale 1 t * symScale 2 t ^ 3 = t ^ (-(5 / 4 : ℝ)) := by
  unfold symScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
  norm_num

/-- The time-derivative bound `|∂_t q_t(z)| ≤ t⁻¹ t^{-5/4} G(S^{t^{-1/4}} z)`
([Hos25, Definition 2.6 (iv)]). -/
theorem abs_parabolicTimeDeriv_le {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    |parabolicTimeDeriv t z| ≤
      t⁻¹ * t ^ (-(5 / 4 : ℝ)) * parabolicTimeProfile (parabolicDilate (t ^ (-(1 / 4 : ℝ))) z) := by
  have hlk : 0 < symScale 2 t := symScale_pos ht 2
  have hlg : 0 < symScale 1 t := symScale_pos ht 1
  have hT : 0 ≤ t⁻¹ := (inv_pos.2 ht).le
  have hk : ∀ b : ℝ, |quarticKernel t b| = symScale 2 t * |quarticKernel 1 (symScale 2 t * b)| := by
    intro b
    rw [show quarticKernel t b = symScale 2 t * quarticKernel 1 (symScale 2 t * b) from
      symKernel_eq_scale (by norm_num) ht b, abs_mul, abs_of_pos hlk]
  have hg : ∀ b : ℝ, |heatKernel1D t b| = symScale 1 t * |heatKernel1D 1 (symScale 1 t * b)| := by
    intro b
    rw [show heatKernel1D t b = symScale 1 t * heatKernel1D 1 (symScale 1 t * b) from
      symKernel_eq_scale (by norm_num) ht b, abs_mul, abs_of_pos hlg]
  have hk' : ∀ b : ℝ, |symKernelTimeDeriv 2 t b| ≤
      (1 / 4) * t⁻¹ * symScale 2 t * |symProfile 2 (symScale 2 t * b)| := fun b => by
    have := abs_symKernelTimeDeriv_le (j := 2) (by norm_num) ht b
    norm_num at this ⊢
    exact this
  have hg' : ∀ b : ℝ, |symKernelTimeDeriv 1 t b| ≤
      (1 / 2) * t⁻¹ * symScale 1 t * |symProfile 1 (symScale 1 t * b)| := fun b => by
    have := abs_symKernelTimeDeriv_le (j := 1) (by norm_num) ht b
    norm_num at this ⊢
    exact this
  have hsq := symScale_two_sq ht
  have hpow := symScale_mul_pow ht
  have hdil : parabolicDilate (t ^ (-(1 / 4 : ℝ))) z =
      (symScale 1 t * z.1, symScale 2 t • z.2) := by
    unfold parabolicDilate
    rw [← hsq]
    rfl
  rw [hdil]
  have := abs_time_deriv_aux (g := heatKernel1D t z.1) (g' := symKernelTimeDeriv 1 t z.1)
    (k₀ := quarticKernel t (z.2 0)) (k₁ := quarticKernel t (z.2 1))
    (k₂ := quarticKernel t (z.2 2)) (k₀' := symKernelTimeDeriv 2 t (z.2 0))
    (k₁' := symKernelTimeDeriv 2 t (z.2 1)) (k₂' := symKernelTimeDeriv 2 t (z.2 2))
    (lg := symScale 1 t) (lk := symScale 2 t) (T := t⁻¹)
    (A := |symProfile 1 (symScale 1 t * z.1)|) (B := |heatKernel1D 1 (symScale 1 t * z.1)|)
    (κ₀ := |quarticKernel 1 (symScale 2 t * z.2 0)|) (κ₁ := |quarticKernel 1 (symScale 2 t * z.2 1)|)
    (κ₂ := |quarticKernel 1 (symScale 2 t * z.2 2)|)
    (Φ₀ := |symProfile 2 (symScale 2 t * z.2 0)|) (Φ₁ := |symProfile 2 (symScale 2 t * z.2 1)|)
    (Φ₂ := |symProfile 2 (symScale 2 t * z.2 2)|) hlk.le hlg.le (abs_nonneg _) (abs_nonneg _)
    (abs_nonneg _) (abs_nonneg _) (hg' _) (hg _) (hk _) (hk _) (hk _) (hk' _) (hk' _) (hk' _)
  unfold parabolicTimeDeriv parabolicTimeProfile
  simp only [Pi.smul_apply, smul_eq_mul]
  calc _ ≤ _ := this
    _ = _ := by rw [mul_assoc t⁻¹, ← hpow]

theorem nonneg_of_decay {f : ℝ → ℝ} {C : ℝ} {n : ℕ}
    (h : ∀ u, |f u| ≤ C * (1 + |u|) ^ (-(n : ℝ))) : 0 ≤ C := by
  have := (abs_nonneg _).trans (h 0)
  simpa using this

/-- Algebraic core of the decay of the profile. -/
theorem time_profile_aux {A B κ₀ κ₁ κ₂ Φ₀ Φ₁ Φ₂ CA CB Ck Cp u v₀ v₁ v₂ : ℝ}
    (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hCk : 0 ≤ Ck) (hCp : 0 ≤ Cp) (hu : 0 ≤ u) (hv₀ : 0 ≤ v₀)
    (hv₁ : 0 ≤ v₁) (hκ₀ : 0 ≤ κ₀) (hκ₁ : 0 ≤ κ₁)
    (hκ₂ : 0 ≤ κ₂) (hΦ₀' : 0 ≤ Φ₀) (hΦ₁' : 0 ≤ Φ₁) (hΦ₂' : 0 ≤ Φ₂)
    (hA : A ≤ CA * u) (hB : B ≤ CB * u) (h₀ : κ₀ ≤ Ck * v₀) (h₁ : κ₁ ≤ Ck * v₁)
    (h₂ : κ₂ ≤ Ck * v₂) (hΦ₀ : Φ₀ ≤ Cp * v₀) (hΦ₁ : Φ₁ ≤ Cp * v₁) (hΦ₂ : Φ₂ ≤ Cp * v₂) :
    (1 / 2) * A * (κ₀ * κ₁ * κ₂) + (1 / 4) * B * (Φ₀ * κ₁ * κ₂ + κ₀ * Φ₁ * κ₂ + κ₀ * κ₁ * Φ₂) ≤
      ((1 / 2) * CA * Ck ^ 3 + (3 / 4) * CB * Cp * Ck ^ 2) * (u * (v₀ * v₁ * v₂)) := by
  have e1 : A * (κ₀ * κ₁ * κ₂) ≤ (CA * u) * ((Ck * v₀) * (Ck * v₁) * (Ck * v₂)) := by gcongr
  have e2 : B * (Φ₀ * κ₁ * κ₂ + κ₀ * Φ₁ * κ₂ + κ₀ * κ₁ * Φ₂) ≤ (CB * u) *
      ((Cp * v₀) * (Ck * v₁) * (Ck * v₂) + (Ck * v₀) * (Cp * v₁) * (Ck * v₂) +
        (Ck * v₀) * (Ck * v₁) * (Cp * v₂)) := by gcongr
  nlinarith [e1, e2]

/-- Rapid decay of the time-derivative profile in every coordinate. -/
theorem parabolicTimeProfile_decay (n : ℕ) :
    ∃ C : ℝ, ∀ w : ParabolicSpace, parabolicTimeProfile w ≤
      C * ((1 + |w.1|) ^ (-(n : ℝ)) * ∏ i, (1 + |w.2 i|) ^ (-(n : ℝ))) := by
  obtain ⟨Ck, hk⟩ := quarticKernel_one_decay n
  obtain ⟨Cp, hp⟩ := symProfile_decay (j := 2) (by norm_num) n
  obtain ⟨Cg, hg⟩ := heatKernel1D_one_decay n
  obtain ⟨CA, hA⟩ := symProfile_decay (j := 1) (by norm_num) n
  have h1 := nonneg_of_decay hk
  have h2 := nonneg_of_decay hp
  have h3 := nonneg_of_decay hg
  have h4 := nonneg_of_decay hA
  refine ⟨(1 / 2) * CA * Ck ^ 3 + (3 / 4) * Cg * Cp * Ck ^ 2, fun w => ?_⟩
  rw [Fin.prod_univ_three]
  have := time_profile_aux (A := |symProfile 1 w.1|) (B := |heatKernel1D 1 w.1|)
    (κ₀ := |quarticKernel 1 (w.2 0)|) (κ₁ := |quarticKernel 1 (w.2 1)|)
    (κ₂ := |quarticKernel 1 (w.2 2)|) (Φ₀ := |symProfile 2 (w.2 0)|)
    (Φ₁ := |symProfile 2 (w.2 1)|) (Φ₂ := |symProfile 2 (w.2 2)|)
    (u := (1 + |w.1|) ^ (-(n : ℝ))) (v₀ := (1 + |w.2 0|) ^ (-(n : ℝ)))
    (v₁ := (1 + |w.2 1|) ^ (-(n : ℝ))) (v₂ := (1 + |w.2 2|) ^ (-(n : ℝ)))
    h4 h3 h1 h2 (Real.rpow_nonneg (add_nonneg zero_le_one (abs_nonneg _)) _)
    (Real.rpow_nonneg (add_nonneg zero_le_one (abs_nonneg _)) _)
    (Real.rpow_nonneg (add_nonneg zero_le_one (abs_nonneg _)) _)
    (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    (hA _) (hg _) (hk _) (hk _) (hk _) (hp _) (hp _) (hp _)
  exact this

end RegularityStructures

end
