/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.KernelAll
public import RegularityStructures.Analysis.Parabolic.GeneratorScaling
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Spatial increments of the parabolic kernel

For the kernel `q_s` of the auxiliary semigroup on `ℝ⁴` and every `r ≥ 0` there is `K_r` with

  `∫ |q_s(z + v) − q_s(z)| ‖z‖_𝔰^r dz ≤ K_r (‖v‖_𝔰 / s^{1/4}) s^{r/4}`  for `‖v‖_𝔰 ≤ s^{1/4}`

(`exists_integral_abs_parabolicKernel_add_sub_le`). The proof reduces to `s = 1` by exact
scaling, writes `q_1(z + v) − q_1(z)` as a telescoping sum of four one-dimensional increments, and
uses the decay of `g_1, k_1` and of their derivatives with the Peetre inequality
`(1 + |a + b|)^{-n} ≤ 2^n (1 + |a|)^{-n}` (`|b| ≤ 1`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The decay profile `(1 + |u|)^{-N}`. -/
def decayProfile (N : ℕ) (u : ℝ) : ℝ := (1 + |u|) ^ (-(N : ℝ))

/-- The product profile `∏_c (1 + |z_c|)^{-N}` on `ℝ⁴`. -/
def decayProduct (N : ℕ) (z : ParabolicSpace) : ℝ :=
  decayProfile N z.1 * ∏ i, decayProfile N (z.2 i)

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

theorem decayProfile_nonneg (N : ℕ) (u : ℝ) : 0 ≤ decayProfile N u :=
  Real.rpow_nonneg (by positivity) _

theorem decayProduct_nonneg (N : ℕ) (z : ParabolicSpace) : 0 ≤ decayProduct N z :=
  mul_nonneg (decayProfile_nonneg _ _) (Finset.prod_nonneg fun _ _ => decayProfile_nonneg _ _)

theorem measurable_decayProfile (N : ℕ) : Measurable (decayProfile N) :=
  (measurable_const.add continuous_abs.measurable).pow_const _

theorem measurable_decayProduct (N : ℕ) : Measurable (decayProduct N) :=
  ((measurable_decayProfile N).comp measurable_fst).mul (Finset.measurable_prod _ fun i _ =>
    (measurable_decayProfile N).comp ((measurable_pi_apply i).comp measurable_snd))

/-- Peetre's inequality: `(1 + |a + b|)^{-n} ≤ 2^n (1 + |a|)^{-n}` for `|b| ≤ 1`. -/
theorem decayProfile_add_le {a b : ℝ} (hb : |b| ≤ 1) (n : ℕ) :
    decayProfile n (a + b) ≤ 2 ^ n * decayProfile n a := by
  unfold decayProfile
  have h1 : 0 < 1 + |a + b| := by positivity
  have h2 : 0 < 1 + |a| := by positivity
  have hkey : 1 + |a| ≤ 2 * (1 + |a + b|) := by
    have : |a| ≤ |a + b| + |b| := by
      calc |a| = |(a + b) + (-b)| := by ring_nf
        _ ≤ |a + b| + |-b| := abs_add_le _ _
        _ = |a + b| + |b| := by rw [abs_neg]
    have := abs_nonneg (a + b)
    linarith
  have hp : (1 + |a|) ^ n ≤ 2 ^ n * (1 + |a + b|) ^ n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ h2.le hkey n
  rw [Real.rpow_neg h1.le, Real.rpow_neg h2.le, Real.rpow_natCast, Real.rpow_natCast]
  have h3 : 0 < (1 + |a + b|) ^ n := pow_pos h1 n
  have h4 : 0 < (1 + |a|) ^ n := pow_pos h2 n
  rw [← div_eq_mul_inv, le_div_iff₀ h4, inv_mul_le_iff₀ h3, mul_comm]
  exact hp

/-- A decay bound survives a shift by at most `1`. -/
theorem abs_le_of_decay_add {f : ℝ → ℝ} {C : ℝ} {n : ℕ}
    (hC : ∀ u, |f u| ≤ C * decayProfile n u) {a b : ℝ} (hb : |b| ≤ 1) :
    |f (a + b)| ≤ C * 2 ^ n * decayProfile n a := by
  have hC0 : 0 ≤ C := by
    have := (abs_nonneg _).trans (hC 0)
    simpa [decayProfile] using this
  calc |f (a + b)| ≤ C * decayProfile n (a + b) := hC _
    _ ≤ C * (2 ^ n * decayProfile n a) := mul_le_mul_of_nonneg_left (decayProfile_add_le hb n) hC0
    _ = _ := by ring

/-- One-dimensional increments: `|f(a + b) − f(a)| ≤ C 2^n (1 + |a|)^{-n} |b|` for `|b| ≤ 1`, if
`|f'| ≤ C (1 + |·|)^{-n}`. -/
theorem abs_sub_le_of_deriv_decay {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C : ℝ} {n : ℕ}
    (hC : ∀ u, |deriv f u| ≤ C * decayProfile n u) {a b : ℝ} (hb : |b| ≤ 1) :
    |f (a + b) - f a| ≤ C * 2 ^ n * decayProfile n a * |b| := by
  have hbound : ∀ u ∈ uIcc a (a + b), ‖deriv f u‖ ≤ C * 2 ^ n * decayProfile n a := by
    intro u hu
    have hu' : |u - a| ≤ 1 := (abs_sub_left_of_mem_uIcc hu).trans (by simpa using hb)
    have := abs_le_of_decay_add (a := a) hC hu'
    have e : a + (u - a) = u := by ring
    rw [e] at this
    rwa [Real.norm_eq_abs]
  have := Convex.norm_image_sub_le_of_norm_deriv_le (fun u _ => hf u) hbound (convex_uIcc a (a + b))
    left_mem_uIcc right_mem_uIcc
  simpa [Real.norm_eq_abs] using this

theorem abs_mul4_le {a b c d A B C D : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) : |a * b * c * d| ≤ A * B * C * D := by
  rw [abs_mul, abs_mul, abs_mul]
  have hA : 0 ≤ A := (abs_nonneg _).trans ha
  have hB : 0 ≤ B := (abs_nonneg _).trans hb
  have hC : 0 ≤ C := (abs_nonneg _).trans hc
  exact mul_le_mul (mul_le_mul (mul_le_mul ha hb (abs_nonneg _) hA) hc (abs_nonneg _)
    (mul_nonneg hA hB)) hd (abs_nonneg _) (mul_nonneg (mul_nonneg hA hB) hC)

/-- **Pointwise increments of `q_1`**: for `|v₀|, |vᵢ| ≤ 1`,
`|q_1(z + v) − q_1(z)| ≤ C (|v₀| + ∑ᵢ |vᵢ|) ∏_c (1 + |z_c|)^{-N}`. -/
theorem exists_abs_parabolicKernel_one_add_sub_le (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z v : ParabolicSpace, |v.1| ≤ 1 → (∀ i, |v.2 i| ≤ 1) →
      |parabolicKernel 1 (z + v) - parabolicKernel 1 z| ≤
        C * (|v.1| + ∑ i, |v.2 i|) * decayProduct N z := by
  obtain ⟨Cg, hCg⟩ := heatKernel1D_one_decay N
  obtain ⟨Cg', hCg'⟩ := deriv_heatKernel1D_one_decay N
  obtain ⟨Ck, hCk⟩ := quarticKernel_one_decay N
  obtain ⟨Ck', hCk'⟩ := deriv_quarticKernel_one_decay N
  set A : ℝ := 2 ^ N * max (max Cg Cg') (max Ck Ck') with hA
  have hCg0 : 0 ≤ Cg := (abs_nonneg _).trans ((hCg 0).trans (by simp))
  have hA0 : 0 ≤ A := mul_nonneg (by positivity) (hCg0.trans ((le_max_left _ _).trans
    (le_max_left _ _)))
  have hgv : ∀ a b, |b| ≤ 1 → |heatKernel1D 1 (a + b)| ≤ A * decayProfile N a := by
    intro a b hb
    refine (abs_le_of_decay_add (C := Cg) (fun u => hCg u) hb).trans ?_
    rw [hA, mul_comm (2 ^ N : ℝ)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_left _ _)) (by positivity)) (decayProfile_nonneg _ _)
  have hkv : ∀ a b, |b| ≤ 1 → |quarticKernel 1 (a + b)| ≤ A * decayProfile N a := by
    intro a b hb
    refine (abs_le_of_decay_add (C := Ck) (fun u => hCk u) hb).trans ?_
    rw [hA, mul_comm (2 ^ N : ℝ)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_right _ _)) (by positivity)) (decayProfile_nonneg _ _)
  have hgd : ∀ a b, |b| ≤ 1 →
      |heatKernel1D 1 (a + b) - heatKernel1D 1 a| ≤ A * decayProfile N a * |b| := by
    intro a b hb
    refine (abs_sub_le_of_deriv_decay differentiable_heatKernel1D_one (C := Cg')
      (fun u => hCg' u) hb).trans ?_
    rw [hA, mul_comm (2 ^ N : ℝ)]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_left _ _)) (by positivity)) (decayProfile_nonneg _ _))
      (abs_nonneg _)
  have hkd : ∀ a b, |b| ≤ 1 →
      |quarticKernel 1 (a + b) - quarticKernel 1 a| ≤ A * decayProfile N a * |b| := by
    intro a b hb
    refine (abs_sub_le_of_deriv_decay differentiable_quarticKernel_one (C := Ck')
      (fun u => hCk' u) hb).trans ?_
    rw [hA, mul_comm (2 ^ N : ℝ)]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_right _ _)) (by positivity)) (decayProfile_nonneg _ _))
      (abs_nonneg _)
  refine ⟨A ^ 4, by positivity, fun z v hv0 hvi => ?_⟩
  have h0 : ∀ a, |heatKernel1D 1 a| ≤ A * decayProfile N a := fun a => by
    simpa using hgv a 0 (by simp)
  have h0' : ∀ a, |quarticKernel 1 a| ≤ A * decayProfile N a := fun a => by
    simpa using hkv a 0 (by simp)
  set G1 := heatKernel1D 1 (z.1 + v.1)
  set G := heatKernel1D 1 z.1
  set K1 := quarticKernel 1 (z.2 0 + v.2 0)
  set K2 := quarticKernel 1 (z.2 1 + v.2 1)
  set K3 := quarticKernel 1 (z.2 2 + v.2 2)
  set L1 := quarticKernel 1 (z.2 0)
  set L2 := quarticKernel 1 (z.2 1)
  set L3 := quarticKernel 1 (z.2 2)
  set w0 := decayProfile N z.1
  set w1 := decayProfile N (z.2 0)
  set w2 := decayProfile N (z.2 1)
  set w3 := decayProfile N (z.2 2)
  have e1 : parabolicKernel 1 (z + v) = G1 * K1 * K2 * K3 := by
    simp only [parabolicKernel, Fin.prod_univ_three, Prod.fst_add, Prod.snd_add, Pi.add_apply,
      G1, K1, K2, K3]
    ring
  have e2 : parabolicKernel 1 z = G * L1 * L2 * L3 := by
    simp only [parabolicKernel, Fin.prod_univ_three, G, L1, L2, L3]
    ring
  have e3 : decayProduct N z = w0 * w1 * w2 * w3 := by
    simp only [decayProduct, Fin.prod_univ_three, w0, w1, w2, w3]
    ring
  have hsplit : G1 * K1 * K2 * K3 - G * L1 * L2 * L3 = (G1 - G) * K1 * K2 * K3 +
      G * (K1 - L1) * K2 * K3 + G * L1 * (K2 - L2) * K3 + G * L1 * L2 * (K3 - L3) := by ring
  rw [e1, e2, e3, hsplit, Fin.sum_univ_three]
  have t1 := abs_mul4_le (hgd z.1 v.1 hv0) (hkv (z.2 0) (v.2 0) (hvi 0))
    (hkv (z.2 1) (v.2 1) (hvi 1)) (hkv (z.2 2) (v.2 2) (hvi 2))
  have t2 := abs_mul4_le (h0 z.1) (hkd (z.2 0) (v.2 0) (hvi 0)) (hkv (z.2 1) (v.2 1) (hvi 1))
    (hkv (z.2 2) (v.2 2) (hvi 2))
  have t3 := abs_mul4_le (h0 z.1) (h0' (z.2 0)) (hkd (z.2 1) (v.2 1) (hvi 1))
    (hkv (z.2 2) (v.2 2) (hvi 2))
  have t4 := abs_mul4_le (h0 z.1) (h0' (z.2 0)) (h0' (z.2 1)) (hkd (z.2 2) (v.2 2) (hvi 2))
  calc |(G1 - G) * K1 * K2 * K3 + G * (K1 - L1) * K2 * K3 + G * L1 * (K2 - L2) * K3 +
        G * L1 * L2 * (K3 - L3)|
      ≤ |(G1 - G) * K1 * K2 * K3| + |G * (K1 - L1) * K2 * K3| + |G * L1 * (K2 - L2) * K3| +
          |G * L1 * L2 * (K3 - L3)| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ A * w0 * |v.1| * (A * w1) * (A * w2) * (A * w3) +
          A * w0 * (A * w1 * |v.2 0|) * (A * w2) * (A * w3) +
          A * w0 * (A * w1) * (A * w2 * |v.2 1|) * (A * w3) +
          A * w0 * (A * w1) * (A * w2) * (A * w3 * |v.2 2|) :=
        add_le_add (add_le_add (add_le_add t1 t2) t3) t4
    _ = A ^ 4 * (|v.1| + (|v.2 0| + |v.2 1| + |v.2 2|)) * (w0 * w1 * w2 * w3) := by ring

/-- One-dimensional integrability: `(1 + |u|)^{-N} |u|^p` is integrable for `p ≥ 0`,
`p + 1 < N`. -/
theorem integrable_decayProfile_mul_rpow {N : ℕ} {p : ℝ} (hp : 0 ≤ p) (hN : p + 1 < N) :
    Integrable (fun u : ℝ => decayProfile N u * |u| ^ p) := by
  have hint : Integrable (fun u : ℝ => (1 + ‖u‖) ^ (-((N : ℝ) - p))) :=
    integrable_one_add_norm (by simp; linarith)
  refine hint.mono' (((measurable_decayProfile N).mul
    (continuous_abs.measurable.pow_const p)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u => ?_)
  have h1 : 0 < 1 + |u| := by positivity
  rw [Real.norm_of_nonneg (mul_nonneg (decayProfile_nonneg _ _)
      (Real.rpow_nonneg (abs_nonneg _) _)),
    Real.norm_eq_abs, decayProfile]
  calc (1 + |u|) ^ (-(N : ℝ)) * |u| ^ p ≤ (1 + |u|) ^ (-(N : ℝ)) * (1 + |u|) ^ p :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) (by linarith) hp)
          (Real.rpow_nonneg h1.le _)
    _ = (1 + |u|) ^ (-((N : ℝ) - p)) := by
        rw [← Real.rpow_add h1]
        ring_nf

/-- The weighted product `(1 + |z₀|)^{-N} |z₀|^a ∏ᵢ (1 + |zᵢ|)^{-N} |zᵢ|^{eᵢ}` is integrable. -/
theorem integrable_decayWeight {N : ℕ} {a : ℝ} {e : Fin 3 → ℝ} (ha : 0 ≤ a) (haN : a + 1 < N)
    (he : ∀ i, 0 ≤ e i) (heN : ∀ i, e i + 1 < N) :
    Integrable (fun z : ParabolicSpace => (decayProfile N z.1 * |z.1| ^ a) *
      ∏ i, (decayProfile N (z.2 i) * |z.2 i| ^ e i)) := by
  have h1 := integrable_decayProfile_mul_rpow ha haN
  have h2 : Integrable (fun y : Fin 3 → ℝ => ∏ i, (decayProfile N (y i) * |y i| ^ e i)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun i b => decayProfile N b * |b| ^ e i)
      fun i => integrable_decayProfile_mul_rpow (he i) (heN i)
  rw [Measure.volume_eq_prod]
  exact h1.mul_prod h2

/-- `∏_c (1 + |z_c|)^{-N} ‖z‖_𝔰^r` is integrable for `r ≥ 0`, `r + 1 < N`. -/
theorem integrable_decayProduct_mul_rpow {N : ℕ} {r : ℝ} (hr : 0 ≤ r) (hN : r + 1 < N) :
    Integrable (fun z : ParabolicSpace => decayProduct N z * parabolicNorm z ^ r) := by
  have hs : ∀ j i : Fin 3, 0 ≤ (Pi.single j r : Fin 3 → ℝ) i := fun j i => by
    rw [Pi.single_apply]; split_ifs <;> simp [hr]
  have hsN : ∀ j i : Fin 3, (Pi.single j r : Fin 3 → ℝ) i + 1 < N := fun j i => by
    rw [Pi.single_apply]
    split_ifs
    · exact hN
    · linarith
  have hN1 : (0 : ℝ) + 1 < N := by linarith
  have i0 := integrable_decayWeight (N := N) (a := r / 2) (e := 0) (by positivity) (by linarith)
    (fun _ => le_rfl) (fun _ => by simpa using hN1)
  have ij := fun j : Fin 3 => integrable_decayWeight (N := N) (a := 0) (e := Pi.single j r)
    le_rfl hN1 (hs j) (hsN j)
  have hsum := ((((i0.add (ij 0)).add (ij 1)).add (ij 2)).const_mul ((4 : ℝ) ^ r))
  refine hsum.mono' (((measurable_decayProduct N).mul
    (continuous_parabolicNorm.measurable.pow_const r)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (decayProduct_nonneg _ _)
    (Real.rpow_nonneg (parabolicNorm_nonneg _) _))]
  have hb := parabolicNorm_rpow_le z hr
  have hd := decayProduct_nonneg N z
  refine (mul_le_mul_of_nonneg_left hb hd).trans (le_of_eq ?_)
  simp only [decayProduct, Fin.prod_univ_three, Pi.single_apply, Pi.zero_apply,
    Real.rpow_zero, mul_one, Pi.add_apply]
  simp
  ring

theorem parabolicDilate_add (c : ℝ) (z w : ParabolicSpace) :
    parabolicDilate c (z + w) = parabolicDilate c z + parabolicDilate c w := by
  simp only [parabolicDilate, Prod.fst_add, Prod.snd_add, smul_add, mul_add]
  rfl

/-- `|v₀| + ∑ᵢ |vᵢ| ≤ 2 ‖v‖_𝔰` when `‖v‖_𝔰 ≤ 1`. -/
theorem abs_fst_add_sum_le {v : ParabolicSpace} (hv : parabolicNorm v ≤ 1) :
    |v.1| + ∑ i, |v.2 i| ≤ 2 * parabolicNorm v := by
  have hs0 := Real.sqrt_nonneg |v.1|
  have hS0 : 0 ≤ ∑ i, |v.2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h1 : Real.sqrt |v.1| ≤ 1 := by
    unfold parabolicNorm at hv
    linarith
  have h2 : |v.1| ≤ Real.sqrt |v.1| := by
    have := mul_le_mul_of_nonneg_left h1 hs0
    rwa [Real.mul_self_sqrt (abs_nonneg _), mul_one] at this
  unfold parabolicNorm
  linarith

/-- **Increments of `q_1` in weighted `L¹`**: `∫ |q_1(z + v) − q_1(z)| ‖z‖^r dz ≤ K ‖v‖` for
`‖v‖_𝔰 ≤ 1`. -/
theorem exists_integral_abs_parabolicKernel_one_add_sub_le {r : ℝ} (hr : 0 ≤ r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : ParabolicSpace, parabolicNorm v ≤ 1 →
      ∫ z, |parabolicKernel 1 (z + v) - parabolicKernel 1 z| * parabolicNorm z ^ r ≤
        K * parabolicNorm v := by
  set N : ℕ := ⌈r⌉₊ + 2 with hNdef
  have hN : r + 1 < N := by
    have := Nat.le_ceil r
    rw [hNdef]
    push_cast
    linarith
  obtain ⟨C, hC0, hC⟩ := exists_abs_parabolicKernel_one_add_sub_le N
  have hint := integrable_decayProduct_mul_rpow hr hN
  set I := ∫ z, decayProduct N z * parabolicNorm z ^ r with hIdef
  have hI : 0 ≤ I := integral_nonneg fun z =>
    mul_nonneg (decayProduct_nonneg _ _) (Real.rpow_nonneg (parabolicNorm_nonneg _) _)
  refine ⟨2 * C * I, by positivity, fun v hv => ?_⟩
  have hv0 := abs_fst_le_one hv
  have hvi := abs_snd_le_one hv
  have hS : 0 ≤ |v.1| + ∑ i, |v.2 i| :=
    add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  calc ∫ z, |parabolicKernel 1 (z + v) - parabolicKernel 1 z| * parabolicNorm z ^ r
      ≤ ∫ z, C * (|v.1| + ∑ i, |v.2 i|) * (decayProduct N z * parabolicNorm z ^ r) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z =>
          mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (parabolicNorm_nonneg _) _))
          (hint.const_mul _) (Filter.Eventually.of_forall fun z => ?_)
        have := mul_le_mul_of_nonneg_right (hC z v hv0 hvi)
          (Real.rpow_nonneg (parabolicNorm_nonneg z) r)
        refine this.trans (le_of_eq ?_)
        ring
    _ = C * (|v.1| + ∑ i, |v.2 i|) * I := integral_const_mul _ _
    _ ≤ C * (2 * parabolicNorm v) * I := by
        gcongr
        exact abs_fst_add_sum_le hv
    _ = 2 * C * I * parabolicNorm v := by ring

/-- **Increments of `q_s` in weighted `L¹`** (exact scaling): for every `r ≥ 0` there is `K` with
`∫ |q_s(z + v) − q_s(z)| ‖z‖_𝔰^r dz ≤ K (s^{-1/4} ‖v‖_𝔰) s^{r/4}` whenever `‖v‖_𝔰 ≤ s^{1/4}`. -/
theorem exists_integral_abs_parabolicKernel_add_sub_le {r : ℝ} (hr : 0 ≤ r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ⦃s : ℝ⦄, 0 < s → ∀ v : ParabolicSpace,
      parabolicNorm v ≤ s ^ (1 / 4 : ℝ) →
      ∫ z, |parabolicKernel s (z + v) - parabolicKernel s z| * parabolicNorm z ^ r ≤
        K * (s ^ (-(1 / 4 : ℝ)) * parabolicNorm v) * s ^ (r / 4) := by
  obtain ⟨K, hK0, hK⟩ := exists_integral_abs_parabolicKernel_one_add_sub_le hr
  refine ⟨K, hK0, fun s hs v hv => ?_⟩
  set c := s ^ (-(1 / 4 : ℝ)) with hcdef
  have hc : 0 < c := Real.rpow_pos_of_pos hs _
  have hcs : s ^ (1 / 4 : ℝ) * c = 1 := by
    rw [hcdef, ← Real.rpow_add hs]
    norm_num
  have hc5 : (c ^ 5)⁻¹ = s ^ (5 / 4 : ℝ) := by
    rw [hcdef, ← Real.rpow_natCast, ← Real.rpow_mul hs.le, ← Real.rpow_neg hs.le]
    norm_num
  set v' := parabolicDilate c v with hv'
  have hNv' : parabolicNorm v' = c * parabolicNorm v := parabolicNorm_parabolicDilate hc.le v
  have hv'1 : parabolicNorm v' ≤ 1 := by
    rw [hNv', ← hcs, mul_comm (s ^ (1 / 4 : ℝ))]
    exact mul_le_mul_of_nonneg_left hv hc.le
  set F : ParabolicSpace → ℝ := fun w =>
    |parabolicKernel 1 (w + v') - parabolicKernel 1 w| * parabolicNorm w ^ r with hF
  have hpt : (fun z => |parabolicKernel s (z + v) - parabolicKernel s z| * parabolicNorm z ^ r) =
      fun z => (s ^ (-(5 / 4 : ℝ)) * s ^ (r / 4)) * F (parabolicDilate c z) := by
    funext z
    have hNz : parabolicNorm z = s ^ (1 / 4 : ℝ) * parabolicNorm (parabolicDilate c z) := by
      rw [parabolicNorm_parabolicDilate hc.le, ← mul_assoc, hcs, one_mul]
    rw [parabolicKernel_eq_scale hs (z + v), parabolicKernel_eq_scale hs z, ← hcdef,
      parabolicDilate_add, ← hv', ← mul_sub, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hs _),
      hNz, Real.mul_rpow (Real.rpow_nonneg hs.le _) (parabolicNorm_nonneg _),
      ← Real.rpow_mul hs.le, hF]
    have e : (1 / 4 : ℝ) * r = r / 4 := by ring
    rw [e]
    ring
  rw [hpt, integral_const_mul, integral_comp_parabolicDilate F hc, hc5]
  have h1 := hK v' hv'1
  rw [hNv'] at h1
  have hp : 0 ≤ s ^ (-(5 / 4 : ℝ)) * s ^ (r / 4) * s ^ (5 / 4 : ℝ) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hs.le _) (Real.rpow_nonneg hs.le _))
      (Real.rpow_nonneg hs.le _)
  have e2 : s ^ (-(5 / 4 : ℝ)) * s ^ (r / 4) * s ^ (5 / 4 : ℝ) = s ^ (r / 4) := by
    rw [mul_right_comm, ← Real.rpow_add hs]
    norm_num
  calc s ^ (-(5 / 4 : ℝ)) * s ^ (r / 4) * (s ^ (5 / 4 : ℝ) * ∫ w, F w)
      = (s ^ (-(5 / 4 : ℝ)) * s ^ (r / 4) * s ^ (5 / 4 : ℝ)) * ∫ w, F w := by ring
    _ ≤ (s ^ (-(5 / 4 : ℝ)) * s ^ (r / 4) * s ^ (5 / 4 : ℝ)) * (K * (c * parabolicNorm v)) :=
        mul_le_mul_of_nonneg_left h1 hp
    _ = K * (c * parabolicNorm v) * s ^ (r / 4) := by rw [e2]; ring

end RegularityStructures

end
