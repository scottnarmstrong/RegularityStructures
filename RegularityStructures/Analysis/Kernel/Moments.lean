/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.Parabolic
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Moment bounds for the parabolic kernel

For `t > 0` and `r ≥ 0`, `∫ |q_t(w)| ‖w‖_𝔰^r dw ≤ M_r t^{r/4}`, with the explicit constant
`M_r = 4^r (G_{r/2} K_0³ + 3 G_0 K_r K_0²)` where `G_s = ∫ |g_1(a)| |a|^s da` and
`K_s = ∫ |k_1(b)| |b|^s db`. The proof bounds `‖w‖_𝔰^r ≤ 4^r (|w₀|^{r/2} + ∑ᵢ |wᵢ|^r)` and evaluates
the resulting product integrals by Fubini (`RegularityStructures.Analysis.Kernel.Parabolic`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The moment constant `M_r = 4^r (G_{r/2} K_0³ + 3 G_0 K_r K_0²)` of the parabolic kernel. -/
def parabolicMomentConst (r : ℝ) : ℝ :=
  (4 : ℝ) ^ r * (heatMoment (r / 2) * quarticMoment 0 ^ 3 +
    3 * (heatMoment 0 * quarticMoment r * quarticMoment 0 ^ 2))

/-- The sum of the four weights bounding `|q_t(z)| ‖z‖^r`. -/
def parabolicMomentBound (t r : ℝ) (z : ParabolicSpace) : ℝ :=
  (4 : ℝ) ^ r * (parabolicKernelWeight t (r / 2) 0 z + parabolicKernelWeight t 0 (Pi.single 0 r) z +
    parabolicKernelWeight t 0 (Pi.single 1 r) z + parabolicKernelWeight t 0 (Pi.single 2 r) z)

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem parabolicMomentConst_nonneg (r : ℝ) : 0 ≤ parabolicMomentConst r := by
  have := heatMoment_nonneg (r / 2)
  have := heatMoment_nonneg 0
  have := quarticMoment_nonneg r
  have := quarticMoment_nonneg 0
  unfold parabolicMomentConst
  refine mul_nonneg (Real.rpow_nonneg (by norm_num) _) (add_nonneg ?_ ?_)
  · exact mul_nonneg (heatMoment_nonneg _) (pow_nonneg (quarticMoment_nonneg 0) 3)
  · exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (heatMoment_nonneg 0)
      (quarticMoment_nonneg r)) (pow_nonneg (quarticMoment_nonneg 0) 2))

/-- `(x₀ + x₁ + x₂ + x₃)^r ≤ 4^r (x₀^r + x₁^r + x₂^r + x₃^r)` for nonnegative `xᵢ`, `r ≥ 0`. -/
theorem add_four_rpow_le {x₀ x₁ x₂ x₃ : ℝ} (h₀ : 0 ≤ x₀) (h₁ : 0 ≤ x₁) (h₂ : 0 ≤ x₂)
    (h₃ : 0 ≤ x₃) {r : ℝ} (hr : 0 ≤ r) :
    (x₀ + x₁ + x₂ + x₃) ^ r ≤ (4 : ℝ) ^ r * (x₀ ^ r + x₁ ^ r + x₂ ^ r + x₃ ^ r) := by
  set M := max (max x₀ x₁) (max x₂ x₃) with hM
  have hsum : x₀ + x₁ + x₂ + x₃ ≤ 4 * M := by
    have : x₀ ≤ M := (le_max_left _ _).trans (le_max_left _ _)
    have : x₁ ≤ M := (le_max_right _ _).trans (le_max_left _ _)
    have : x₂ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    have : x₃ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
    linarith
  have hM0 : 0 ≤ M := h₀.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hMr : M ^ r ≤ x₀ ^ r + x₁ ^ r + x₂ ^ r + x₃ ^ r := by
    have p₀ := Real.rpow_nonneg h₀ r
    have p₁ := Real.rpow_nonneg h₁ r
    have p₂ := Real.rpow_nonneg h₂ r
    have p₃ := Real.rpow_nonneg h₃ r
    have hc : M = x₀ ∨ M = x₁ ∨ M = x₂ ∨ M = x₃ := by
      rcases max_choice (max x₀ x₁) (max x₂ x₃) with h | h
      · rcases max_choice x₀ x₁ with h1 | h1
        · left; rw [hM, h, h1]
        · right; left; rw [hM, h, h1]
      · rcases max_choice x₂ x₃ with h2 | h2
        · right; right; left; rw [hM, h, h2]
        · right; right; right; rw [hM, h, h2]
    rcases hc with e | e | e | e <;> rw [e] <;> linarith
  calc (x₀ + x₁ + x₂ + x₃) ^ r ≤ (4 * M) ^ r :=
        Real.rpow_le_rpow (by positivity) hsum hr
    _ = (4 : ℝ) ^ r * M ^ r := Real.mul_rpow (by norm_num) hM0
    _ ≤ _ := by gcongr

/-- `‖z‖_𝔰^r ≤ 4^r (|z₀|^{r/2} + ∑ᵢ |zᵢ|^r)`. -/
theorem parabolicNorm_rpow_le (z : ParabolicSpace) {r : ℝ} (hr : 0 ≤ r) :
    parabolicNorm z ^ r ≤ (4 : ℝ) ^ r *
      (|z.1| ^ (r / 2) + |z.2 0| ^ r + |z.2 1| ^ r + |z.2 2| ^ r) := by
  have h := add_four_rpow_le (Real.sqrt_nonneg |z.1|) (abs_nonneg (z.2 0)) (abs_nonneg (z.2 1))
    (abs_nonneg (z.2 2)) hr
  have e : parabolicNorm z = Real.sqrt |z.1| + |z.2 0| + |z.2 1| + |z.2 2| := by
    unfold parabolicNorm
    rw [Fin.sum_univ_three]
    ring
  rw [e]
  have hs : Real.sqrt |z.1| ^ r = |z.1| ^ (r / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    ring
  rwa [hs] at h

theorem abs_parabolicKernel_mul_le (t : ℝ) {r : ℝ} (hr : 0 ≤ r) (z : ParabolicSpace) :
    |parabolicKernel t z| * parabolicNorm z ^ r ≤ parabolicMomentBound t r z := by
  have hP : 0 ≤ |heatKernel1D t z.1| * |quarticKernel t (z.2 0)| * |quarticKernel t (z.2 1)| *
      |quarticKernel t (z.2 2)| := by positivity
  have h := mul_le_mul_of_nonneg_left (parabolicNorm_rpow_le z hr) hP
  have e1 : |parabolicKernel t z| = |heatKernel1D t z.1| * |quarticKernel t (z.2 0)| *
      |quarticKernel t (z.2 1)| * |quarticKernel t (z.2 2)| := by
    unfold parabolicKernel
    rw [abs_mul, Finset.abs_prod, Fin.prod_univ_three]
    ring
  rw [e1]
  refine h.trans (le_of_eq ?_)
  simp only [parabolicMomentBound, parabolicKernelWeight, Fin.prod_univ_three, Pi.single_apply,
    Pi.zero_apply, Real.rpow_zero, mul_one]
  simp
  ring

theorem integrable_parabolicMomentBound {t : ℝ} (ht : 0 < t) {r : ℝ} (hr : 0 ≤ r) :
    Integrable (parabolicMomentBound t r) := by
  have hs : ∀ i : Fin 3, ∀ k : Fin 3, 0 ≤ (Pi.single i r : Fin 3 → ℝ) k := fun i k => by
    rw [Pi.single_apply]
    split_ifs <;> simp [hr]
  have h0 := integrable_parabolicKernelWeight ht (by positivity : 0 ≤ r / 2) (e := 0)
    (fun _ => le_rfl)
  have h1 := fun i : Fin 3 => integrable_parabolicKernelWeight ht le_rfl (hs i)
  exact (((h0.add (h1 0)).add (h1 1)).add (h1 2)).const_mul _

theorem integral_parabolicMomentBound {t : ℝ} (ht : 0 < t) {r : ℝ} (hr : 0 ≤ r) :
    ∫ z, parabolicMomentBound t r z = parabolicMomentConst r * t ^ (r / 4) := by
  have hs : ∀ i : Fin 3, ∀ k : Fin 3, 0 ≤ (Pi.single i r : Fin 3 → ℝ) k := fun i k => by
    rw [Pi.single_apply]
    split_ifs <;> simp [hr]
  have h0 := integrable_parabolicKernelWeight ht (by positivity : 0 ≤ r / 2) (e := 0)
    (fun _ => le_rfl)
  have h1 := fun i : Fin 3 => integrable_parabolicKernelWeight ht le_rfl (hs i)
  have a1 : Integrable (fun z => parabolicKernelWeight t (r / 2) 0 z +
      parabolicKernelWeight t 0 (Pi.single 0 r) z) := h0.add (h1 0)
  have a2 : Integrable (fun z => parabolicKernelWeight t (r / 2) 0 z +
      parabolicKernelWeight t 0 (Pi.single 0 r) z + parabolicKernelWeight t 0 (Pi.single 1 r) z) :=
    a1.add (h1 1)
  unfold parabolicMomentBound
  rw [integral_const_mul, integral_add a2 (h1 2), integral_add a1 (h1 1), integral_add h0 (h1 0)]
  simp only [integral_parabolicWeight ht, Fin.prod_univ_three, Pi.single_apply, Pi.zero_apply,
    parabolicMomentConst]
  rw [show r / 2 / 2 = r / 4 by ring]
  simp
  ring

end RegularityStructures

end
