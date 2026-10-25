/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.GeneratorDeriv
public import RegularityStructures.Analysis.Kernel.TimeDeriv

/-!
# The heat equation for the parabolic kernel

`kernelDerivs t a b₀ b₁ b₂ (s, x) = g_t^{(a)}(s) k_t^{(b₀)}(x₀) k_t^{(b₁)}(x₁) k_t^{(b₂)}(x₂)`
are the partial derivatives of `parabolicKernel t = kernelDerivs t 0 0 0 0`. We show that
differentiating along `timeDir` raises `a`, and along `spaceDir i` raises `bᵢ`, and deduce the
pointwise heat equation `∂_t q_t = L q_t`, `L = (4π²)⁻¹ ∂₀² - (16π⁴)⁻¹ ∑ᵢ ∂ᵢ⁴`
(`parabolicTimeDeriv_eq`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The directional derivative `D_d f = x ↦ f'(x) d`. -/
def dirDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (d : E) (f : E → ℝ) : E → ℝ :=
  fun x => fderiv ℝ f x d

/-- Partial derivatives of the parabolic kernel. -/
def kernelDerivs (t : ℝ) (a b₀ b₁ b₂ : ℕ) (w : ParabolicSpace) : ℝ :=
  iteratedDeriv a (symKernel 1 t) w.1 *
    (iteratedDeriv b₀ (symKernel 2 t) (w.2 0) * iteratedDeriv b₁ (symKernel 2 t) (w.2 1) *
      iteratedDeriv b₂ (symKernel 2 t) (w.2 2))

end RegularityStructures

end

public section

open scoped ContDiff

namespace RegularityStructures

theorem parabolicKernel_eq_kernelDerivs (t : ℝ) :
    parabolicKernel t = kernelDerivs t 0 0 0 0 := by
  funext w
  simp [parabolicKernel, kernelDerivs, Fin.prod_univ_three, heatKernel1D, quarticKernel]

theorem contDiff_iteratedDeriv_symKernel {t : ℝ} (ht : 0 < t) {j : ℕ} (hj : 0 < j) (a : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv a (symKernel j t)) := by
  rw [iteratedDeriv_eq_iterate]
  exact (contDiff_symKernel ht hj).iterate_deriv a

theorem hasDerivAt_iteratedDeriv_symKernel {t : ℝ} (ht : 0 < t) {j : ℕ} (hj : 0 < j) (a : ℕ)
    (x : ℝ) : HasDerivAt (iteratedDeriv a (symKernel j t)) (iteratedDeriv (a + 1) (symKernel j t) x)
      x := by
  have h := ((contDiff_iteratedDeriv_symKernel ht hj a).differentiable (by simp) x).hasDerivAt
  rwa [← iteratedDeriv_succ] at h

theorem contDiff_kernelDerivs {t : ℝ} (ht : 0 < t) (a b₀ b₁ b₂ : ℕ) :
    ContDiff ℝ ∞ (kernelDerivs t a b₀ b₁ b₂) := by
  have h1 : ContDiff ℝ ∞ fun w : ParabolicSpace => iteratedDeriv a (symKernel 1 t) w.1 :=
    (contDiff_iteratedDeriv_symKernel ht one_pos a).comp
      (contDiff_fst (E := ℝ) (F := Fin 3 → ℝ))
  have h2 : ∀ (b : ℕ) (i : Fin 3), ContDiff ℝ ∞ fun w : ParabolicSpace =>
      iteratedDeriv b (symKernel 2 t) (w.2 i) := fun b i =>
    (contDiff_iteratedDeriv_symKernel ht two_pos b).comp
      ((contDiff_apply ℝ ℝ i).comp (contDiff_snd (E := ℝ) (F := Fin 3 → ℝ)))
  exact h1.mul (((h2 b₀ 0).mul (h2 b₁ 1)).mul (h2 b₂ 2))

theorem contDiff_parabolicKernel {t : ℝ} (ht : 0 < t) : ContDiff ℝ ∞ (parabolicKernel t) := by
  rw [parabolicKernel_eq_kernelDerivs]
  exact contDiff_kernelDerivs ht 0 0 0 0

theorem dirDeriv_eq_deriv_line {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (d w : ParabolicSpace) :
    dirDeriv d f w = deriv (fun s : ℝ => f (w + s • d)) 0 := by
  have hd : DifferentiableAt ℝ f w := (hf.differentiable (by simp)) w
  have := hd.lineDeriv_eq_fderiv (v := d)
  rw [dirDeriv, ← this, lineDeriv]

end RegularityStructures

end
