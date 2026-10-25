/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaMomentLinear
public import Phi43.BPHZ.GammaMomentTaylorKernel
import Mathlib.Tactic

/-!
# Second moments of the gradient increment `g_i` and of `v₁`

With `K♯ = hairerKernelTorus N`, `G_i = hairerKernelTorusGrad N i` and `Ψ = hairerPsiField`:

* `gammaGrad N ξ i x y = ∫ (G_i (y - w) - G_i (x - w)) Ψ(w) dw`, the increment of the spatial
  gradient of `K ∗ Ψ` (degree `1/2 - κ`);
* `gammaPsiTaylor N ξ x t a = ∫ (K♯(x + h - w) - K♯(x - w) - ∑ᵢ G_i(x - w) aᵢ) Ψ(w) dw`, `h = (t, proj a)`,
  the recentred convolution of `Ψ` minus its first-order spatial Taylor term (degree `3/2 - κ`).

For `δ ∈ (0, 1)`, uniformly in `ε ∈ (0, 1]`, the base point and the probability space:
`E g_i² ≤ C d^(1-δ)` for `d = s(y - x) ≤ 1` and `E v₁² ≤ C r^(3-δ)` for `r = ‖(t, a)‖_𝔰 ≤ 1/2`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- The increment of the spatial gradient of `K ∗ Ψ`, written through the gradient kernel. -/
def gammaGrad {Ω : Type*} (N : ℕ) (ξ : Ω → SpaceTime → ℝ) (i : Fin 3) (x y : SpaceTime)
    (ω : Ω) : ℝ :=
  ∫ w, hairerGradIncrementKernel N i x y w * hairerPsiField N ξ ω w

/-- The recentred convolution of `Ψ` minus its first-order spatial Taylor term. -/
def gammaPsiTaylor {Ω : Type*} (N : ℕ) (ξ : Ω → SpaceTime → ℝ) (x : SpaceTime) (t : ℝ)
    (a : Fin 3 → ℝ) (ω : Ω) : ℝ :=
  ∫ w, hairerTaylorKernel N x t a w * hairerPsiField N ξ ω w

end RegularityStructures.Phi43

end

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem gmg_rpow_mul_self {r e : ℝ} (hr : 0 ≤ r) (he : 0 < e) :
    r ^ e * r ^ e = r ^ (2 * e) := by
  rw [← Real.rpow_add' hr (by linarith)]
  congr 1
  ring

/-- **Second moment of the gradient increment.**  For `δ ∈ (0, 1)`,
`E g_i(x, y)² ≤ C s(y - x)^(1-δ)` whenever `s(y - x) ≤ 1`, uniformly in `ε ∈ (0, 1]`. -/
theorem gammaGrad_second_moment_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    (i : Fin 3) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : SpaceTime, torusParabolicSize (y - x) ≤ 1 →
        ∫ ω, gammaGrad N ξ i x y ω ^ 2 ∂P ≤ C * torusParabolicSize (y - x) ^ (1 - δ) := by
  set γ : ℝ := (1 - δ) / 2 with hγ
  obtain ⟨M, hM, hMaj⟩ := gammaMajorant_hairerGradIncrement N i (γ := γ) (by rw [hγ]; linarith)
    (by rw [hγ]; linarith)
  obtain ⟨C0, hC0, hC⟩ := gammaPsi_tested_second_moment_le.{u} N hρ (a := γ) (p := 4 + γ)
    (by rw [hγ]; linarith) (by rw [hγ]; linarith) (by rw [hγ]; linarith)
  refine ⟨C0 * M * M, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y hd
  have hxy : |y.1 - x.1| ≤ 1 := gammaMoment_abs_time_le_one hd rfl
  have h := hC hW hε hξ (hMaj hxy) (integrable_hairerGradIncrementKernel N i x y) hxy
  have e : ∀ ω, gammaGrad N ξ i x y ω ^ 2 =
      (∫ w, hairerGradIncrementKernel N i x y w * hairerPsiField N ξ ω w) ^ 2 := fun ω => rfl
  simp only [e]
  refine h.trans (le_of_eq ?_)
  have hq := gmg_rpow_mul_self (torusParabolicSize_nonneg (y - x)) (e := γ) (by rw [hγ]; linarith)
  have e2 : 2 * γ = 1 - δ := by rw [hγ]; ring
  rw [e2] at hq
  calc C0 * M * M * torusParabolicSize (y - x) ^ γ * torusParabolicSize (y - x) ^ γ
      = C0 * M * M * (torusParabolicSize (y - x) ^ γ * torusParabolicSize (y - x) ^ γ) := by ring
    _ = _ := by rw [hq]

/-- **Second moment of `v₁`.**  For `δ ∈ (0, 1)`, `E v₁(x, t, a)² ≤ C ‖(t, a)‖^(3-δ)` whenever
`‖(t, a)‖_𝔰 ≤ 1/2`, uniformly in `ε ∈ (0, 1]`. -/
theorem gammaPsiTaylor_second_moment_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ (x : SpaceTime) (t : ℝ) (a : Fin 3 → ℝ), parabolicNorm (t, a) ≤ 1 / 2 →
        ∫ ω, gammaPsiTaylor N ξ x t a ω ^ 2 ∂P ≤ C * parabolicNorm (t, a) ^ (3 - δ) := by
  set θ : ℝ := (1 - δ) / 2 with hθ
  obtain ⟨M, hM, hMaj⟩ := gammaMajorant_hairerTaylorKernel N (θ := θ) (by rw [hθ]; linarith)
    (by rw [hθ]; linarith)
  obtain ⟨C0, hC0, hC⟩ := gammaPsi_tested_second_moment_le.{u} N hρ (a := 1 + θ) (p := 4 + θ)
    (by rw [hθ]; linarith) (by rw [hθ]; linarith) (by rw [hθ]; linarith)
  refine ⟨C0 * M * M, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x t a hn
  have hai : ∀ i, |a i| ≤ 1 / 2 := fun i => by
    refine (Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)).trans ?_
    simp only [parabolicNorm] at hn
    linarith [Real.sqrt_nonneg |t|]
  have ht : |t| ≤ 1 := by
    have h1 : √|t| ≤ 1 / 2 := by
      simp only [parabolicNorm] at hn
      linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => abs_nonneg (a i)]
    have h2 : |t| ≤ (1 / 2) ^ 2 := by
      rw [← Real.sqrt_le_left (by norm_num)]; exact h1
    linarith
  have hxy : |(x + (t, torusProj a)).1 - x.1| ≤ 1 := by simpa using ht
  have h := hC hW hε hξ (hMaj hai ht) (integrable_hairerTaylorKernel N x t a) hxy
  have e : ∀ ω, gammaPsiTaylor N ξ x t a ω ^ 2 =
      (∫ w, hairerTaylorKernel N x t a w * hairerPsiField N ξ ω w) ^ 2 := fun ω => rfl
  simp only [e]
  refine h.trans (le_of_eq ?_)
  have hq := gmg_rpow_mul_self (parabolicNorm_nonneg (t, a)) (e := 1 + θ) (by rw [hθ]; linarith)
  have e2 : 2 * (1 + θ) = 3 - δ := by rw [hθ]; ring
  rw [e2] at hq
  calc C0 * M * M * parabolicNorm (t, a) ^ (1 + θ) * parabolicNorm (t, a) ^ (1 + θ)
      = C0 * M * M * (parabolicNorm (t, a) ^ (1 + θ) * parabolicNorm (t, a) ^ (1 + θ)) := by ring
    _ = _ := by rw [hq]

end RegularityStructures.Phi43

end
