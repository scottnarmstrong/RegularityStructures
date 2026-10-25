/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaMomentLinearDiff
public import Phi43.BPHZ.GammaMomentGradLq
import Mathlib.Tactic

/-!
# Two-scale differences of `g_i` and `v₁`

For regularised noises `ξ` (mollifier `ρ`, scale `ε`), `ξ'` (mollifier `ρ'`, scale `ε'`) of the same
white noise, `θ, δ > 0` with `2θ + δ ≤ 1`, uniformly in the base point and the probability space:

* `gammaGrad_sub_second_moment_le`:
  `E (g_i^ε - g_i^ε')² ≤ C (ε ∨ ε')^(2θ) d^(1 - 2θ - δ)`, `d = s(y - x) ≤ 1`;
* `gammaPsiTaylor_sub_second_moment_le`:
  `E (v₁^ε - v₁^ε')² ≤ C (ε ∨ ε')^(2θ) r^(3 - 2θ - δ)`, `r = ‖(t, a)‖_𝔰 ≤ 1/2`;

and the corresponding all-moment (`gammaPsi_tested_sub_integrable_pow_le`), Kolmogorov
(`*_sub_lintegral_enorm_pow_le`) and homogeneity (`*_sub_lintegral_enorm_pow_le_kappa`) forms.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem gdf_rpow_mul_self {r e : ℝ} (hr : 0 ≤ r) (he : 0 ≤ e) :
    r ^ e * r ^ e = r ^ (2 * e) := by
  rcases he.lt_or_eq with h | h
  · rw [← Real.rpow_add' hr (by linarith)]
    congr 1
    ring
  · subst h
    simp

/-- **All moments of a two-scale difference of kernel-tested copies of `Ψ`.** -/
theorem gammaPsi_tested_sub_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ}
      {ξ ξ' : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsMollifier ρ' → IsWhiteNoise P W →
      0 < ε → 0 < ε' → IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {g : SpaceTime → ℝ} {x y : SpaceTime} {r M a q : ℝ}, gammaMajorant g x y r M a q →
        Integrable g → |y.1 - x.1| ≤ 1 →
        Integrable (fun ω => ((∫ w, g w * hairerPsiField N ξ ω w) -
          ∫ w, g w * hairerPsiField N ξ' ω w) ^ (2 * p)) P ∧
        ∫ ω, ((∫ w, g w * hairerPsiField N ξ ω w) -
          ∫ w, g w * hairerPsiField N ξ' ω w) ^ (2 * p) ∂P ≤
          A * (∫ ω, ((∫ w, g w * hairerPsiField N ξ ω w) -
            ∫ w, g w * hairerPsiField N ξ' ω w) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ := integrable_and_integral_pow_two_mul_le_of_polyIntegral_sub.{u} 1 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ρ' ε ε' ξ ξ'} N hρ hρ' hW hε hε' hξ hξ' {g x y r M a q}
    hg hgi hxy => ?_⟩
  have hS : IsCompact (Set.Icc (x.1 - 2) (x.1 + 2) ×ˢ (Set.univ : Set Torus3)) :=
    isCompact_Icc.prod isCompact_univ
  have h := hA hW (continuous_hairerPsiField N hξ.1) (continuous_hairerPsiField N hξ'.1)
    (measurable_hairerPsiField_apply N hξ) (measurable_hairerPsiField_apply N hξ')
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (exists_hairerPsiField_pairing N hρ' hε' hW hξ')
    (V := max (hairerCovariance N ρ ε 0) (hairerCovariance N ρ' ε' 0))
    (fun z => (integral_hairerPsiField_sq_le N hρ hε hW hξ z).trans (le_max_left _ _))
    (fun z => (integral_hairerPsiField_sq_le N hρ' hε' hW hξ' z).trans (le_max_right _ _))
    hS ⟨(x.1, 0), ⟨by linarith, by linarith⟩, Set.mem_univ _⟩ hg.2.2.1 hgi
    (fun w hw => by
      refine ⟨?_, Set.mem_univ _⟩
      by_contra hc
      apply hw
      refine gammaMajorant_eq_zero_of_not_slab hg hxy fun hle => hc ?_
      have := abs_le.1 hle
      exact ⟨by linarith, by linarith⟩)
    Polynomial.X Polynomial.X (by simp) (by simp)
  have e : ∀ (ξ₀ : Ω → SpaceTime → ℝ) (ω : Ω), (∫ w, g w * hairerPsiField N ξ₀ ω w) =
      ∫ w, Polynomial.X.eval (hairerPsiField N ξ₀ ω w) * g w := fun ξ₀ ω => by
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp [mul_comm]
  simp only [e]
  exact h

/-- **Two-scale second moment of `g_i`.** -/
theorem gammaGrad_sub_second_moment_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (i : Fin 3) {θ δ : ℝ} (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hδ : 0 < δ) (hθδ : 2 * θ + δ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : SpaceTime, torusParabolicSize (y - x) ≤ 1 →
        ∫ ω, (gammaGrad N ξ i x y ω - gammaGrad N ξ' i x y ω) ^ 2 ∂P ≤
          C * (max ε ε') ^ (2 * θ) * torusParabolicSize (y - x) ^ (1 - 2 * θ - δ) := by
  set γ : ℝ := (1 - 2 * θ - δ) / 2 with hγ
  obtain ⟨M, hM, hMaj⟩ := gammaMajorant_hairerGradIncrement N i (γ := γ) (by rw [hγ]; linarith)
    (by rw [hγ]; linarith)
  obtain ⟨C0, hC0, hC⟩ := gammaPsi_tested_sub_second_moment_le.{u} N hρ hρ' (a := γ) (p := 4 + γ)
    hθ hθ1 (by rw [hγ]; linarith) (by rw [hγ]; linarith) (by rw [hγ]; linarith)
    (by rw [hγ]; linarith)
  refine ⟨C0 * M * M, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y hd
  have hxy : |y.1 - x.1| ≤ 1 := gammaMoment_abs_time_le_one hd rfl
  have h := hC hW hε hε' hξ hξ' (hMaj hxy) (integrable_hairerGradIncrementKernel N i x y) hxy
  refine h.trans (le_of_eq ?_)
  have hq := gdf_rpow_mul_self (torusParabolicSize_nonneg (y - x)) (e := γ) (by rw [hγ]; linarith)
  have e2 : 2 * γ = 1 - 2 * θ - δ := by rw [hγ]; ring
  rw [e2] at hq
  calc C0 * M * M * (max ε ε') ^ (2 * θ) * torusParabolicSize (y - x) ^ γ *
        torusParabolicSize (y - x) ^ γ
      = C0 * M * M * (max ε ε') ^ (2 * θ) *
        (torusParabolicSize (y - x) ^ γ * torusParabolicSize (y - x) ^ γ) := by ring
    _ = _ := by rw [hq]

/-- **Two-scale second moment of `v₁`.** -/
theorem gammaPsiTaylor_sub_second_moment_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hδ : 0 < δ) (hθδ : 2 * θ + δ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ (x : SpaceTime) (t : ℝ) (a : Fin 3 → ℝ), parabolicNorm (t, a) ≤ 1 / 2 →
        ∫ ω, (gammaPsiTaylor N ξ x t a ω - gammaPsiTaylor N ξ' x t a ω) ^ 2 ∂P ≤
          C * (max ε ε') ^ (2 * θ) * parabolicNorm (t, a) ^ (3 - 2 * θ - δ) := by
  set γ : ℝ := (1 - 2 * θ - δ) / 2 with hγ
  obtain ⟨M, hM, hMaj⟩ := gammaMajorant_hairerTaylorKernel N (θ := γ) (by rw [hγ]; linarith)
    (by rw [hγ]; linarith)
  obtain ⟨C0, hC0, hC⟩ := gammaPsi_tested_sub_second_moment_le.{u} N hρ hρ' (a := 1 + γ)
    (p := 4 + γ) hθ hθ1 (by rw [hγ]; linarith) (by rw [hγ]; linarith) (by rw [hγ]; linarith)
    (by rw [hγ]; linarith)
  refine ⟨C0 * M * M, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x t a hn
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
  have h := hC hW hε hε' hξ hξ' (hMaj hai ht) (integrable_hairerTaylorKernel N x t a) hxy
  refine h.trans (le_of_eq ?_)
  have hq := gdf_rpow_mul_self (parabolicNorm_nonneg (t, a)) (e := 1 + γ) (by rw [hγ]; linarith)
  have e2 : 2 * (1 + γ) = 3 - 2 * θ - δ := by rw [hγ]; ring
  rw [e2] at hq
  calc C0 * M * M * (max ε ε') ^ (2 * θ) * parabolicNorm (t, a) ^ (1 + γ) *
        parabolicNorm (t, a) ^ (1 + γ)
      = C0 * M * M * (max ε ε') ^ (2 * θ) *
        (parabolicNorm (t, a) ^ (1 + γ) * parabolicNorm (t, a) ^ (1 + γ)) := by ring
    _ = _ := by rw [hq]

end RegularityStructures.Phi43

end
