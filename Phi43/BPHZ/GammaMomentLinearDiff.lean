/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaMomentLinear
public import Phi43.BPHZ.GammaMomentDiffAll
public import Phi43.BPHZ.CrossMollifierPsi
public import Phi43.BPHZ.CrossMollifierDifference
import Mathlib.Tactic

/-!
# Two-scale differences of a kernel-tested copy of `Ψ` with a majorant kernel

For regularised noises `ξ` (mollifier `ρ`, scale `ε`) and `ξ'` (mollifier `ρ'`, scale `ε'`) of the
same white noise and a measurable integrable kernel `A` with `gammaMajorant A x y r M a p`:

* `gammaPsi_tested_sub_second_moment_le`:
  `E |∫ A (Ψ - Ψ')|² ≤ C M² (ε ∨ ε')^(2θ) r^a r^a` (`4 < p`-type constraints in the statement);
* `gammaPsi_tested_sub_integrable_pow_le`: all moments of `∫ A (Ψ - Ψ')`.

The covariance of `Ψ - Ψ'` is bounded by `(ε ∨ ε')^(2θ) s^(-1-2θ)`
(`hairerKernelDiffCovarianceTwo_abs_le`) and the principal pairing is
`gammaMajorant_lint_diag` with `e = 1 + 2θ`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem gld_pos_of_time {z : SpaceTime} (h : 1 < |z.1|) : 0 < torusParabolicSize z := by
  have h1 : 0 < √|z.1| := Real.sqrt_pos.2 (by linarith)
  unfold torusParabolicSize
  linarith [torusSpatialNorm_nonneg z.2]

/-- A kernel with a majorant vanishes outside the time slab (for `|y₀ - x₀| ≤ 1`). -/
theorem gammaMajorant_eq_zero_of_not_slab {A : SpaceTime → ℝ} {x y : SpaceTime} {r M a p : ℝ}
    (hA : gammaMajorant A x y r M a p) (hxy : |y.1 - x.1| ≤ 1) {w : SpaceTime}
    (hw : ¬ |w.1 - x.1| ≤ 2) : A w = 0 := by
  have h1 : 1 < |(y - w).1| := by
    simp only [Prod.fst_sub]
    have : |w.1 - x.1| ≤ |(y.1 - x.1)| + |y.1 - w.1| := by
      calc |w.1 - x.1| = |(y.1 - x.1) - (y.1 - w.1)| := by congr 1; ring
        _ ≤ _ := abs_sub _ _
    linarith [not_le.1 hw]
  have h2 : 1 < |(x - w).1| := by
    simp only [Prod.fst_sub]
    rw [abs_sub_comm]
    linarith [not_le.1 hw]
  have h := hA.2.2.2 w (gld_pos_of_time h1) (gld_pos_of_time h2)
  have hs : i2Psi2Slab x.1 w = 0 := by unfold i2Psi2Slab; simp [hw]
  rw [hs, zero_mul] at h
  exact abs_nonpos_iff.1 h

/-- A kernel with a majorant times a continuous function is integrable. -/
theorem integrable_mul_of_gammaMajorant {A : SpaceTime → ℝ} {x y : SpaceTime} {r M a p : ℝ}
    (hA : gammaMajorant A x y r M a p) (hAi : Integrable A) (hxy : |y.1 - x.1| ≤ 1)
    {F : SpaceTime → ℝ} (hF : Continuous F) : Integrable (fun w => A w * F w) :=
  integrable_mul_of_compact_support hAi
    (isCompact_Icc (a := x.1 - 2) (b := x.1 + 2) |>.prod (isCompact_univ (X := Torus3)))
    (fun w hw => by
      refine ⟨?_, Set.mem_univ _⟩
      by_contra hc
      apply hw
      refine gammaMajorant_eq_zero_of_not_slab hA hxy fun hle => hc ?_
      have := abs_le.1 hle
      exact ⟨by linarith, by linarith⟩) hF

private theorem gld_abs_flip_le {Rr : SpaceTime → ℝ} {C e : ℝ} (he : 0 ≤ e) (hC : 0 ≤ C)
    (h : ∀ x, 0 < torusParabolicSize x → |Rr x| ≤ C * torusParabolicSize x ^ (-e))
    {u v : SpaceTime} (hv : 0 < torusParabolicSize (v - u)) :
    |Rr (u - v)| ≤ (C * 2 ^ e) * torusParabolicSize (v - u) ^ (-e) := by
  have hpos : 0 < torusParabolicSize (u - v) := torusParabolicSize_pos_of_sub_pos hv
  have h1 := h (u - v) hpos
  have hn : -(u - v) = v - u := neg_sub u v
  have h2 := torusParabolicSize_rpow_neg_le_flip he (u := u - v) (by rw [hn]; exact hv)
  rw [hn] at h2
  calc |Rr (u - v)| ≤ C * torusParabolicSize (u - v) ^ (-e) := h1
    _ ≤ C * (2 ^ e * torusParabolicSize (v - u) ^ (-e)) := mul_le_mul_of_nonneg_left h2 hC
    _ = _ := by ring

/-- **Two-scale second moment of a majorant-kernel pairing of `Ψ`.** -/
theorem gammaPsi_tested_sub_second_moment_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ a p : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hp0 : 0 < p) (hp5 : p < 5) (hpe : 5 < p + (1 + 2 * θ)) (hpp : p + (p + (1 + 2 * θ) - 5) < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {A : SpaceTime → ℝ} {x y : SpaceTime} {r M : ℝ}, gammaMajorant A x y r M a p →
        Integrable A → |y.1 - x.1| ≤ 1 →
        ∫ ω, ((∫ w, A w * hairerPsiField N ξ ω w) - ∫ w, A w * hairerPsiField N ξ' ω w) ^ 2 ∂P ≤
          C * M * M * (max ε ε') ^ (2 * θ) * r ^ a * r ^ a := by
  obtain ⟨CD, hCD, hD⟩ := gammaMajorant_lint_diag (a := a) (a' := a) (p := p) (p' := p)
    (e := 1 + 2 * θ) hp0 hp5 (by linarith) (by linarith) hpe hp0 hpp
  obtain ⟨CQ, hCQ, hQ⟩ := hairerKernelDiffCovarianceTwo_abs_le N ρ ρ' hρ hρ' hθ hθ1
  have he : (0 : ℝ) ≤ 1 + 2 * θ := by linarith
  have h2e : (0 : ℝ) ≤ 2 ^ (1 + 2 * θ) := Real.rpow_nonneg (by norm_num) _
  refine ⟨CQ * 2 ^ (1 + 2 * θ) * CD, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' A x y r M hA hAi hxy
  have := hW.isProbabilityMeasure
  have hMx : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hcov := hairerPsiField_sub_integral_mulTwo N hρ hρ' hε.1 hε'.1 hW hξ hξ'
  have hlint := hD hA hA hxy hxy
  have hM := hA.2.1
  have hr := hA.1
  have key := gammaMoment_second_le_of_lintBound (P := P)
    (Y := fun ω u => hairerPsiField N ξ ω u - hairerPsiField N ξ' ω u)
    ((measurable_hairerPsiField_uncurry N hξ).sub (measurable_hairerPsiField_uncurry N hξ'))
    (fun u => (hairerPsiField_memLp N hρ hε.1 hW hξ u).sub
      (hairerPsiField_memLp N hρ' hε'.1 hW hξ' u))
    (M₀ := hairerKernelDiffCovarianceTwo N ρ ε ρ' ε' 0)
    (fun u => by rw [hcov u u, sub_self]) (R := hairerKernelDiffCovarianceTwo N ρ ε ρ' ε') hcov
    (p := 1 + 2 * θ) (A := CQ * (max ε ε') ^ (2 * θ) * 2 ^ (1 + 2 * θ))
    (mul_nonneg (mul_nonneg hCQ hMx) h2e)
    (fun u v hv => gld_abs_flip_le (Rr := hairerKernelDiffCovarianceTwo N ρ ε ρ' ε')
      (C := CQ * (max ε ε') ^ (2 * θ)) he (mul_nonneg hCQ hMx) (fun z hz => by
        have h0 := hQ hε.1 hε.2 hε'.1 hε'.2 z hz
        rw [show -1 - 2 * θ = -(1 + 2 * θ) by ring] at h0
        exact h0) hv)
    hA.2.2.1 hAi (M := CD * M * M * r ^ a * r ^ a)
    (by have := Real.rpow_nonneg hr a; positivity) (by simpa using hlint)
  have e : ∀ ω, |∫ w, (hairerPsiField N ξ ω w - hairerPsiField N ξ' ω w) * A w| ^ 2 =
      ((∫ w, A w * hairerPsiField N ξ ω w) - ∫ w, A w * hairerPsiField N ξ' ω w) ^ 2 := fun ω => by
    have hint : ∫ w, (hairerPsiField N ξ ω w - hairerPsiField N ξ' ω w) * A w =
        (∫ w, A w * hairerPsiField N ξ ω w) - ∫ w, A w * hairerPsiField N ξ' ω w := by
      rw [← integral_sub (integrable_mul_of_gammaMajorant hA hAi hxy
        (continuous_hairerPsiField N hξ.1 ω)) (integrable_mul_of_gammaMajorant hA hAi hxy
        (continuous_hairerPsiField N hξ'.1 ω))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp only
      ring
    rw [sq_abs, hint]
  simp only [e] at key
  refine key.trans (le_of_eq ?_)
  ring

end RegularityStructures.Phi43

end
