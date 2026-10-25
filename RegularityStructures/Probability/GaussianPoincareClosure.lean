/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.GaussianPolynomialAlgebra
public import RegularityStructures.Probability.GaussianSteinSolutionGrowth

/-!
# The one-dimensional Gaussian Poincare theorem under polynomial growth

The explicit Stein proof is closed here: the datum, Stein solution, derivative identities, and
every boundary term are supplied with explicit polynomial bounds and then integrated by the
Gaussian moment lemmas.  This is the one-dimensional input for product tensorisation.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace RegularityStructures

theorem gaussian_poincare_one_dimensional_of_polynomial_growth {f : ℝ → ℝ}
    (hcont_f : ContDiff ℝ 1 f)
    (hgrowth_f : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ N) :
    Var[(fun x => f x); gaussianReal 0 1] ≤
      ∫ x, (fderiv ℝ f x 1) ^ 2 ∂(gaussianReal 0 1) := by
  rcases hgrowth_f with ⟨C, N, hC, hgrowth_f⟩
  let m : ℝ := ∫ y, f y ∂(gaussianReal 0 1)
  let g : ℝ → ℝ := fun x => f x - m
  let q : ℝ → ℝ := fun x => (f x - m) * gaussianPDFReal 0 1 x
  let u : ℝ → ℝ := gaussianSteinSolution f m
  have hf_bound : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ, |f x| ≤ C * (1 + |x|) ^ N := by
    refine ⟨C, N, hC, ?_⟩
    intro x
    have h : |f x| ≤ |f x| + ‖fderiv ℝ f x‖ :=
      le_add_of_nonneg_right (norm_nonneg (fderiv ℝ f x))
    simpa [Real.norm_eq_abs] using h.trans (hgrowth_f x)
  have hfp_bound : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ, |fderiv ℝ f x 1| ≤ C * (1 + |x|) ^ N := by
    refine ⟨C, N, hC, ?_⟩
    intro x
    have happly := ContinuousLinearMap.le_opNorm (fderiv ℝ f x) (1 : ℝ)
    have hderiv : ‖fderiv ℝ f x 1‖ ≤ ‖fderiv ℝ f x‖ := by
      simpa using happly
    have hsum : ‖fderiv ℝ f x‖ ≤ |f x| + ‖fderiv ℝ f x‖ :=
      le_add_of_nonneg_left (abs_nonneg (f x))
    have hfinal := hderiv.trans (hsum.trans (hgrowth_f x))
    simpa [Real.norm_eq_abs] using hfinal
  have hdatum := gaussianStein_datum_polynomial_weight hcont_f
    ⟨C, N, hC, hgrowth_f⟩
  have hqint : Integrable q (volume : Measure ℝ) := by
    simpa [q, m] using hdatum.1
  have hqzero : ∫ x, q x = 0 := by
    simpa [q, m] using hdatum.2.1
  have hqbound : ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧
      ∀ x : ℝ, |q x| ≤ K * (1 + |x|) ^ N * rexp (-x ^ 2 / 2) := by
    simpa [q, m] using hdatum.2.2
  have hsol := gaussianSteinSolution_polynomial_bound_of_datum hqint hqzero hqbound
  have hu_bound : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ, |u x| ≤ C * (1 + |x|) ^ N := by
    simpa [u, gaussianSteinSolution] using hsol
  have hcont_u : ContDiff ℝ 1 u := by
    simpa [u] using contDiff_gaussianSteinSolution hcont_f hqint
  have hcont_g : Continuous g := by
    dsimp [g]
    fun_prop
  have hcont_fp : Continuous (fun x : ℝ => fderiv ℝ f x 1) := by
    have h := hcont_f.continuous_fderiv_apply one_ne_zero
    simpa [Function.comp_def] using h.comp
      (by fun_prop : Continuous (fun x : ℝ => (x, (1 : ℝ))))
  have hcont_up : Continuous (fun x : ℝ => fderiv ℝ u x 1) := by
    have h := hcont_u.continuous_fderiv_apply one_ne_zero
    simpa [Function.comp_def] using h.comp
      (by fun_prop : Continuous (fun x : ℝ => (x, (1 : ℝ))))
  have hcont_fm : Continuous (fun x : ℝ => f x - m) := by fun_prop
  have hfm_bound := polynomial_bound_sub hf_bound (polynomial_bound_const m)
  have huderiv_eq : ∀ x : ℝ, fderiv ℝ u x 1 = x * u x + (f x - m) := by
    intro x
    rw [fderiv_apply_one_eq_deriv]
    simpa [u] using (hasDerivAt_gaussianSteinSolution hcont_f hqint x).deriv
  have hxu_bound := polynomial_bound_mul polynomial_bound_id hu_bound
  have hup_rhs_bound := polynomial_bound_add hxu_bound hfm_bound
  have hup_bound : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ, |fderiv ℝ u x 1| ≤ C * (1 + |x|) ^ N := by
    rcases hup_rhs_bound with ⟨D, M, hD, hD_bound⟩
    refine ⟨D, M, hD, ?_⟩
    intro x
    rw [huderiv_eq x]
    exact hD_bound x
  have hgu_bound := polynomial_bound_mul hfm_bound hu_bound
  have hfp_u_bound := polynomial_bound_mul hfp_bound hu_bound
  have hguprime_bound := polynomial_bound_mul hfm_bound hup_bound
  have hgu_deriv_rhs := polynomial_bound_add hfp_u_bound hguprime_bound
  have hgu_deriv_eq : ∀ x : ℝ,
      fderiv ℝ (fun y => (f y - m) * u y) x 1 =
        fderiv ℝ f x 1 * u x + (f x - m) * fderiv ℝ u x 1 := by
    intro x
    rw [fderiv_apply_one_eq_deriv]
    change deriv ((fun y : ℝ => f y - m) * u) x = _
    have hsub : ContDiff ℝ 1 (fun y : ℝ => f y - m) := hcont_f.sub contDiff_const
    have h := ((hsub.differentiable one_ne_zero x).hasDerivAt.mul
      (hcont_u.differentiable one_ne_zero x).hasDerivAt).deriv
    simpa [fderiv_apply_one_eq_deriv] using h
  have hgu_deriv_bound : ∃ D : ℝ, ∃ M : ℕ, 0 ≤ D ∧ ∀ x : ℝ,
      |fderiv ℝ (fun y => (f y - m) * u y) x 1| ≤ D * (1 + |x|) ^ M := by
    rcases hgu_deriv_rhs with ⟨D, M, hD, hD_bound⟩
    refine ⟨D, M, hD, ?_⟩
    intro x
    rw [hgu_deriv_eq x]
    exact hD_bound x
  have husq_bound := polynomial_bound_mul hu_bound hu_bound
  have hup_sq_bound := polynomial_bound_mul hup_bound hup_bound
  have htwo_u_up_bound := polynomial_bound_mul
    (polynomial_bound_mul (polynomial_bound_const (2 : ℝ)) hu_bound) hup_bound
  have husq_deriv_eq : ∀ x : ℝ,
      fderiv ℝ (fun y => u y ^ 2) x 1 = 2 * u x * fderiv ℝ u x 1 := by
    intro x
    rw [fderiv_apply_one_eq_deriv]
    change deriv (u ^ 2) x = _
    have h := ((hcont_u.differentiable one_ne_zero x).hasDerivAt.pow 2).deriv
    simpa [fderiv_apply_one_eq_deriv] using h
  have husq_deriv_bound : ∃ D : ℝ, ∃ M : ℕ, 0 ≤ D ∧ ∀ x : ℝ,
      |fderiv ℝ (fun y => u y ^ 2) x 1| ≤ D * (1 + |x|) ^ M := by
    rcases htwo_u_up_bound with ⟨D, M, hD, hD_bound⟩
    refine ⟨D, M, hD, ?_⟩
    intro x
    rw [husq_deriv_eq x]
    exact hD_bound x
  have hxu_sq_bound := polynomial_bound_mul polynomial_bound_id husq_bound
  have hxu_up_bound := polynomial_bound_mul hxu_bound hup_bound
  have hxu_sq_deriv_rhs := polynomial_bound_add husq_bound
    (polynomial_bound_mul (polynomial_bound_const (2 : ℝ)) hxu_up_bound)
  have hxu_sq_deriv_eq : ∀ x : ℝ,
      fderiv ℝ (fun y => y * u y ^ 2) x 1 =
        u x ^ 2 + 2 * x * u x * fderiv ℝ u x 1 := by
    intro x
    rw [fderiv_apply_one_eq_deriv]
    change deriv (id * (u ^ 2)) x = u x ^ 2 + 2 * x * u x * deriv u x
    have h := (hasDerivAt_id x).mul ((hcont_u.differentiable one_ne_zero x).hasDerivAt.pow 2)
    convert h.deriv using 1
    simp [id, pow_two]
    ring
  have hxu_sq_deriv_bound : ∃ D : ℝ, ∃ M : ℕ, 0 ≤ D ∧ ∀ x : ℝ,
      |fderiv ℝ (fun y => y * u y ^ 2) x 1| ≤ D * (1 + |x|) ^ M := by
    rcases hxu_sq_deriv_rhs with ⟨D, M, hD, hD_bound⟩
    refine ⟨D, M, hD, ?_⟩
    intro x
    rw [hxu_sq_deriv_eq x]
    simpa [pow_two, mul_assoc] using hD_bound x
  have hnorm_clm : ∀ {L : ℝ →L[ℝ] ℝ}, ‖L‖ = |L 1| := by
    intro L
    apply le_antisymm
    · apply L.opNorm_le_bound (abs_nonneg (L 1))
      intro x
      calc
        ‖L x‖ = ‖L (x • (1 : ℝ))‖ := by simp
        _ = ‖x • L 1‖ := by rw [map_smul]
        _ = ‖x‖ * ‖L 1‖ := by rw [norm_smul]
        _ = ‖L 1‖ * ‖x‖ := by ring
        _ ≤ |L 1| * ‖x‖ := by rw [Real.norm_eq_abs]
    · have h := L.le_opNorm (1 : ℝ)
      simpa [Real.norm_eq_abs] using h
  have hcenter_sq_bound := polynomial_bound_pow hfm_bound 2
  have hderiv_sq_bound := polynomial_bound_pow hfp_bound 2
  have hg_uprime_bound := polynomial_bound_mul hfm_bound hup_bound
  have hx_g_u_bound := polynomial_bound_mul
    (polynomial_bound_mul polynomial_bound_id hfm_bound) hu_bound
  have hfprime_u_bound := polynomial_bound_mul hfp_bound hu_bound
  have hx_sq_u_sq_bound := polynomial_bound_mul
    (polynomial_bound_pow polynomial_bound_id 2) husq_bound
  have hx_u_uprime_bound := polynomial_bound_mul hxu_bound hup_bound
  have hgrowth_prod_bound := polynomial_bound_sum_norm hgu_bound hgu_deriv_bound
  have hgrowth_u_sq_bound := polynomial_bound_sum_norm husq_bound husq_deriv_bound
  have hgrowth_x_u_sq_bound := polynomial_bound_sum_norm hxu_sq_bound hxu_sq_deriv_bound
  have hgrowth_prod : ∃ D : ℝ, ∃ M : ℕ, 0 ≤ D ∧ ∀ x : ℝ,
      |(f x - m) * u x| +
          ‖fderiv ℝ ((fun y => f y - m) * u) x‖ ≤ D * (1 + ‖x‖) ^ M := by
    rcases hgrowth_prod_bound with ⟨D, M, hD, hD_bound⟩
    refine ⟨D, M, hD, ?_⟩
    intro x
    rw [hnorm_clm]
    change |(f x - m) * u x| +
        |fderiv ℝ (fun y => (f y - m) * u y) x 1| ≤ D * (1 + |x|) ^ M
    simpa [Real.norm_eq_abs] using hD_bound x
  have hgrowth_u_sq : ∃ D : ℝ, ∃ M : ℕ, 0 ≤ D ∧ ∀ x : ℝ,
      |u x ^ 2| + ‖fderiv ℝ (fun y => u y ^ 2) x‖ ≤ D * (1 + ‖x‖) ^ M := by
    rcases hgrowth_u_sq_bound with ⟨D, M, hD, hD_bound⟩
    refine ⟨D, M, hD, ?_⟩
    intro x
    rw [hnorm_clm]
    simpa [Real.norm_eq_abs, pow_two] using hD_bound x
  have hgrowth_x_u_sq : ∃ D : ℝ, ∃ M : ℕ, 0 ≤ D ∧ ∀ x : ℝ,
      |x * u x ^ 2| + ‖fderiv ℝ (fun y => y * u y ^ 2) x‖ ≤ D * (1 + ‖x‖) ^ M := by
    rcases hgrowth_x_u_sq_bound with ⟨D, M, hD, hD_bound⟩
    refine ⟨D, M, hD, ?_⟩
    intro x
    rw [hnorm_clm]
    simpa [Real.norm_eq_abs, pow_two, mul_assoc] using hD_bound x
  have hIntG : ∀ {v : ℝ → ℝ}, Continuous v →
      (∃ D : ℝ, ∃ M : ℕ, 0 ≤ D ∧ ∀ x : ℝ, |v x| ≤ D * (1 + |x|) ^ M) →
      Integrable v (gaussianReal 0 1) := by
    intro v hv hb
    exact integrable_continuous_polynomial_bound_gaussian hv hb
  have hIntW : ∀ {v : ℝ → ℝ}, Continuous v →
      (∃ D : ℝ, ∃ M : ℕ, 0 ≤ D ∧ ∀ x : ℝ, |v x| ≤ D * (1 + |x|) ^ M) →
      Integrable (fun x => v x * gaussianPDFReal 0 1 x) (volume : Measure ℝ) := by
    intro v hv hb
    exact integrable_continuous_polynomial_weight hv hb
  have hcenter_sq := hIntG (by fun_prop : Continuous (fun x : ℝ => g x ^ 2)) hcenter_sq_bound
  have hderiv_sq := hIntG (by fun_prop : Continuous (fun x : ℝ => fderiv ℝ f x 1 ^ 2)) hderiv_sq_bound
  have hu_sq_bound' : ∃ D : ℝ, ∃ M : ℕ, 0 ≤ D ∧ ∀ x : ℝ,
      |u x ^ 2| ≤ D * (1 + |x|) ^ M := by
    simpa [pow_two] using husq_bound
  have hup_sq_bound' : ∃ D : ℝ, ∃ M : ℕ, 0 ≤ D ∧ ∀ x : ℝ,
      |fderiv ℝ u x 1 ^ 2| ≤ D * (1 + |x|) ^ M := by
    simpa [pow_two] using hup_sq_bound
  have hx_sq_u_sq_bound' : ∃ D : ℝ, ∃ M : ℕ, 0 ≤ D ∧ ∀ x : ℝ,
      |x ^ 2 * u x ^ 2| ≤ D * (1 + |x|) ^ M := by
    simpa [pow_two] using hx_sq_u_sq_bound
  have hxu_sq_bound' : ∃ D : ℝ, ∃ M : ℕ, 0 ≤ D ∧ ∀ x : ℝ,
      |x * u x ^ 2| ≤ D * (1 + |x|) ^ M := by
    simpa [pow_two] using hxu_sq_bound
  have hxu_sq_deriv_rhs' : ∃ D : ℝ, ∃ M : ℕ, 0 ≤ D ∧ ∀ x : ℝ,
      |u x ^ 2 + 2 * x * u x * fderiv ℝ u x 1| ≤ D * (1 + |x|) ^ M := by
    simpa [pow_two, mul_assoc] using hxu_sq_deriv_rhs
  have hu_sq := hIntG (by fun_prop : Continuous (fun x : ℝ => u x ^ 2)) hu_sq_bound'
  have hderiv_memLp := memLp_continuous_polynomial_bound_gaussian hcont_fp hfp_bound
  have hu_memLp := memLp_continuous_polynomial_bound_gaussian hcont_u.continuous hu_bound
  have hprod := hIntW (by fun_prop : Continuous (fun x : ℝ => (f x - m) * u x)) hgu_bound
  have hprod_deriv := hIntW (by fun_prop : Continuous (fun x : ℝ =>
      fderiv ℝ f x 1 * u x + (f x - m) * fderiv ℝ u x 1)) hgu_deriv_rhs
  have hprod_x := hIntW (by fun_prop : Continuous (fun x : ℝ =>
      x * (f x - m) * u x)) hx_g_u_bound
  have h_g_uprime := hIntG (by fun_prop : Continuous (fun x : ℝ =>
      (f x - m) * fderiv ℝ u x 1)) hg_uprime_bound
  have h_x_g_u := hIntG (by fun_prop : Continuous (fun x : ℝ =>
      x * (f x - m) * u x)) hx_g_u_bound
  have h_fprime_u := hIntG (by fun_prop : Continuous (fun x : ℝ =>
      fderiv ℝ f x 1 * u x)) hfprime_u_bound
  have h_uprime_sq_gaussian := hIntG (by fun_prop : Continuous (fun x : ℝ =>
      fderiv ℝ u x 1 ^ 2)) hup_sq_bound'
  have h_x_sq_u_sq_gaussian := hIntG (by fun_prop : Continuous (fun x : ℝ =>
      x ^ 2 * u x ^ 2)) hx_sq_u_sq_bound'
  have h_x_u_uprime_gaussian := hIntG (by fun_prop : Continuous (fun x : ℝ =>
      x * u x * fderiv ℝ u x 1)) hx_u_uprime_bound
  have hu_deriv_sq := hIntW (by fun_prop : Continuous (fun x : ℝ =>
      fderiv ℝ u x 1 ^ 2)) hup_sq_bound'
  have hu_x_sq := hIntW (by fun_prop : Continuous (fun x : ℝ =>
      x ^ 2 * u x ^ 2)) hx_sq_u_sq_bound'
  have hu_x_deriv := hIntW (by fun_prop : Continuous (fun x : ℝ =>
      x * u x * fderiv ℝ u x 1)) hx_u_uprime_bound
  have hu_sq_volume := hIntW (by fun_prop : Continuous (fun x : ℝ => u x ^ 2)) hu_sq_bound'
  have hu_sq_deriv_volume := hIntW (by fun_prop : Continuous (fun x : ℝ =>
      2 * u x * fderiv ℝ u x 1)) htwo_u_up_bound
  have hu_x_sq_volume := hIntW (by fun_prop : Continuous (fun x : ℝ =>
      x * u x ^ 2)) hxu_sq_bound'
  have hu_x_sq_deriv_volume := hIntW (by fun_prop : Continuous (fun x : ℝ =>
      u x ^ 2 + 2 * x * u x * fderiv ℝ u x 1)) hxu_sq_deriv_rhs'
  have hstein : ∀ x : ℝ, f x - ∫ y, f y ∂(gaussianReal 0 1) =
      fderiv ℝ u x 1 - x * u x := by
    intro x
    have h := huderiv_eq x
    dsimp [m] at h ⊢
    linarith
  exact gaussian_poincare_one_dimensional_of_explicit_stein
    (f := f) hcont_f
    (⟨C, N, hC, hgrowth_f⟩)
    (by simpa [q, m] using hqint)
    (by simpa [m, u] using hgrowth_prod)
    (by simpa [m, u] using hgrowth_u_sq)
    (by simpa [m, u] using hgrowth_x_u_sq)
    (by simpa [m, u, g, Real.norm_eq_abs] using hcenter_sq)
    (by simpa [m, u, Real.norm_eq_abs] using hderiv_sq)
    (by simpa [m, u] using hu_sq)
    (by simpa [m, u] using hderiv_memLp)
    (by simpa [m, u] using hu_memLp)
    (by simpa [m, u] using hprod)
    (by simpa [m, u] using hprod_deriv)
    (by simpa [m, u] using hprod_x)
    (by simpa [m, u] using h_g_uprime)
    (by simpa [m, u] using h_x_g_u)
    (by simpa [m, u] using h_fprime_u)
    (by simpa [m, u] using h_uprime_sq_gaussian)
    (by simpa [m, u] using h_x_sq_u_sq_gaussian)
    (by simpa [m, u] using h_x_u_uprime_gaussian)
    (by simpa [m, u] using hu_deriv_sq)
    (by simpa [m, u] using hu_x_sq)
    (by simpa [m, u] using hu_x_deriv)
    (by simpa [m, u] using hu_sq_volume)
    (by simpa [m, u] using hu_sq_deriv_volume)
    (by simpa [m, u] using hu_x_sq_volume)
    (by simpa [m, u] using hu_x_sq_deriv_volume)

end RegularityStructures

end
