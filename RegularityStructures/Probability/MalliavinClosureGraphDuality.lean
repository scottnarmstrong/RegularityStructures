/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureTestAdjoint
public import RegularityStructures.Probability.MalliavinClosureSpectralGap

/-!
# Cylindrical graph duality against a smooth test field

For a fixed cylindrical representation and a fixed smooth finite-rank test field, the pairing of
the cylindrical derivative with that test field equals the pairing of the cylindrical value with
the test field's adjoint coefficient.  The proof uses the automatic Gaussian random-test identity
term by term and explicit `L²` product estimates.  This is the concrete duality needed before
passing to the graph closure in [HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

theorem malliavin_graph_pairing_smooth_test
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ}
    {n : ℕ} {h : Fin n → SpaceTime → ℝ} {f : (Fin n → ℝ) → ℝ}
    (hW : IsWhiteNoise P W)
    (hmem_h : ∀ i, MemLp (h i) 2)
    (hcont_f : ContDiff ℝ 1 f)
    (hgrowth_f : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin n → ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ K * (1 + ‖x‖) ^ M)
    (hF : MemLp (cylindricalFunctional W h f) 2 P)
    (hD : MemLp (fun p : Ω × SpaceTime =>
      cylindricalDerivative W h f p.1 p.2) 2 (whiteNoiseDerivativeMeasure P))
    {m r : ℕ} {a : Fin r → SpaceTime → ℝ}
    {u : Fin m → (Fin r → ℝ) → ℝ} {k : Fin m → SpaceTime → ℝ}
    (ha : ∀ i, MemLp (a i) 2)
    (hu_cont : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u j))
    (hu_support : ∀ j, HasCompactSupport (u j))
    (hu_lp : ∀ j, MemLp (fun ω => u j (fun i => W (a i) ω)) 2 P)
    (hk : ∀ j, MemLp (k j) 2)
    (hsum : MemLp (fun p : Ω × SpaceTime =>
      ∑ j, u j (fun i => W (a i) p.1) * k j p.2) 2
      (whiteNoiseDerivativeMeasure P))
    {R : Ω → ℝ} (hR : MemLp R 2 P)
    (hR_eq : R = fun ω =>
      ∑ j, (u j (fun i => W (a i) ω) * W (k j) ω -
        ∑ i, (∫ z, a i z * k j z) *
          coordinateDerivative (u j) i (fun l => W (a l) ω)))
    (hRj : ∀ j, MemLp (fun ω => u j (fun i => W (a i) ω) * W (k j) ω -
      ∑ i, (∫ z, a i z * k j z) *
        coordinateDerivative (u j) i (fun l => W (a l) ω)) 2 P) :
      (ContinuousLinearMap.mul ℝ ℝ).lpPairing
          (whiteNoiseDerivativeMeasure P) 2 2
          (hD.toLp (fun p : Ω × SpaceTime =>
            cylindricalDerivative W h f p.1 p.2))
          (hsum.toLp (fun p : Ω × SpaceTime =>
            ∑ j, u j (fun i => W (a i) p.1) * k j p.2)) =
        (ContinuousLinearMap.mul ℝ ℝ).lpPairing P 2 2
          (hF.toLp (cylindricalFunctional W h f)) (hR.toLp R) := by
  let hDfun : Ω × SpaceTime → ℝ := fun p => cylindricalDerivative W h f p.1 p.2
  let hFfun : Ω → ℝ := cylindricalFunctional W h f
  let hSfun : Ω × SpaceTime → ℝ := fun p =>
    ∑ j, u j (fun i => W (a i) p.1) * k j p.2
  have hpairD :
      (ContinuousLinearMap.mul ℝ ℝ).lpPairing
          (whiteNoiseDerivativeMeasure P) 2 2 (hD.toLp hDfun)
          (hsum.toLp hSfun) = ∫ p, hDfun p * hSfun p
        ∂(whiteNoiseDerivativeMeasure P) := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hD.coeFn_toLp, hsum.coeFn_toLp] with p hp hs
    rw [ContinuousLinearMap.mul_apply', hp, hs]
  have hpairF :
      (ContinuousLinearMap.mul ℝ ℝ).lpPairing P 2 2 (hF.toLp hFfun)
          (hR.toLp R) =
        ∫ ω, hFfun ω * R ω ∂P := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp, hR.coeFn_toLp] with ω hω hRω
    rw [ContinuousLinearMap.mul_apply', hω, hRω]
  have hterm (j : Fin m) : MemLp
      (fun p : Ω × SpaceTime => hDfun p *
        (u j (fun i => W (a i) p.1) * k j p.2)) 1
      (whiteNoiseDerivativeMeasure P) := by
    have hu_k : MemLp (fun p : Ω × SpaceTime =>
        u j (fun i => W (a i) p.1) * k j p.2) 2
        (whiteNoiseDerivativeMeasure P) :=
      memLp_prod_mul_of_memLp_two (hu_lp j) (hk j)
    exact hD.mul hu_k
  have hleft_split :
      ∫ p, hDfun p * hSfun p ∂(whiteNoiseDerivativeMeasure P) =
        ∑ j, ∫ p, hDfun p *
          (u j (fun i => W (a i) p.1) * k j p.2)
            ∂(whiteNoiseDerivativeMeasure P) := by
    have heq : (fun p => hDfun p * hSfun p) =
        (fun p => ∑ j, hDfun p *
          (u j (fun i => W (a i) p.1) * k j p.2)) := by
      funext p
      simp only [hSfun, Finset.mul_sum]
    rw [heq, integral_finsetSum]
    intro j hj
    exact memLp_one_iff_integrable.1 (hterm j)
  have hterm_value (j : Fin m) : MemLp
      (fun ω => hFfun ω *
        (u j (fun i => W (a i) ω) * W (k j) ω -
          ∑ i, (∫ z, a i z * k j z) *
            coordinateDerivative (u j) i (fun l => W (a l) ω))) 1 P := by
    exact hF.mul (hRj j)
  have hright_split :
      ∫ ω, hFfun ω * R ω ∂P =
        ∑ j, ∫ ω, hFfun ω *
          (u j (fun i => W (a i) ω) * W (k j) ω -
            ∑ i, (∫ z, a i z * k j z) *
              coordinateDerivative (u j) i (fun l => W (a l) ω)) ∂P := by
    have heq : (fun ω => hFfun ω * R ω) =
        (fun ω => ∑ j, hFfun ω *
          (u j (fun i => W (a i) ω) * W (k j) ω -
            ∑ i, (∫ z, a i z * k j z) *
              coordinateDerivative (u j) i (fun l => W (a l) ω))) := by
      funext ω
      rw [hR_eq, Finset.mul_sum]
    rw [heq, integral_finsetSum]
    intro j hj
    exact memLp_one_iff_integrable.1 (hterm_value j)
  have hduality (j : Fin m) :
      ∫ p, hDfun p *
          (u j (fun i => W (a i) p.1) * k j p.2)
            ∂(whiteNoiseDerivativeMeasure P) =
        ∫ ω, hFfun ω *
          (u j (fun i => W (a i) ω) * W (k j) ω -
            ∑ i, (∫ z, a i z * k j z) *
              coordinateDerivative (u j) i (fun l => W (a l) ω)) ∂P := by
    have hu1 : ContDiff ℝ 1 (u j) := (hu_cont j).of_le (by norm_num)
    have hgrowth_u := malliavin_compact_contDiff_polynomial_bound
      (hu_support j) (hu_cont j)
    simpa [hDfun, hFfun, cylindricalFunctional] using
      (malliavin_random_test_duality_of_polynomial_growth hW hmem_h ha
        (hk j) hcont_f hu1 hgrowth_f hgrowth_u)
  rw [hpairD, hleft_split, hpairF, hright_split]
  apply Finset.sum_congr rfl
  intro j hj
  exact hduality j

end RegularityStructures

end
