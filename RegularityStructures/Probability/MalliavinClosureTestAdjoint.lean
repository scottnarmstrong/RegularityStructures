/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureAutomaticDuality
public import RegularityStructures.Probability.MalliavinClosureTestFields

/-!
# The adjoint coefficient of a smooth finite-rank test field

For a test field `∑ⱼ uⱼ(W a) kⱼ`, this file constructs the fixed `L²` coefficient
`∑ⱼ uⱼ(W a) W(kⱼ) - ∑ᵢⱼ ⟪aᵢ,kⱼ⟫ ∂ᵢuⱼ(W a)`.  Compact support gives uniform bounds for both
the coefficient and its coordinate derivatives, so the construction uses only the stated
`MemLp` assumptions and Gaussian measurability.  This is the adjoint appearing in the
finite-rank duality of [HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RegularityStructures

private lemma malliavin_test_value_bound_local {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} (hsupport : HasCompactSupport u)
    (hcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |u x| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := hsupport.exists_bound_iteratedFDeriv hcont 1
  refine ⟨C, hC, ?_⟩
  intro x
  simpa [Real.norm_eq_abs] using hbound 0 (by norm_num) x

private lemma malliavin_test_coordinate_bound_local {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} (hsupport : HasCompactSupport u)
    (hcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (i : Fin n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |coordinateDerivative u i x| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := hsupport.exists_bound_iteratedFDeriv hcont 1
  refine ⟨C, hC, ?_⟩
  intro x
  have hnorm : ‖fderiv ℝ u x (Pi.single i 1)‖ ≤ ‖fderiv ℝ u x‖ := by
    have h := ContinuousLinearMap.le_opNorm (fderiv ℝ u x) (Pi.single i 1)
    have hs : ‖(Pi.single i (1 : ℝ) : Fin n → ℝ)‖ = 1 := by
      classical
      rw [Pi.norm_single]
      simp
    simpa [hs] using h
  have hderiv : ‖fderiv ℝ u x‖ ≤ C := by
    simpa [norm_iteratedFDeriv_one] using hbound 1 (by norm_num) x
  simpa [coordinateDerivative, Real.norm_eq_abs] using hnorm.trans hderiv

private lemma malliavin_test_coordinate_continuous_local {n : ℕ}
    {u : (Fin n → ℝ) → ℝ}
    (hcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (i : Fin n) :
    Continuous (coordinateDerivative u i) := by
  have h := hcont.continuous_fderiv_apply (by norm_num)
  change Continuous (fun x : Fin n → ℝ => fderiv ℝ u x (Pi.single i 1))
  simpa [Function.comp_def] using h.comp
    (by fun_prop : Continuous (fun x : Fin n → ℝ => (x, Pi.single i 1)))

theorem malliavin_smooth_test_adjoint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ}
    {n m : ℕ} {a : Fin n → SpaceTime → ℝ}
    {u : Fin m → (Fin n → ℝ) → ℝ} {k : Fin m → SpaceTime → ℝ}
    (hW : IsWhiteNoise P W)
    (ha : ∀ i, MemLp (a i) 2)
    (hu_cont : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u j))
    (hu_support : ∀ j, HasCompactSupport (u j))
    (_hu_lp : ∀ j, MemLp (fun ω => u j (fun i => W (a i) ω)) 2 P)
    (hk : ∀ j, MemLp (k j) 2) :
    ∃ R : Ω → ℝ, MemLp R 2 P ∧
      R = (fun ω =>
        ∑ j, (u j (fun i => W (a i) ω) * W (k j) ω -
          ∑ i, (∫ z, a i z * k j z) *
            coordinateDerivative (u j) i (fun l => W (a l) ω))) ∧
      ∀ j, MemLp (fun ω => u j (fun i => W (a i) ω) * W (k j) ω -
        ∑ i, (∫ z, a i z * k j z) *
          coordinateDerivative (u j) i (fun l => W (a l) ω)) 2 P := by
  let X : Ω → (Fin n → ℝ) := fun ω i => W (a i) ω
  have hX : AEMeasurable X P := (hW.2 n a ha).1
  have hXmeas : Measurable X := by
    rw [measurable_pi_iff]
    intro i
    exact hW.1 (a i) (ha i)
  have hWk : ∀ j, MemLp (fun ω => W (k j) ω) 2 P := by
    intro j
    exact (hW.2 m k hk).memLp_two_apply j
  have hprod (j : Fin m) : MemLp
      (fun ω => u j (X ω) * W (k j) ω) 2 P := by
    obtain ⟨C, hC, hu_bound⟩ := malliavin_test_value_bound_local
      (hu_support j) (hu_cont j)
    have hmeas : AEStronglyMeasurable
        (fun ω => u j (X ω) * W (k j) ω) P := by
      exact (((hu_cont j).continuous.measurable.comp hXmeas).mul
        (hW.1 (k j) (hk j))).aestronglyMeasurable
    apply (hWk j).of_le_mul hmeas
    filter_upwards [] with ω
    rw [norm_mul]
    have huω : ‖u j (X ω)‖ ≤ C := by
      simpa [Real.norm_eq_abs] using hu_bound (X ω)
    calc
      ‖u j (X ω)‖ * ‖W (k j) ω‖ ≤ C * ‖W (k j) ω‖ :=
        mul_le_mul_of_nonneg_right huω (norm_nonneg _)
      _ = C * ‖W (k j) ω‖ := rfl
  have hcoord (j : Fin m) (i : Fin n) : MemLp
      (fun ω => coordinateDerivative (u j) i (X ω)) 2 P := by
    obtain ⟨C, hC, hu_bound⟩ := malliavin_test_coordinate_bound_local
      (hu_support j) (hu_cont j) i
    have hone : MemLp (fun _ : Ω => (1 : ℝ)) 2 P :=
      MeasureTheory.memLp_const (p := (2 : ℝ≥0∞)) (μ := P) (1 : ℝ)
    have hmeas : AEStronglyMeasurable
        (fun ω => coordinateDerivative (u j) i (X ω)) P := by
      have hmeas' := Measurable.comp_aemeasurable
        (malliavin_test_coordinate_continuous_local (hu_cont j) i).measurable hX
      exact hmeas'.aestronglyMeasurable
    apply hone.of_le_mul hmeas
    filter_upwards [] with ω
    have hω := hu_bound (X ω)
    simpa [Real.norm_eq_abs] using hω
  have hinner (j : Fin m) (i : Fin n) : Integrable (fun z => a i z * k j z) :=
    (ha i).integrable_mul (hk j)
  have hsum_j (j : Fin m) : MemLp
      (fun ω => ∑ i, (∫ z, a i z * k j z) *
        coordinateDerivative (u j) i (X ω)) 2 P := by
    apply memLp_finsetSum
    intro i hi
    exact (hcoord j i).const_mul (∫ z, a i z * k j z)
  have hterm (j : Fin m) : MemLp
      (fun ω => u j (X ω) * W (k j) ω -
        ∑ i, (∫ z, a i z * k j z) * coordinateDerivative (u j) i (X ω)) 2 P :=
    (hprod j).sub (hsum_j j)
  have hR : MemLp
      (fun ω => ∑ j, (u j (X ω) * W (k j) ω -
        ∑ i, (∫ z, a i z * k j z) * coordinateDerivative (u j) i (X ω))) 2 P := by
    apply memLp_finsetSum
    intro j hj
    exact hterm j
  refine ⟨(fun ω =>
      ∑ j, (u j (fun i => W (a i) ω) * W (k j) ω -
        ∑ i, (∫ z, a i z * k j z) *
          coordinateDerivative (u j) i (fun l => W (a l) ω))), ?_, rfl, ?_⟩
  · simpa [X] using hR
  · intro j
    simpa [X] using hterm j

end RegularityStructures

end
