module

public import RegularityStructures.Probability.CovarianceEnergy
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.CharFun

/-! Law uniqueness for the finite Gaussian vectors in the white-noise contract. -/

public section

namespace GlobalPhi43.Attachment
open MeasureTheory ProbabilityTheory RegularityStructures
open scoped ENNReal

private theorem dual_fin_expand {n : ℕ} (L : StrongDual ℝ (Fin n → ℝ))
    (x : Fin n → ℝ) : L x = ∑ i, L (Pi.single i 1) * x i := by
  classical
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin n → ℝ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  calc
    L x = L (∑ i, x i • (Pi.single i 1 : Fin n → ℝ)) := congrArg L hx
    _ = ∑ i, L (Pi.single i 1) * x i := by
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm]

private theorem centredGaussian_mean_dual {n : ℕ} {C : Fin n → Fin n → ℝ}
  {A : Type*} [MeasurableSpace A] {μ : Measure A} {V : A → Fin n → ℝ}
    (hV : IsCentredGaussianVector μ V C) (L : StrongDual ℝ (Fin n → ℝ)) :
    ∫ ω, L (V ω) ∂μ = 0 := by
  have hgV : HasGaussianLaw V μ := ⟨hV.1, hV.2.1⟩
  have hi (i : Fin n) : Integrable (fun ω => V ω i) μ := by
    exact (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).integrable_comp hgV.integrable
  have he : (fun ω => L (V ω)) = (fun ω => ∑ i, L (Pi.single i 1) * V ω i) := by
    funext ω; exact dual_fin_expand L (V ω)
  rw [he]
  rw [integral_finsetSum _ (fun i _ => (hi i).const_mul _)]
  simp_rw [integral_const_mul, hV.2.2.1, mul_zero, Finset.sum_const_zero]

/-- A centred Gaussian vector's law is determined by its stipulated covariance matrix.
This works across different underlying probability spaces. -/
theorem centredGaussianVector_map_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {n : ℕ} {X : Ω → Fin n → ℝ}
    {Y : Ω' → Fin n → ℝ} {C : Fin n → Fin n → ℝ}
    (hX : IsCentredGaussianVector P X C) (hY : IsCentredGaussianVector P' Y C) :
    P.map X = P'.map Y := by
  have hgX : HasGaussianLaw X P := ⟨hX.1, hX.2.1⟩
  have hgY : HasGaussianLaw Y P' := ⟨hY.1, hY.2.1⟩
  let _ : IsGaussian (P.map X) := hX.2.1
  let _ : IsGaussian (P'.map Y) := hY.2.1
  apply Measure.ext_of_charFunDual
  ext L
  rw [hgX.charFunDual_map_eq_fun, hgY.charFunDual_map_eq_fun, centredGaussian_mean_dual hX L, centredGaussian_mean_dual hY L]
  have hvX := centredGaussian_linear_variance_eq_covarianceEnergy hX (fun i => L (Pi.single i 1))
  have hvY := centredGaussian_linear_variance_eq_covarianceEnergy hY (fun i => L (Pi.single i 1))
  have heX : (fun ω => L (X ω)) = (fun ω => ∑ i, L (Pi.single i 1) * X ω i) := by
    funext ω; exact dual_fin_expand L (X ω)
  have heY : (fun ω => L (Y ω)) = (fun ω => ∑ i, L (Pi.single i 1) * Y ω i) := by
    funext ω; exact dual_fin_expand L (Y ω)
  rw [heX, heY, hvX, hvY]

end GlobalPhi43.Attachment
