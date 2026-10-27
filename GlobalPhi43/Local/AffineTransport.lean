module

public import GlobalPhi43.Local.ParabolicTransport
public import GlobalPhi43.Local.PastAffineError
public import GlobalPhi43.MW20.ScalarSupNorm

public section

namespace GlobalPhi43.Local

open RegularityStructures Set MW20
open scoped ENNReal

/-- The actual local scalar supremum transports as an extended value. -/
theorem localScalarSup_parabolicPullback (a : ℝ) (f : ParabolicSpace → ℝ)
    (b : ParabolicSpace) (ℓ : ℝ) (D : Set ParabolicSpace) :
    localScalarSup (parabolicPullback a f b ℓ) D =
      ENNReal.ofReal |a| * localScalarSup f (parabolicMap b ℓ '' D) := by
  simp only [localScalarSup, iSup_image, ENNReal.mul_iSup, parabolicPullback,
    abs_mul, ENNReal.ofReal_mul (abs_nonneg a)]

/-- Transforming all affine coefficients, with the correct spatial length factor. -/
theorem spatialAffine_parabolicMap (a : ℝ) (b : ParabolicSpace) (ℓ : ℝ)
    (x y : ParabolicSpace) (c : ℝ) (ν : Fin 3 → ℝ) :
    spatialAffine x (a*c) (fun i => a*ℓ*ν i) y =
      a*spatialAffine (parabolicMap b ℓ x) c ν (parabolicMap b ℓ y) := by
  unfold spatialAffine spatialLinear
  simp only [parabolicMap,parabolicDilate,Prod.snd_sub,
    Pi.sub_apply,Pi.smul_apply,smul_eq_mul,add_sub_add_left_eq_sub]
  rw [mul_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact error supremum for the transported affine coefficients. -/
theorem affine_error_sup_parabolicMap (a : ℝ) (f : ParabolicSpace → ℝ)
    (b : ParabolicSpace) (ℓ : ℝ) (x : ParabolicSpace) (D : Set ParabolicSpace)
    (c : ℝ) (ν : Fin 3 → ℝ) :
    (⨆ y ∈ D, ENNReal.ofReal |parabolicPullback a f b ℓ y-
      spatialAffine x (a*c) (fun i => a*ℓ*ν i) y|) =
    ENNReal.ofReal |a| * ⨆ z ∈ parabolicMap b ℓ '' D,
      ENNReal.ofReal |f z-spatialAffine (parabolicMap b ℓ x) c ν z| := by
  simp only [iSup_image, ENNReal.mul_iSup]
  apply iSup_congr
  intro y
  apply iSup_congr
  intro _
  rw [spatialAffine_parabolicMap]
  change ENNReal.ofReal |a*f (parabolicMap b ℓ y)-a*_| = _
  rw [← mul_sub,abs_mul,ENNReal.ofReal_mul (abs_nonneg a)]

/-- Both affine infima transport exactly; no minimizer or finiteness premise. -/
theorem pastAffineError_parabolicPullback (a : ℝ) (ha : a ≠ 0)
    (f : ParabolicSpace → ℝ) (b : ParabolicSpace) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (x : ParabolicSpace) (R : ℝ) :
    pastAffineError (parabolicPullback a f b ℓ) x R =
      ENNReal.ofReal |a| * pastAffineError f (parabolicMap b ℓ x) (ℓ*R) := by
  have hp : ENNReal.ofReal |a| ≠ 0 := (ENNReal.ofReal_pos.mpr (abs_pos.mpr ha)).ne'
  have hs (c : ℝ) (ν : Fin 3 → ℝ) :=
    affine_error_sup_parabolicMap a f b ℓ x (pastBall x R) c ν
  simp only [parabolicMap_image_pastBall b hℓ x R] at hs
  unfold pastAffineError
  rw [ENNReal.mul_iInf_of_ne hp ENNReal.ofReal_ne_top]
  simp_rw [ENNReal.mul_iInf_of_ne hp ENNReal.ofReal_ne_top]
  apply le_antisymm
  · refine le_iInf fun c => le_iInf fun ν => ?_
    exact iInf_le_of_le (a*c) (iInf_le_of_le (fun i => a*ℓ*ν i) (hs c ν).le)
  · refine le_iInf fun c => le_iInf fun ν => ?_
    have hc : a*(c/a) = c := by field_simp
    have hν : (fun i => a*ℓ*(ν i/(a*ℓ))) = ν := by
      funext i
      field_simp
    have hh := (hs (c/a) (fun i => ν i/(a*ℓ))).symm.le
    rw [hc,hν] at hh
    exact iInf_le_of_le (c/a) (iInf_le_of_le (fun i => ν i/(a*ℓ)) hh)

end GlobalPhi43.Local
