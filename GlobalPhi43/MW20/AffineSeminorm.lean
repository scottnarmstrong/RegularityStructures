module

public import GlobalPhi43.MW20.OptimalAffineCoefficient
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Attainment of the affine infimum in MW20 (2.6)

Extended nonnegative suprema faithfully retain infinite seminorms. On every
open domain the infimum is attained by the spatial derivative in the second
variable on the diagonal. This includes the infinite case and does not
assume the existence of a finite affine coefficient.
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set
open scoped ENNReal ContDiff

/-- The actual remainder supremum for one base point and coefficient. -/
@[expose] noncomputable def affineRemainderSeminorm
    (U : ParabolicSpace × ParabolicSpace → ℝ) (D : Set ParabolicSpace)
    (γ : ℝ) (x : ParabolicSpace) (ν : Fin 3 → ℝ) : ℝ≥0∞ :=
  ⨆ y ∈ D, ⨆ (_ : y ≠ x),
    ENNReal.ofReal (|U (x, y) - ∑ j, ν j * (y.2 j - x.2 j)| / pdist x y ^ γ)

/-- MW20's local two-variable Hölder seminorm, with its original quantifier
order: supremum over base points, infimum over affine coefficients. -/
@[expose] noncomputable def localAffineSeminorm
    (U : ParabolicSpace × ParabolicSpace → ℝ) (D : Set ParabolicSpace) (γ : ℝ) : ℝ≥0∞ :=
  ⨆ x ∈ D, ⨅ ν, affineRemainderSeminorm U D γ x ν

/-- Distinct space-time points have positive max parabolic distance. -/
theorem pdist_pos_of_ne {x y : ParabolicSpace} (hne : y ≠ x) : 0 < pdist x y := by
  by_contra hn
  have hz : pdist x y ≤ 0 := not_lt.mp hn
  have hs : x.2 = y.2 := sub_eq_zero.mp (norm_eq_zero.mp
    (le_antisymm ((le_max_right _ _).trans hz) (norm_nonneg _)))
  have ht : Real.sqrt |x.1 - y.1| ≤ 0 := (le_max_left _ _).trans hz
  have habs : |x.1 - y.1| = 0 := by
    nlinarith [Real.sqrt_nonneg |x.1 - y.1|, Real.sq_sqrt (abs_nonneg (x.1 - y.1))]
  exact hne (Prod.ext (sub_eq_zero.mp (abs_eq_zero.mp habs)) hs).symm

/-- A finite actual remainder supremum supplies its literal pointwise bound. -/
theorem affineRemainderSeminorm_bound
    (U : ParabolicSpace × ParabolicSpace → ℝ) (D : Set ParabolicSpace)
    (γ : ℝ) (x : ParabolicSpace) (ν : Fin 3 → ℝ)
    (hfinite : affineRemainderSeminorm U D γ x ν ≠ ⊤)
    {y : ParabolicSpace} (hy : y ∈ D) (hne : y ≠ x) :
    |U (x, y) - ∑ j, ν j * (y.2 j - x.2 j)| ≤
      (affineRemainderSeminorm U D γ x ν).toReal * pdist x y ^ γ := by
  have hall : ∀ y ∈ D, ∀ (_ : y ≠ x),
      ENNReal.ofReal (|U (x, y) - ∑ j, ν j * (y.2 j - x.2 j)| / pdist x y ^ γ) ≤
        affineRemainderSeminorm U D γ x ν := by
    simpa only [affineRemainderSeminorm, iSup_le_iff] using
      (le_rfl : affineRemainderSeminorm U D γ x ν ≤ affineRemainderSeminorm U D γ x ν)
  have hb := (ENNReal.ofReal_le_iff_le_toReal hfinite).mp (hall y hy hne)
  exact (div_le_iff₀ (Real.rpow_pos_of_pos (pdist_pos_of_ne hne) _)).mp hb

/-- Every affine coefficient has at least the canonical remainder supremum;
infinite competitors are handled without assuming finite Hölder regularity. -/
theorem diagonalSpatialCoefficient_minimizes
    (U : ParabolicSpace × ParabolicSpace → ℝ) (hU : ContDiff ℝ ∞ U)
    (D : Set ParabolicSpace) (hD : IsOpen D) {x : ParabolicSpace} (hx : x ∈ D)
    {γ : ℝ} (hγ : 1 < γ) (ν : Fin 3 → ℝ) :
    affineRemainderSeminorm U D γ x (diagonalSpatialCoefficient U x) ≤
      affineRemainderSeminorm U D γ x ν := by
  by_cases hfinite : affineRemainderSeminorm U D γ x ν = ⊤
  · rw [hfinite]
    exact le_top
  · have he := diagonalSpatialCoefficient_eq_on_open U hU D hD hx ν hγ
      (fun y hy hne => affineRemainderSeminorm_bound U D γ x ν hfinite hy hne)
    rw [he]

/-- The infimum in (2.6) is attained by the diagonal spatial gradient. -/
theorem affineRemainderSeminorm_iInf_eq
    (U : ParabolicSpace × ParabolicSpace → ℝ) (hU : ContDiff ℝ ∞ U)
    (D : Set ParabolicSpace) (hD : IsOpen D) {x : ParabolicSpace} (hx : x ∈ D)
    {γ : ℝ} (hγ : 1 < γ) :
    (⨅ ν, affineRemainderSeminorm U D γ x ν) =
      affineRemainderSeminorm U D γ x (diagonalSpatialCoefficient U x) := by
  apply le_antisymm (iInf_le _ _)
  exact le_iInf (diagonalSpatialCoefficient_minimizes U hU D hD hx hγ)

/-- The complete local source seminorm is the supremum of remainders with
exactly the prescribed coefficient; no allowance or constant is enlarged. -/
theorem localAffineSeminorm_eq_diagonalSpatialCoefficient
    (U : ParabolicSpace × ParabolicSpace → ℝ) (hU : ContDiff ℝ ∞ U)
    (D : Set ParabolicSpace) (hD : IsOpen D)
    {γ : ℝ} (hγ : 1 < γ) :
    localAffineSeminorm U D γ =
      ⨆ x ∈ D, affineRemainderSeminorm U D γ x (diagonalSpatialCoefficient U x) := by
  apply iSup_congr
  intro x
  apply iSup_congr
  intro hx
  exact affineRemainderSeminorm_iInf_eq U hU D hD hx hγ

/-- Extract the complete remainder estimate from the source seminorm, with
its actual minimizing coefficient and exactly the supplied finite allowance. -/
theorem localAffineSeminorm_remainder_bound
    (U : ParabolicSpace × ParabolicSpace → ℝ) (hU : ContDiff ℝ ∞ U)
    (D : Set ParabolicSpace) (hD : IsOpen D) {γ C : ℝ} (hγ : 1 < γ) (hC : 0 ≤ C)
    (hnorm : localAffineSeminorm U D γ ≤ ENNReal.ofReal C)
    {x y : ParabolicSpace} (hx : x ∈ D) (hy : y ∈ D) (hne : y ≠ x) :
    |U (x, y) - ∑ j, diagonalSpatialCoefficient U x j * (y.2 j - x.2 j)| ≤
      C * pdist x y ^ γ := by
  have hall : ∀ x ∈ D,
      affineRemainderSeminorm U D γ x (diagonalSpatialCoefficient U x) ≤ ENNReal.ofReal C := by
    simpa only [localAffineSeminorm_eq_diagonalSpatialCoefficient U hU D hD hγ,
      iSup_le_iff] using hnorm
  have hb := hall x hx
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have hreal : (affineRemainderSeminorm U D γ x (diagonalSpatialCoefficient U x)).toReal ≤ C := by
    simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  exact (affineRemainderSeminorm_bound U D γ x _ hfinite hy hne).trans
    (mul_le_mul_of_nonneg_right hreal (Real.rpow_nonneg (pdist_nonneg x y) _))

end GlobalPhi43.MW20
