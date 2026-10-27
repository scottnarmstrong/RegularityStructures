module

public import GlobalPhi43.MW20.AffineSeminorm

/-! Radius-truncated affine seminorms. Residuals are tested only up to
the specified distance cutoff. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set
open scoped ENNReal ContDiff

/-- The true radius-restricted inner supremum in (2.6). -/
@[expose] noncomputable def radiusAffineRemainderSeminorm
    (U : ParabolicSpace × ParabolicSpace → ℝ) (D : Set ParabolicSpace)
    (γ L : ℝ) (x : ParabolicSpace) (a : Fin 3 → ℝ) : ℝ≥0∞ :=
  affineRemainderSeminorm U (D ∩ {y | pdist x y ≤ L}) γ x a

/-- The radius-local affine norm: sup in x, inf in a, sup over
pairs with distance at most L. -/
@[expose] noncomputable def radiusAffineSeminorm
    (U : ParabolicSpace × ParabolicSpace → ℝ) (D : Set ParabolicSpace)
    (γ L : ℝ) : ℝ≥0∞ :=
  ⨆ x ∈ D, ⨅ a, radiusAffineRemainderSeminorm U D γ L x a

/-- Even the truncated affine infimum selects the same diagonal derivative:
only arbitrarily short coordinate rays inside D are used in its proof. -/
theorem radiusAffineRemainderSeminorm_iInf_eq
    (U : ParabolicSpace × ParabolicSpace → ℝ) (hU : ContDiff ℝ ∞ U)
    (D : Set ParabolicSpace) (hD : IsOpen D) {γ L : ℝ} (hγ : 1 < γ) (hL : 0 < L)
    {x : ParabolicSpace} (hx : x ∈ D) :
    (⨅ a, radiusAffineRemainderSeminorm U D γ L x a) =
      radiusAffineRemainderSeminorm U D γ L x (diagonalSpatialCoefficient U x) := by
  apply le_antisymm (iInf_le _ _)
  apply le_iInf
  intro a
  by_cases hfinite : radiusAffineRemainderSeminorm U D γ L x a = ⊤
  · rw [hfinite]
    exact le_top
  · have hc : Continuous (fun y => pdist x y) := by unfold pdist; fun_prop
    have hE : IsOpen (D ∩ {y | pdist x y < L}) :=
      hD.inter (isOpen_lt hc continuous_const)
    have hxE : x ∈ D ∩ {y | pdist x y < L} := ⟨hx, by simpa [pdist] using hL⟩
    have he := diagonalSpatialCoefficient_eq_on_open U hU _ hE hxE a hγ
      (fun y hy hne => affineRemainderSeminorm_bound U
        (D ∩ {y | pdist x y ≤ L}) γ x a hfinite ⟨hy.1, (show pdist x y < L from hy.2).le⟩ hne)
    rw [he]

/-- The actual truncated source norm is attained by the diagonal derivative. -/
theorem radiusAffineSeminorm_eq_diagonalSpatialCoefficient
    (U : ParabolicSpace × ParabolicSpace → ℝ) (hU : ContDiff ℝ ∞ U)
    (D : Set ParabolicSpace) (hD : IsOpen D) {γ L : ℝ} (hγ : 1 < γ) (hL : 0 < L) :
    radiusAffineSeminorm U D γ L =
      ⨆ x ∈ D, radiusAffineRemainderSeminorm U D γ L x (diagonalSpatialCoefficient U x) := by
  apply iSup_congr
  intro x
  apply iSup_congr
  intro hx
  exact radiusAffineRemainderSeminorm_iInf_eq U hU D hD hγ hL hx

/-- Extract only the radius-local remainder estimate; there is no claim for
pairs farther than L. -/
theorem radiusAffineSeminorm_remainder_bound
    (U : ParabolicSpace × ParabolicSpace → ℝ) (hU : ContDiff ℝ ∞ U)
    (D : Set ParabolicSpace) (hD : IsOpen D) {γ L A : ℝ} (hγ : 1 < γ) (hL : 0 < L)
    (hA : 0 ≤ A) (hnorm : radiusAffineSeminorm U D γ L ≤ ENNReal.ofReal A)
    {x y : ParabolicSpace} (hx : x ∈ D) (hy : y ∈ D) (hxy : pdist x y ≤ L) (hne : y ≠ x) :
    |U (x, y) - ∑ j, diagonalSpatialCoefficient U x j * (y.2 j - x.2 j)| ≤
      A * pdist x y ^ γ := by
  have hall : ∀ x ∈ D,
      radiusAffineRemainderSeminorm U D γ L x (diagonalSpatialCoefficient U x) ≤ ENNReal.ofReal A := by
    simpa only [radiusAffineSeminorm_eq_diagonalSpatialCoefficient U hU D hD hγ hL,
      iSup_le_iff] using hnorm
  have hb := hall x hx
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have hreal : (radiusAffineRemainderSeminorm U D γ L x (diagonalSpatialCoefficient U x)).toReal ≤ A := by
    simpa only [ENNReal.toReal_ofReal hA] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  exact (affineRemainderSeminorm_bound U (D ∩ {y | pdist x y ≤ L}) γ x _ hfinite ⟨hy, hxy⟩ hne).trans
    (mul_le_mul_of_nonneg_right hreal (Real.rpow_nonneg (pdist_nonneg x y) _))

end GlobalPhi43.MW20
