module

public import GlobalPhi43.MW20.CoefficientNormBridges
public import GlobalPhi43.MW20.ParabolicAffineFiniteness
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import GlobalPhi43.MW20.SmoothAffineCoefficient
public import GlobalPhi43.MW20.DyadicKernelSupport
public import GlobalPhi43.Local.SmoothingComparison
public import GlobalPhi43.MW20.AffineSeminorm
public import GlobalPhi43.MW20.SourceAffineCoefficient

/-! Finiteness of the full and radius-truncated affine seminorms for smooth
diagonal-normalized fields on bounded domains. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set
open scoped ENNReal ContDiff

/-- Both actual affine seminorms are finite for smooth diagonal-normalized
fields on bounded domains. No openness, optimality field or finite-norm
premise is needed; the actual infimum is bounded by the canonical field. -/
theorem smooth_affine_seminorms_finite
    (U : ParabolicSpace × ParabolicSpace → ℝ) (hU : ContDiff ℝ ∞ U)
    (D : Set ParabolicSpace) (R : ℝ) (hD : D ⊆ Metric.closedBall 0 R)
    {γ : ℝ} (hγ : 0 ≤ γ) (hγ2 : γ ≤ 2) (hdiag : ∀ x ∈ D, U (x, x) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ localAffineSeminorm U D γ ≤ ENNReal.ofReal C ∧
      ∀ L : ℝ, radiusAffineSeminorm U D γ L ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hb⟩ := parabolic_affine_remainder_finite_bound U hU R hγ hγ2
  have hpoint : ∀ x ∈ D, ∀ y ∈ D,
      |U (x, y) - ∑ i, diagonalSpatialCoefficient U x i * (y.2 i - x.2 i)| ≤
        C * Local.pdist x y ^ γ := by
    intro x hx y hy
    simpa only [hdiag x hx, sub_zero] using hb x (hD hx) y (hD hy)
  refine ⟨C, hC, ?_, ?_⟩
  · simp only [localAffineSeminorm, iSup_le_iff]
    intro x hx
    apply (iInf_le (fun ν => affineRemainderSeminorm U D γ x ν)
      (diagonalSpatialCoefficient U x)).trans
    simp only [affineRemainderSeminorm, iSup_le_iff]
    intro y hy hne
    apply ENNReal.ofReal_le_ofReal
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (pdist_pos_of_ne hne) γ)).2 (hpoint x hx y hy)
  · intro L
    exact radiusAffineSeminorm_le_of_remainder_bound U D (diagonalSpatialCoefficient U) γ L C
      (fun x hx y hy _ _ => hpoint x hx y hy)

/-- Finiteness of the actual full norm, with no source estimate assumed. -/
theorem localAffineSeminorm_ne_top_of_smooth
    (U : ParabolicSpace × ParabolicSpace → ℝ) (hU : ContDiff ℝ ∞ U)
    (D : Set ParabolicSpace) (R : ℝ) (hD : D ⊆ Metric.closedBall 0 R)
    {γ : ℝ} (hγ : 0 ≤ γ) (hγ2 : γ ≤ 2) (hdiag : ∀ x ∈ D, U (x, x) = 0) :
    localAffineSeminorm U D γ ≠ ⊤ := by
  obtain ⟨C, _, hC, _⟩ := smooth_affine_seminorms_finite U hU D R hD hγ hγ2 hdiag
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hC

/-- Finiteness of every actual radius-local norm, including empty domains. -/
theorem radiusAffineSeminorm_ne_top_of_smooth
    (U : ParabolicSpace × ParabolicSpace → ℝ) (hU : ContDiff ℝ ∞ U)
    (D : Set ParabolicSpace) (R : ℝ) (hD : D ⊆ Metric.closedBall 0 R)
    {γ : ℝ} (hγ : 0 ≤ γ) (hγ2 : γ ≤ 2) (hdiag : ∀ x ∈ D, U (x, x) = 0) (L : ℝ) :
    radiusAffineSeminorm U D γ L ≠ ⊤ := by
  obtain ⟨C, _, _, hC⟩ := smooth_affine_seminorms_finite U hU D R hD hγ hγ2 hdiag
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC L)

end GlobalPhi43.MW20
