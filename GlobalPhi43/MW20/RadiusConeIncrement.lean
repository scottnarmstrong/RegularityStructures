module

public import GlobalPhi43.MW20.AffineThreePoint
public import GlobalPhi43.MW20.SourceConeEstimate

/-! The near-pair coefficient increment from radius-local residuals. All
three residual pairs are proved to lie within the supplied radius L. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set

/-- A cone witness at distance δ uses residuals only up to 2δ, yielding
a radius-local coefficient increment bound. -/
theorem radius_cone_holder_increment
    (U : ParabolicSpace × ParabolicSpace → ℝ) (D : Set ParabolicSpace)
    (ν : ParabolicSpace → Fin 3 → ℝ)
    {γ β L r₀ lam A M : ℝ} (hγ : 0 ≤ γ) (hA : 0 ≤ A)
    (hcone : SpatialInteriorCone D r₀ lam)
    (hres : ∀ x ∈ D, ∀ y ∈ D, pdist x y ≤ L →
      |U (x, y) - spatialPair (ν x) x y| ≤ A * pdist x y ^ γ)
    (hthree : ∀ x ∈ D, ∀ z ∈ D, ∀ y ∈ D,
      pdist x z ≤ L / 2 → pdist z y ≤ L / 2 →
      |U (x, y) - U (x, z) - U (z, y)| ≤ M * pdist x z ^ β * pdist z y ^ (γ - β))
    {x z : ParabolicSpace} (hx : x ∈ D) (hz : z ∈ D)
    (hδ : 0 < pdist x z) (hδr : pdist x z ≤ r₀) (hδL : pdist x z ≤ L / 2) :
    lam * ‖ν x - ν z‖ ≤ ((2 ^ γ + 2) * A + M) * pdist x z ^ (γ - 1) := by
  obtain ⟨y, hy, hd, hpair⟩ := hcone (pdist x z) hδ hδr z hz (ν x - ν z)
  have hdist : pdist x y ≤ 2 * pdist x z := by
    have hh := pdist_triangle x z y
    linarith
  have hxyL : pdist x y ≤ L := by linarith
  have hxzL : pdist x z ≤ L := by linarith
  have hzyL : pdist z y ≤ L := hd.le.trans hxzL
  have hpow : pdist x y ^ γ ≤ 2 ^ γ * pdist x z ^ γ := by
    calc
      _ ≤ (2 * pdist x z) ^ γ := Real.rpow_le_rpow (pdist_nonneg x y) hdist hγ
      _ = _ := Real.mul_rpow (by norm_num) (pdist_nonneg x z)
  have hprod : pdist x z ^ β * pdist x z ^ (γ - β) = pdist x z ^ γ := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have hthree' : |U (x, y) - U (x, z) - U (z, y)| ≤ M * pdist x z ^ γ := by
    simpa only [hd, mul_assoc, hprod] using hthree x hx z hz y hy hδL (by simpa only [hd] using hδL)
  have hb := affine_three_remainder_bound U ν x z y
    (hres x hx y hy hxyL) (hres x hx z hz hxzL) (hres z hz y hy hzyL) hthree'
  rw [hd] at hb
  have hbound : lam * ‖ν x - ν z‖ * pdist x z ≤
      ((2 ^ γ + 2) * A + M) * pdist x z ^ γ := by
    apply hpair.trans
    change |spatialPair (ν x - ν z) z y| ≤ _
    apply hb.trans
    nlinarith only [mul_le_mul_of_nonneg_left hpow hA]
  have hh := (le_div_iff₀ hδ).2 hbound
  rw [Real.rpow_sub_one hδ.ne']
  simpa only [mul_div_assoc] using hh

end GlobalPhi43.MW20
