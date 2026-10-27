module

public import GlobalPhi43.MW20.RadiusAffineSeminorm
public import GlobalPhi43.MW20.RadiusHolderSeminorm
public import GlobalPhi43.MW20.RadiusConeIncrement
public import GlobalPhi43.MW20.CylinderCoefficientBounds

/-! Full coefficient Holder control from radius-local U control. Far pairs
are bounded by the local cone estimate for the coefficient supremum; no
unrestricted U norm is asserted or used. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set
open scoped ENNReal ContDiff

/-- Both coefficient bounds from genuinely radius-local residual control. -/
theorem radius_cone_coefficient_bounds_global
    (U : ParabolicSpace × ParabolicSpace → ℝ) (D : Set ParabolicSpace)
    (ν : ParabolicSpace → Fin 3 → ℝ)
    {γ β L r₀ r A B M : ℝ} (hγ : 1 < γ) (hne : D.Nonempty)
    (hr : 0 < r) (hrr : r ≤ r₀) (hrL : r ≤ L / 2)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hcone : SpatialInteriorCone D r₀ (1 / 2))
    (hsup : localTwoPointSup U D r ≤ ENNReal.ofReal B)
    (hres : ∀ x ∈ D, ∀ y ∈ D, pdist x y ≤ L →
      |U (x, y) - spatialPair (ν x) x y| ≤ A * pdist x y ^ γ)
    (hthree : ∀ x ∈ D, ∀ z ∈ D, ∀ y ∈ D,
      pdist x z ≤ L / 2 → pdist z y ≤ L / 2 →
      |U (x, y) - U (x, z) - U (z, y)| ≤ M * pdist x z ^ β * pdist z y ^ (γ - β)) :
    BddAbove ((fun x => ‖ν x‖) '' D) ∧
      (1 / 2 : ℝ) * sSup ((fun x => ‖ν x‖) '' D) ≤ A * r ^ (γ - 1) + B / r ∧
      localCoefficientHolderSeminorm ν D (γ - 1) ≤
        ENNReal.ofReal (2 * (2 ^ γ + 4) * (A + M + r ^ (-γ) * B)) := by
  have hrL' : r ≤ L := by linarith
  have hc := cone_estimate_sup D hne ν (fun x y => U (x, y))
    (fun a x y => spatialPair a x y) pdist hr (by norm_num) (hcone r hr hrr)
    (fun x hx y hy hd => by simpa only [hd] using hres x hx y hy (hd.le.trans hrL'))
    (fun x hx y hy hd => localTwoPointSup_bound U D r hB hsup hx hy hd.le)
  have hpoint : ∀ x ∈ D, (1 / 2 : ℝ) * ‖ν x‖ ≤ A * r ^ (γ - 1) + B / r := by
    intro x hx
    exact (mul_le_mul_of_nonneg_left (le_csSup hc.1 ⟨x, hx, rfl⟩) (by norm_num)).trans hc.2
  refine ⟨hc.1, hc.2, ?_⟩
  have hh : localCoefficientHolderSeminorm ν D (γ - 1) ≤
      ENNReal.ofReal (((2 ^ γ + 4) * A + M + 2 * B * r ^ (-γ)) / (1 / 2)) := by
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    apply iSup_le
    intro z
    apply iSup_le
    intro hz
    apply iSup_le
    intro hcut
    apply ENNReal.ofReal_le_ofReal
    have hδ := pdist_pos_of_ne hcut
    have htotal : (1 / 2 : ℝ) * ‖ν x - ν z‖ ≤
        ((2 ^ γ + 4) * A + M + 2 * B * r ^ (-γ)) * pdist x z ^ (γ - 1) := by
      by_cases hnear : pdist x z ≤ r
      · have hn := radius_cone_holder_increment U D ν (by linarith) hA hcone hres hthree
          hx hz hδ (hnear.trans hrr) (hnear.trans hrL)
        apply hn.trans
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hδ.le _)
        have hb : 0 ≤ B * r ^ (-γ) := mul_nonneg hB (Real.rpow_nonneg hr.le _)
        linarith
      · have hf := cone_holder_far_pair ν hγ.le hr (by norm_num) hA hB
          (le_of_not_ge hnear) (hpoint x hx) (hpoint z hz)
        apply hf.trans
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hδ.le _)
        have hp := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) γ
        nlinarith
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 1 / 2)).2
    rw [mul_comm, ← mul_div_assoc]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hδ _)).2 htotal
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  have hp := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) γ
  have hb : 0 ≤ B * r ^ (-γ) := mul_nonneg hB (Real.rpow_nonneg hr.le _)
  nlinarith [mul_nonneg hp hM, mul_nonneg hp hb]

/-- Finite radius-local source bounds control the selected coefficient
and its Hölder seminorm, without a separate finiteness assumption or an
unrestricted affine norm. -/
theorem radius_cylinder_coefficient_bounds_global
    (U : ParabolicSpace × ParabolicSpace → ℝ) (hU : ContDiff ℝ ∞ U)
    {R d γ β L r A B M : ℝ} (hR : R < 1 / 2) (hγ : 1 < γ)
    (hne : (cylinderInterior R d).Nonempty) (hr : 0 < r) (hrr : r ≤ 1 / 2 - d) (hrL : r ≤ L / 2)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hdiag : ∀ x ∈ cylinderInterior R d, U (x, x) = 0)
    (hnorm : radiusAffineSeminorm U (cylinderInterior R d) γ L ≤ ENNReal.ofReal A)
    (hsup : localTwoPointSup U (cylinderInterior R d) r ≤ ENNReal.ofReal B)
    (hthree : ∀ x ∈ cylinderInterior R d, ∀ z ∈ cylinderInterior R d,
      ∀ y ∈ cylinderInterior R d, pdist x z ≤ L / 2 → pdist z y ≤ L / 2 →
      |U (x, y) - U (x, z) - U (z, y)| ≤ M * pdist x z ^ β * pdist z y ^ (γ - β)) :
    BddAbove ((fun x => ‖diagonalSpatialCoefficient U x‖) '' cylinderInterior R d) ∧
      (1 / 2 : ℝ) * sSup ((fun x => ‖diagonalSpatialCoefficient U x‖) '' cylinderInterior R d) ≤
        A * r ^ (γ - 1) + B / r ∧
      localCoefficientHolderSeminorm (diagonalSpatialCoefficient U) (cylinderInterior R d) (γ - 1) ≤
        ENNReal.ofReal (2 * (2 ^ γ + 4) * (A + M + r ^ (-γ) * B)) := by
  apply radius_cone_coefficient_bounds_global U _ _ hγ hne hr hrr hrL hA hB hM
    (cylinderInterior_spatialInteriorCone hR) hsup ?_ hthree
  intro x hx y hy hxy
  by_cases he : y = x
  · subst y
    simp only [spatialPair, sub_self, mul_zero, Finset.sum_const_zero, hdiag x hx, abs_zero]
    exact mul_nonneg hA (Real.rpow_nonneg (pdist_nonneg x x) γ)
  · simpa only [spatialPair] using radiusAffineSeminorm_remainder_bound U hU _
      (isOpen_cylinderInterior R d) hγ (by linarith) hA hnorm hx hy hxy he

end GlobalPhi43.MW20
