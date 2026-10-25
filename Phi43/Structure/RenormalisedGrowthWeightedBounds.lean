/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedPositivePolynomialTails
public import Phi43.Structure.RenormalisedExtensionModel
public import Phi43.Structure.CanonicalSmoothMomentBounds
public import RegularityStructures.Abstract.PolyGrowth.Reconstruction
public import RegularityStructures.Abstract.Model

/-!
# Polynomially weighted Pi bounds for the corrected smooth Model

The positive cancellation and global tail estimates for the explicit
renormalised lift are combined with the semigroup moment bounds to produce
the weighted `PiBoundGrowth` required by the abstract reconstruction theorem.
-/

@[expose] public noncomputable section

open Set

namespace RegularityStructures.Phi43

private theorem coord_symm_single_renormalised_growth (τ : Symbol) :
    phi43CoordinateEquiv.symm (Pi.single τ 1) = basis τ := by
  apply phi43CoordinateEquiv.injective
  simp [phi43CoordinateEquiv_basis]

private theorem positive_bounds_renormalised (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ r : ℕ, ∀ τ : Symbol,
      0 < homogeneity κ τ → homogeneity κ τ < gamma κ →
      ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x,
        |(canonicalRenormalisedModel N κ noise Cg q hg C).regPi x
            (Pi.single τ 1) t x| ≤
          K * (1 + parabolicNorm x) ^ r *
            t ^ (homogeneity κ τ / parabolicSemigroup.order) := by
  obtain ⟨A, B, hA0, hB0, r, n, hn, hb⟩ :=
    renormalisedExtensionPi_positive_weighted_two_power_bound N κ noise Cg q hg C
  let K : Symbol → ℝ := fun τ => A * parabolicSemigroup.momentConst (homogeneity κ τ) +
    B * parabolicSemigroup.momentConst n
  have hK0 (τ : Symbol) : 0 ≤ K τ :=
    add_nonneg (mul_nonneg hA0 (parabolicSemigroup.momentConst_nonneg _))
      (mul_nonneg hB0 (parabolicSemigroup.momentConst_nonneg _))
  refine ⟨∑ τ, K τ, Finset.sum_nonneg (fun τ _ => hK0 τ), r, ?_⟩
  intro τ hτ0 hτγ t ht x
  rw [canonicalRenormalisedModel_regPi N κ noise Cg q hg C x _ ht.1,
    coord_symm_single_renormalised_growth]
  have hx0 : 0 ≤ (1 + parabolicNorm x) ^ r :=
    pow_nonneg (by linarith [parabolicNorm_nonneg x]) _
  have hbn : homogeneity κ τ ≤ (n : ℝ) := by
    have hdeg := (by
      have hκ0 := κ.property.1
      have hκ1 := κ.property.2
      cases τ <;> simp only [homogeneity, gamma] at hτγ ⊢ <;> linarith :
        homogeneity κ τ ≤ 1)
    exact hdeg.trans (by exact_mod_cast hn)
  have hbound (y : ParabolicSpace) :
      |(hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x
          (basis τ) y| ≤
        ((1 + parabolicNorm x) ^ r * A) *
            parabolicNorm (y - x) ^ homogeneity κ τ +
        ((1 + parabolicNorm x) ^ r * B) *
            parabolicNorm (y - x) ^ (n : ℝ) :=
    (hb τ hτ0 hτγ x y).trans_eq (by ring)
  have hm := canonicalSmooth_apply_two_power_bound
    (renormalisedExtensionPi_growth N noise
      (canonicalNoise_polyBounded_of_derivatives noise Cg q hg) C x (basis τ)) x
    hτ0.le hbn (mul_nonneg hx0 hA0) (mul_nonneg hx0 hB0)
      hbound ht.1 ht.2
  have hm' : |parabolicSemigroup.apply t
      ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x
        (basis τ)) x| ≤
      K τ * (1 + parabolicNorm x) ^ r *
        t ^ (homogeneity κ τ / parabolicSemigroup.order) :=
    hm.trans_eq (by dsimp [K]; ring)
  exact hm'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun σ _ => hK0 σ) (Finset.mem_univ τ)) hx0)
    (Real.rpow_nonneg ht.1.le _))

private theorem bounded_growth_renormalised (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ r : ℕ, ∀ τ : Symbol, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x,
      |(canonicalRenormalisedModel N κ noise Cg q hg C).regPi x
          (Pi.single τ 1) t x| ≤ K * (1 + parabolicNorm x) ^ r := by
  obtain ⟨D, hD0, a, b, hD⟩ :=
    renormalisedExtensionPi_global_polynomial_envelope N κ noise Cg q hg C
  obtain ⟨M, hM⟩ := exists_kernelPowMoment_le b
  have hM' : ∀ t : ℝ, 0 < t → t ≤ 1 → kernelPowMoment b t ≤ max M 0 :=
    fun t ht ht1 => (hM t ht ht1).trans (le_max_left _ _)
  refine ⟨D * max M 0, mul_nonneg hD0 (le_max_right _ _), a + b, ?_⟩
  intro τ t ht x
  rw [canonicalRenormalisedModel_regPi N κ noise Cg q hg C x _ ht.1,
    coord_symm_single_renormalised_growth]
  have hb (y : ParabolicSpace) :
      |(hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x
          (basis τ) y| ≤
        (D * (1 + parabolicNorm x) ^ a) *
          (1 + parabolicNorm y) ^ b := hD τ x y
  have hm := abs_apply_le_of_kernelPowMoment_le
    (renormalisedExtensionPi_smooth N noise C x (basis τ)).continuous.measurable hb
      hM' ht.1 ht.2 x
  exact hm.trans_eq (by rw [pow_add]; ring)

theorem canonicalRenormalisedModel_piBoundGrowth (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ q' : ℕ,
      (canonicalRenormalisedModel N κ noise Cg q hg C).PiBoundGrowth (gamma κ) B
        (fun z => (1 + parabolicNorm z) ^ q') := by
  obtain ⟨A, hA0, a, hA⟩ := positive_bounds_renormalised N κ noise Cg q hg C
  obtain ⟨B, hB0, b, hB⟩ := bounded_growth_renormalised N κ noise Cg q hg C
  refine ⟨A + B, add_nonneg hA0 hB0, max a b, ?_⟩
  intro τ hτ t ht x
  have hx1 : 1 ≤ 1 + parabolicNorm x := by linarith [parabolicNorm_nonneg x]
  have hx0 : 0 ≤ (1 + parabolicNorm x) ^ max a b :=
    pow_nonneg (zero_le_one.trans hx1) _
  have hpa := pow_le_pow_right₀ hx1 (le_max_left a b)
  have hpb := pow_le_pow_right₀ hx1 (le_max_right a b)
  by_cases hpos : 0 < homogeneity κ τ
  · exact (hA τ hpos hτ t ht x).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (le_add_of_nonneg_right hB0) hpa
        (pow_nonneg (zero_le_one.trans hx1) _)
        (add_nonneg hA0 hB0)) (Real.rpow_nonneg ht.1.le _))
  · have hh := (hB τ t ht x).trans
      (mul_le_mul (le_add_of_nonneg_left hA0) hpb
        (pow_nonneg (zero_le_one.trans hx1) _)
        (add_nonneg hA0 hB0))
    exact hh.trans (le_mul_of_one_le_right (mul_nonneg (add_nonneg hA0 hB0) hx0)
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2
        (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hpos)
          parabolicSemigroup.order_pos.le)))

end RegularityStructures.Phi43

end
