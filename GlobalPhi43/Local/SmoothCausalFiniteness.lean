/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.SmoothSectionTaylor
public import GlobalPhi43.MW20.AffineSeminorm

/-! Standing local smoothness makes the small-past remainder finite. The
resulting derivative-dependent constant is only for finiteness; the scale
argument must remove it from the final data bound. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ContDiff

theorem diagonalCoefficient_eq_section_coordinates (U : GermPoint → ℝ) (x : ParabolicSpace)
    (hU : DifferentiableAt ℝ U (x, x)) :
    diagonalSpatialCoefficient U x = fun i => sectionSpaceDerivative U (x, x) (Pi.single i 1) := by
  funext i
  rw [diagonalSpatialCoefficient_eq_fderiv_local U x hU i]
  simp [sectionSpaceDerivative, sectionSpatialInsert]

/-- The normalized remainder is quadratic on every sufficiently short past
pair, from the actual derivatives of U and the prescribed coefficient. -/
theorem smooth_causal_quadratic (U : GermPoint → ℝ) {r d S : ℝ}
    (hS : 0 ≤ S)
    (hU : ∀ p ∈ sourceCylinder r ×ˢ sourceCylinder r, ContDiffAt ℝ ∞ U p)
    (hbound : ∀ p ∈ sourceCylinder r ×ˢ sourceCylinder r,
      |sectionTimeDerivative U p| ≤ S ∧ ‖sectionSpaceHessian U p‖ ≤ S)
    (hdiag : ∀ x ∈ sourceCylinder r, U (x, x) = 0)
    {x y : ParabolicSpace} (hx : x ∈ cylinderInterior r d) (hd : 0 < d)
    (ht : y.1 < x.1) (hcut : pdist x y ≤ d / 2) :
    |affineRemainder (fun a b => U (a, b)) (diagonalSpatialCoefficient U) x y| ≤
      8 * S * pdist x y ^ 2 := by
  have hne : y ≠ x := by intro he; subst y; exact (lt_irrefl _ ht)
  have hρ := pdist_pos_of_ne hne
  have hxD := cylinderInterior_mem_domain hd.le hx
  have hy : y ∈ pastBall x (2 * pdist x y) := ⟨by linarith, ht⟩
  have hb := source_section_taylor U (by positivity : 0 ≤ 2 * pdist x y)
    (by linarith : 2 * pdist x y ≤ d) hS hU hbound hx hy
  have he : spatialLinear (diagonalSpatialCoefficient U x) (y - x) =
      sectionSpaceDerivative U (x, x) (y.2 - x.2) := by
    rw [diagonalCoefficient_eq_section_coordinates U x ((hU _ ⟨hxD, hxD⟩).differentiableAt (by simp)),
      spatialLinear_eq_differential]
    rfl
  rw [affineRemainder, he]
  rw [hdiag x hxD, sub_zero] at hb
  convert hb using 1; ring

/-- Local smoothness supplies one finite Q on all admissible depths. Q is
not inserted into the final Schauder data; it just licenses absorption. -/
theorem exists_finite_small_past_bound (U : GermPoint → ℝ)
    {r η γ : ℝ} (hr : 0 ≤ r) (hη : 0 < η) (hηsmall : η ≤ 1 / 16)
    (hγ : 0 ≤ γ) (hγ₂ : γ ≤ 2)
    (hU : ∃ O : Set GermPoint, IsOpen O ∧
      closure (sourceCylinder r) ×ˢ closure (sourceCylinder r) ⊆ O ∧ ContDiffOn ℝ ∞ U O)
    (hdiag : ∀ x ∈ sourceCylinder r, U (x, x) = 0) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ d > 0, ∀ x ∈ cylinderInterior r d,
      ∀ y ∈ pastBall x (2 * η * d),
        |affineRemainder (fun a b => U (a, b)) (diagonalSpatialCoefficient U) x y| ≤
          Q * (pdist x y / d) ^ γ := by
  obtain ⟨S, hS, hbound⟩ := exists_source_section_bound U hr hU
  obtain ⟨O, hO, hKO, hsmooth⟩ := hU
  have hUD : ∀ p ∈ sourceCylinder r ×ˢ sourceCylinder r, ContDiffAt ℝ ∞ U p := by
    intro p hp
    exact hsmooth.contDiffAt (hO.mem_nhds (hKO ⟨subset_closure hp.1, subset_closure hp.2⟩))
  have hboundD : ∀ p ∈ sourceCylinder r ×ˢ sourceCylinder r,
      |sectionTimeDerivative U p| ≤ S ∧ ‖sectionSpaceHessian U p‖ ≤ S := by
    intro p hp
    exact hbound p ⟨subset_closure hp.1, subset_closure hp.2⟩
  refine ⟨8 * S, by positivity, fun d hd x hx y hy => ?_⟩
  have hd₁ : d < 1 := by nlinarith [hx.1, hx.2.1, sq_nonneg r]
  have hne : y ≠ x := by intro he; subst y; exact (lt_irrefl _ hy.2)
  have hρ := pdist_pos_of_ne hne
  have hcut : pdist x y ≤ d / 2 := by nlinarith [hy.1]
  have hρ₁ : pdist x y ≤ 1 := by nlinarith [hy.1]
  have hratio : pdist x y ≤ pdist x y / d := (le_div_iff₀ hd).2 (by nlinarith)
  have hpower : pdist x y ^ 2 ≤ (pdist x y / d) ^ γ := by
    calc
      _ = pdist x y ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ ≤ pdist x y ^ γ := Real.rpow_le_rpow_of_exponent_ge hρ hρ₁ hγ₂
      _ ≤ _ := Real.rpow_le_rpow hρ.le hratio hγ
  exact (smooth_causal_quadratic U hS hUD hboundD hdiag hx hd hy.2 hcut).trans
    (mul_le_mul_of_nonneg_left hpower (by positivity))

end GlobalPhi43.Local
