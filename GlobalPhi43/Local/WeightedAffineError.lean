/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.SmoothSectionTaylor

/-! The actual weighted affine-error quantity used by the first absorption. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ENNReal ContDiff

def weightedPastAffineError (U : GermPoint → ℝ) (r d₀ θ γ : ℝ) : ℝ≥0∞ :=
  ⨆ d ∈ Ioc (0 : ℝ) d₀, ⨆ x ∈ cylinderInterior r d, ⨆ R ∈ Ioc (0 : ℝ) (θ * d),
    ENNReal.ofReal (d ^ γ / R ^ γ) * pastAffineError (fun y => U (x, y)) x R

/-- A quadratic bound makes the actual weighted affine error finite; the
parabolic exponents only require 0<=gamma<=2. -/
theorem weightedPastAffineError_le_of_quadratic (U : GermPoint → ℝ)
    {r d₀ θ γ K : ℝ} (hθ : θ ≤ 1) (hγ : 0 ≤ γ) (hγ₂ : γ ≤ 2) (hK : 0 ≤ K)
    (herror : ∀ d ∈ Ioc (0 : ℝ) d₀, ∀ x ∈ cylinderInterior r d,
      ∀ R ∈ Ioc (0 : ℝ) (θ * d), pastAffineError (fun y => U (x, y)) x R ≤ ENNReal.ofReal (K * R ^ 2)) :
    weightedPastAffineError U r d₀ θ γ ≤ ENNReal.ofReal K := by
  apply iSup_le
  intro d
  apply iSup_le
  intro hd
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply iSup_le
  intro R
  apply iSup_le
  intro hR
  have hd₁ : d ≤ 1 := by nlinarith [hx.1, hx.2.1, sq_nonneg r]
  have hRd : R ≤ d := hR.2.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hθ hd.1.le)
  have hR₁ : R ≤ 1 := hRd.trans hd₁
  have hpd : d ^ γ ≤ 1 := Real.rpow_le_one hd.1.le hd₁ hγ
  have hpR : R ^ (2 - γ) ≤ 1 := Real.rpow_le_one hR.1.le hR₁ (by linarith)
  have hpower : d ^ γ * R ^ (2 - γ) ≤ 1 := by
    have hh := mul_le_mul hpd hpR (Real.rpow_nonneg hR.1.le (2 - γ)) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have heq : (d ^ γ / R ^ γ) * (K * R ^ 2) = K * (d ^ γ * R ^ (2 - γ)) := by
    rw [Real.rpow_sub hR.1, Real.rpow_two]
    ring
  calc
    _ ≤ ENNReal.ofReal (d ^ γ / R ^ γ) * ENNReal.ofReal (K * R ^ 2) :=
      mul_le_mul le_rfl (herror d hd x hx R hR) (by positivity) (by positivity)
    _ = ENNReal.ofReal ((d ^ γ / R ^ γ) * (K * R ^ 2)) := by
      rw [ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg hd.1.le _) (Real.rpow_nonneg hR.1.le _))]
    _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal (by
      rw [heq]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpower hK)

/-- Finiteness of the actual affine-error supremum is a consequence of the
source local smoothness, never an additional theorem hypothesis. -/
theorem weightedPastAffineError_ne_top (U : GermPoint → ℝ)
    {r d₀ θ γ : ℝ} (hr : 0 ≤ r) (hθ : θ ≤ 1) (hγ : 0 ≤ γ) (hγ₂ : γ ≤ 2)
    (hU : ∃ O : Set GermPoint, IsOpen O ∧
      closure (sourceCylinder r) ×ˢ closure (sourceCylinder r) ⊆ O ∧ ContDiffOn ℝ ∞ U O) :
    weightedPastAffineError U r d₀ θ γ ≠ ⊤ := by
  obtain ⟨S, hS, hbound⟩ := exists_source_section_bound U hr hU
  obtain ⟨O, hO, hKO, hsmooth⟩ := hU
  have hUD : ∀ p ∈ sourceCylinder r ×ˢ sourceCylinder r, ContDiffAt ℝ ∞ U p := by
    intro p hp
    exact hsmooth.contDiffAt (hO.mem_nhds (hKO ⟨subset_closure hp.1, subset_closure hp.2⟩))
  have hboundD : ∀ p ∈ sourceCylinder r ×ˢ sourceCylinder r,
      |sectionTimeDerivative U p| ≤ S ∧ ‖sectionSpaceHessian U p‖ ≤ S := by
    intro p hp
    exact hbound p ⟨subset_closure hp.1, subset_closure hp.2⟩
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  apply weightedPastAffineError_le_of_quadratic U hθ hγ hγ₂ (by positivity : 0 ≤ 2 * S)
  intro d hd x hx R hR
  have hRd : R ≤ d := hR.2.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hθ hd.1.le)
  exact source_section_affine_error U hR.1.le hRd hS hUD hboundD hx

end GlobalPhi43.Local
