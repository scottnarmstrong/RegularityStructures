/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreePsiField
public import RegularityStructures.Probability.WhiteNoise

/-!
# The tree `Ψ` is a centred Gaussian field

Any finite family `(Ψ_{ε_i}(z_i))_i` of values of the tree `Ψ` at (possibly different) scales and
points is a centred Gaussian vector with covariance given by the cross covariance
`∫ K_{ε_i}(z_i - w) K_{ε_j}(z_j - w) dw = Q_{ε_i, ε_j}(z_i - z_j)`.  This is derived from
`IsWhiteNoise` and the almost sure identities `Ψ(z) = W (K_ε(z - ·))`, using that being a centred
Gaussian vector is stable under almost everywhere modification.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- The cross covariance `Q_{ε, ε'}(x) = ∫ K_ε(x + w) K_ε'(w) dw` of two scales of the mollified
kernel; for `ε = ε'` it is `hairerCovariance`. -/
def hairerCrossCovariance (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε ε' : ℝ) (x : SpaceTime) : ℝ :=
  ∫ w, hairerMollifiedKernel N ρ ε (x + w) * hairerMollifiedKernel N ρ ε' w

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} {X X' : Ω → Fin n → ℝ}
  {C : Fin n → Fin n → ℝ}

/-- Being a centred Gaussian vector with covariance `C` is stable under almost everywhere
modification. -/
theorem IsCentredGaussianVector.of_ae_eq (h : IsCentredGaussianVector P X C)
    (hX : X =ᵐ[P] X') : IsCentredGaussianVector P X' C := by
  obtain ⟨hm, hg, h0, hC⟩ := h
  have hmap : P.map X' = P.map X := (Measure.map_congr hX).symm
  refine ⟨hm.congr hX, by rw [hmap]; exact hg, fun i => ?_, fun i j => ?_⟩
  · rw [← h0 i]
    refine integral_congr_ae ?_
    filter_upwards [hX] with ω hω
    rw [hω]
  · rw [← hC i j]
    refine integral_congr_ae ?_
    filter_upwards [hX] with ω hω
    rw [hω]

end RegularityStructures

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ}

/-- `hairerCrossCovariance N ρ ε ε = hairerCovariance N ρ ε`. -/
theorem hairerCrossCovariance_self (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) :
    hairerCrossCovariance N ρ ε ε = hairerCovariance N ρ ε := rfl

/-- `∫ K_ε(z - w) K_ε'(z' - w) dw = Q_{ε,ε'}(z - z')`. -/
theorem integral_hairerMollifiedKernel_sub_mul_cross (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (ε ε' : ℝ) (z z' : SpaceTime) :
    ∫ w, hairerMollifiedKernel N ρ ε (z - w) * hairerMollifiedKernel N ρ ε' (z' - w) =
      hairerCrossCovariance N ρ ε ε' (z - z') := by
  have h := integral_comp_sub_left_spaceTime
    (fun v => hairerMollifiedKernel N ρ ε (z - z' + v) * hairerMollifiedKernel N ρ ε' v) z'
  simp only [sub_add_sub_cancel] at h
  rw [hairerCrossCovariance, h]

/-- **Multiscale Gaussian vector of the tree `Ψ`.** For finitely many points `z i` and scales
`ε i`, the vector `(Ψ_{ε i}(z i))_i` is a centred Gaussian vector with covariance
`Q_{ε i, ε j}(z i - z j)`. -/
theorem hairerPsiField_isCentredGaussianVector_multiscale (N : ℕ) (hρ : IsMollifier ρ) {n : ℕ}
    {ε : Fin n → ℝ} {ξ : Fin n → Ω → SpaceTime → ℝ} (hε : ∀ i, 0 < ε i)
    (hW : IsWhiteNoise P W) (hξ : ∀ i, IsRegularisedNoise P W ρ (ε i) (ξ i))
    (z : Fin n → SpaceTime) :
    IsCentredGaussianVector P (fun ω i => hairerPsiField N (ξ i) ω (z i))
      (fun i j => hairerCrossCovariance N ρ (ε i) (ε j) (z i - z j)) := by
  have hG := hW.2 n (fun i w => hairerMollifiedKernel N ρ (ε i) (z i - w))
    (fun i => memLp_hairerMollifiedKernel_sub N hρ (hε i) (z i))
  have hC : (fun i j => ∫ w, hairerMollifiedKernel N ρ (ε i) (z i - w) *
      hairerMollifiedKernel N ρ (ε j) (z j - w)) =
      fun i j => hairerCrossCovariance N ρ (ε i) (ε j) (z i - z j) :=
    funext fun i => funext fun j => integral_hairerMollifiedKernel_sub_mul_cross N ρ _ _ _ _
  rw [hC] at hG
  refine hG.of_ae_eq ?_
  have hall : ∀ᵐ ω ∂P, ∀ i, hairerPsiField N (ξ i) ω (z i) =
      W (fun w => hairerMollifiedKernel N ρ (ε i) (z i - w)) ω :=
    ae_all_iff.2 fun i => hairerPsiField_ae_eq N hρ (hε i) hW (hξ i) (z i)
  filter_upwards [hall] with ω hω
  exact (funext hω).symm

/-- **Gaussian vector of the tree `Ψ`** at one scale: `(Ψ_ε(z i))_i` is a centred Gaussian vector
with covariance `Q_ε(z i - z j)`. -/
theorem hairerPsiField_isCentredGaussianVector (N : ℕ) {ε : ℝ} (hρ : IsMollifier ρ)
    (hε : 0 < ε) {ξ : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W)
    (hξ : IsRegularisedNoise P W ρ ε ξ) {m : ℕ} (z : Fin m → SpaceTime) :
    IsCentredGaussianVector P (fun ω i => hairerPsiField N ξ ω (z i))
      (fun i j => hairerCovariance N ρ ε (z i - z j)) :=
  hairerPsiField_isCentredGaussianVector_multiscale N hρ (ε := fun _ => ε) (ξ := fun _ => ξ)
    (fun _ => hε) hW (fun _ => hξ) z

/-- **Two-scale Gaussian vector**: the pair `(Ψ_ε(z), Ψ_ε'(z'))` is a centred Gaussian vector with
covariance entries `Q_{ε,ε'}(z - z')` off the diagonal (cross covariance `∫ K_ε(z - w) K_ε'(z' - w)`).
General families are covered by `hairerPsiField_isCentredGaussianVector_multiscale`. -/
theorem hairerPsiField_isCentredGaussianVector_two_scale (N : ℕ) {ε ε' : ℝ} (hρ : IsMollifier ρ)
    (hε : 0 < ε) (hε' : 0 < ε') {ξ ξ' : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hξ' : IsRegularisedNoise P W ρ ε' ξ')
    (z z' : SpaceTime) :
    IsCentredGaussianVector P
      (fun ω => ![hairerPsiField N ξ ω z, hairerPsiField N ξ' ω z'])
      (fun i j => hairerCrossCovariance N ρ (![ε, ε'] i) (![ε, ε'] j) (![z, z'] i - ![z, z'] j)) := by
  have h := hairerPsiField_isCentredGaussianVector_multiscale N hρ (ε := ![ε, ε'])
    (ξ := ![ξ, ξ']) (z := ![z, z']) (fun i => by fin_cases i <;> simpa) hW
    (fun i => by fin_cases i <;> simpa)
  refine h.of_ae_eq (Filter.Eventually.of_forall fun ω => ?_)
  funext i
  fin_cases i <;> rfl

end RegularityStructures.Phi43

end
