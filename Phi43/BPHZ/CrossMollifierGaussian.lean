/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.CrossMollifierCovariance

/-!
# Gaussian vectors of the tree `Ψ` with several mollifiers

Any finite family `(Ψ_{ρ_i,ε_i}(z_i))_i`, where coordinate `i` is built from its own mollifier
`ρ_i`, scale `ε_i` and regularised noise `ξ_i`, all driven by the same white noise `W`, is a
centred Gaussian vector with covariance `Q(K_{ρ_i,ε_i}, K_{ρ_j,ε_j})(z_i - z_j)`, i.e.
`hairerCrossCovarianceTwo N (ρ i) (ε i) (ρ j) (ε j) (z i - z j)`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}

/-- `∫ K_{ρ,ε}(z - w) K_{ρ',ε'}(z' - w) dw = Q(K_{ρ,ε}, K_{ρ',ε'})(z - z')`. -/
theorem integral_hairerMollifiedKernel_sub_mul_crossTwo (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ)
    (ε ε' : ℝ) (z z' : SpaceTime) :
    ∫ w, hairerMollifiedKernel N ρ ε (z - w) * hairerMollifiedKernel N ρ' ε' (z' - w) =
      hairerCrossCovarianceTwo N ρ ε ρ' ε' (z - z') := by
  have h := integral_comp_sub_left_spaceTime
    (fun v => hairerMollifiedKernel N ρ ε (z - z' + v) * hairerMollifiedKernel N ρ' ε' v) z'
  simp only [sub_add_sub_cancel] at h
  rw [hairerCrossCovarianceTwo, h]

/-- **Multiscale, multi-mollifier Gaussian vector of the tree `Ψ`.**  The vector
`(Ψ_{ρ i, ε i}(z i))_i` built from regularised noises `ξ i` of the same white noise is a centred
Gaussian vector with covariance `hairerCrossCovarianceTwo N (ρ i) (ε i) (ρ j) (ε j) (z i - z j)`. -/
theorem hairerPsiField_isCentredGaussianVector_multiscaleTwo (N : ℕ) {n : ℕ}
    {ρ : Fin n → ℝ × (Fin 3 → ℝ) → ℝ} {ε : Fin n → ℝ} {ξ : Fin n → Ω → SpaceTime → ℝ}
    (hρ : ∀ i, IsMollifier (ρ i)) (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) (z : Fin n → SpaceTime) :
    IsCentredGaussianVector P (fun ω i => hairerPsiField N (ξ i) ω (z i))
      (fun i j => hairerCrossCovarianceTwo N (ρ i) (ε i) (ρ j) (ε j) (z i - z j)) := by
  have hG := hW.2 n (fun i w => hairerMollifiedKernel N (ρ i) (ε i) (z i - w))
    (fun i => memLp_hairerMollifiedKernel_sub N (hρ i) (hε i) (z i))
  have hC : (fun i j => ∫ w, hairerMollifiedKernel N (ρ i) (ε i) (z i - w) *
      hairerMollifiedKernel N (ρ j) (ε j) (z j - w)) =
      fun i j => hairerCrossCovarianceTwo N (ρ i) (ε i) (ρ j) (ε j) (z i - z j) :=
    funext fun i => funext fun j => integral_hairerMollifiedKernel_sub_mul_crossTwo N _ _ _ _ _ _
  rw [hC] at hG
  refine hG.of_ae_eq ?_
  have hall : ∀ᵐ ω ∂P, ∀ i, hairerPsiField N (ξ i) ω (z i) =
      W (fun w => hairerMollifiedKernel N (ρ i) (ε i) (z i - w)) ω :=
    ae_all_iff.2 fun i => hairerPsiField_ae_eq N (hρ i) (hε i) hW (hξ i) (z i)
  filter_upwards [hall] with ω hω
  exact (funext hω).symm

/-- **Two-mollifier Gaussian pair**: `(Ψ_{ρ,ε}(z), Ψ_{ρ',ε'}(z'))` is a centred Gaussian vector
with covariance entries given by `hairerCrossCovarianceTwo`. -/
theorem hairerPsiField_isCentredGaussianVector_two_mollifier (N : ℕ)
    {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ} (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    (hε : 0 < ε) (hε' : 0 < ε') {ξ ξ' : Ω → SpaceTime → ℝ} (hW : IsWhiteNoise P W)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (hξ' : IsRegularisedNoise P W ρ' ε' ξ')
    (z z' : SpaceTime) :
    IsCentredGaussianVector P
      (fun ω => ![hairerPsiField N ξ ω z, hairerPsiField N ξ' ω z'])
      (fun i j => hairerCrossCovarianceTwo N (![ρ, ρ'] i) (![ε, ε'] i) (![ρ, ρ'] j) (![ε, ε'] j)
        (![z, z'] i - ![z, z'] j)) := by
  have h := hairerPsiField_isCentredGaussianVector_multiscaleTwo N (ρ := ![ρ, ρ']) (ε := ![ε, ε'])
    (ξ := ![ξ, ξ']) (z := ![z, z']) (fun i => by fin_cases i <;> simpa)
    (fun i => by fin_cases i <;> simpa) hW (fun i => by fin_cases i <;> simpa)
  refine h.of_ae_eq (Filter.Eventually.of_forall fun ω => ?_)
  funext i
  fin_cases i <;> rfl

end RegularityStructures.Phi43

end
