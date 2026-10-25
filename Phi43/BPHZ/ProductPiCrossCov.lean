/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductPiFieldCrossPair
public import Phi43.BPHZ.ProductPiDiffBounds

/-!
# The covariance of the difference `I₂Ψ_{ρ,ε} - I₂Ψ_{ρ',ε'}`

`productISqPsiField_sub_integral_mul_cross`: with `z = y - x`, `z' = ȳ - x`,
`E[Δ(y) Δ(ȳ)] = ∫∫ a(w) b(v) (2 E₁ + 4 E₂ + 4 E₃)(w, v) dw dv`, where `a, b` are the recentred
kernels and `E₁, E₂, E₃` the second differences of the pieces of the block kernel.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem integral_integral_comb4_isq {h₁ h₂ h₃ h₄ : SpaceTime → SpaceTime → ℝ}
    (i₁ : Integrable (Function.uncurry h₁) (volume.prod volume))
    (i₂ : Integrable (Function.uncurry h₂) (volume.prod volume))
    (i₃ : Integrable (Function.uncurry h₃) (volume.prod volume))
    (i₄ : Integrable (Function.uncurry h₄) (volume.prod volume)) :
    ∫ w, ∫ v, (h₁ w v - h₂ w v - h₃ w v + h₄ w v) =
      (∫ w, ∫ v, h₁ w v) - (∫ w, ∫ v, h₂ w v) - (∫ w, ∫ v, h₃ w v) + ∫ w, ∫ v, h₄ w v := by
  have hs : Integrable (Function.uncurry fun w v => h₁ w v - h₂ w v - h₃ w v + h₄ w v)
      (volume.prod volume) := (((i₁.sub i₂).sub i₃).add i₄)
  calc ∫ w, ∫ v, (h₁ w v - h₂ w v - h₃ w v + h₄ w v)
      = ∫ p, Function.uncurry (fun w v => h₁ w v - h₂ w v - h₃ w v + h₄ w v) p
          ∂(volume.prod volume) := (integral_prod _ hs).symm
    _ = ∫ p, (Function.uncurry h₁ p - Function.uncurry h₂ p - Function.uncurry h₃ p +
          Function.uncurry h₄ p) ∂(volume.prod volume) := rfl
    _ = (∫ p, Function.uncurry h₁ p ∂(volume.prod volume)) -
          (∫ p, Function.uncurry h₂ p ∂(volume.prod volume)) -
          (∫ p, Function.uncurry h₃ p ∂(volume.prod volume)) +
          ∫ p, Function.uncurry h₄ p ∂(volume.prod volume) := by
        have j2 : Integrable (fun p => Function.uncurry h₁ p - Function.uncurry h₂ p)
            (volume.prod volume) := i₁.sub i₂
        have j3 : Integrable (fun p => Function.uncurry h₁ p - Function.uncurry h₂ p -
            Function.uncurry h₃ p) (volume.prod volume) := j2.sub i₃
        rw [integral_add j3 i₄, integral_sub j2 i₃, integral_sub i₁ i₂]
    _ = _ := by
        rw [integral_prod _ i₁, integral_prod _ i₂, integral_prod _ i₃, integral_prod _ i₄]
        rfl

variable {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}

/-- **Covariance of the difference of `I₂Ψ` at two scales.** -/
theorem productISqPsiField_sub_integral_mul_cross (N : ℕ) (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    (hε : 0 < ε)
    (hε' : 0 < ε') (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ' ε' ξ') (x y y' : SpaceTime) :
    ∫ ω, (productISqPsiField N ρ ε ξ x ω y - productISqPsiField N ρ' ε' ξ' x ω y) *
        (productISqPsiField N ρ ε ξ x ω y' - productISqPsiField N ρ' ε' ξ' x ω y') ∂P =
      ∫ a, ∫ b, (hairerKernelTorus N (y - x - a) - hairerKernelTorus N (-a)) *
        (hairerKernelTorus N (y' - x - b) - hairerKernelTorus N (-b)) *
        (2 * isqDiffE1 N ρ ρ' ε ε' (a - b) (y - x - (y' - x)) +
          4 * isqDiffE2 N ρ ρ' ε ε' (a - b) (a - (y' - x)) (y - x - b) +
          4 * isqDiffE3 N ρ ρ' ε ε' (a - (y - x)) (a - b) (b - (y' - x))) := by
  have p11 := (productISqPsiField_two_scale_pair_integrable_cross N hρ hρ hε hε hW hξ hξ x y y').1
  have p12 := (productISqPsiField_two_scale_pair_integrable_cross N hρ hρ' hε hε' hW hξ hξ' x y y').1
  have p21 := (productISqPsiField_two_scale_pair_integrable_cross N hρ' hρ hε' hε hW hξ' hξ x y y').1
  have p22 :=
    (productISqPsiField_two_scale_pair_integrable_cross N hρ' hρ' hε' hε' hW hξ' hξ' x y y').1
  have hexp : ∫ ω, (productISqPsiField N ρ ε ξ x ω y - productISqPsiField N ρ' ε' ξ' x ω y) *
        (productISqPsiField N ρ ε ξ x ω y' - productISqPsiField N ρ' ε' ξ' x ω y') ∂P =
      (∫ ω, productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ ε ξ x ω y' ∂P) -
        (∫ ω, productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ' ε' ξ' x ω y' ∂P) -
        (∫ ω, productISqPsiField N ρ' ε' ξ' x ω y * productISqPsiField N ρ ε ξ x ω y' ∂P) +
        ∫ ω, productISqPsiField N ρ' ε' ξ' x ω y * productISqPsiField N ρ' ε' ξ' x ω y' ∂P := by
    have h3 : Integrable (fun ω => productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ ε ξ x ω y' -
        productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ' ε' ξ' x ω y') P := p11.sub p12
    have h5 : Integrable (fun ω => productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ ε ξ x ω y' -
        productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ' ε' ξ' x ω y' -
        productISqPsiField N ρ' ε' ξ' x ω y * productISqPsiField N ρ ε ξ x ω y') P := h3.sub p21
    calc _ = ∫ ω, (productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ ε ξ x ω y' -
        productISqPsiField N ρ ε ξ x ω y * productISqPsiField N ρ' ε' ξ' x ω y' -
        productISqPsiField N ρ' ε' ξ' x ω y * productISqPsiField N ρ ε ξ x ω y' +
        productISqPsiField N ρ' ε' ξ' x ω y * productISqPsiField N ρ' ε' ξ' x ω y') ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
      _ = _ := by rw [integral_add h5 p22, integral_sub h3 p21, integral_sub p11 p12]
  rw [hexp, productISqPsiField_integral_mul_two_scale_cross N hρ hρ hε hε hW hξ hξ x x y y',
    productISqPsiField_integral_mul_two_scale_cross N hρ hρ' hε hε' hW hξ hξ' x x y y',
    productISqPsiField_integral_mul_two_scale_cross N hρ' hρ hε' hε hW hξ' hξ x x y y',
    productISqPsiField_integral_mul_two_scale_cross N hρ' hρ' hε' hε' hW hξ' hξ' x x y y',
    ← integral_integral_comb4_isq
      (productISqPsiField_two_scale_kernel_integrable_cross N hρ hρ hε hε hW hξ hξ x x y y')
      (productISqPsiField_two_scale_kernel_integrable_cross N hρ hρ' hε hε' hW hξ hξ' x x y y')
      (productISqPsiField_two_scale_kernel_integrable_cross N hρ' hρ hε' hε hW hξ' hξ x x y y')
      (productISqPsiField_two_scale_kernel_integrable_cross N hρ' hρ' hε' hε' hW hξ' hξ' x x y y')]
  have key : ∀ H : SpaceTime → SpaceTime → ℝ,
      ∫ w, ∫ w', H w w' = ∫ a, ∫ b, H (x + a) (x + b) := by
    intro H
    rw [← integral_comp_add_left_spaceTime (fun w => ∫ w', H w w') x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    exact (integral_comp_add_left_spaceTime (fun w' => H (x + a) w') x).symm
  rw [key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  have e1 : y - (x + a) = y - x - a := by abel
  have e2 : x - (x + a) = -a := by abel
  have e3 : y' - (x + b) = y' - x - b := by abel
  have e4 : x - (x + b) = -b := by abel
  have e5 : x + a - y = a - (y - x) := by abel
  have e6 : x + a - (x + b) = a - b := by abel
  have e7 : x + b - y' = b - (y' - x) := by abel
  have e8 : y - y' = y - x - (y' - x) := by abel
  have e9 : x + a - y' = a - (y' - x) := by abel
  have e11 : y - (x + b) = y - x - b := by abel
  simp only [isqBlockKernel, isqDiffE1, isqDiffE2, isqDiffE3, hairerI2Psi2Kernel,
    hairerCrossCovarianceTwo_self, hairerCrossCovariance_self, e1, e2, e3, e4, e5, e6, e7, e8, e9,
    e11]
  ring

end RegularityStructures.Phi43

end
