/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Reconstruction.Solution
public import Phi43.Reconstruction.ClassicalSolution

/-!
# The unit identity of a restart solution

`phi43_unit_identity`: for a solution `S` of the fixed point at a restart (`Phi43RestartSolution`),
`S.U(t, x)_1 = (P_t w_s)(x) + θ_s(t, x) - ∫ H((t, x) - y) 𝟙_{slab}(y) (w³ - c w)(y) dy`,
`w(y) = (K ∗ ζ)(y + (s, 0)) + S.U(y)_1`, `c = 3C₁ - 9C₂`.
-/

public section

open Set MeasureTheory RegularityStructures.PDE

namespace RegularityStructures.Phi43

open Inhomogeneity

variable {κ : Kappa} {N : ℕ} {η : NegExponent}
  {M : Model (phi43RegularityStructureF κ) parabolicSemigroup}
  {CPi CGam CΓ CGam₁ CΓ₁ T : ℝ}

theorem phi43_unit_identity (hyp : Phi43NearHyp κ N M CPi CGam CΓ CGam₁ CΓ₁ T) (hN : 3 ≤ N)
    (hη₁ : -2 / 3 < (η : ℝ)) (hκη : κ.1 < -1 / 2 - (η : ℝ))
    (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) {s : ℝ}
    (hC : Restart.EnlargedCompat κ ((canonicalRenormalisedModel N κ noise Cg q hg C).translate
      (LiftBounds.restartPoint s)) M)
    (S : Phi43RestartSolution N η hyp.real.poly hyp.hT1 noise s)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x : Fin 3 → ℝ) :
    S.U.val (t, x) (.old .one) =
      (heatOp t S.ws (torusProj x) +
        duhamelField (Potential.perSmooth_zeta_restart noise N s) (t, x)) -
      ∫ y, heatKernelR4 (((t, x) : ParabolicSpace) - y) * (timeSlab T).indicator (fun y =>
        (phi43PsiAt N κ noise C (y + LiftBounds.restartPoint s) + S.U.val y (.old .one)) ^ 3 -
          (3 * C₁ C - 9 * C₂ C) * (phi43PsiAt N κ noise C (y + LiftBounds.restartPoint s) +
            S.U.val y (.old .one))) y := by
  set a := LiftBounds.restartPoint s with ha
  have hgF : M.IsSmoothFunctionModelBelow (phi43EnlargedBase N κ noise C a)
      (gamma κ + phi43Alpha κ + phi43Alpha κ) := by
    rw [Restart.gamma_add_alpha_add_alpha]
    exact isSmoothFunctionModelBelow_phi43EnlargedBase N κ noise Cg q hg C a hC
  have hvm : ∀ y ∈ timeSlab T, (phi43InhomTheta κ η M hyp.real.poly hyp.hT1
      (toHolderBesov η S.ws) (Potential.perSmooth_zeta_restart noise N s) S.hB S.hGc S.hGζ).val y
        - phi43EF .psi ∈ (phi43PolynomialSectorF κ).subspace :=
    fun y hy => phi43InhomTheta_sub_psi_mem κ η M hyp.real.poly hyp.hT1 _ _ S.hB S.hGc S.hGζ hy
  have hx : ((t, x) : ParabolicSpace) ∈ timeSlab T := ⟨ht.1, ht.2⟩
  have h1 := phi43_unit_coeff hyp hN hη₁ hκη noise C a (phi43EnlargedBase N κ noise C a) hgF
    (fun y τ => rfl) S.U _ S.𝒦 S.h𝒦 S.hfix hvm hx
  rw [h1, phi43InhomTheta_unit κ η M hyp.real.poly hyp.hT1 _ _ S.hB S.hGc S.hGζ hx,
    datumField_toHolderBesov_apply η S.ws ht.1 x]

end RegularityStructures.Phi43

end
