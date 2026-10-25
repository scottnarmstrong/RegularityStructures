/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Reconstruction.Path
public import Phi43.Reconstruction.UnitPeriodic
public import Phi43.Reconstruction.ClassicalSolution

/-!
# The reconstruction of the fixed point at a restart is the classical solution

`phi43_reconstruction_eq_classical_of_potential_identity`: the identification of the reconstructed
solution with the classical one, from the expansion of the abstract solution to the classical
solution, with the potential identity
`(K ∗ ζ)(s + t) + θ_s(t) = P_t (K ∗ ζ)(s) + ∫₀ᵗ P_{t-r} f(s + r) dr` as hypothesis.
-/

public section

open Set RegularityStructures.PDE

namespace RegularityStructures.Phi43

open Inhomogeneity

variable {κ : Kappa} {N : ℕ} {η : NegExponent}
  {M : Model (phi43RegularityStructureF κ) parabolicSemigroup}
  {CPi CGam CΓ CGam₁ CΓ₁ T : ℝ}

theorem phi43_reconstruction_eq_classical_of_potential_identity
    (hyp : Phi43NearHyp κ N M CPi CGam CΓ CGam₁ CΓ₁ T) (hN : 3 ≤ N)
    (hη₁ : -2 / 3 < (η : ℝ)) (hκη : κ.1 < -1 / 2 - (η : ℝ))
    (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) {s : ℝ} (hs : 0 < s)
    (hC : Restart.EnlargedCompat κ ((canonicalRenormalisedModel N κ noise Cg q hg C).translate
      (LiftBounds.restartPoint s)) M)
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    {u₀ : C(Torus3, ℝ)} {u : ℝ → C(Torus3, ℝ)}
    (hu : IsClassicalSolution (3 * C₁ C - 9 * C₂ C) f u₀ u)
    (S : Phi43RestartSolution N η hyp.real.poly hyp.hT1 noise s)
    (hws : ∀ x : Fin 3 → ℝ, S.ws (torusProj x) = u s (torusProj x) - phi43PsiAt N κ noise C (s, x))
    (hpot : ∀ t ∈ Ioc 0 T, ∀ x : Fin 3 → ℝ,
      phi43PsiAt N κ noise C ((t, x) + LiftBounds.restartPoint s) +
        duhamelField (Potential.perSmooth_zeta_restart noise N s) (t, x) =
      heatOp t (u s - S.ws) (torusProj x) + duhamel (fun r => nemytskii (cubicHeatNonlinearity
        (3 * C₁ C - 9 * C₂ C) (isSmoothOnSpaceTime_shiftForcing hf s)) r 0) t (torusProj x)) :
    ∀ t ∈ Ioc 0 T, ∀ x : Fin 3 → ℝ, S.U.val (t, x) (.old .one) +
      phi43PsiAt N κ noise C ((t, x) + LiftBounds.restartPoint s) = u (s + t) (torusProj x) := by
  obtain ⟨W, hWc, hW0, hWdef⟩ := exists_phi43_path hyp hN hη₁ hκη noise Cg q hg C hC S (u s) hws (phi43_unit_periodic hyp hN hη₁ hκη noise Cg q hg C hC S)
  exact phi43_reconstruction_eq_classical_of_potential hN η hη₁ hκη hyp noise Cg q hg C hs hC hf hu
    S.ws S.hB S.hGc S.hGζ S.U S.𝒦 S.h𝒦 S.hfix W hWc hW0 hWdef hpot

end RegularityStructures.Phi43

end
