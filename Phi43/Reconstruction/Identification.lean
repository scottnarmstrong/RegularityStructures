/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Reconstruction.ClassicalSolutionRestart
public import Phi43.Reconstruction.PotentialIdentity

/-!
# Identification at a restart: the reconstruction of the fixed point is the classical solution

`phi43_reconstruction_eq_classical`: let `u` be a classical solution of
`∂_t u = Δ u - u³ + (3C₁ - 9C₂) u + f` and `s > 0`.  Let `U = -𝒦 (U³) + v` be a solution of the fixed
point equation of `phi43FixedPointF_window_nearOne` on `(0, T]` for an enlarged model compatible
with the translate by `(s, 0)` of the renormalised canonical model of the noise `ζ = f`, with the
inhomogeneity `v = Ψ·1 + datum(w_s) + jet(θ_s)`, `w_s = u(s) - (K ∗ ζ)(s)`.  Then for
`0 < t ≤ T` and `x ∈ ℝ³`,
`U(t, x)_1 + (K ∗ ζ)(s + t, x) = u(s + t, x)`.
-/

public section

open Set RegularityStructures.PDE

namespace RegularityStructures.Phi43

variable {κ : Kappa} {N : ℕ} {η : NegExponent}
  {M : Model (phi43RegularityStructureF κ) parabolicSemigroup}
  {CPi CGam CΓ CGam₁ CΓ₁ T : ℝ}

theorem phi43_reconstruction_eq_classical
    (hyp : Phi43NearHyp κ N M CPi CGam CΓ CGam₁ CΓ₁ T) (hN : 3 ≤ N)
    (hη₁ : -2 / 3 < (η : ℝ)) (hκη : κ.1 < -1 / 2 - (η : ℝ))
    (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) {s : ℝ} (hs : 0 < s)
    (hC : Restart.EnlargedCompat κ ((canonicalRenormalisedModel N κ noise Cg q hg C).translate
      (LiftBounds.restartPoint s)) M)
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (hnz : ∀ z : ParabolicSpace, noise.zeta z = f (z.1, torusProj z.2))
    {u₀ : C(Torus3, ℝ)} {u : ℝ → C(Torus3, ℝ)}
    (hu : IsClassicalSolution (3 * C₁ C - 9 * C₂ C) f u₀ u)
    (S : Phi43RestartSolution N η hyp.real.poly hyp.hT1 noise s)
    (hws : ∀ x : Fin 3 → ℝ, S.ws (torusProj x) = u s (torusProj x) - phi43PsiAt N κ noise C (s, x)) :
    ∀ t ∈ Ioc 0 T, ∀ x : Fin 3 → ℝ, S.U.val (t, x) (.old .one) +
      phi43PsiAt N κ noise C ((t, x) + LiftBounds.restartPoint s) = u (s + t) (torusProj x) :=
  phi43_reconstruction_eq_classical_of_potential_identity hyp hN hη₁ hκη noise Cg q hg C hs hC hf hu
    S hws fun _ ht x => phi43_potential_identity N κ noise C hf hnz s _ (u s) S.ws hws ht.1 x

end RegularityStructures.Phi43

end
