/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Reconstruction.Identification
public import Phi43.Reconstruction.InhomUnit

/-!
# The classical solution after a restart, in mild form with the cubic term from the fixed point

`classical_eq_heat_add_duhamel_sub_cube`: let `U = -𝒦 (U⋆³) + v` be the window fixed point at the
restart time `s > 0`, with inhomogeneity `v = phi43InhomTheta (w_s, ζ_s)`, datum
`w_s = u(s) - Ψ(s)`, where `u` is the classical solution.  Then for `t ∈ (0, T]`
`u(s + t) = P_t u(s) + ∫₀ᵗ P_{t-r} f(s + r) dr - ⟨1, 𝒦 (U⋆³)(t, ·)⟩`.
It combines the reconstruction identity `phi43_reconstruction_eq_classical`
(`⟨1, U(t)⟩ + Ψ(s + t) = u(s + t)`), the unit coefficient of the inhomogeneity
(`phi43InhomTheta_unit`: `⟨1, v(t)⟩ = P_t w_s + θ_s(t)`) and the potential identity
`phi43_potential_identity` (`Ψ(s + t) + θ_s(t) = P_t Ψ(s) + ∫₀ᵗ P_{t-r} f(s + r) dr`).
-/

public section

open Set RegularityStructures.PDE

namespace RegularityStructures.Phi43.LocalLipschitz

open RegularityStructures.Inhomogeneity

variable {κ : Kappa} {N : ℕ} {η : NegExponent}
  {M : Model (phi43RegularityStructureF κ) parabolicSemigroup}
  {CPi CGam CΓ CGam₁ CΓ₁ T : ℝ}

/-- **The restarted classical solution in mild form.** -/
theorem classical_eq_heat_add_duhamel_sub_cube
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
    (ws : C(Torus3, ℝ))
    (hws : ∀ x : Fin 3 → ℝ, ws (torusProj x) = u s (torusProj x) - phi43PsiAt N κ noise C (s, x))
    {B : ℝ} (hB : 0 ≤ B) {Gc : ℕ → ℝ} (hGc : ∀ L, 0 ≤ Gc L)
    (hGζ : ∀ L, DerivHyp (Potential.potZeta noise.zeta N s) (Gc L * B) L)
    (U : M.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T))
    (𝒦 : M.SlabSpace timeZeroDist ⊤ (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * (η : ℝ))
        (timeSlab T) →ₗ[ℝ] M.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T))
    (h𝒦 : ∀ g : M.SlabSpace timeZeroDist ⊤ (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * (η : ℝ))
        (timeSlab T), ∀ x ∈ timeSlab T, (𝒦 g).val x =
      RegularityStructures.lowerProj (phi43RegularityStructureF κ).deg (gamma κ)
        (M.kGammaRemG (annKernel0C N) (annRemainderC N) (phi43PolynomialSectorF κ) phi43IntegrationF
          (gamma κ + phi43Alpha κ + phi43Alpha κ)
          (Model.SlabSpace.blockProj phi43XiFreeF (phi43_hAG κ M) g).val x))
    (hfix : U = -𝒦 (Model.SlabSpace.cube (phi43ProductF κ)
      (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * (η : ℝ)) U) +
        phi43InhomTheta κ η M hyp.real.poly hyp.hT1 (toHolderBesov η ws)
          (Potential.perSmooth_zeta_restart noise N s) hB hGc hGζ) :
    ∀ t ∈ Ioc 0 T, ∀ x : Fin 3 → ℝ,
      u (s + t) (torusProj x) = heatOp t (u s) (torusProj x) +
        duhamel (fun r => nemytskii (cubicHeatNonlinearity (3 * C₁ C - 9 * C₂ C)
          (isSmoothOnSpaceTime_shiftForcing hf s)) r 0) t (torusProj x) -
        (𝒦 (Model.SlabSpace.cube (phi43ProductF κ) (gamma κ + phi43Alpha κ + phi43Alpha κ)
          (3 * (η : ℝ)) U)).val (t, x) (.old .one) := by
  intro t ht x
  let S : Phi43RestartSolution N η hyp.real.poly hyp.hT1 noise s :=
    ⟨ws, B, hB, Gc, hGc, hGζ, U, 𝒦, h𝒦, hfix⟩
  have hrec := phi43_reconstruction_eq_classical hyp hN hη₁ hκη noise Cg q hg C hs hC hf hnz hu S
    hws t ht x
  have hxT : ((t, x) : ParabolicSpace) ∈ timeSlab T := ht
  have hU : U.val (t, x) (.old .one) =
      -(𝒦 (Model.SlabSpace.cube (phi43ProductF κ) (gamma κ + phi43Alpha κ + phi43Alpha κ)
        (3 * (η : ℝ)) U)).val (t, x) (.old .one) +
      (Datum.datumField η (toHolderBesov η ws) (t, x) +
        duhamelField (Potential.perSmooth_zeta_restart noise N s) (t, x)) := by
    rw [← phi43InhomTheta_unit κ η M hyp.real.poly hyp.hT1 (toHolderBesov η ws)
      (Potential.perSmooth_zeta_restart noise N s) hB hGc hGζ hxT]
    conv_lhs => rw [hfix]
    rfl
  have hpot := phi43_potential_identity N κ noise C hf hnz s (3 * C₁ C - 9 * C₂ C) (u s) ws hws
    ht.1 x
  rw [datumField_toHolderBesov_apply η ws ht.1 x] at hU
  change U.val (t, x) (.old .one) + _ = _ at hrec
  have hlin : heatOp t (u s - ws) (torusProj x) =
      heatOp t (u s) (torusProj x) - heatOp t ws (torusProj x) := by
    rw [heatOp_sub]
    rfl
  rw [hlin] at hpot
  linarith

end RegularityStructures.Phi43.LocalLipschitz

end
