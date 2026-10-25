/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Reconstruction.InhomUnit
public import Phi43.Reconstruction.PsiSmooth
public import Phi43.Potential.ZetaBound
public import Phi43.Restart.Package

/-!
# A solution of the fixed point equation at a restart

`Phi43RestartSolution` bundles the data of the fixed point of `phi43FixedPointF_window_nearOne`
for the inhomogeneity `v = phi43InhomTheta` of a restart at time `s`: the datum `w_s`, the
constants of the forcing `ζ_s = Q ∗ ζ(· + (s, 0))`, the operator `𝒦` with its defining formula and
the solution `U = -𝒦 (U³) + v`.  `phi43_unit_identity` is the unit-coordinate identity
(`phi43_unit_coeff` with the unit coordinate of `v`).
-/

public section

namespace RegularityStructures.Phi43

open Inhomogeneity

/-- The data of the fixed point at a restart. -/
structure Phi43RestartSolution {κ : Kappa} (N : ℕ) (η : NegExponent)
    {M : Model (phi43RegularityStructureF κ) parabolicSemigroup} {T : ℝ}
    (hM : M.IsPolyCompatible (phi43PolynomialSectorF κ)) (hT : T ≤ 1) (noise : CanonicalNoise)
    (s : ℝ) where
  ws : C(Torus3, ℝ)
  B : ℝ
  hB : 0 ≤ B
  Gc : ℕ → ℝ
  hGc : ∀ L, 0 ≤ Gc L
  hGζ : ∀ L, DerivHyp (Potential.potZeta noise.zeta N s) (Gc L * B) L
  U : M.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T)
  𝒦 : M.SlabSpace timeZeroDist ⊤ (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * (η : ℝ))
    (timeSlab T) →ₗ[ℝ] M.SlabSpace timeZeroDist phi43SectorV (gamma κ) η (timeSlab T)
  h𝒦 : ∀ g : M.SlabSpace timeZeroDist ⊤ (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * (η : ℝ))
      (timeSlab T), ∀ x ∈ timeSlab T, (𝒦 g).val x =
    RegularityStructures.lowerProj (phi43RegularityStructureF κ).deg (gamma κ)
      (M.kGammaRemG (annKernel0C N) (annRemainderC N) (phi43PolynomialSectorF κ) phi43IntegrationF
        (gamma κ + phi43Alpha κ + phi43Alpha κ)
        (Model.SlabSpace.blockProj phi43XiFreeF (phi43_hAG κ M) g).val x)
  hfix : U = -𝒦 (Model.SlabSpace.cube (phi43ProductF κ)
    (gamma κ + phi43Alpha κ + phi43Alpha κ) (3 * (η : ℝ)) U) +
      phi43InhomTheta κ η M hM hT (toHolderBesov η ws)
        (Potential.perSmooth_zeta_restart noise N s) hB hGc hGζ

end RegularityStructures.Phi43

end
