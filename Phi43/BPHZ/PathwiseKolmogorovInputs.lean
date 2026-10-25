/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PolynomialPiBounds
public import Phi43.BPHZ.RandomCanonicalModel
import Mathlib.Tactic

/-!
# The pathwise `Dπ`-hypotheses of the Kolmogorov bound for the model norms

For random models `Z₁, Z₂` which are polynomial compatible for every `ω` (for instance
`ω ↦ canonicalModelOfLift N κ C (ξ ω)`, `canonicalModelOfLift_polyCompatible`), with
`Dπ = piDeterministic` and any constant `C ≥ polyPiConst 2`: the two deterministic hypotheses of
`kolmogorov_modelNorm` on `Dπ`, the single bound (`piDeterministic_bound`) and the difference
bound (`piDeterministic_sub_bound`), in exactly the form of that statement.
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

variable {κ : Kappa} {Ω : Type*}

theorem canonicalModelOfLift_polyCompatible {N : ℕ} {C : RenormalisationConstants}
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f) :
    (canonicalModelOfLift N κ C f).IsPolyCompatible (phi43PolynomialSector κ) :=
  (canonicalModelOfLift_isRenormalisedCanonicalModel hf hg).1.poly

/-- The hypothesis of the Kolmogorov bound on `Dπ` (single bounds). -/
theorem piDeterministic_bound {Z : Ω → Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hpoly : ∀ ω, (Z ω).IsPolyCompatible (phi43PolynomialSector κ)) {C : ℝ}
    (hC : polyPiConst 2 ≤ C) :
    ∀ i ∈ piDeterministic, ∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
      |(Z ω).regPi x (Pi.single i 1) t x| ≤
        C * t ^ (homogeneity κ i / parabolicSemigroup.order) := by
  intro i hi ω t ht x
  refine (abs_regPi_diag_le_of_mem_piDeterministic (hpoly ω) hi ht.1 x).trans ?_
  exact mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg ht.1.le _)

/-- The hypothesis of the Kolmogorov bound on `Dπ` (differences). -/
theorem piDeterministic_sub_bound
    {Z₁ Z₂ : Ω → Model (phi43RegularityStructure κ) parabolicSemigroup}
    (h₁ : ∀ ω, (Z₁ ω).IsPolyCompatible (phi43PolynomialSector κ))
    (h₂ : ∀ ω, (Z₂ ω).IsPolyCompatible (phi43PolynomialSector κ)) {C ε θ : ℝ} (hC : 0 ≤ C)
    (hε : 0 ≤ ε) :
    ∀ i ∈ piDeterministic, ∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
      |(Z₁ ω).regPi x (Pi.single i 1) t x - (Z₂ ω).regPi x (Pi.single i 1) t x| ≤
        C * ε ^ θ * t ^ (homogeneity κ i / parabolicSemigroup.order) := fun _ hi ω _ ht x =>
  abs_regPi_diag_sub_le_of_mem_piDeterministic (h₁ ω) (h₂ ω) hi ht.1 x hC hε

end RegularityStructures.Phi43

end
