/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalModel

/-!
# Explicit smooth extension of Hairer's renormalised H0 data

Hairer [Hai14, (9.3)–(9.5), Theorem 8.44]. The Wick-subtracted global
functions and corrected characters below define the full retained smooth
extension. In particular the auxiliary integrated-cubic square is the
actual square of the corrected potential; it is not given by the algebraic
tensor formula `renormalisedPi`.

These are explicit function formulas for supplied CanonicalData; no analytic
or source-compatibility assertion for arbitrary kernel fields is made here.
Actual-model theorems use the concrete causal hairerCanonicalData and must
prove agreement with the tensor formula on H0 separately.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

namespace CanonicalData

variable {κ : Kappa} (D : CanonicalData κ)

/-- The renormalised integrated cubic potential, before recentering. -/
def renormalisedExtensionPotential (c : RenormalisationConstants) (y : ParabolicSpace) : ℝ :=
  D.globalIPsiCube y - 3 * C₁ c * D.globalIPsi y

/-- Explicit global functions on every retained symbol. The nontrivial H0
rows are Hairer's table (9.3); positive auxiliary products use the corrected
global primitives. -/
def renormalisedExtensionGlobalBasis (c : RenormalisationConstants) : Symbol → ParabolicSpace → ℝ
  | .psiSq => fun y => D.globalPsiSq y - C₁ c
  | .psiCube => fun y => D.globalPsiCube y - 3 * C₁ c * D.globalPsi y
  | .psiSqX i => fun y => (D.globalPsiSq y - C₁ c) * parabolicCoords y i.succ
  | .iPsiCube => D.renormalisedExtensionPotential c
  | .iPsiPsiSq => fun y => D.globalIPsi y * (D.globalPsiSq y - C₁ c)
  | .iPsiSqPsiSq => fun y => D.globalIPsiSq y * (D.globalPsiSq y - C₁ c) - C₂ c
  | .iPsiCubePsi => fun y => D.renormalisedExtensionPotential c y * D.globalPsi y
  | .iPsiCubePsiSq => fun y =>
      D.renormalisedExtensionPotential c y * (D.globalPsiSq y - C₁ c) - 3 * C₂ c * D.globalPsi y
  | .iPsiCubeSq => fun y => D.renormalisedExtensionPotential c y * D.renormalisedExtensionPotential c y
  | τ => D.globalPiBasis τ

/-- Linear extension of the actual renormalised global tree functions. -/
def renormalisedExtensionGlobalPi (c : RenormalisationConstants) :
    T →ₗ[ℝ] (ParabolicSpace → ℝ) :=
  Finsupp.linearCombination ℝ (D.renormalisedExtensionGlobalBasis c)

/-- Corrected primitive character. The integrated-cubic constant is the
negative corrected potential; all other primitive characters are unchanged. -/
def renormalisedExtensionCharacter (c : RenormalisationConstants) (x : ParabolicSpace) : G :=
  { D.canonicalCharacter x with
    cPsiCube := (D.canonicalCharacter x).cPsiCube + 3 * C₁ c * D.globalIPsi x }

/-- Actual function-valued renormalised lift, recentered by its corrected
character. No arbitrary pi function or covariance certificate is an input. -/
def renormalisedExtensionPi (c : RenormalisationConstants) (x : ParabolicSpace) :
    T →ₗ[ℝ] (ParabolicSpace → ℝ) :=
  (D.renormalisedExtensionGlobalPi c).comp
    (structureGroupMap (D.renormalisedExtensionCharacter c x))

/-- The transition character of the full retained smooth extension. -/
def renormalisedExtensionGammaParameter (c : RenormalisationConstants)
    (x y : ParabolicSpace) : G :=
  structureGroupInv (D.renormalisedExtensionCharacter c x) * D.renormalisedExtensionCharacter c y

/-- Structure-group action obtained from the corrected transition character. -/
def renormalisedExtensionGamma (c : RenormalisationConstants)
    (x y : ParabolicSpace) : T →ₗ[ℝ] T :=
  structureGroupMap (D.renormalisedExtensionGammaParameter c x y)

end CanonicalData

end RegularityStructures.Phi43

end

public noncomputable section

namespace RegularityStructures.Phi43.CanonicalData

variable {κ : Kappa} (D : CanonicalData κ)

/-- The explicitly defined global extension has its stated basis values. -/
theorem renormalisedExtensionGlobalPi_basis (c : RenormalisationConstants) (τ : Symbol) :
    D.renormalisedExtensionGlobalPi c (basis τ) = D.renormalisedExtensionGlobalBasis c τ := by
  simp [renormalisedExtensionGlobalPi, basis]

end RegularityStructures.Phi43.CanonicalData

end
