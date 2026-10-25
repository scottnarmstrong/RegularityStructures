/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.Abstract
public import Phi43.Structure.AbstractIntegration
public import Phi43.Structure.AbstractPolynomial
public import Phi43.Structure.CanonicalKernelHairer
public import Phi43.Structure.CanonicalModel
public import RegularityStructures.Abstract.Profile.Realising

/-!
# Renormalised canonical models

A model `Z` of the Φ⁴₃ regularity structure is the renormalised canonical model `M_C Z(noise)`
of a smooth periodic noise, with renormalisation constants `C = (C₁, C₂)`, if three things hold.
First, it is admissible: it realises the truncated heat kernel `K_N` for the abstract integration
map [Hai14, Definition 5.9]. Second, on each symbol `τ` of negative homogeneity, its regularised
realisation is the heat-semigroup regularisation of Hairer's renormalised canonical realisation
`Π^M_x τ = (Π_x ⊗ f_x)Δ^M τ` [Hai14, (8.34)]. Third, its norms are finite on compact sets.

Source: [Hai14, Definition 5.9, (8.34), Section 8.3].
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- `Z` is the renormalised canonical model `M_C Z(noise)`: it realises the truncated kernel `K_N`
for the abstract integration map (admissibility, [Hai14, Definition 5.9]), its realisation on the
symbols `F₋` of negative homogeneity is Hairer's `Π^M_x τ = (Π_x ⊗ f_x)Δ^M τ` [Hai14, (8.34)], and
its norms are finite on compact sets. -/
def Statements.IsRenormalisedCanonicalModel (N : ℕ) (κ : RegularityStructures.Phi43.Kappa)
    (noise : RegularityStructures.Phi43.CanonicalNoise)
    (C : RegularityStructures.Phi43.RenormalisationConstants)
    (Z : RegularityStructures.Model (RegularityStructures.Phi43.phi43RegularityStructure κ)
      RegularityStructures.parabolicSemigroup) : Prop :=
  Z.IsRealisingP (RegularityStructures.annKernel0C N) (RegularityStructures.Phi43.gamma κ)
      (RegularityStructures.Phi43.phi43PolynomialSector κ)
      RegularityStructures.Phi43.phi43AbstractIntegration
      RegularityStructures.Phi43.phi43IntegrationSector ∧
    (∀ τ ∈ RegularityStructures.Phi43.fMinus, ∀ (x : RegularityStructures.ParabolicSpace) (t : ℝ),
      0 < t → ∀ z : RegularityStructures.ParabolicSpace,
        Z.regPi x (Pi.single τ 1) t z =
          RegularityStructures.parabolicSemigroup.apply t
            ((RegularityStructures.Phi43.hairerCanonicalData (κ := κ) N noise).renormalisedPi C x
              (RegularityStructures.Phi43.basis τ)) z) ∧
    ∀ S : Set RegularityStructures.ParabolicSpace, IsCompact S →
      Z.normOn (RegularityStructures.Phi43.gamma κ) S ≠ ⊤

end RegularityStructures.Phi43

end
