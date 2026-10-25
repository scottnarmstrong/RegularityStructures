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
public import RegularityStructures.Abstract.PolyGrowth.Reconstruction
public import RegularityStructures.Analysis.Semigroup.Weighted.Defs

/-!
# Renormalised canonical models with a moderate weight

A renormalised canonical model (`IsRenormalisedCanonicalModel`) that also satisfies a weighted
bound on the whole space. For one polynomially moderate weight `ρ` and a constant `B`, its
regularised realisations satisfy `|(Q_t Π_x e_τ)(x)| ≤ B ρ(x) t^{|τ|/ℓ}` for every symbol `τ` of
degree below the cutoff `γ`. The weight controls the model at large distances, which compact-set
norms do not see. This is the property used by the uniqueness of the renormalised canonical model
on the whole space and by the solution theory for lifts.

Source: [Hai14, Definition 5.9, (8.34)]; [Hos25].
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/--
`Z` is the renormalised canonical model `M_C Z(noise)`: it realises the truncated kernel `K_N` for
the abstract integration map (admissibility, [Hai14, Definition 5.9]), its realisation on the
symbols `F₋` of negative homogeneity is Hairer's `Π^M_x τ = (Π_x ⊗ f_x)Δ^M τ` [Hai14, (8.34)], and
its norms are finite on compact sets, and its diagonal `|(Q_t Π_x e_τ)(x)| ≤ B ρ(x) t^{|τ|/ℓ}` (all
`τ` below `γ`) holds for one polynomially moderate weight `ρ`. -/
def Statements.IsModerateRenormalisedCanonicalModel (N : ℕ) (κ : RegularityStructures.Phi43.Kappa)
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
    (∀ S : Set RegularityStructures.ParabolicSpace, IsCompact S →
      Z.normOn (RegularityStructures.Phi43.gamma κ) S ≠ ⊤) ∧
    ∃ (ρ : RegularityStructures.ParabolicSpace → ℝ) (p B : ℝ),
      RegularityStructures.RegularisingSemigroup.IsModerateWeight
          RegularityStructures.parabolicSemigroup ρ p ∧
        0 ≤ B ∧
        RegularityStructures.Model.PiBoundGrowth Z (RegularityStructures.Phi43.gamma κ) B ρ

end RegularityStructures.Phi43

end
