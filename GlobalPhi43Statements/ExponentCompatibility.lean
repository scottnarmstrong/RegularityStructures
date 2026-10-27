/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43Statements.Defs.IsGlobalPhi43Flow
public import GlobalPhi43Statements.Defs.HolderBesovEmbed
public import GlobalPhi43.Proofs.ExponentCompatibility

/-!
# Compatibility across Hölder exponents

The global flows of `GlobalPhi43Statements.GlobalDynamics` chosen compatibly for all exponents at
once. The proof is `GlobalPhi43.exponentCompatibility`.
-/

public section

namespace GlobalPhi43.Statements

open MeasureTheory Set
open scoped NNReal
open RegularityStructures

/-- **Compatibility across Hölder exponents.** For a mass `a` there are constant profiles
`K_{a,η}`, `η ∈ (-2/3, -1/2)`, chosen before the noise space, such that on every admissible noise
space there is a family of witnesses `(Ω₀^η, u^η, μ^η)`, `η ∈ (-2/3, -1/2)`, each satisfying
(B1)–(B8) for `(a, η)` with `K_{a,η}`, and compatible across exponents: for `η < η'' < -1/2`,
almost surely `ι(u^{η''}(t,s;x)) = u^η(t,s;ιx)` for all `0 ≤ s ≤ t` and `x ∈ 𝒞^{η''}`, where
`ι : 𝒞^{η''} → 𝒞^η` is the canonical embedding. The profiles `K_{a,η}` are existential and chosen
here; they are not required to be those of `GlobalPhi43.Statements.globalDynamics`.

The family is indexed by all `η : NegExponent` and constrained only for `η ∈ (-2/3, -1/2)`; its
members off that range are never read. -/
theorem exponentCompatibility :
    ∀ (a : ℝ),
    ∃ K : NegExponent → ℝ → ℝ≥0,
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
      (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W),
    ∃ (Ω₀ : NegExponent → Set Ω)
      (u : (η : NegExponent) → ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
      (μ : (η : NegExponent) → Measure (HolderBesov η)),
      (∀ η : NegExponent, (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)) →
        GlobalPhi43.IsGlobalPhi43Flow (K η) P W a η (Ω₀ η) (u η) (μ η)) ∧
      ∀ (η η'' : NegExponent) (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
        (hηη'' : (η : ℝ) < η'') (hη'' : (η'' : ℝ) < -(1 / 2 : ℝ)),
        ∀ᵐ ω ∂P, ∀ s t, 0 ≤ s → s ≤ t → ∀ x : HolderBesov η'',
          GlobalPhi43.holderBesovEmbed η η'' hηη''.le (u η'' t s x ω) =
            u η t s (GlobalPhi43.holderBesovEmbed η η'' hηη''.le x) ω :=
  by exact GlobalPhi43.exponentCompatibility

end GlobalPhi43.Statements

end
