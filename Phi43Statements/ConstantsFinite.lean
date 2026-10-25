/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Constants.Finite

/-!
# Finiteness of the renormalisation constants

The objects in the definition of the renormalisation constants (Definition 2.5 of the statement)
are well defined: each `ρ_{ε,z}` is square-integrable, the massive heat kernel `G` is integrable,
the integrals defining `G_ε(z)` and `Q_ε(z)` converge absolutely, `G_ε` is bounded, integrable and
continuous, `Q_ε` is bounded and continuous, and `G_ε²` and `G Q_ε²` are integrable. So `C₁^ε` and
`C₂^ε` are finite.

This is item (W3) of Lemma 4.1 of the statement. Items (W1)–(W5) show that Theorem A is not vacuous:
the white noises, regularised noises and classical solutions over which it quantifies exist, and its
conditions are meaningful.

The proof is `RegularityStructures.Phi43.constants_finite`,
in the module `Phi43.Constants.Finite`.

Source: the statement, Lemma 4.1 (W3), Definition 2.5.
-/

public section

namespace RegularityStructures.Phi43.Statements

open MeasureTheory Set
open scoped ENNReal

/-- **Finite constants** (Lemma 4.1 (W3)). Each `ρ_{ε,z}` is square-integrable, and the
kernels are integrable and bounded, so the constants are finite. -/
theorem constants_finite :
    ∀ (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ}
    (hε : ε ∈ Ioc (0 : ℝ) 1),
    Integrable massiveHeatKernel ∧
      (∀ z, MemLp (mollifierAt ρ ε z) 2) ∧
      (∀ z, Integrable fun w => massiveHeatKernel (z - w) * periodise ρ ε w) ∧
      (Continuous (mollifiedKernel ρ ε) ∧ Integrable (mollifiedKernel ρ ε) ∧
        ∃ C, ∀ z, |mollifiedKernel ρ ε z| ≤ C) ∧
      (∀ z, Integrable fun w => mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w) ∧
      (Continuous (covariance ρ ε) ∧ ∃ C, ∀ z, |covariance ρ ε z| ≤ C) ∧
      Integrable (fun z => mollifiedKernel ρ ε z ^ 2) ∧
      Integrable fun z => massiveHeatKernel z * covariance ρ ε z ^ 2 :=
  by exact RegularityStructures.Phi43.constants_finite

end RegularityStructures.Phi43.Statements

end
