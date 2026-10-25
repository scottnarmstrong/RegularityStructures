/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Constants
public import RegularityStructures.Probability.SpaceTimeMeasure
public import RegularityStructures.Probability.GaussianVector

/-!
# The stationary mollified field `Ψ_ε`

See the remark after Definition 2.5 of the statement. For a white noise `W` the stationary
solution of `(∂ₜ - Δ + 1) Ψ_ε = ξ_ε` is, at each point, `Ψ_ε(z) = W(G_ε(z - ·))`. We take this as
the definition of `stationaryField W ρ ε z`. Under the hypothesis `G_ε ∈ L²` (implied by item (W3) of Lemma 4.1 of the
statement, proved elsewhere and assumed here):

* every finite family `(Ψ_ε(zᵢ))` is a centred Gaussian vector with covariance `Q_ε(zᵢ - zⱼ)`
  (`isCentredGaussianVector_stationaryField`);
* `E[Ψ_ε(z) Ψ_ε(z')] = Q_ε(z - z')` and `E[Ψ_ε(z)²] = C₁^ε`.

The deterministic inputs are `∫ G_ε(z - w) G_ε(z' - w) dw = Q_ε(z - z')`, `Q_ε(0) = C₁^ε` and
`Q_ε(-u) = Q_ε(u)`. They use only the translation and reflection invariance of the measure on
`ℝ × T³`, and hold without integrability hypotheses (both sides are Bochner integrals).
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- The stationary mollified field `Ψ_ε(z) = W(G_ε(z - ·))`, where `G_ε = mollifiedKernel ρ ε`. -/
def stationaryField {Ω : Type*} (W : (SpaceTime → ℝ) → Ω → ℝ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (ε : ℝ) (z : SpaceTime) : Ω → ℝ :=
  W fun w => mollifiedKernel ρ ε (z - w)

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}

/-! ### Deterministic identities for `Q_ε` -/

/-- `Q_ε(0) = C₁^ε`. -/
theorem covariance_zero : covariance ρ ε 0 = wickConstant ρ ε := by
  simp only [covariance, wickConstant, zero_add, sq]

/-! ### The Gaussian field -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}

theorem memLp_mollifiedKernel_sub (hG : MemLp (mollifiedKernel ρ ε) 2) (z : SpaceTime) :
    MemLp (fun w => mollifiedKernel ρ ε (z - w)) 2 :=
  memLp_comp_sub_left_spaceTime hG z

end RegularityStructures.Phi43

end
