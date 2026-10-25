/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Operator

/-!
# Pairing of a `Q`-distribution with a test function: definitions

A `Q`-distribution `Λ` (a family `Λ_t = Q_t Λ`, see
`RegularityStructures.Analysis.Semigroup.Basic`) is paired with a
function `φ` by `⟨Λ, φ⟩ = lim_{s ↓ 0} ∫ Λ_s φ dμ`.

* `pairing`: this limit (`limUnder`; when the limit does not exist the value is an unspecified
  junk value chosen by `Classical.epsilon`, so every use must come with a convergence statement);
* `IsGeneratorPair φ ψ`: `ψ = Lφ` in integrated form, `Q_h φ - φ = ∫_0^h Q_v ψ dv`;
* `IsSymmetric`, `IsMetricScale`: symmetry of the kernel, and `scaleDist` being a metric-like size;
* `IsLocalOrder Λ x₀ γ A C`: `Λ` is "of order `γ` at `x₀`", the hypothesis on
  `Rf - Π_{x₀} f(x₀)` in the reconstruction bound [Hai14, Theorem 3.10, (3.3)];
* `pairingConst A`, the constant in the bound `|⟨Λ, φ^λ_{x₀}⟩| ≲ λ^γ`.

Source: [Hai14] = arXiv:1303.5113v4.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

/-- `⟨Λ, φ⟩ = lim_{s ↓ 0} ∫ Λ_s φ dμ`. The semigroup `K` only fixes the measure `μ`. -/
def pairing (_K : RegularisingSemigroup E μ) (Λ : ℝ → E → ℝ) (φ : E → ℝ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun s => ∫ y, Λ s y * φ y ∂μ

/-- `ψ = Lφ` for the generator `L` of the semigroup, in integrated form:
`Q_h φ - φ = ∫_0^h Q_v ψ dv`. -/
def IsGeneratorPair (φ ψ : E → ℝ) : Prop :=
  ∀ ⦃h : ℝ⦄, 0 < h → ∀ z, K.apply h φ z - φ z = ∫ v in (0 : ℝ)..h, K.apply v ψ z

/-- The kernel is symmetric. -/
def IsSymmetric : Prop := ∀ t x y, K.kernel t x y = K.kernel t y x

/-- `scaleDist` is symmetric and satisfies the triangle inequality. -/
structure IsMetricScale : Prop where
  symm : ∀ x y, K.scaleDist x y = K.scaleDist y x
  triangle : ∀ x y z, K.scaleDist x z ≤ K.scaleDist x y + K.scaleDist y z

/-- The kernel is jointly measurable in the time and both space variables. (The interface only
asks for measurability in the space variables for each fixed time; the integrated generator
identity needs Fubini in the time variable.) -/
def IsJointMeasurable : Prop :=
  Measurable fun p : ℝ × E × E => K.kernel p.1 p.2.1 p.2.2

/-- Constant of the test-function bound. -/
def pairingConst (A : Finset ℝ) : ℝ := ∑ a ∈ A, (1 + K.order / (a + K.order))

/-- The primitive `β ∑_a (δ^{a/ℓ+1}/(a/ℓ+1)) λ^{γ-a}` of the bound `β ∑_a u^{a/ℓ} λ^{γ-a}` on
`∫ Λ_u ψ`, used to bound the increments of `s ↦ ∫ Λ_s φ`. -/
def incrBound (A : Finset ℝ) (γ lam β δ : ℝ) : ℝ :=
  β * ∑ a ∈ A, (δ ^ (a / K.order + 1) / (a / K.order + 1)) * lam ^ (γ - a)

end RegularityStructures.RegularisingSemigroup

end

public section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

include K in
theorem pairing_eq_of_tendsto {Λ : ℝ → E → ℝ} {φ : E → ℝ} {L : ℝ}
    (h : Tendsto (fun s => ∫ y, Λ s y * φ y ∂μ) (𝓝[>] 0) (𝓝 L)) : K.pairing Λ φ = L :=
  h.limUnder_eq

end RegularityStructures.RegularisingSemigroup

end
