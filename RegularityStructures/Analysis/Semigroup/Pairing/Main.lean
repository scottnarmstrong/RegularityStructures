/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Pairing.Tendsto
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# The test-function bound `|⟨Λ, φ^λ_{x₀}⟩| ≲ λ^γ`

* `tendsto_integral_pairing`: `∫ Λ_s φ → ⟨Λ, φ⟩` as `s ↓ 0`;
* `abs_pairing_le`: `|⟨Λ, φ⟩| ≤ C · pairingConst A · (B₀ + B₁) · λ^γ`.

This is the bridge from the `Q`-distribution `Rf - Π_{x₀} f(x₀)` of local order `γ` to the
reconstruction bound [Hai14, Theorem 3.10, (3.3)]. Here `φ` is a test function adapted to the
scale `λ` (`∫ |φ| ≤ B₀`) with `ψ = Lφ` (`∫ |ψ| ≤ B₁ λ^{-ℓ}`). The proof evaluates the increment
bounds of `LocalData.abs_integral_sub_le` at `T = λ^ℓ`: `|G(T)| ≤ C B₀ |A| λ^γ` and
`|G(T) - G(s)| ≤ C B₁ (∑_a ℓ/(a+ℓ)) λ^γ`.

Source: [Hai14] = arXiv:1303.5113v4.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {K : RegularisingSemigroup E μ}

theorem incrBound_pow_order {A : Finset ℝ} (hA : ∀ a ∈ A, -K.order < a) {γ lam : ℝ}
    (hlam : 0 < lam) (C B₁ : ℝ) :
    K.incrBound A γ lam (C * (B₁ * lam ^ (-K.order))) (lam ^ K.order) =
      C * B₁ * lam ^ γ * ∑ a ∈ A, K.order / (a + K.order) := by
  have hℓ := K.order_pos
  unfold incrBound
  have key : ∀ a ∈ A, lam ^ (-K.order) *
      (((lam ^ K.order) ^ (a / K.order + 1) / (a / K.order + 1)) * lam ^ (γ - a)) =
      lam ^ γ * (K.order / (a + K.order)) := by
    intro a ha
    have hpos : 0 < a + K.order := by linarith [hA a ha]
    have e1 : (lam ^ K.order) ^ (a / K.order + 1) = lam ^ (a + K.order) := by
      rw [← Real.rpow_mul hlam.le]; congr 1; field_simp
    have e2 : 1 / (a / K.order + 1) = K.order / (a + K.order) := by
      field_simp
    have e3 : lam ^ (-K.order) * lam ^ (a + K.order) * lam ^ (γ - a) = lam ^ γ := by
      rw [← Real.rpow_add hlam, ← Real.rpow_add hlam]; congr 1; ring
    calc _ = (lam ^ (-K.order) * lam ^ (a + K.order) * lam ^ (γ - a)) *
          (1 / (a / K.order + 1)) := by rw [e1]; ring
      _ = _ := by rw [e3, e2]
  have hs := Finset.sum_congr rfl key
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hs
  linear_combination (C * B₁) * hs

end RegularityStructures.RegularisingSemigroup

end
