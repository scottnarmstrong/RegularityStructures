/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Sector.Coeff
public import RegularityStructures.Analysis.Heat.Schauder.DTaylorLinear
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# Lipschitz bounds for the coefficients of `J(x)` and `N_γ f`

The derivative-shell pairing is linear in the `Q`-family when both families have a local order
(`derivShellPairing_sub`). Applying the derivative-shell bound of the first half to the
differences of `Q`-families of two models gives

* `abs_jCoeff_sub_le_in`:
  `|jCoeff M₁ N x i k − jCoeff M₂ N x i k| ≤ c_{J,i,k} (max(C_Γ¹, 1) ‖Π¹ − Π²‖ + ‖Γ¹ − Γ²‖ C_Π²)`
  for `|k|_𝔰 < deg i + 2`, with the same constant `c_{J,i,k} = jCoeffConstIn 𝒯 V γ N i k`
  as for a single model;
* `abs_nCoeff_sub_le_in`:
  `|nCoeff M₁ N f₁ x k − nCoeff M₂ N f₂ x k| ≤ c_{N,k} (C_{f¹} ‖Π¹ − Π²‖ + ‖Π²‖ |||f¹; f²|||)`
  for `|k|_𝔰 < γ + 2`, with `c_{N,k} = nCoeffConstIn 𝒯 V γ N k`.

Source: [Hai14] = arXiv:1303.5113v4, (5.11), (5.16), Theorem 5.12 (last statement).
-/

public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  {V : Submodule ℝ (ι → ℝ)}

/-- The pairing is additive in the `Q`-family, if the integrals converge. -/
theorem pairing_sub_of_tendsto {E : Type*} [MeasurableSpace E] {μ : Measure E}
    (K : RegularisingSemigroup E μ) {Λ Λ' : ℝ → E → ℝ} {φ : E → ℝ} {L L' : ℝ}
    (hi : ∀ s ∈ Ioc (0 : ℝ) 1, Integrable (fun y => Λ s y * φ y) μ)
    (hi' : ∀ s ∈ Ioc (0 : ℝ) 1, Integrable (fun y => Λ' s y * φ y) μ)
    (h : Tendsto (fun s => ∫ y, Λ s y * φ y ∂μ) (𝓝[>] 0) (𝓝 L))
    (h' : Tendsto (fun s => ∫ y, Λ' s y * φ y ∂μ) (𝓝[>] 0) (𝓝 L')) :
    K.pairing (fun t z => Λ t z - Λ' t z) φ = K.pairing Λ φ - K.pairing Λ' φ := by
  rw [K.pairing_eq_of_tendsto h, K.pairing_eq_of_tendsto h']
  refine K.pairing_eq_of_tendsto ((h.sub h').congr' ?_)
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with s hs
  have hs' : s ∈ Ioc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
  simp only [sub_mul]
  rw [integral_sub (hi s hs') (hi' s hs')]

end RegularityStructures

end
