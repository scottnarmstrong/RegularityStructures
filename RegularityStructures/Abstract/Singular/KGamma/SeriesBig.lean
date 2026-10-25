/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SeriesLinear

/-!
# The series for large scales `2^{-n} ≥ d`
For `s = 2^n d ≤ 1` the term is estimated in the large form (`polyUS_eq_large_of_slab`),
`polyUS n = ⟨Rf − Π_x f(x), K^{k,γ}_{n;yx}⟩ − ∑_{|k| ≥ deg i + 2} τ_i ⟨Π_y e_i, D^k K_n(y−·)⟩`,
with the Taylor kernel for the exponent `σ' = ⌈σ⌉ > σ = γ + 2 − |k|` (same `taylorIdx`):
* if `128 · 2^{-n} ≤ W`, by the local bound (6.6): `d^σ s^{σ'−σ} W^{η−γ}`;
* if `128 · 2^{-n} > W` (including `n = 0`), by the layer bound and the model bound for
  `Π_x f(x) = ∑_i f(x)_i Π_x e_i`: `d^σ s^{σ'−σ} W^{α∧η−γ}`;
* the `τ`-terms by the model bound.
Result: `exists_abs_polyUS_le_of_le_one`: `|polyUS n| ≤ C K₀ C_f d^σ W^{α∧η−γ} s^a`.
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N N' : ℕ}
  {h : ParabolicSpace → ℝ}

/-- `u^g ≤ 128^g W^{-g}` if `u W ≤ 128` and `g ≥ 0`. -/
theorem rpow_le_of_mul_le {u W g : ℝ} (hu : 0 < u) (hW : 0 < W) (h : u * W ≤ 128) (hg : 0 ≤ g) :
    u ^ g ≤ 128 ^ g * W ^ (-g) := by
  have h1 : u ≤ 128 * W⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hW]; exact h
  calc u ^ g ≤ (128 * W⁻¹) ^ g := Real.rpow_le_rpow hu.le h1 hg
    _ = 128 ^ g * W ^ (-g) := by
        rw [Real.mul_rpow (by norm_num) (inv_nonneg.2 hW.le), Real.rpow_neg hW.le,
          Real.inv_rpow hW.le]

/-- The exponent comparison `W^{η−γ} ≤ W^{α∧η−γ}` for `W ≤ 1`. -/
theorem rpow_le_rpow_min {W η α γ : ℝ} (hW : 0 < W) (hW1 : W ≤ 1) :
    W ^ (η - γ) ≤ W ^ (min α η - γ) :=
  Real.rpow_le_rpow_of_exponent_ge hW hW1 (by linarith [min_le_right α η])

end RegularityStructures

end
