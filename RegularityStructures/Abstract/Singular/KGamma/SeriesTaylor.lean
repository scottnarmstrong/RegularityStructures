/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.WrapShell
public import RegularityStructures.Abstract.Singular.TaylorKernel.ScaledTest
public import RegularityStructures.Abstract.Singular.Local.Const

/-!
# The Taylor-remainder kernel against the lattice reconstruction and the model, scales `n ≥ 1`
For `n ≥ 1`, `0 < d = ‖y − x‖_𝔰 ≤ 2^{-n}` the kernel `K^{k,σ}_{n;yx}` (`dTaylorKernel`) is a test
function scaled at `x` with radius `2 · 2^{-n}` and constant `C (d 2^n)^σ (2^n)^{|k|+3}`. With
`A R⁵ R^c = C' d^σ (2^n)^{σ + |k| − 2 − c}` the local and layer bounds for scaled test functions
give, for `g = dTaylorKernel h k n σ x y`:
* `exists_abs_latticeRecon_sub_pairing_dTaylor_le`: the local bound (6.6), `c = γ`, for
  `128 · 2^{-n} ≤ ‖x‖_P`, with the extra factor `‖x‖_P^{η − γ}`;
* `exists_abs_latticeRecon_dTaylor_le`: the layer bound, `c = α ∧ η`;
* `exists_abs_pairing_dTaylor_le`: `|⟨Π_x e_i, g⟩|`, `c = deg i`.
Source: [Hai14] = arXiv:1303.5113v4, (5.48)–(5.50), Prop. 6.16.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace RegularityStructures

/-- The scale bookkeeping `C (d u)^σ u^{L+3} (2/u)⁵ (2/u)^c = C 2⁵ 2^c d^σ u^{σ+L-2-c}`. -/
theorem taylor_scale_eq {u d : ℝ} (hu : 0 < u) (hd : 0 < d) (Cd σ L c : ℝ) :
    Cd * (d * u) ^ σ * u ^ (L + 3) * (2 * u⁻¹) ^ (5 : ℕ) * (2 * u⁻¹) ^ c =
      (Cd * 2 ^ 5 * 2 ^ c) * d ^ σ * u ^ (σ + L - 2 - c) := by
  have h5 : (u⁻¹) ^ (5 : ℕ) = u ^ (-5 : ℝ) := by
    rw [Real.rpow_neg hu.le, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
  have hc : (u⁻¹) ^ c = u ^ (-c) := by
    rw [Real.rpow_neg hu.le, Real.inv_rpow hu.le]
  have key : u ^ σ * u ^ (L + 3) * u ^ (-5 : ℝ) * u ^ (-c) = u ^ (σ + L - 2 - c) := by
    rw [← Real.rpow_add hu, ← Real.rpow_add hu, ← Real.rpow_add hu]
    congr 1; ring
  rw [Real.mul_rpow hd.le hu.le, mul_pow, Real.mul_rpow (by norm_num) (inv_nonneg.2 hu.le), h5, hc]
  linear_combination (Cd * 2 ^ 5 * 2 ^ c * d ^ σ) * key

theorem dTaylorKernel_eq_zero_of_lt {h : ParabolicSpace → ℝ} (hh : ContDiff ℝ ∞ h)
    (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) (k : Fin 4 →₀ ℕ) (n : ℕ) (σ : ℝ)
    {x y : ParabolicSpace} {T : ℝ} (hx : x.1 ≤ T) (hy : y.1 ≤ T) (w : ParabolicSpace)
    (hw : T < w.1) : dTaylorKernel h k n σ x y w = 0 := by
  unfold dTaylorKernel
  rw [lineIter_multiDirs_scaledShell_sub_eq_zero hh hc k n (hy.trans hw.le), zero_sub, neg_eq_zero]
  exact Finset.sum_eq_zero fun l _ => by
    rw [lineIter_multiDirs_scaledShell_sub_eq_zero hh hc (k + l) n (hx.trans hw.le), mul_zero]

end RegularityStructures

end
