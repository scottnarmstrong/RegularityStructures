/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.Defs
public import RegularityStructures.Abstract.Singular.Kernel

/-!
# The shell derivatives `D^k K_n(x - ·)` against the lattice reconstruction

Specialisation of the local and layer bounds for scaled test functions to the test functions
`y ↦ D^k K_n(x - y)`, `K_n = scaledShell h n`, of a (causal) shell profile `h`, which are scaled at
`x` with radius `2^{-n}` and constant `C (2^n)^{|k|_𝔰 + 3}`. For `x` in the time slab:

* `exists_abs_singShellPairing_le`: small scales `64 · 2^{-n} ≤ ‖x‖_P`,
  `|⟨R f - Π_x f(x), D^k K_n(x - ·)⟩| ≤ C K₀ C_f 2^{(|k| - 2 - γ) n} ‖x‖_P^{η - γ}`;
* `exists_abs_latticeRecon_shell_le`: all scales (layer bound),
  `|⟨R f, D^k K_n(x - ·)⟩| ≤ C K₀ C_f 2^{(|k| - 2 - α ∧ η) n}`;
* `exists_abs_latticeRecon_shell_le_timeTaylor`: for `0 ≤ x₀ ≤ 4^{-n}`, `1 ≤ n`,
  `|⟨R f, D^k K_n(x - ·)⟩| ≤ C K₀ C_f (x₀ 4^n)^m 2^{(|k| - 2 - α ∧ η) n}`;
* `exists_abs_pairing_shell_le`: `|⟨Π_x e_i, D^k K_n(x - ·)⟩| ≤ C K₀ 2^{(|k| - 2 - deg i) n}`.

Source: [Hai14] = arXiv:1303.5113v4, (5.15)–(5.16), Prop. 6.9, (6.6), §7.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace RegularityStructures

theorem shell_scale_eq {u : ℝ} (hu : 0 < u) (C L c : ℝ) :
    C * u ^ (L + 3) * (u⁻¹) ^ (5 : ℕ) * (u⁻¹) ^ c = C * u ^ (L - 2 - c) := by
  have h5 : (u⁻¹) ^ (5 : ℕ) = u ^ (-5 : ℝ) := by
    rw [Real.rpow_neg hu.le, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
  have hc : (u⁻¹) ^ c = u ^ (-c) := by
    rw [Real.rpow_neg hu.le, Real.inv_rpow hu.le]
  rw [h5, hc, mul_assoc, mul_assoc, ← Real.rpow_add hu, ← Real.rpow_add hu]
  congr 2
  ring

end RegularityStructures

end
