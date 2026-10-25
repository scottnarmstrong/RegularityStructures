/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Basic

/-!
# Multilevel Schauder: the polynomial components of `𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x)`

`Model.abs_kGamma_sub_gamma_poly_le`: for `k` with `|k|_𝔰 < γ + 2`,
`|(𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x))_{X^k}| ≤ c C_Π max(C_Γ, 1) C_f d(y, x)^{γ + 2 − |k|_𝔰}`,
the polynomial part of the `D^{γ+2}` bound in [Hai14, Theorem 5.12] (together with
`Model.abs_kGamma_sub_gamma_nonpoly_le` for the other components).  The constant `c` depends only
on `𝒯, γ, N, k`; the hypotheses are those of the non-polynomial bound plus
`I` produces no `T̄` component (`hIpoly`), the polynomial compatibility `M.IsPolyCompatible P`,
and the non-integrality conditions `γ + 2 − |k|_𝔰 ≠ |l|_𝔰` (all `l`) and `|k|_𝔰 ≠ deg i + 2`
(`deg i < γ`, `i` not a polynomial component `P.emb l`; the polynomial components contribute
vanishing pairings `PolyPairing.Main` because `N' ≤ N`).  [Hai14, proof of Theorem 5.12, (5.44)–(5.50)].
-/

public section

open Set

namespace RegularityStructures

theorem eq_zero_of_parabolicNorm_eq_zero {z : ParabolicSpace} (h : parabolicNorm z = 0) :
    z = 0 := by
  have h0 := Real.sqrt_nonneg |z.1|
  have h1 : 0 ≤ ∑ i, |z.2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h2 : Real.sqrt |z.1| = 0 := by unfold parabolicNorm at h; linarith
  have h3 : ∑ i, |z.2 i| = 0 := by unfold parabolicNorm at h; linarith
  have hz1 : z.1 = 0 := by
    have := (Real.sqrt_eq_zero (abs_nonneg _)).1 h2
    exact abs_eq_zero.1 this
  have hz2 : ∀ i, z.2 i = 0 := fun i => by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => abs_nonneg _)).1 h3 i (Finset.mem_univ i)
    exact abs_eq_zero.1 this
  exact Prod.ext hz1 (funext hz2)

end RegularityStructures

end
