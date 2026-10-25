/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Set.Finite.List
public import Phi43.Potential.TestFunction
public import RegularityStructures.Abstract.RegularityStructure
public import RegularityStructures.Abstract.Singular.Local.Const

/-!
# The forcing `ζ = Q ∗ ξ` in `DerivHyp` form

Packaging of `abs_ddA_potConv_le` for `Phi43.Inhomogeneity.Theta`: the derivative constants
`potGc N 𝒯 γ L = r4ModelConst 𝒯 γ · ∑_{|l| ≤ L} potTestConst N l` depend only on the structure, the
cutoff `γ` and the kernel `Q`; with `B = max(1, C_Γ) C_Π` one has `DerivHyp (Q ∗ ξ) (Gc L * B) L`
for all `L` (`derivHyp_potConv`), and `Q ∗ ξ` is smooth and spatially periodic
(`perSmooth_potConv'`) when `ξ` is.
-/

public section

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace RegularityStructures.Potential

open RegularityStructures.Inhomogeneity

/-- The sum of the test constants over all words of length at most `L`. -/
@[expose] noncomputable def potWordConst (N L : ℕ) : ℝ :=
  ∑ l ∈ (List.finite_length_le (Fin 4) L).toFinset, potTestConst N l

theorem potWordConst_nonneg (N L : ℕ) : 0 ≤ potWordConst N L :=
  Finset.sum_nonneg fun l _ => (potTestConst_pos N l).le

theorem potTestConst_le_potWordConst (N : ℕ) {L : ℕ} {l : List (Fin 4)} (hl : l.length ≤ L) :
    potTestConst N l ≤ potWordConst N L :=
  Finset.single_le_sum (f := fun l => potTestConst N l) (fun l _ => (potTestConst_pos N l).le)
    ((List.finite_length_le (Fin 4) L).mem_toFinset.2 hl)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- The derivative constants of `ζ = Q ∗ ξ`. -/
@[expose] noncomputable def potGc (N : ℕ) (𝒯 : RegularityStructure ι) (γ : ℝ) (L : ℕ) : ℝ :=
  r4ModelConst 𝒯 γ * potWordConst N L

theorem potGc_nonneg (N : ℕ) {γ : ℝ} (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (L : ℕ) :
    0 ≤ potGc N 𝒯 γ L :=
  mul_nonneg (r4ModelConst_nonneg 𝒯 hdeg) (potWordConst_nonneg N L)

theorem perSmooth_potConv' {ξ : ParabolicSpace → ℝ} (hξ : PerSmooth ξ) (N : ℕ) :
    PerSmooth (potConv ξ (potQ N)) :=
  perSmooth_potConv hξ (contDiff_potQ N) (by simpa [ddA] using hasCompactSupport_ddA_potQ N [])

/-- Integer spatial periodicity and smoothness give `PerSmooth`. -/
theorem perSmooth_of_integer_periodic {ξ : ParabolicSpace → ℝ} (hs : ContDiff ℝ ∞ ξ)
    (hp : ∀ (n : Fin 3 → ℤ) (z : ParabolicSpace), ξ (z.1, fun i => z.2 i + (n i : ℝ)) = ξ z) :
    PerSmooth ξ where
  smooth := hs
  periodic z c hc := by
    have : ∀ i, ∃ n : ℤ, c i = n := fun i => by
      have h := congrFun hc i
      simp only [torusProj] at h
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h
      exact ⟨n, by simpa using hn.symm⟩
    choose n hn using this
    have := hp n z
    simp only [← hn] at this
    exact this

end RegularityStructures.Potential

end
