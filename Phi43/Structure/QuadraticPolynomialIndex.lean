/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.AbstractPolynomial
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.IntervalCases

/-!
# Explicit polynomial indices of parabolic degree at most two

These are the eleven monomials required for the polynomial cutoff 3 in
the Phi4 fixed point [Hai14, Sections 2.2, 9.4, Proposition 9.8]. The
existing strict cutoff-2 sector is not modified.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- Exactly the eleven multiindices of parabolic degree less than three. -/
def phi43QuadraticIndices : Finset (Fin 4 →₀ ℕ) :=
  {0, Finsupp.single 0 1, Finsupp.single 1 1, Finsupp.single 2 1, Finsupp.single 3 1,
    Finsupp.single 1 2, Finsupp.single 1 1 + Finsupp.single 2 1,
    Finsupp.single 1 1 + Finsupp.single 3 1, Finsupp.single 2 2,
    Finsupp.single 2 1 + Finsupp.single 3 1, Finsupp.single 3 2}

/-- Literal identification of each degree≤2 multiindex with its existing symbol. -/
def phi43QuadraticSymbolOfIndex (a : Fin 4 →₀ ℕ) : Symbol :=
  if a 0 = 1 then .x0
  else if a 1 + a 2 + a 3 = 0 then .one
  else if a 1 + a 2 + a 3 = 1 then
    if a 1 = 1 then .x 0 else if a 2 = 1 then .x 1 else .x 2
  else if a 1 = 2 then .xMul s(0, 0)
  else if a 2 = 2 then .xMul s(1, 1)
  else if a 3 = 2 then .xMul s(2, 2)
  else if a 1 = 1 then
    if a 2 = 1 then .xMul s(0, 1) else .xMul s(0, 2)
  else .xMul s(1, 2)

/-- Embedding of the polynomial cutoff 3 into the retained symbol type. -/
def phi43QuadraticPolyEmb (k : PolyIndex 3) : Symbol := phi43QuadraticSymbolOfIndex k.1

/-- Polynomial multiindex of an existing polynomial symbol. -/
def phi43QuadraticSymbolIndex : Symbol → (Fin 4 →₀ ℕ)
  | .x0 => Finsupp.single 0 1
  | .x i => Finsupp.single i.succ 1
  | .xMul p => Sym2.lift ⟨fun i j => Finsupp.single i.succ 1 + Finsupp.single j.succ 1,
      fun _ _ => add_comm _ _⟩ p
  | _ => 0

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

private theorem spatial_mem (b c d : ℕ) (h : b + c + d < 3) :
    Finsupp.single (1 : Fin 4) b + Finsupp.single 2 c + Finsupp.single 3 d ∈
      phi43QuadraticIndices := by
  have hb : b < 3 := by omega
  have hc : c < 3 := by omega
  have hd : d < 3 := by omega
  interval_cases b <;> interval_cases c <;> interval_cases d
  all_goals first | omega | simp [phi43QuadraticIndices]

theorem phi43QuadraticIndex_mem (k : PolyIndex 3) : k.1 ∈ phi43QuadraticIndices := by
  have hk := k.2
  rw [weight_parabolicWeight] at hk
  have he : k.1 = Finsupp.single 0 (k.1 0) + Finsupp.single 1 (k.1 1) +
      Finsupp.single 2 (k.1 2) + Finsupp.single 3 (k.1 3) := by
    ext i
    fin_cases i <;> simp
  by_cases h0 : k.1 0 = 1
  · have h1 : k.1 1 = 0 := by omega
    have h2 : k.1 2 = 0 := by omega
    have h3 : k.1 3 = 0 := by omega
    rw [he]
    simp [h0, h1, h2, h3, phi43QuadraticIndices]
  · have h00 : k.1 0 = 0 := by omega
    rw [he]
    simpa only [h00, Finsupp.single_zero, zero_add] using
      spatial_mem (k.1 1) (k.1 2) (k.1 3) (by omega)

theorem phi43QuadraticSymbolIndex_emb (k : PolyIndex 3) :
    phi43QuadraticSymbolIndex (phi43QuadraticPolyEmb k) = k.1 := by
  have hk := phi43QuadraticIndex_mem k
  simp only [phi43QuadraticIndices, Finset.mem_insert, Finset.mem_singleton] at hk
  change phi43QuadraticSymbolIndex (phi43QuadraticSymbolOfIndex k.1) = k.1
  rcases hk with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
  all_goals rw [hk]
  all_goals norm_num [phi43QuadraticSymbolOfIndex, phi43QuadraticSymbolIndex, Finsupp.single_apply]
  all_goals ext i; fin_cases i <;> norm_num [Finsupp.single_apply]

theorem phi43QuadraticPolyEmb_injective : Function.Injective phi43QuadraticPolyEmb := by
  intro k l hkl
  apply Subtype.ext
  rw [← phi43QuadraticSymbolIndex_emb k, ← phi43QuadraticSymbolIndex_emb l, hkl]

theorem phi43QuadraticPolyEmb_deg (κ : Kappa) (k : PolyIndex 3) :
    homogeneity κ (phi43QuadraticPolyEmb k) = polyDeg 3 k := by
  have hk := phi43QuadraticIndex_mem k
  simp only [phi43QuadraticIndices, Finset.mem_insert, Finset.mem_singleton] at hk
  change homogeneity κ (phi43QuadraticSymbolOfIndex k.1) = (Finsupp.weight parabolicWeight k.1 : ℝ)
  rcases hk with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
  all_goals rw [hk]
  all_goals norm_num [phi43QuadraticSymbolOfIndex, homogeneity, weight_parabolicWeight,
    Finsupp.single_apply]

end RegularityStructures.Phi43

end
