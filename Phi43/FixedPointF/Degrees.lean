/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.FixedPointF.Sectors
import Mathlib.Tactic.Linarith

/-!
# Degrees of the symbols of `V` and `W`; regularity of the sectors

[Hai14, Section 9.4]. With `α = -1/2 - κ`: every symbol of `V` has degree `≥ α`, every symbol of
`W` degree `≥ α + α`, and every planted symbol degree `≥ 3/2 - 5κ`.  Hence `V` is a sector of
regularity `α` and `W` one of regularity `α + α`.
-/

public section

namespace RegularityStructures.Phi43

theorem phi43DegreeF_planted_ge (κ : Kappa) (τ : Phi43PlantSource) :
    3 / 2 - 5 * κ.1 ≤ phi43DegreeF κ (.planted τ) := by
  have h0 := κ.2.1
  have h1 := κ.2.2
  cases τ <;> simp only [phi43DegreeF, Phi43PlantSource.symbol, homogeneity] <;> linarith

theorem phi43DegreeF_V_ge (κ : Kappa) {j : SymbolF} (hj : phi43VBool j = true) :
    -1 / 2 - κ.1 ≤ phi43DegreeF κ j := by
  have h0 := κ.2.1
  have h1 := κ.2.2
  cases j with
  | planted τ =>
    have := phi43DegreeF_planted_ge κ τ
    linarith
  | old τ => cases τ <;> simp [phi43VBool] at hj <;> simp only [phi43DegreeF, homogeneity] <;>
      linarith

theorem phi43DegreeF_W_ge (κ : Kappa) {j : SymbolF} (hj : phi43WBool j = true) :
    (-1 / 2 - κ.1) + (-1 / 2 - κ.1) ≤ phi43DegreeF κ j := by
  have h0 := κ.2.1
  have h1 := κ.2.2
  by_cases hv : phi43VBool j = true
  · have := phi43DegreeF_V_ge κ hv
    linarith
  · cases j with
    | planted τ => simp [phi43VBool] at hv
    | old τ => cases τ <;> simp [phi43VBool, phi43WBool] at hv hj <;>
        simp only [phi43DegreeF, homogeneity] <;> linarith

theorem phi43SectorV_ofRegularity (κ : Kappa) :
    RegularityStructure.IsSector.OfRegularity (phi43RegularityStructureF κ) phi43SectorV
      (-1 / 2 - κ.1) := by
  intro β hβ a ha
  funext j
  rw [homogeneousProj_apply]
  split_ifs with h
  · by_contra hne
    have hv : phi43VBool j = true := by
      by_contra hv
      exact hne (mem_phi43SectorV.1 ha j (by simpa using hv))
    have := phi43DegreeF_V_ge κ hv
    change phi43DegreeF κ j = β at h
    linarith
  · rfl

theorem phi43SectorW_ofRegularity (κ : Kappa) :
    RegularityStructure.IsSector.OfRegularity (phi43RegularityStructureF κ) phi43SectorW
      ((-1 / 2 - κ.1) + (-1 / 2 - κ.1)) := by
  intro β hβ a ha
  funext j
  rw [homogeneousProj_apply]
  split_ifs with h
  · by_contra hne
    have hv : phi43WBool j = true := by
      by_contra hv
      exact hne (mem_phi43SectorW.1 ha j (by simpa using hv))
    have := phi43DegreeF_W_ge κ hv
    change phi43DegreeF κ j = β at h
    linarith
  · rfl

end RegularityStructures.Phi43

end
