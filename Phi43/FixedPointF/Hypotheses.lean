/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.FixedPointF.ProductClosure
public import Phi43.FixedPointF.SectorSupport
public import RegularityStructures.Abstract.Singular.BlockInvariant
public import RegularityStructures.Analysis.Parabolic.SingularKernel
import Mathlib.Tactic.Linarith

/-!
# Structural hypotheses of the window fixed point at the `Φ⁴₃` data

[Hai14, Section 9.4, Proposition 9.8]. With `γ₀ = gamma κ = 1 + 3κ`, `α = -1/2 - κ`,
`ζ = -3/2 - 3κ`: block invariance of the `Ξ`-free symbols (`hAG`), the degree and non-resonance
hypotheses (`hdeg`, `hAζ`, `hnat`, `hni`, `hpolyV`), and the facts on the integration
`phi43IntegrationF` needed by the model clauses.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The regularity `α = -1/2 - κ` of the `Φ⁴₃` solution sector. -/
abbrev phi43Alpha (κ : Kappa) : ℝ := -1 / 2 - κ.1

/-- The regularity `ζ = -3/2 - 3κ` of the `Ξ`-free block. -/
abbrev phi43Zeta (κ : Kappa) : ℝ := -3 / 2 - 3 * κ.1

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

theorem phi43XiFreeF_isBlockInvariant (κ : Kappa) :
    (phi43RegularityStructureF κ).IsBlockInvariant phi43XiFreeF :=
  isBlockInvariant_univ_erase (ξ := SymbolF.old .noise)
    (fun g hg => phi43ExtensionGroupF_noise_fixed κ g hg)
    (fun g hg i hi => by
      rw [phi43ExtensionGroupF_noise_coord κ g hg]
      exact Pi.single_eq_of_ne hi.symm 1)

theorem phi43DegreeF_gt_neg_four (κ : Kappa) (j : SymbolF) : -4 < phi43DegreeF κ j := by
  have h0 := κ.2.1
  have h1 := κ.2.2
  cases j with
  | planted τ =>
    have := phi43DegreeF_planted_ge κ τ
    linarith
  | old τ => cases τ <;> simp only [phi43DegreeF, homogeneity] <;> linarith

theorem phi43DegreeF_xiFree_ge (κ : Kappa) {i : SymbolF} (hi : i ∈ phi43XiFreeF) :
    phi43Zeta κ ≤ phi43DegreeF κ i := by
  have h0 := κ.2.1
  have h1 := κ.2.2
  cases i with
  | planted τ =>
    have := phi43DegreeF_planted_ge κ τ
    simp only [phi43Zeta]
    linarith
  | old τ =>
    have hτ : τ ≠ .noise := by simpa [phi43XiFreeF] using hi
    cases τ <;> first | exact absurd rfl hτ | (simp only [phi43Zeta, phi43DegreeF, homogeneity]; linarith)

theorem phi43_hnat (κ : Kappa) (k : Fin 4 →₀ ℕ)
    (l : Fin 4 →₀ ℕ) :
    (multiDeg l : ℝ) ≠ gamma κ + phi43Alpha κ + phi43Alpha κ + 2 - multiDeg k := by
  intro h
  have h0 := κ.2.1
  have h1 := κ.2.2
  have he : ((multiDeg l + multiDeg k : ℕ) : ℝ) = κ.1 + 2 := by
    push_cast
    simp only [gamma, phi43Alpha] at h
    linarith
  have h2 : ((multiDeg l + multiDeg k : ℕ) : ℝ) < 3 := by linarith
  have h3 : (2 : ℝ) < ((multiDeg l + multiDeg k : ℕ) : ℝ) := by linarith
  have h2' : multiDeg l + multiDeg k < 3 := by exact_mod_cast h2
  have h3' : 2 < multiDeg l + multiDeg k := by exact_mod_cast h3
  omega

theorem phi43_hni (κ : Kappa) (k : Fin 4 →₀ ℕ) (i : SymbolF)
    (hi : i ∉ Set.range (phi43PolynomialSectorF κ).emb) :
    (multiDeg k : ℝ) ≠ (phi43RegularityStructureF κ).deg i + 2 :=
  phi43DegreeF_nonpolynomial_shifted_ne_nat κ i hi _

theorem phi43IntegrationF_polyEmb_eq_zero (κ : Kappa) (a : SymbolF → ℝ) (k : PolyIndex 3) :
    phi43IntegrationF a ((phi43PolynomialSectorF κ).emb k) = 0 := by
  change phi43IntegrationF a (SymbolF.old (phi43QuadraticPolyEmb k)) = 0
  rcases phi43QuadraticPolyEmb_cases k with h | h | ⟨i, h⟩ | ⟨q, h⟩ <;>
    simp [h, phi43IntegrationF]

theorem phi43IntegrationF_single_abs_le (i j : SymbolF) :
    |phi43IntegrationF (Pi.single i 1) j| ≤ 1 := by
  rw [phi43IntegrationF_single]
  cases phi43IntegrationSymbolF i with
  | none => simp
  | some σ =>
    simp only [Pi.single_apply]
    split_ifs <;> simp

theorem phi43IntegrationF_mem_sectorV (a : SymbolF → ℝ) : phi43IntegrationF a ∈ phi43SectorV :=
  mem_phi43SectorV.2 fun _ hj => phi43IntegrationF_coord_of_VBool a hj

theorem phi43_hpolyV (κ : Kappa) (k : PolyIndex 3) :
    (Pi.single ((phi43PolynomialSectorF κ).emb k) 1 : SymbolF → ℝ) ∈ phi43SectorV :=
  single_mem_phi43SectorV (phi43VBool_polyEmbF k)

end RegularityStructures.Phi43

end
