/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Identification.CubeFull
public import Phi43.Structure.EnlargedDegreesF
public import Phi43.Structure.QuadraticPolynomialSector
public import RegularityStructures.Abstract.Singular.Slab.BlockProj
import Mathlib.Tactic.Linarith

/-!
# Expansion of the abstract solution

This is a step of the identification of the renormalised equation ([Hai14, (9.22)]).

The fixed point equation `U = -Q_{<γ}(𝒦 (cube U)) + v` has the vector form
`U = -lowerProj γ K + v` with `K - I (blockProj A (Q_{<κ} U³)) ∈ T̄` (the operator `𝒦` has
non-polynomial part `I`; `Model.kGammaRemG_sub_mem_subspace`) and `v - Ψ ∈ T̄` (the datum has
non-polynomial part `Ψ`).  For `U` in the span of `Ψ, 1, I(Ψ³), I(Ψ²), Xᵢ`
(`phi43AnsatzF a φ c₃ c₂ ψ`) this forces `a = 1`, `c₃ = -1`, `c₂ = -3φ`
(`phi43_expansion_of_fixedPoint`).
-/

public section

namespace RegularityStructures.Phi43

private theorem old_not_mem_range {τ : Symbol} (h1 : τ ≠ .one) (h2 : τ ≠ .x0)
    (h3 : ∀ i, τ ≠ .x i) (h4 : ∀ p, τ ≠ .xMul p) :
    SymbolF.old τ ∉ Set.range phi43PolyEmbF := by
  rw [phi43PolyEmbF_old_range, phi43QuadraticPolyEmb_range]
  rintro (h | h | ⟨i, h⟩ | ⟨p, h⟩)
  exacts [h1 h, h2 h, h3 i h, h4 p h]

private theorem coord_of_poly {κ : Kappa} {w : SymbolF → ℝ}
    (hw : w ∈ (phi43PolynomialSectorF κ).subspace) {τ : Symbol} (h1 : τ ≠ .one) (h2 : τ ≠ .x0)
    (h3 : ∀ i, τ ≠ .x i) (h4 : ∀ p, τ ≠ .xMul p) : w (.old τ) = 0 :=
  hw _ (old_not_mem_range h1 h2 h3 h4)

private theorem ansatz_coord (a φ c₃ c₂ : ℝ) (ψ : Fin 3 → ℝ) :
    phi43AnsatzF a φ c₃ c₂ ψ (.old .psi) = a ∧
    phi43AnsatzF a φ c₃ c₂ ψ (.old .iPsiCube) = c₃ ∧
    phi43AnsatzF a φ c₃ c₂ ψ (.old .iPsiSq) = c₂ := by
  simp [phi43AnsatzF, phi43EF, Finset.sum_apply]

private theorem cubeLow_coord (a φ c₃ c₂ : ℝ) (ψ : Fin 3 → ℝ) :
    phi43CubeLowF a φ c₃ c₂ ψ (.old .psiCube) = a ^ 3 ∧
    phi43CubeLowF a φ c₃ c₂ ψ (.old .psiSq) = 3 * a ^ 2 * φ := by
  simp [phi43CubeLowF, phi43EF, Finset.sum_apply]

/-- **Expansion of the abstract solution** ([Hai14, (9.22)]): if `U` in the span of
`Ψ, 1, I(Ψ³), I(Ψ²), Xᵢ` solves `U = -Q_{<γ} K + v` with `K ≡ I (blockProj A Q_{<κ}U³)` and
`v ≡ Ψ` modulo the polynomials, then `U = Ψ + φ·1 - I(Ψ³) - 3φ I(Ψ²) + φᵢ Xᵢ`. -/
theorem phi43_expansion_of_fixedPoint (κ : Kappa) (a φ c₃ c₂ : ℝ) (ψ : Fin 3 → ℝ)
    (K v : SymbolF → ℝ)
    (hU : phi43AnsatzF a φ c₃ c₂ ψ =
      -RegularityStructures.lowerProj (phi43RegularityStructureF κ).deg (gamma κ) K + v)
    (hK : K - phi43IntegrationF (RegularityStructures.blockProj phi43XiFreeF
        (RegularityStructures.lowerProj (phi43RegularityStructureF κ).deg κ.1
          ((phi43ProductF κ).mul (phi43AnsatzF a φ c₃ c₂ ψ)
            ((phi43ProductF κ).mul (phi43AnsatzF a φ c₃ c₂ ψ) (phi43AnsatzF a φ c₃ c₂ ψ))))) ∈
      (phi43PolynomialSectorF κ).subspace)
    (hv : v - phi43EF .psi ∈ (phi43PolynomialSectorF κ).subspace) :
    a = 1 ∧ c₃ = -1 ∧ c₂ = -3 * φ := by
  have hk : 0 < κ.1 := κ.2.1
  have hk' : κ.1 < 1 / 16 := κ.2.2
  have hcube := lowerProj_cube_ansatz κ a φ c₃ c₂ ψ 0 (fun _ _ => rfl)
  simp only [add_zero] at hcube
  rw [hcube] at hK
  obtain ⟨hc1, hc2⟩ := cubeLow_coord a φ c₃ c₂ ψ
  obtain ⟨ha1, ha2, ha3⟩ := ansatz_coord a φ c₃ c₂ ψ
  have hlt : ∀ τ : Symbol, homogeneity κ τ < gamma κ → RegularityStructures.lowerProj
      (phi43RegularityStructureF κ).deg (gamma κ) K (.old τ) = K (.old τ) := fun τ h =>
    RegularityStructures.lowerProj_apply_of_lt h
  have hKc (τ : Symbol) (h1 : τ ≠ .one) (h2 : τ ≠ .x0) (h3 : ∀ i, τ ≠ .x i)
      (h4 : ∀ p, τ ≠ .xMul p) : K (.old τ) =
      phi43IntegrationF (RegularityStructures.blockProj phi43XiFreeF (phi43CubeLowF a φ c₃ c₂ ψ))
        (.old τ) := by
    have := coord_of_poly hK h1 h2 h3 h4
    simpa [sub_eq_zero] using this
  have hvc (τ : Symbol) (h0 : τ ≠ .psi) (h1 : τ ≠ .one) (h2 : τ ≠ .x0) (h3 : ∀ i, τ ≠ .x i)
      (h4 : ∀ p, τ ≠ .xMul p) : v (.old τ) = 0 := by
    have := coord_of_poly hv h1 h2 h3 h4
    simpa [phi43EF, Pi.single_apply, h0] using this
  have hXi : ∀ τ ∈ ({.psiCube, .psiSq} : Finset Symbol), SymbolF.old τ ∈ phi43XiFreeF := by
    intro τ hτ
    simp only [phi43XiFreeF, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq]
    intro h
    simp at hτ
    rcases hτ with rfl | rfl <;> cases h
  have hdeg : ∀ τ, τ = .psi ∨ τ = .iPsiCube ∨ τ = .iPsiSq → homogeneity κ τ < gamma κ := by
    intro τ h
    unfold gamma
    rcases h with rfl | rfl | rfl <;> simp only [homogeneity] <;> linarith
  have e1 := congrFun hU (.old .psi)
  have e2 := congrFun hU (.old .iPsiCube)
  have e3 := congrFun hU (.old .iPsiSq)
  simp only [Pi.add_apply, Pi.neg_apply] at e1 e2 e3
  rw [hlt _ (hdeg _ (Or.inl rfl)), hKc .psi (by simp) (by simp) (by simp) (by simp)] at e1
  rw [hlt _ (hdeg _ (Or.inr (Or.inl rfl))),
    hKc .iPsiCube (by simp) (by simp) (by simp) (by simp)] at e2
  rw [hlt _ (hdeg _ (Or.inr (Or.inr rfl))),
    hKc .iPsiSq (by simp) (by simp) (by simp) (by simp)] at e3
  have hvp : v (.old .psi) = 1 := by
    have := coord_of_poly hv (τ := .psi) (by simp) (by simp) (by simp) (by simp)
    simp [phi43EF] at this
    linarith
  rw [hvc _ (by simp) (by simp) (by simp) (by simp) (by simp)] at e2 e3
  have hn : SymbolF.old Symbol.noise ∉ phi43XiFreeF := by simp [phi43XiFreeF]
  have i1 : phi43IntegrationF (RegularityStructures.blockProj phi43XiFreeF
      (phi43CubeLowF a φ c₃ c₂ ψ)) (.old .psi) = 0 := by
    exact RegularityStructures.blockProj_apply_of_notMem hn (phi43CubeLowF a φ c₃ c₂ ψ)
  have i2 : phi43IntegrationF (RegularityStructures.blockProj phi43XiFreeF
      (phi43CubeLowF a φ c₃ c₂ ψ)) (.old .iPsiCube) = phi43CubeLowF a φ c₃ c₂ ψ (.old .psiCube) := by
    change RegularityStructures.blockProj phi43XiFreeF _ (.old .psiCube) = _
    exact RegularityStructures.blockProj_apply_of_mem (hXi .psiCube (by simp))
      (phi43CubeLowF a φ c₃ c₂ ψ)
  have i3 : phi43IntegrationF (RegularityStructures.blockProj phi43XiFreeF
      (phi43CubeLowF a φ c₃ c₂ ψ)) (.old .iPsiSq) = phi43CubeLowF a φ c₃ c₂ ψ (.old .psiSq) := by
    change RegularityStructures.blockProj phi43XiFreeF _ (.old .psiSq) = _
    exact RegularityStructures.blockProj_apply_of_mem (hXi .psiSq (by simp))
      (phi43CubeLowF a φ c₃ c₂ ψ)
  rw [i1] at e1
  rw [i2] at e2
  rw [i3] at e3
  rw [hc1] at e2
  rw [hc2] at e3
  rw [ha1, hvp] at e1
  have haa : a = 1 := by linarith
  subst haa
  refine ⟨rfl, ?_, ?_⟩
  · rw [ha2] at e2; linarith
  · rw [ha3] at e3; linarith

end RegularityStructures.Phi43

end
