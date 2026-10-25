/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.FixedPointF.Sectors

/-!
# Support of the group action on the symbols of `V` and `W`

[Hai14, Definition 2.5]. For `p : G`, the coordinates of `Γ_p e_τ` outside `V` (resp. `W`) vanish
for `τ ∈ V` (resp. `W`): explicit computations for `Ψ`, `I(Ψ)`, `I(Ψ²)`, `I(Ψ³)` and the extra
symbols of `W`, the polynomial sector for `1, X₀, Xᵢ, XᵢXⱼ`, and the integral structure
`Γ e_{𝓘 d} - 𝓘 Γ e_d ∈ T̄` for the planted symbols.
-/

public section

namespace RegularityStructures.Phi43

private theorem act_psi (p : G) (σ : Symbol) (hσ : phi43VBool (.old σ) = false) :
    phi43CoordinateEquiv (structureBasisAction p .psi) σ = 0 := by
  cases σ <;> simp [phi43VBool, phi43CoordinateEquiv, structureBasisAction, primitiveAction,
    basis] at hσ ⊢

private theorem act_iPsi (p : G) (σ : Symbol) (hσ : phi43VBool (.old σ) = false) :
    phi43CoordinateEquiv (structureBasisAction p .iPsi) σ = 0 := by
  cases σ <;> simp [phi43VBool, phi43CoordinateEquiv, structureBasisAction, primitiveAction,
    basis] at hσ ⊢

private theorem act_iPsiSq (p : G) (σ : Symbol) (hσ : phi43VBool (.old σ) = false) :
    phi43CoordinateEquiv (structureBasisAction p .iPsiSq) σ = 0 := by
  cases σ <;> simp [phi43VBool, phi43CoordinateEquiv, structureBasisAction, primitiveAction,
    basis] at hσ ⊢

private theorem act_iPsiCube (p : G) (σ : Symbol) (hσ : phi43VBool (.old σ) = false) :
    phi43CoordinateEquiv (structureBasisAction p .iPsiCube) σ = 0 := by
  cases σ <;> simp [phi43VBool, phi43CoordinateEquiv, structureBasisAction, primitiveAction,
    basis] at hσ ⊢

private theorem act_psiSq (p : G) (σ : Symbol) (hσ : phi43WBool (.old σ) = false) :
    phi43CoordinateEquiv (structureBasisAction p .psiSq) σ = 0 := by
  cases σ <;> simp [phi43WBool, phi43VBool, phi43CoordinateEquiv, structureBasisAction,
    primitiveAction, basis, basisProduct, productSymbol] at hσ ⊢

private theorem act_psiX (p : G) (i : Fin 3) (σ : Symbol) (hσ : phi43WBool (.old σ) = false) :
    phi43CoordinateEquiv (structureBasisAction p (.psiX i)) σ = 0 := by
  cases σ <;> simp [phi43WBool, phi43VBool, phi43CoordinateEquiv, structureBasisAction,
    primitiveAction, basis, basisProduct, productSymbol] at hσ ⊢

private theorem act_iPsiPsi (p : G) (σ : Symbol) (hσ : phi43WBool (.old σ) = false) :
    phi43CoordinateEquiv (structureBasisAction p .iPsiPsi) σ = 0 := by
  cases σ <;> simp [phi43WBool, phi43VBool, phi43CoordinateEquiv, structureBasisAction,
    integratedPsiProductAction, basis] at hσ ⊢

private theorem act_iPsiSqPsi (p : G) (σ : Symbol) (hσ : phi43WBool (.old σ) = false) :
    phi43CoordinateEquiv (structureBasisAction p .iPsiSqPsi) σ = 0 := by
  cases σ <;> simp [phi43WBool, phi43VBool, phi43CoordinateEquiv, structureBasisAction,
    primitiveAction, basis, basisProduct, productSymbol] at hσ ⊢

private theorem act_iPsiCubePsi (p : G) (σ : Symbol) (hσ : phi43WBool (.old σ) = false) :
    phi43CoordinateEquiv (structureBasisAction p .iPsiCubePsi) σ = 0 := by
  cases σ <;> simp [phi43WBool, phi43VBool, phi43CoordinateEquiv, structureBasisAction,
    primitiveAction, basis, basisProduct, productSymbol] at hσ ⊢

private theorem act_iPsiCubeSq (p : G) (σ : Symbol) (hσ : phi43WBool (.old σ) = false) :
    phi43CoordinateEquiv (structureBasisAction p .iPsiCubeSq) σ = 0 := by
  cases σ <;> simp [phi43WBool, phi43VBool, phi43CoordinateEquiv, structureBasisAction,
    primitiveAction, basis, basisProduct, productSymbol] at hσ ⊢

theorem phi43VBool_polyEmbF (k : PolyIndex 3) : phi43VBool (phi43PolyEmbF k) = true := by
  rcases phi43QuadraticPolyEmb_cases k with h | h | ⟨i, h⟩ | ⟨q, h⟩ <;>
    simp [phi43PolyEmbF, h, phi43VBool]

private theorem not_mem_polyRange_of_VBool {j : SymbolF} (hj : phi43VBool j = false) :
    j ∉ Set.range phi43PolyEmbF := by
  rintro ⟨k, rfl⟩
  rw [phi43VBool_polyEmbF] at hj
  exact Bool.noConfusion hj

theorem phi43IntegrationF_coord_of_VBool (a : SymbolF → ℝ) {j : SymbolF}
    (hj : phi43VBool j = false) : phi43IntegrationF a j = 0 := by
  cases j with
  | old σ => cases σ <;> simp [phi43IntegrationF, phi43VBool] at hj ⊢
  | planted σ => simp [phi43VBool] at hj

private theorem poly_single_support {τ : Symbol} (hτ : τ ∈ Set.range phi43QuadraticPolyEmb) :
    ∀ i, i ∉ Set.range phi43PolyEmbF → (Pi.single (.old τ) 1 : SymbolF → ℝ) i = 0 := by
  intro i hi
  have : i ≠ .old τ := fun h => hi (h ▸ (phi43PolyEmbF_old_range τ).2 hτ)
  exact Pi.single_eq_of_ne this _

theorem phi43ExtensionGroupF_V_support (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (SymbolF → ℝ))
    (hg : g ∈ (phi43RegularityStructureF κ).group) {i j : SymbolF}
    (hi : phi43VBool i = true) (hj : phi43VBool j = false) :
    g.val (Pi.single i 1) j = 0 := by
  have hjp := not_mem_polyRange_of_VBool hj
  cases i with
  | planted τ =>
    have h := (phi43PolynomialSubspaceF_mem κ _).1
      (phi43PolynomialSectorF_subspace κ ▸ phi43ExtensionGroupF_planted_mod_polynomial κ g hg τ)
      j hjp
    rw [Pi.sub_apply, sub_eq_zero] at h
    rw [h, phi43IntegrationF_coord_of_VBool _ hj]
  | old τ =>
    obtain ⟨p, hp⟩ := phi43ExtensionGroupF_old_params κ g hg
    have hpoly : τ ∈ Set.range phi43QuadraticPolyEmb → g.val (Pi.single (.old τ) 1) j = 0 :=
      fun hτ => (phi43PolynomialSectorF κ).invariant g hg _ (poly_single_support hτ) j hjp
    have hq : ∀ q : Symbol, (∀ σ, phi43VBool (.old σ) = false →
        phi43CoordinateEquiv (structureBasisAction p q) σ = 0) → q = τ →
        g.val (Pi.single (.old τ) 1) j = 0 := by
      rintro q hq rfl
      rw [hp]
      cases j with
      | old σ => exact hq σ hj
      | planted σ => rfl
    cases τ with
    | one => exact hpoly (by rw [phi43QuadraticPolyEmb_range]; simp)
    | x0 => exact hpoly (by rw [phi43QuadraticPolyEmb_range]; simp)
    | x i => exact hpoly (by rw [phi43QuadraticPolyEmb_range]; simp)
    | xMul q => exact hpoly (by rw [phi43QuadraticPolyEmb_range]; simp)
    | psi => exact hq _ (act_psi p) rfl
    | iPsi => exact hq _ (act_iPsi p) rfl
    | iPsiSq => exact hq _ (act_iPsiSq p) rfl
    | iPsiCube => exact hq _ (act_iPsiCube p) rfl
    | noise => simp [phi43VBool] at hi
    | psiCube => simp [phi43VBool] at hi
    | psiSq => simp [phi43VBool] at hi
    | psiX _ => simp [phi43VBool] at hi
    | psiSqX _ => simp [phi43VBool] at hi
    | iPsiPsi => simp [phi43VBool] at hi
    | iPsiPsiSq => simp [phi43VBool] at hi
    | iPsiSqPsi => simp [phi43VBool] at hi
    | iPsiSqPsiSq => simp [phi43VBool] at hi
    | iPsiCubePsi => simp [phi43VBool] at hi
    | iPsiCubePsiSq => simp [phi43VBool] at hi
    | iPsiCubeSq => simp [phi43VBool] at hi

theorem phi43ExtensionGroupF_W_support (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (SymbolF → ℝ))
    (hg : g ∈ (phi43RegularityStructureF κ).group) {i j : SymbolF}
    (hi : phi43WBool i = true) (hj : phi43WBool j = false) :
    g.val (Pi.single i 1) j = 0 := by
  by_cases hv : phi43VBool i = true
  · exact phi43ExtensionGroupF_V_support κ g hg hv (phi43VBool_of_phi43WBool_false hj)
  · obtain ⟨p, hp⟩ := phi43ExtensionGroupF_old_params κ g hg
    cases i with
    | planted τ => simp [phi43VBool] at hv
    | old τ =>
      have hq : ∀ q : Symbol, (∀ σ, phi43WBool (.old σ) = false →
          phi43CoordinateEquiv (structureBasisAction p q) σ = 0) → q = τ →
          g.val (Pi.single (.old τ) 1) j = 0 := by
        rintro q hq rfl
        rw [hp]
        cases j with
        | old σ => exact hq σ hj
        | planted σ => rfl
      cases τ with
      | psiSq => exact hq _ (act_psiSq p) rfl
      | psiX i => exact hq _ (act_psiX p i) rfl
      | iPsiPsi => exact hq _ (act_iPsiPsi p) rfl
      | iPsiSqPsi => exact hq _ (act_iPsiSqPsi p) rfl
      | iPsiCubePsi => exact hq _ (act_iPsiCubePsi p) rfl
      | iPsiCubeSq => exact hq _ (act_iPsiCubeSq p) rfl
      | one => simp [phi43VBool] at hv
      | noise => simp [phi43WBool, phi43VBool] at hi
      | x0 => simp [phi43VBool] at hv
      | x _ => simp [phi43VBool] at hv
      | xMul _ => simp [phi43VBool] at hv
      | psi => simp [phi43VBool] at hv
      | iPsi => simp [phi43VBool] at hv
      | psiCube => simp [phi43WBool, phi43VBool] at hi
      | psiSqX _ => simp [phi43WBool, phi43VBool] at hi
      | iPsiSq => simp [phi43VBool] at hv
      | iPsiCube => simp [phi43VBool] at hv
      | iPsiPsiSq => simp [phi43WBool, phi43VBool] at hi
      | iPsiSqPsiSq => simp [phi43WBool, phi43VBool] at hi
      | iPsiCubePsiSq => simp [phi43WBool, phi43VBool] at hi

theorem phi43SectorV_isSector (κ : Kappa) :
    (phi43RegularityStructureF κ).IsSector phi43SectorV :=
  isSector_blockSpan_of_support fun g hg i hi j hj =>
    phi43ExtensionGroupF_V_support κ g hg (by simpa [phi43VSyms] using hi)
      (by simpa [phi43VSyms] using hj)

theorem phi43SectorW_isSector (κ : Kappa) :
    (phi43RegularityStructureF κ).IsSector phi43SectorW :=
  isSector_blockSpan_of_support fun g hg i hi j hj =>
    phi43ExtensionGroupF_W_support κ g hg (by simpa [phi43WSyms] using hi)
      (by simpa [phi43WSyms] using hj)

end RegularityStructures.Phi43

end
