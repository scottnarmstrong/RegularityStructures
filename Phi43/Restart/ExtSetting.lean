/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Restart.Compat
public import RegularityStructures.Abstract.Ext514W.GammaNear
public import RegularityStructures.Abstract.Ext514W.SettingNear
public import Phi43.Structure.EnlargedXiFreeSectorF
public import Phi43.Structure.EnlargedIntegrationAxiomsF
public import Phi43.Structure.EnlargedPolynomialF
public import RegularityStructures.Abstract.Profile.Basic
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Profile.Realising

/-!
# The extension estimates (5.18) for the enlarged `Φ⁴₃` model at level `κ`

For an enlarged model `M'` realising the kernel for `phi43IntegrationF` on the `Ξ`-free block, with
window bounds at level `κ` and a qualitative growth model, `ExtSettingWNear` holds for
`V' = blockSpan phi43XiFreeF`, and the per-symbol Hairer estimate
(`Model.exists_abs_gammaMap_integral_le_win_near`) is summed over the symbols of degree `< κ` to
give, with a constant `c` independent of the model, the bound of `Γ'_{yx} 𝓘 e_i` for
`i ∈ {Ψ, Ψ², Ψ³} ∪ {d ∈ D : deg d < κ}` (all non-polynomial `Ξ`-free symbols of degree `< κ`).
-/

public section

open Set

namespace RegularityStructures.Phi43.Restart

variable {κ : Kappa} {N : ℕ} {M' : Model (phi43RegularityStructureF κ) parabolicSemigroup}

/-- The non-polynomial `Ξ`-free symbols of degree `< κ`. -/
@[expose] def ExtSource (κ : Kappa) (i : SymbolF) : Prop :=
  ∃ τ : Symbol, i = .old τ ∧ τ ≠ .noise ∧ τ ≠ .one ∧ homogeneity κ τ < κ.1

theorem old_one_mem_range : SymbolF.old .one ∈ Set.range (phi43PolynomialSectorF κ).emb := by
  obtain ⟨k, hk⟩ := (phi43QuadraticPolyEmb_range Symbol.one).2 (Or.inl rfl)
  exact ⟨k, by change SymbolF.old (phi43QuadraticPolyEmb k) = _; rw [hk]⟩

theorem ExtSource.mem {i : SymbolF} (h : ExtSource κ i) :
    (Pi.single i 1 : SymbolF → ℝ) ∈ blockSpan phi43XiFreeF ∧ phi43DegreeF κ i < κ.1 := by
  obtain ⟨τ, rfl, hn, -, hd⟩ := h
  exact ⟨Submodule.subset_span ⟨.old τ, by simpa [phi43XiFreeF] using hn, rfl⟩, hd⟩

theorem extSetting (hN : 3 ≤ N) (hreal : M'.IsRealisingP (annKernel0C N) κ.1
      (phi43PolynomialSectorF κ) phi43IntegrationF (blockSpan phi43XiFreeF))
    (hgr : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M'.GrowthModel κ.1 C' C'' ρP ρG p q)
    {CPi CGam₁ : ℝ} (hCPi : 0 ≤ CPi) (hPi : M'.PiBoundOn κ.1 CPi hairerTimeWindow)
    (hGam : M'.GammaBoundNearOn κ.1 CGam₁ 1 hairerTimeWindow) :
    M'.ExtSettingWNear (annKernel0C N) N κ.1 (phi43PolynomialSectorF κ) phi43IntegrationF
      (blockSpan phi43XiFreeF) CPi (gammaChainConst (Fintype.card SymbolF) CGam₁ 16) := by
  have hk : 0 < κ.1 := κ.2.1
  have hk' : κ.1 < 1 / 16 := κ.2.2
  exact
  { profile := shellProfile_annKernel0C N
    realising := hreal
    integration := phi43IntegrationF_isAbstractIntegration κ
    sector := phi43XiFreeF_isSector κ
    basis_mem := isCoordClosed_blockSpan _
    deg_gtV := fun j hj hjd => by
      have hjA := mem_of_single_mem_blockSpan hj
      cases j with
      | planted p =>
          have := phi43DegreeF_planted_ge κ p
          change -2 < phi43DegreeF κ (.planted p)
          linarith
      | old τ =>
          have hn : τ ≠ .noise := by simpa [phi43XiFreeF] using hjA
          change -2 < homogeneity κ τ
          cases τ <;> simp only [homogeneity] <;> first | exact absurd rfl hn | linarith
    deg_gt4 := fun j _ => phi43DegreeF_gt_neg_four κ j
    piBound := hPi
    gammaBound := hGam.toGammaNearOn M' segmentClosed_hairerTimeWindow
    piBound_nonneg := hCPi
    growth := hgr
    poly_largeV := fun j _ hjd k hk3 => by
      have h2 : (multiDeg k : ℝ) < 3 := by linarith
      exact_mod_cast h2
    integration_poly := fun a _ kk => phi43IntegrationF_polyEmb_eq_zero κ a kk
    poly_le := hN }

end RegularityStructures.Phi43.Restart

end
