/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Persistence.Instance
public import Phi43.Restart.Package
public import Phi43.Reconstruction.UnitCoeff
public import RegularityStructures.Abstract.Singular.Phi4FixedPointInstancePolyPairing

/-!
# The enlarged restarted model realises the kernel on the `Ξ`-free block at level `κ`

The enlarged model `phi43EnlargedRenormalisedModel` realises the kernel for `phi43IntegrationF`
only on the lifted source sector (the whole `Ξ`-free block at level `γ` is not realised).  Below
the level `κ = γ + α + α` every basis vector of the `Ξ`-free block is either a source
(`Ψ, Ψ², Ψ³`), a plant source (`Ψ²X, I Ψ Ψ²…`) or the unit `𝟙`.  The sources and the plant
sources are covered by the source-sector realisation; for the unit both sides vanish
(`phi43IntegrationF e_𝟙 = 0`, and the germ of a polynomial is annihilated by `annKernel0C N`,
`pairing_polyReg_taylorKernel_eq_zero`).  The statement is then transported through the time
translation.
-/

public section

open RegularityStructures.IntExt

namespace RegularityStructures.Phi43.Persistence

/-- Below the level `κ`, a non-noise symbol is the unit, a source or a plant source. -/
theorem old_symbol_below_kappa (κ : Kappa) {τ : Symbol} (h : homogeneity κ τ < κ.1)
    (hn : τ ≠ .noise) : τ = .one ∨ τ ∈ phi43SourceSector ∨ τ ∈ phi43PlantD := by
  have hk : 0 < κ.1 := κ.2.1
  have hk' : κ.1 < 1 / 16 := κ.2.2
  cases τ with
  | one => exact Or.inl rfl
  | noise => exact absurd rfl hn
  | psi => exact Or.inr (Or.inl (by simp [phi43SourceSector]))
  | psiSq => exact Or.inr (Or.inl (by simp [phi43SourceSector]))
  | psiCube => exact Or.inr (Or.inl (by simp [phi43SourceSector]))
  | psiSqX i => exact Or.inr (Or.inr (phi43PlantD_mem_iff.2 ⟨.psiSqX i, rfl⟩))
  | iPsiSqPsiSq => exact Or.inr (Or.inr (phi43PlantD_mem_iff.2 ⟨.iPsiSqPsiSq, rfl⟩))
  | iPsiCubePsi => exact Or.inr (Or.inr (phi43PlantD_mem_iff.2 ⟨.iPsiCubePsi, rfl⟩))
  | iPsiCubePsiSq => exact Or.inr (Or.inr (phi43PlantD_mem_iff.2 ⟨.iPsiCubePsiSq, rfl⟩))
  | _ => exfalso; simp only [homogeneity] at h; linarith

/-- The basis vector of a source or a plant source, lifted to the enlarged structure, lies in the
lifted source sector. -/
theorem single_old_mem_liftedSector {τ : Symbol}
    (h : τ ∈ phi43SourceSector ∨ τ ∈ phi43PlantD) :
    (Pi.single (SymbolF.old τ) 1 : SymbolF → ℝ) ∈
      liftedSector SymbolF.old phi43SourceSectorSpace phi43PlantD := by
  rw [← liftOld_single (fun _ _ hh => SymbolF.old.inj hh)]
  refine Submodule.mem_map_of_mem ?_
  rcases h with h | h
  · exact Submodule.mem_sup_left (Submodule.subset_span ⟨τ, h, rfl⟩)
  · exact Submodule.mem_sup_right (single_mem_spanD h 1)

theorem phi43IntegrationF_single_one :
    phi43IntegrationF (Pi.single (SymbolF.old .one) 1) = 0 := by
  funext σ
  cases σ with
  | old τ => cases τ <;> simp [phi43IntegrationF]
  | planted τ => cases τ <;> simp [phi43IntegrationF, Phi43PlantSource.symbol]

variable (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
  (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
    ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
  (C : RenormalisationConstants)

/-- **The unit case.**  The germ of the unit vanishes, so the unit is trivially realised with
`𝓘 𝟙 = 0`. -/
theorem enlargedModel_realises_unit (hN : 3 ≤ N) (x : ParabolicSpace) (t : ℝ) (z : ParabolicSpace) :
    (phi43EnlargedRenormalisedModel N κ noise Cg q hg C).regPi x
        (phi43IntegrationF (Pi.single (SymbolF.old .one) 1)) t z =
      realRegP (phi43EnlargedRenormalisedModel N κ noise Cg q hg C) (annKernel0C N) x
        (SymbolF.old .one) t z := by
  set M := phi43EnlargedRenormalisedModel N κ noise Cg q hg C with hM
  have hpoly := (phi43EnlargedRenormalisedModel_isRealising N κ noise Cg q hg C).poly
  have hreg : (fun t z => M.regPi x (Pi.single (SymbolF.old .one) 1) t z) =
      polyReg x (Pi.single phi43OneIdx 1) := by
    funext t z
    have := hpoly x phi43OneIdx t z
    rwa [emb_phi43OneIdx] at this
  have hgerm : ∀ y, realGermP M (annKernel0C N) x (SymbolF.old .one) y = 0 := by
    intro y
    unfold realGermP
    refine (tsum_congr fun n => ?_).trans tsum_zero
    rw [hreg]
    exact pairing_polyReg_taylorKernel_eq_zero (shellProfile_annKernel0C N) hN n _ x y _
  rw [phi43IntegrationF_single_one]
  have h0 : M.regPi x 0 t z = 0 := by
    show (((M.pi x 0 : parabolicSemigroup.distributions) : ℝ → ParabolicSpace → ℝ) t z) = 0
    rw [map_zero]
    rfl
  rw [h0]
  unfold realRegP
  split_ifs
  · have : realGermP M (annKernel0C N) x (SymbolF.old .one) = fun _ => 0 :=
      funext hgerm
    rw [this]
    simp [RegularisingSemigroup.apply]
  · rfl

/-- **The enlarged model realises the kernel on the `Ξ`-free block at level `κ = γ + α + α`.** -/
theorem enlargedModel_realisesKernelP (hN : 3 ≤ N) :
    (phi43EnlargedRenormalisedModel N κ noise Cg q hg C).RealisesKernelP (annKernel0C N)
      (gamma κ + phi43Alpha κ + phi43Alpha κ) phi43IntegrationF (blockSpan phi43XiFreeF) := by
  rw [Restart.gamma_add_alpha_add_alpha]
  intro x i hi hV t ht z
  have hk : 0 < κ.1 := κ.2.1
  have hXi : i ∈ phi43XiFreeF := mem_of_single_mem_blockSpan hV
  cases i with
  | planted p =>
      exfalso
      have h1 := phi43DegreeF_planted_ge κ p
      have hk' : κ.1 < 1 / 16 := κ.2.2
      change phi43DegreeF κ (.planted p) < κ.1 at hi
      linarith
  | old τ =>
      have hn : τ ≠ .noise := fun h => by subst h; simp [phi43XiFreeF] at hXi
      rcases old_symbol_below_kappa κ hi hn with rfl | hs | hs
      · exact enlargedModel_realises_unit N κ noise Cg q hg C hN x t z
      · refine (phi43EnlargedRenormalisedModel_isRealising N κ noise Cg q hg C).realises x _
          ?_ (single_old_mem_liftedSector (Or.inl hs)) t ht z
        change homogeneity κ τ < gamma κ
        have : κ.1 < gamma κ := by simp only [gamma]; linarith
        exact lt_trans hi this
      · refine (phi43EnlargedRenormalisedModel_isRealising N κ noise Cg q hg C).realises x _
          ?_ (single_old_mem_liftedSector (Or.inr hs)) t ht z
        change homogeneity κ τ < gamma κ
        have : κ.1 < gamma κ := by simp only [gamma]; linarith
        exact lt_trans hi this

/-- **The enlarged restarted model realises the kernel at level `κ` on the `Ξ`-free block**
(`RestartQualitative`, first component). -/
theorem enlargedRestartModel_isRealisingP (hN : 3 ≤ N) (s : ℝ) :
    (enlargedRestartModel N κ noise Cg q hg C s).IsRealisingP (annKernel0C N)
      (gamma κ + phi43Alpha κ + phi43Alpha κ) (phi43PolynomialSectorF κ) phi43IntegrationF
      (blockSpan phi43XiFreeF) :=
  Model.isRealisingP_translate _ _
    ⟨enlargedModel_realisesKernelP N κ noise Cg q hg C hN,
      (phi43EnlargedRenormalisedModel_isRealising N κ noise Cg q hg C).poly⟩

end RegularityStructures.Phi43.Persistence

end
