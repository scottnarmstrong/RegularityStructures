/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalJointMeasurable
public import Phi43.Structure.QuadraticIntegration
public import Phi43.Structure.QuadraticModelRealising
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
public import Phi43.Structure.EnlargedDegreesF
public import Phi43.Structure.EnlargedIntegrationBridgeF
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Profile.Realising

/-!
# The source-sector extension of the smooth canonical model

The generic planted extension requires its source sector to have degree above
`-2`.  The raw noise is therefore excluded from the old source sector used to
construct the extension.  The resulting model is then shown to realise the
causal integration map on the full enlarged `Ξ`-free block: the three old
sources are handled by the extension theorem, while all remaining integration
rows are zero or planted rows handled by the explicit finite map.

Hairer [Hai14, Theorem 5.14, Definition 5.9, Proposition 8.27].
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures
open RegularityStructures.IntExt

/-- The three old symbols on which the nontrivial old integration is needed. -/
def phi43SourceSector : Finset Symbol := {.psi, .psiSq, .psiCube}

/-- The old coordinate sector used to instantiate the planted extension. -/
def phi43SourceSectorSpace : Submodule ℝ (Symbol → ℝ) :=
  blockSpan phi43SourceSector

private theorem phi43SourceSector_le_integrationSector {a : Symbol → ℝ}
    (ha : a ∈ phi43SourceSectorSpace) : a ∈ phi43IntegrationSector := by
  intro τ hτn hτp hτs hτc
  have hτ : τ ∉ phi43SourceSector := by
    intro hτ'
    simp only [phi43SourceSector, Finset.mem_insert, Finset.mem_singleton] at hτ'
    rcases hτ' with rfl | rfl | rfl <;> simp_all
  exact eq_zero_of_notMem_of_mem_blockSpan ha hτ

private theorem phi43SourceSector_coord :
    ∀ a ∈ phi43SourceSectorSpace, ∀ j, a j ≠ 0 →
      (Pi.single j 1 : Symbol → ℝ) ∈ phi43SourceSectorSpace := by
  exact isCoordClosed_blockSpan phi43SourceSector

private theorem phi43SourceSector_isSector (κ : Kappa) :
    (phi43RegularityStructure κ).IsSector phi43SourceSectorSpace := by
  refine {graded := ?_, invariant := ?_}
  · intro α a ha
    apply mem_blockSpan_of_forall
    intro i hi
    rw [homogeneousProj_apply]
    split_ifs with hα
    · exact eq_zero_of_notMem_of_mem_blockSpan ha hi
    · rfl
  · intro g hg a ha
    have haI : a ∈ phi43IntegrationSector :=
      phi43SourceSector_le_integrationSector ha
    have hbig := (phi43IntegrationSector_isSector κ).invariant g hg a haI
    apply mem_blockSpan_of_forall
    intro i hi
    by_cases hnoise : i = .noise
    · subst i
      rw [phi43OldGroup_noise_coord κ g hg]
      exact eq_zero_of_notMem_of_mem_blockSpan ha (by simp [phi43SourceSector])
    · exact hbig i hnoise (by
        intro h
        exact (hi (by rw [h]; simp [phi43SourceSector])).elim) (by
        intro h
        exact (hi (by rw [h]; simp [phi43SourceSector])).elim) (by
        intro h
        exact (hi (by rw [h]; simp [phi43SourceSector])).elim)

private theorem phi43SourceSector_isAbstractIntegration (κ : Kappa) :
    IsAbstractIntegration (phi43PolynomialSectorQuadratic κ) phi43SourceSectorSpace
      phi43AbstractIntegration 2 := by
  have hI := phi43AbstractIntegration_isAbstractIntegration_quadratic κ
  refine ⟨hI.pos, ?_, ?_, ?_⟩
  · intro α a ha haα
    exact hI.map_homogeneous α a (phi43SourceSector_le_integrationSector ha) haα
  · intro a ha haP
    exact hI.map_poly a (phi43SourceSector_le_integrationSector ha) haP
  · intro g hg a ha
    exact hI.comm g hg a (phi43SourceSector_le_integrationSector ha)

private theorem phi43Source_degree_bounds (κ : Kappa) {j : Symbol}
    (hj : (Pi.single j 1 : Symbol → ℝ) ∈ phi43SourceSectorSpace) :
    -2 < homogeneity κ j ∧ homogeneity κ j < gamma κ ∧ homogeneity κ j < 1 := by
  have hmem := mem_of_single_mem_blockSpan (A := phi43SourceSector) hj
  have hcases : j = .psi ∨ j = .psiSq ∨ j = .psiCube := by
    simpa only [phi43SourceSector, Finset.mem_insert, Finset.mem_singleton] using hmem
  rcases hcases with h | h | h
  · subst j
    dsimp [homogeneity, gamma]
    constructor
    · linarith [κ.2.1, κ.2.2]
    · constructor <;> linarith [κ.2.1, κ.2.2]
  · subst j
    dsimp [homogeneity, gamma]
    constructor
    · linarith [κ.2.1, κ.2.2]
    · constructor <;> linarith [κ.2.1, κ.2.2]
  · subst j
    dsimp [homogeneity, gamma]
    constructor
    · linarith [κ.2.1, κ.2.2]
    · constructor <;> linarith [κ.2.1, κ.2.2]

private theorem phi43PlantSource_degree_bounds (κ : Kappa) (τ : Phi43PlantSource) :
    -2 < homogeneity κ τ.symbol ∧ homogeneity κ τ.symbol < gamma κ ∧
      homogeneity κ τ.symbol < 1 := by
  cases τ <;> simp only [Phi43PlantSource.symbol, homogeneity, gamma] <;>
    constructor
  · linarith [κ.2.1, κ.2.2]
  · constructor <;> linarith [κ.2.1, κ.2.2]
  · linarith [κ.2.1, κ.2.2]
  · constructor <;> linarith [κ.2.1, κ.2.2]
  · linarith [κ.2.1, κ.2.2]
  · constructor <;> linarith [κ.2.1, κ.2.2]
  · linarith [κ.2.1, κ.2.2]
  · constructor <;> linarith [κ.2.1, κ.2.2]
  · linarith [κ.2.1, κ.2.2]
  · constructor <;> linarith [κ.2.1, κ.2.2]
  · linarith [κ.2.1, κ.2.2]
  · constructor <;> linarith [κ.2.1, κ.2.2]
  · linarith [κ.2.1, κ.2.2]
  · constructor <;> linarith [κ.2.1, κ.2.2]
  · linarith [κ.2.1, κ.2.2]
  · constructor <;> linarith [κ.2.1, κ.2.2]

private theorem phi43Source_or_plant_degree_bounds (κ : Kappa) {j : Symbol}
    (hj : (Pi.single j 1 : Symbol → ℝ) ∈ phi43SourceSectorSpace ∨
      j ∈ phi43PlantD) :
    -2 < homogeneity κ j ∧ homogeneity κ j < gamma κ ∧ homogeneity κ j < 1 := by
  rcases hj with hj | hj
  · exact phi43Source_degree_bounds κ hj
  · obtain ⟨τ, hτ⟩ := (phi43PlantD_mem_iff).1 hj
    rw [← hτ]
    exact phi43PlantSource_degree_bounds κ τ

private theorem phi43Source_or_plant_not_mem_sector {j : Symbol}
    (hj : j ∈ phi43PlantD) :
    (Pi.single j 1 : Symbol → ℝ) ∉ phi43SourceSectorSpace := by
  intro h
  have hjS := mem_of_single_mem_blockSpan (A := phi43SourceSector) h
  obtain ⟨τ, hτ⟩ := (phi43PlantD_mem_iff).1 hj
  subst j
  cases τ <;> simp_all [phi43SourceSector, Phi43PlantSource.symbol]

private theorem phi43Source_or_plant_degree_gt_neg_two (κ : Kappa) {j : Symbol}
    (hj : (Pi.single j 1 : Symbol → ℝ) ∈ phi43SourceSectorSpace ∨
      j ∈ phi43PlantD) :
    (phi43RegularityStructure κ).deg j > -2 := by
  rw [phi43RegularityStructure_deg]
  exact (phi43Source_or_plant_degree_bounds κ hj).1

private theorem phi43Source_or_plant_poly_deg (κ : Kappa) {j : Symbol}
    (hj : (Pi.single j 1 : Symbol → ℝ) ∈ phi43SourceSectorSpace ∨
      j ∈ phi43PlantD) (k : Fin 4 →₀ ℕ)
    (hk : (multiDeg k : ℝ) < (phi43RegularityStructure κ).deg j + 2) :
    multiDeg k < 3 := by
  have hj1 : (phi43RegularityStructure κ).deg j < 1 := by
    rw [phi43RegularityStructure_deg]
    exact (phi43Source_or_plant_degree_bounds κ hj).2.2
  have hk' : (multiDeg k : ℝ) < 3 := by
    rw [show (3 : ℝ) = 1 + 2 by norm_num]
    linarith [hk, hj1]
  exact_mod_cast hk'

private theorem phi43PlantBasis_mem_spanSup {d : Symbol} (hd : d ∈ phi43PlantD) :
    (Pi.single d 1 : Symbol → ℝ) ∈
      Submodule.span ℝ ((fun d => (Pi.single d 1 : Symbol → ℝ)) ''
        (phi43PlantD : Set Symbol)) ⊔ phi43SourceSectorSpace := by
  exact Submodule.mem_sup_left (Submodule.subset_span ⟨d, hd, rfl⟩)

private theorem phi43SourceBasis_mem_spanSup {d : Symbol} (hd : d ∈ phi43SourceSector) :
    (Pi.single d 1 : Symbol → ℝ) ∈
      Submodule.span ℝ ((fun d => (Pi.single d 1 : Symbol → ℝ)) ''
        (phi43PlantD : Set Symbol)) ⊔ phi43SourceSectorSpace := by
  exact Submodule.mem_sup_right (Submodule.subset_span ⟨d, hd, rfl⟩)

private theorem phi43PlantAction_mem_spanSup
    (κ : Kappa)
    {g : LinearMap.GeneralLinearGroup ℝ (Symbol → ℝ)}
    (hg : g ∈ (phi43RegularityStructure κ).group) {d : Symbol}
    (hd : d ∈ phi43PlantD) :
    (g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ)) (Pi.single d 1) ∈
      Submodule.span ℝ ((fun d => (Pi.single d 1 : Symbol → ℝ)) ''
        (phi43PlantD : Set Symbol)) ⊔ phi43SourceSectorSpace := by
  obtain ⟨p, rfl⟩ := hg
  obtain ⟨τ, hτ⟩ := (phi43PlantD_mem_iff).1 hd
  subst d
  have hsumPsiX (f : Fin 3 → ℝ) :
      (∑ i, f i • (Pi.single (.psiX i) 1 : Symbol → ℝ)) ∈
        Submodule.span ℝ ((fun d => (Pi.single d 1 : Symbol → ℝ)) ''
          (phi43PlantD : Set Symbol)) ⊔ phi43SourceSectorSpace := by
    refine Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ ?_
    exact phi43PlantBasis_mem_spanSup ((phi43PlantD_mem_iff).2 ⟨.psiX i, rfl⟩)
  have hsumPsiSqX (f : Fin 3 → ℝ) :
      (∑ i, f i • (Pi.single (.psiSqX i) 1 : Symbol → ℝ)) ∈
        Submodule.span ℝ ((fun d => (Pi.single d 1 : Symbol → ℝ)) ''
          (phi43PlantD : Set Symbol)) ⊔ phi43SourceSectorSpace := by
    refine Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ ?_
    exact phi43PlantBasis_mem_spanSup ((phi43PlantD_mem_iff).2 ⟨.psiSqX i, rfl⟩)
  have hPsi : (Pi.single .psi 1 : Symbol → ℝ) ∈
      Submodule.span ℝ ((fun d => (Pi.single d 1 : Symbol → ℝ)) ''
        (phi43PlantD : Set Symbol)) ⊔ phi43SourceSectorSpace :=
    phi43SourceBasis_mem_spanSup (by simp [phi43SourceSector])
  have hPsiSq : (Pi.single .psiSq 1 : Symbol → ℝ) ∈
      Submodule.span ℝ ((fun d => (Pi.single d 1 : Symbol → ℝ)) ''
        (phi43PlantD : Set Symbol)) ⊔ phi43SourceSectorSpace :=
    phi43SourceBasis_mem_spanSup (by simp [phi43SourceSector])
  have hPsiCube : (Pi.single .psiCube 1 : Symbol → ℝ) ∈
      Submodule.span ℝ ((fun d => (Pi.single d 1 : Symbol → ℝ)) ''
        (phi43PlantD : Set Symbol)) ⊔ phi43SourceSectorSpace :=
    phi43SourceBasis_mem_spanSup (by simp [phi43SourceSector])
  rw [phi43StructureGroupElement_apply_single, structureGroupMap_basis]
  cases τ <;>
    simp [Phi43PlantSource.symbol, structureBasisAction, primitiveAction,
      integratedPsiProductAction, multiply_basis, basisProduct, productSymbol,
      phi43CoordinateEquiv_basis]
  · exact Submodule.add_mem _
      (phi43PlantBasis_mem_spanSup ((phi43PlantD_mem_iff).2 ⟨.psiX _, rfl⟩))
      (Submodule.smul_mem _ _ hPsi)
  · exact Submodule.add_mem _
      (phi43PlantBasis_mem_spanSup ((phi43PlantD_mem_iff).2 ⟨.psiSqX _, rfl⟩))
      (Submodule.smul_mem _ _ hPsiSq)
  · exact Submodule.add_mem _
      (Submodule.add_mem _
        (phi43PlantBasis_mem_spanSup ((phi43PlantD_mem_iff).2 ⟨.iPsiPsi, rfl⟩))
        (Submodule.smul_mem _ _ hPsi))
      (hsumPsiX _)
  · exact Submodule.add_mem _
      (Submodule.add_mem _
        (phi43PlantBasis_mem_spanSup ((phi43PlantD_mem_iff).2 ⟨.iPsiPsiSq, rfl⟩))
        (Submodule.smul_mem _ _ hPsiSq))
      (hsumPsiSqX _)
  · exact Submodule.add_mem _
      (phi43PlantBasis_mem_spanSup ((phi43PlantD_mem_iff).2 ⟨.iPsiSqPsi, rfl⟩))
      (Submodule.smul_mem _ _ hPsi)
  · exact Submodule.add_mem _
      (phi43PlantBasis_mem_spanSup ((phi43PlantD_mem_iff).2 ⟨.iPsiSqPsiSq, rfl⟩))
      (Submodule.smul_mem _ _ hPsiSq)
  · exact Submodule.add_mem _
      (phi43PlantBasis_mem_spanSup ((phi43PlantD_mem_iff).2 ⟨.iPsiCubePsi, rfl⟩))
      (Submodule.smul_mem _ _ hPsi)
  · exact Submodule.add_mem _
      (phi43PlantBasis_mem_spanSup ((phi43PlantD_mem_iff).2 ⟨.iPsiCubePsiSq, rfl⟩))
      (Submodule.smul_mem _ _ hPsiSq)

/-! A reusable source-sector wrapper for another genuine old-space model. -/

theorem phi43SourceSector_intExtHyp_of
    (N : ℕ) (κ : Kappa)
    (M : Model (phi43RegularityStructure κ) parabolicSemigroup)
    (hRealising : M.IsRealisingP (annKernel0C N) (gamma κ)
      (phi43PolynomialSectorQuadratic κ) phi43AbstractIntegration
      phi43IntegrationSector)
    (hGrowth : ∃ (C C' r s : ℝ) (ρP ρG : ParabolicSpace → ℝ),
      M.GrowthModel (gamma κ) C C' ρP ρG r s) :
    IntExtHyp M (phi43IntegrationExtensionF κ) (annKernel0C N) N (gamma κ)
      phi43SourceSectorSpace := by
  refine
    { profile := shellProfile_annKernel0C N
      realising := ?_
      integration := phi43SourceSector_isAbstractIntegration κ
      sector := phi43SourceSector_isSector κ
      coord := phi43SourceSector_coord
      deg_gt := ?_
      growth := hGrowth
      poly_deg := ?_
      deg_D := ?_
      notMem_D := ?_
      closure := ?_ }
  · refine ⟨?_, hRealising.poly⟩
    intro x i hi hiV t ht z
    exact hRealising.realises x i hi
      (phi43SourceSector_le_integrationSector hiV) t ht z
  · intro j hj hjγ
    exact phi43Source_or_plant_degree_gt_neg_two κ hj
  · intro j hj hjγ k hk
    exact phi43Source_or_plant_poly_deg κ hj k hk
  · intro d hd
    obtain ⟨τ, hτ⟩ := (phi43PlantD_mem_iff).1 hd
    rw [← hτ]
    exact (phi43PlantSource_degree_bounds κ τ).2.1
  · intro d hd
    exact phi43Source_or_plant_not_mem_sector hd
  · intro g hg d hd
    exact phi43PlantAction_mem_spanSup κ hg hd

theorem phi43SourceSector_isRealising_of
    (N : ℕ) (κ : Kappa)
    (M : Model (phi43RegularityStructure κ) parabolicSemigroup)
    (H : IntExtHyp M (phi43IntegrationExtensionF κ) (annKernel0C N) N
      (gamma κ) phi43SourceSectorSpace)
    (hJ : M.IsJointMeasurable) :
    (H.intExtendOfJoint hJ).IsRealisingP (annKernel0C N) (gamma κ)
      (phi43PolynomialSectorF κ) phi43IntegrationF
      (IntExt.liftedSector SymbolF.old phi43SourceSectorSpace phi43PlantD) := by
  have hmeas : IntExtMeas M (annKernel0C N) phi43PlantD :=
    H.intExtMeas_of_isJointMeasurable hJ
  have hExt := H.isRealisingP_intExtend hmeas
  have hle : IntExt.liftedSector SymbolF.old phi43SourceSectorSpace phi43PlantD ≤
      phi43IntegrationSectorF := by
    change (IntExt.extSector phi43SourceSectorSpace phi43PlantD).map
        (IntExt.liftOld SymbolF.old) ≤
      (IntExt.extSector phi43IntegrationSector phi43PlantD).map
        (IntExt.liftOld SymbolF.old)
    apply Submodule.map_mono
    exact sup_le_sup (fun a ha => phi43SourceSector_le_integrationSector ha) le_rfl
  rw [phi43IntegrationExtensionF_old_eq κ, phi43IntegrationExtensionF_new_eq κ] at hExt
  have hExt' : (H.intExtendOfJoint hJ).IsRealisingP (annKernel0C N) (gamma κ)
      (phi43PolynomialSectorF κ)
      (IntExt.intExt SymbolF.old phi43PlantNew phi43PlantD phi43AbstractIntegration)
      (IntExt.liftedSector SymbolF.old phi43SourceSectorSpace phi43PlantD) := by
    simpa only [IntExtHyp.intExtendOfJoint] using hExt
  refine ⟨?_, hExt'.poly⟩
  intro x j hjγ hjV t ht z
  have hjV' : (Pi.single j 1 : SymbolF → ℝ) ∈ phi43IntegrationSectorF :=
    hle hjV
  have h := hExt'.realises x j hjγ hjV t ht z
  have hI := phi43IntegrationExtensionF_intExt_on_sector κ hjV'
  rw [hI] at h
  exact h

theorem phi43_gamma_le_plant (κ : Kappa) :
    ∀ d ∈ phi43PlantD,
      gamma κ ≤ (phi43RegularityStructure κ).deg d + 2 := by
  intro d hd
  obtain ⟨τ, hτ⟩ := (phi43PlantD_mem_iff).1 hd
  rw [← hτ]
  exact (phi43PlantSource_degree_gt_gamma κ τ).le

end RegularityStructures.Phi43

end
