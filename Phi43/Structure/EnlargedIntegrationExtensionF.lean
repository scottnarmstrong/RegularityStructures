/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedExtensionCriterionF
public import RegularityStructures.Abstract.IntExt.Basic
import Mathlib.Tactic.Abel

/-!
# The abstract integration-extension data for the enlarged Φ⁴₃ structure

This file identifies the planted completion with main's algebraic
`IntegrationExtension` interface.  The construction is the finite version of
Hairer [Hai14, Theorem 5.14].  It supplies no analytic growth hypothesis and
does not claim the model-extension theorem by itself.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The old symbols which receive a retained planted integral. -/
def phi43PlantD : Finset Symbol := Finset.univ.image Phi43PlantSource.symbol

/-- A source symbol in `phi43PlantD` has a unique planted representative. -/
theorem phi43PlantD_mem_iff {d : Symbol} :
    d ∈ phi43PlantD ↔ ∃ τ : Phi43PlantSource, τ.symbol = d := by
  simp [phi43PlantD]

/-- Extend the planted-source map arbitrarily away from its finite domain. -/
def phi43PlantNew : Symbol → SymbolF
  | .psiX i => .planted (.psiX i)
  | .psiSqX i => .planted (.psiSqX i)
  | .iPsiPsi => .planted .iPsiPsi
  | .iPsiPsiSq => .planted .iPsiPsiSq
  | .iPsiSqPsi => .planted .iPsiSqPsi
  | .iPsiSqPsiSq => .planted .iPsiSqPsiSq
  | .iPsiCubePsi => .planted .iPsiCubePsi
  | .iPsiCubePsiSq => .planted .iPsiCubePsiSq
  | d => .old d

theorem phi43PlantNew_of_mem (d : Symbol) (hd : d ∈ phi43PlantD) :
    ∃ τ : Phi43PlantSource, phi43PlantNew d = .planted τ ∧ τ.symbol = d := by
  obtain ⟨τ, hτ⟩ := (phi43PlantD_mem_iff).1 hd
  subst d
  cases τ <;> simp [phi43PlantNew, Phi43PlantSource.symbol]

private theorem phi43PlantNew_eq_of_source (τ : Phi43PlantSource) :
    phi43PlantNew τ.symbol = .planted τ := by
  cases τ <;> rfl

theorem phi43PlantNew_injOn :
    Set.InjOn phi43PlantNew (phi43PlantD : Set Symbol) := by
  intro a ha b hb hab
  obtain ⟨τ, hτ, hτa⟩ := phi43PlantNew_of_mem a ha
  obtain ⟨σ, hσ, hσb⟩ := phi43PlantNew_of_mem b hb
  have hτσ : τ = σ := by simpa [hτ, hσ] using hab
  exact hτa.symm.trans (hτσ ▸ hσb)

theorem phi43PlantNew_cover (j : SymbolF) :
    (∃ i : Symbol, .old i = j) ∨
      ∃ d ∈ phi43PlantD, phi43PlantNew d = j := by
  cases j with
  | old τ => exact Or.inl ⟨τ, rfl⟩
  | planted τ =>
      right
      refine ⟨τ.symbol, (phi43PlantD_mem_iff).2 ⟨τ, rfl⟩, ?_⟩
      exact phi43PlantNew_eq_of_source τ

theorem phi43PlantSource_abstractIntegration_zero (τ : Phi43PlantSource) :
    phi43AbstractIntegration (Pi.single τ.symbol 1) = 0 := by
  funext i
  rw [phi43AbstractIntegration_apply_coord]
  cases τ <;> cases i <;> simp [Phi43PlantSource.symbol]

private theorem phi43AbstractIntegration_single_formula (d : Symbol) :
    phi43AbstractIntegration (Pi.single d 1) =
      match d with
      | .noise => Pi.single .psi 1
      | .psi => Pi.single .iPsi 1
      | .psiSq => Pi.single .iPsiSq 1
      | .psiCube => Pi.single .iPsiCube 1
      | _ => 0 := by
  funext i
  rw [phi43AbstractIntegration_apply_coord]
  cases d <;> cases i <;> simp

private theorem phi43IntegrationExtension_old_single (d : Symbol) :
    IntExt.intExt SymbolF.old phi43PlantNew phi43PlantD phi43AbstractIntegration
        (phi43OldEmbF (Pi.single d 1)) =
      phi43IntegrationF (phi43OldEmbF (Pi.single d 1)) := by
  have hold : Function.Injective (SymbolF.old : Symbol → SymbolF) :=
    fun _ _ h => SymbolF.old.inj h
  rw [phi43OldEmbF_single, IntExt.intExt_single_old hold phi43AbstractIntegration]
  by_cases hd : d ∈ phi43PlantD
  · obtain ⟨τ, hnew, hsource⟩ := phi43PlantNew_of_mem d hd
    have hI : phi43AbstractIntegration (Pi.single d 1) = 0 := by
      rw [← hsource]
      exact phi43PlantSource_abstractIntegration_zero τ
    rw [hI, phi43IntegrationF_single, ← hsource,
      phi43IntegrationSymbolF_planted_source]
    by_cases hD : τ.symbol ∈ phi43PlantD
    · simp [hD, phi43PlantNew_eq_of_source]
    · exact (hD ((phi43PlantD_mem_iff).2 ⟨τ, rfl⟩)).elim
  · cases d with
    | one =>
        simp [phi43AbstractIntegration_single_formula, phi43IntegrationF_single,
          phi43IntegrationSymbolF, hd]
    | noise =>
        simp [phi43AbstractIntegration_single_formula, phi43IntegrationF_single,
          phi43IntegrationSymbolF, IntExt.liftOld_single hold, hd]
    | x0 =>
        simp [phi43AbstractIntegration_single_formula, phi43IntegrationF_single,
          phi43IntegrationSymbolF, hd]
    | x i =>
        simp [phi43AbstractIntegration_single_formula, phi43IntegrationF_single,
          phi43IntegrationSymbolF, hd]
    | xMul p =>
        simp [phi43AbstractIntegration_single_formula, phi43IntegrationF_single,
          phi43IntegrationSymbolF, hd]
    | psi =>
        simp [phi43AbstractIntegration_single_formula, phi43IntegrationF_single,
          phi43IntegrationSymbolF, IntExt.liftOld_single hold, hd]
    | iPsi =>
        simp [phi43AbstractIntegration_single_formula, phi43IntegrationF_single,
          phi43IntegrationSymbolF, hd]
    | psiSq =>
        simp [phi43AbstractIntegration_single_formula, phi43IntegrationF_single,
          phi43IntegrationSymbolF, IntExt.liftOld_single hold, hd]
    | psiCube =>
        simp [phi43AbstractIntegration_single_formula, phi43IntegrationF_single,
          phi43IntegrationSymbolF, IntExt.liftOld_single hold, hd]
    | psiX i =>
        exact (hd ((phi43PlantD_mem_iff).2 ⟨.psiX i, rfl⟩)).elim
    | psiSqX i =>
        exact (hd ((phi43PlantD_mem_iff).2 ⟨.psiSqX i, rfl⟩)).elim
    | iPsiSq =>
        simp [phi43AbstractIntegration_single_formula, phi43IntegrationF_single,
          phi43IntegrationSymbolF, hd]
    | iPsiCube =>
        simp [phi43AbstractIntegration_single_formula, phi43IntegrationF_single,
          phi43IntegrationSymbolF, hd]
    | iPsiPsi =>
        exact (hd ((phi43PlantD_mem_iff).2 ⟨.iPsiPsi, rfl⟩)).elim
    | iPsiPsiSq =>
        exact (hd ((phi43PlantD_mem_iff).2 ⟨.iPsiPsiSq, rfl⟩)).elim
    | iPsiSqPsi =>
        exact (hd ((phi43PlantD_mem_iff).2 ⟨.iPsiSqPsi, rfl⟩)).elim
    | iPsiSqPsiSq =>
        exact (hd ((phi43PlantD_mem_iff).2 ⟨.iPsiSqPsiSq, rfl⟩)).elim
    | iPsiCubePsi =>
        exact (hd ((phi43PlantD_mem_iff).2 ⟨.iPsiCubePsi, rfl⟩)).elim
    | iPsiCubePsiSq =>
        exact (hd ((phi43PlantD_mem_iff).2 ⟨.iPsiCubePsiSq, rfl⟩)).elim
    | iPsiCubeSq =>
        simp [phi43AbstractIntegration_single_formula, phi43IntegrationF_single,
          phi43IntegrationSymbolF, hd]

private theorem phi43OldEmbF_eq_liftOld :
    phi43OldEmbF = IntExt.liftOld SymbolF.old := by
  apply LinearMap.ext
  intro a
  funext τ
  cases τ with
  | old τ =>
      change a τ = IntExt.liftOld SymbolF.old a (.old τ)
      rw [IntExt.liftOld_apply_old (fun _ _ h => SymbolF.old.inj h)]
  | planted τ =>
      change 0 = IntExt.liftOld SymbolF.old a (.planted τ)
      rw [IntExt.liftOld_apply_of_notMem a]
      intro i h
      cases h

private theorem phi43IntegrationExtension_old_bridge (a : Symbol → ℝ) :
    IntExt.intExt SymbolF.old phi43PlantNew phi43PlantD phi43AbstractIntegration
        (phi43OldEmbF a) = phi43IntegrationF (phi43OldEmbF a) := by
  rw [show phi43OldEmbF a = ∑ d : Symbol, a d • Pi.single (.old d) 1 by
    funext j
    cases j with
    | old j =>
        simpa only [phi43OldEmbF, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul, Pi.single_apply, SymbolF.old.injEq] using
          congrFun (eq_sum_single a) j
    | planted τ => simp [phi43OldEmbF]]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro d hd
  simpa only [phi43OldEmbF_single] using
    congrArg (fun v => a d • v) (phi43IntegrationExtension_old_single d)

private theorem phi43IntegrationExtension_unipotent (κ : Kappa)
    (g' : LinearMap.GeneralLinearGroup ℝ (SymbolF → ℝ))
    (hold : ∃ g₀ ∈ (phi43RegularityStructure κ).group,
      ∀ a, g'.val (phi43OldEmbF a) = phi43OldEmbF (g₀.val a))
    (hnew : ∀ d ∈ phi43PlantD,
      g'.val (Pi.single (phi43PlantNew d) 1) -
          IntExt.intExt SymbolF.old phi43PlantNew phi43PlantD phi43AbstractIntegration
            (g'.val (Pi.single (.old d) 1)) ∈
        (phi43PolynomialSectorF κ).subspace ⊓
          lowerSubspace (phi43DegreeF κ) (phi43DegreeF κ (phi43PlantNew d))) :
    IsGradedUnipotent (phi43DegreeF κ) g'.val := by
  obtain ⟨g₀, hg₀, hact⟩ := hold
  intro j
  rcases phi43PlantNew_cover j with ⟨i, rfl⟩ | ⟨d, hd, rfl⟩
  · rw [← phi43OldEmbF_single, hact, ← map_sub]
    exact phi43OldEmbF_lower κ _ _ ((phi43RegularityStructure κ).isGradedUnipotent g₀ hg₀ i)
  · obtain ⟨τ, hnewτ, hs⟩ := phi43PlantNew_of_mem d hd
    have hA := (hnew d hd).2
    have hactd : g'.val (Pi.single (.old d) 1) =
        phi43OldEmbF (g₀.val (Pi.single d 1)) := by
      rw [← phi43OldEmbF_single]
      exact hact _
    have hdelta : g₀.val (Pi.single d 1) - Pi.single d 1 ∈
        lowerSubspace (homogeneity κ) (homogeneity κ d) :=
      (phi43RegularityStructure κ).isGradedUnipotent g₀ hg₀ d
    have hdeltaF : phi43OldEmbF (g₀.val (Pi.single d 1) - Pi.single d 1) ∈
        lowerSubspace (phi43DegreeF κ) (homogeneity κ d) :=
      phi43OldEmbF_lower κ _ _ hdelta
    have hIlower := phi43IntegrationF_lower κ (homogeneity κ d) _ hdeltaF
    have hInew : phi43IntegrationF (phi43OldEmbF (Pi.single d 1)) =
        Pi.single (.planted τ) 1 := by
      rw [← hs, phi43OldEmbF_single]
      exact phi43IntegrationF_old_source τ
    have hbase :
        IntExt.intExt SymbolF.old phi43PlantNew phi43PlantD phi43AbstractIntegration
              (g'.val (Pi.single (.old d) 1)) - Pi.single (.planted τ) 1 ∈
          lowerSubspace (phi43DegreeF κ) (phi43DegreeF κ (.planted τ)) := by
      rw [hactd, phi43IntegrationExtension_old_bridge]
      have hdecomp : g₀.val (Pi.single d 1) =
          (g₀.val (Pi.single d 1) - Pi.single d 1) + Pi.single d 1 := by abel
      rw [hdecomp, map_add, map_add, hInew]
      have hdeg : phi43DegreeF κ (.planted τ) = homogeneity κ d + 2 := by
        simp [phi43DegreeF, hs]
      rw [hdeg]
      have hvec : phi43IntegrationF (phi43OldEmbF
          (g₀.val (Pi.single d 1) - Pi.single d 1)) + Pi.single (.planted τ) 1 -
          Pi.single (.planted τ) 1 =
          phi43IntegrationF (phi43OldEmbF
            (g₀.val (Pi.single d 1) - Pi.single d 1)) := by abel
      rw [hvec]
      exact hIlower
    have hnewlower :
        g'.val (Pi.single (.planted τ) 1) -
              IntExt.intExt SymbolF.old phi43PlantNew phi43PlantD phi43AbstractIntegration
                (g'.val (Pi.single (.old d) 1)) ∈
          lowerSubspace (phi43DegreeF κ) (phi43DegreeF κ (.planted τ)) := by
      rw [hnewτ] at hA
      exact hA
    have heq : g'.val (Pi.single (.planted τ) 1) -
          Pi.single (.planted τ) 1 =
        (g'.val (Pi.single (.planted τ) 1) -
            IntExt.intExt SymbolF.old phi43PlantNew phi43PlantD phi43AbstractIntegration
              (g'.val (Pi.single (.old d) 1))) +
          (IntExt.intExt SymbolF.old phi43PlantNew phi43PlantD phi43AbstractIntegration
              (g'.val (Pi.single (.old d) 1)) -
            Pi.single (.planted τ) 1) := by abel
    rw [hnewτ, heq]
    exact Submodule.add_mem _ hnewlower hbase

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

def phi43IntegrationExtensionF (κ : Kappa) :
    IntegrationExtension
      (phi43RegularityStructure κ)
      (phi43RegularityStructureF κ)
      (phi43PolynomialSectorQuadratic κ)
      (phi43PolynomialSectorF κ)
      phi43AbstractIntegration
      phi43PlantD := by
  refine
    { old := SymbolF.old
      new := phi43PlantNew
      old_injective := fun _ _ h => SymbolF.old.inj h
      new_injOn := phi43PlantNew_injOn
      old_ne_new := ?_
      cover := phi43PlantNew_cover
      deg_old := ?_
      deg_new := ?_
      poly_emb := ?_
      I_D := ?_
      mem_group := ?_ }
  · intro i d hd h
    obtain ⟨τ, hnew, _⟩ := phi43PlantNew_of_mem d hd
    rw [hnew] at h
    cases h
  · intro i
    rfl
  · intro d hd
    obtain ⟨τ, hnew, hs⟩ := phi43PlantNew_of_mem d hd
    rw [hnew, ← hs]
    rfl
  · intro k
    rfl
  · intro d hd
    obtain ⟨τ, hs⟩ := (phi43PlantD_mem_iff).1 hd
    rw [← hs]
    exact phi43PlantSource_abstractIntegration_zero τ
  · intro g' hOld hNew
    obtain ⟨g₀, hg₀, hact⟩ := hOld
    have hOld' : ∃ g₀ ∈ (phi43RegularityStructure κ).group,
        ∀ a, g'.val (phi43OldEmbF a) = phi43OldEmbF (g₀.val a) := by
      refine ⟨g₀, hg₀, ?_⟩
      intro a
      rw [phi43OldEmbF_eq_liftOld]
      exact hact a
    have htri := phi43IntegrationExtension_unipotent κ g' hOld' hNew
    apply (phi43ExtensionGroupF_mem_iff_planted κ g').2
    obtain ⟨g₀, hg₀, hact⟩ := hOld'
    refine ⟨htri, g₀, hg₀, hact, ?_⟩
    intro τ
    let d : Symbol := τ.symbol
    have hd : d ∈ phi43PlantD := (phi43PlantD_mem_iff).2 ⟨τ, rfl⟩
    have hcomm :
        IntExt.intExt SymbolF.old phi43PlantNew phi43PlantD phi43AbstractIntegration
              (g'.val (Pi.single (.old d) 1)) =
          phi43IntegrationF (g'.val (Pi.single (.old d) 1)) := by
      have hactd : g'.val (Pi.single (.old d) 1) =
          phi43OldEmbF (g₀.val (Pi.single d 1)) := by
        rw [← phi43OldEmbF_single]
        exact hact _
      rw [hactd, phi43IntegrationExtension_old_bridge]
    have hpoly := (hNew d hd).1
    have hnewτ : phi43PlantNew d = .planted τ := phi43PlantNew_eq_of_source τ
    rw [hnewτ, hcomm] at hpoly
    exact hpoly

theorem phi43IntegrationExtensionF_old_eq (κ : Kappa) :
    (phi43IntegrationExtensionF κ).old = SymbolF.old := by
  rfl

theorem phi43IntegrationExtensionF_new_eq (κ : Kappa) :
    (phi43IntegrationExtensionF κ).new = phi43PlantNew := by
  rfl

end RegularityStructures.Phi43

end
