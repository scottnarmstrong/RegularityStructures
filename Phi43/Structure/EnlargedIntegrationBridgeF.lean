/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedIntegrationExtensionF
public import RegularityStructures.Abstract.IntExt.OldSymbols

/-!
# The concrete integration bridge for the enlarged Φ⁴₃ structure

The planted completion is presented both by the explicit coordinate map
`phi43IntegrationF` and by the abstract `IntExt.intExt` construction.  This
module records their equality and names the lifted integration sector used by
the abstract model-extension API.  The structural integration axiom on the
larger Xi-free block is supplied by `EnlargedIntegrationAxiomsF`.

Hairer [Hai14, Definition 5.7, Theorem 5.14].
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The old integration sector lifted into the planted completion. -/
def phi43IntegrationSectorF : Submodule ℝ (SymbolF → ℝ) :=
  IntExt.liftedSector SymbolF.old phi43IntegrationSector phi43PlantD

private theorem phi43AbstractIntegration_single_bridge (d : Symbol) :
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

private theorem phi43IntegrationExtensionF_intExt_single (d : Symbol) :
    IntExt.intExt SymbolF.old phi43PlantNew phi43PlantD phi43AbstractIntegration
        (phi43OldEmbF (Pi.single d 1)) =
      phi43IntegrationF (phi43OldEmbF (Pi.single d 1)) := by
  have hold : Function.Injective (SymbolF.old : Symbol → SymbolF) :=
    fun _ _ h => SymbolF.old.inj h
  rw [phi43OldEmbF_single, IntExt.intExt_single_old hold]
  by_cases hd : d ∈ phi43PlantD
  · obtain ⟨τ, hnew, hsource⟩ := phi43PlantNew_of_mem d hd
    have hI : phi43AbstractIntegration (Pi.single d 1) = 0 := by
      rw [← hsource]
      exact phi43PlantSource_abstractIntegration_zero τ
    have hmem : τ.symbol ∈ phi43PlantD :=
      (phi43PlantD_mem_iff).2 ⟨τ, rfl⟩
    have hnewτ : phi43PlantNew τ.symbol = .planted τ := by
      cases τ <;> rfl
    rw [hI, phi43IntegrationF_single, ← hsource,
      phi43IntegrationSymbolF_planted_source]
    simp [hmem, hnewτ]
  · cases d with
    | one =>
        simp [phi43AbstractIntegration_single_bridge, phi43IntegrationF_single,
          phi43IntegrationSymbolF, hd]
    | noise =>
        simp [phi43AbstractIntegration_single_bridge, phi43IntegrationF_single,
          phi43IntegrationSymbolF, IntExt.liftOld_single hold, hd]
    | x0 =>
        simp [phi43AbstractIntegration_single_bridge, phi43IntegrationF_single,
          phi43IntegrationSymbolF, hd]
    | x i =>
        simp [phi43AbstractIntegration_single_bridge, phi43IntegrationF_single,
          phi43IntegrationSymbolF, hd]
    | xMul p =>
        simp [phi43AbstractIntegration_single_bridge, phi43IntegrationF_single,
          phi43IntegrationSymbolF, hd]
    | psi =>
        simp [phi43AbstractIntegration_single_bridge, phi43IntegrationF_single,
          phi43IntegrationSymbolF, IntExt.liftOld_single hold, hd]
    | iPsi =>
        simp [phi43AbstractIntegration_single_bridge, phi43IntegrationF_single,
          phi43IntegrationSymbolF, hd]
    | psiSq =>
        simp [phi43AbstractIntegration_single_bridge, phi43IntegrationF_single,
          phi43IntegrationSymbolF, IntExt.liftOld_single hold, hd]
    | psiCube =>
        simp [phi43AbstractIntegration_single_bridge, phi43IntegrationF_single,
          phi43IntegrationSymbolF, IntExt.liftOld_single hold, hd]
    | psiX i =>
        exact (hd ((phi43PlantD_mem_iff).2 ⟨.psiX i, rfl⟩)).elim
    | psiSqX i =>
        exact (hd ((phi43PlantD_mem_iff).2 ⟨.psiSqX i, rfl⟩)).elim
    | iPsiSq =>
        simp [phi43AbstractIntegration_single_bridge, phi43IntegrationF_single,
          phi43IntegrationSymbolF, hd]
    | iPsiCube =>
        simp [phi43AbstractIntegration_single_bridge, phi43IntegrationF_single,
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
        simp [phi43AbstractIntegration_single_bridge, phi43IntegrationF_single,
          phi43IntegrationSymbolF, hd]

theorem phi43IntegrationExtensionF_intExt_old (_κ : Kappa) (a : Symbol → ℝ) :
    IntExt.intExt SymbolF.old phi43PlantNew phi43PlantD phi43AbstractIntegration
        (phi43OldEmbF a) = phi43IntegrationF (phi43OldEmbF a) := by
  rw [show phi43OldEmbF a = ∑ d : Symbol, a d • phi43OldEmbF (Pi.single d 1) by
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
    congrArg (fun v => a d • v) (phi43IntegrationExtensionF_intExt_single d)

theorem phi43IntegrationExtensionF_intExt_on_sector (κ : Kappa)
    {a : SymbolF → ℝ} (ha : a ∈ phi43IntegrationSectorF) :
    IntExt.intExt SymbolF.old phi43PlantNew phi43PlantD phi43AbstractIntegration a =
      phi43IntegrationF a := by
  obtain ⟨v, hv, hva⟩ := Submodule.mem_map.1 ha
  rw [← hva]
  have hEmb : phi43OldEmbF v = IntExt.liftOld SymbolF.old v := by
    funext τ
    cases τ with
    | old τ =>
        change v τ = IntExt.liftOld SymbolF.old v (.old τ)
        rw [IntExt.liftOld_apply_old (fun _ _ h => SymbolF.old.inj h)]
    | planted τ =>
        change 0 = IntExt.liftOld SymbolF.old v (.planted τ)
        rw [IntExt.liftOld_apply_of_notMem]
        exact fun i h => by cases h
  rw [← hEmb, phi43IntegrationExtensionF_intExt_old κ]

end RegularityStructures.Phi43

end
