/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalSmoothCharacters
import Mathlib.Tactic

/-!
# Measurability of the finite structure-group action in the parameters

If the five components of `g ω : G` are measurable in `ω`, then so is every matrix coefficient
`ω ↦ structureGroupMap (g ω) (basis τ) σ` (`measurable_structureGroupMap_basis`).  It is obtained
from the continuity lemma `continuous_structureGroupMap_basis` applied to the parameter space
`ℝ⁴ × ℝ × ℝ³ × ℝ × ℝ`.  Also: the components of `g⁻¹ h` (`structureGroupInv g * h`) are measurable
if those of `g` and `h` are (`measurable_inv_mul_components`).
-/

public section

namespace RegularityStructures.Phi43

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The parameter space of the structure group. -/
abbrev StructureParamSpace : Type := (Fin 4 → ℝ) × ℝ × (Fin 3 → ℝ) × ℝ × ℝ

/-- The structure group element with given parameters. -/
abbrev structureOfParams (p : StructureParamSpace) : G := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩

theorem measurable_structureGroupMap_basis (g : Ω → G)
    (hx : ∀ i, Measurable fun ω => (g ω).shift i) (hp : Measurable fun ω => (g ω).cPsi)
    (hpg : ∀ i, Measurable fun ω => (g ω).cPsiGrad i)
    (hs : Measurable fun ω => (g ω).cPsiSq) (hc : Measurable fun ω => (g ω).cPsiCube)
    (τ σ : Symbol) : Measurable fun ω => structureGroupMap (g ω) (basis τ) σ := by
  have hcont : Continuous fun p : StructureParamSpace =>
      structureGroupMap (structureOfParams p) (basis τ) σ :=
    continuous_structureGroupMap_basis structureOfParams
      (fun i => (continuous_apply i).comp continuous_fst)
      (continuous_fst.comp continuous_snd)
      (fun i => (continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd)))
      (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))
      (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))) τ σ
  have hpar : Measurable fun ω => (((g ω).shift, (g ω).cPsi, (g ω).cPsiGrad, (g ω).cPsiSq,
      (g ω).cPsiCube) : StructureParamSpace) :=
    (measurable_pi_iff.2 hx).prodMk (hp.prodMk ((measurable_pi_iff.2 hpg).prodMk (hs.prodMk hc)))
  have e : (fun ω => structureGroupMap (g ω) (basis τ) σ) = (fun p : StructureParamSpace =>
      structureGroupMap (structureOfParams p) (basis τ) σ) ∘ (fun ω => (((g ω).shift, (g ω).cPsi,
        (g ω).cPsiGrad, (g ω).cPsiSq, (g ω).cPsiCube) : StructureParamSpace)) := by
    funext ω
    rfl
  rw [e]
  exact hcont.measurable.comp hpar

theorem measurable_inv_mul_components (g h : Ω → G)
    (hgx : ∀ i, Measurable fun ω => (g ω).shift i) (hgp : Measurable fun ω => (g ω).cPsi)
    (hgg : ∀ i, Measurable fun ω => (g ω).cPsiGrad i)
    (hgs : Measurable fun ω => (g ω).cPsiSq) (hgc : Measurable fun ω => (g ω).cPsiCube)
    (hhx : ∀ i, Measurable fun ω => (h ω).shift i) (hhp : Measurable fun ω => (h ω).cPsi)
    (hhg : ∀ i, Measurable fun ω => (h ω).cPsiGrad i)
    (hhs : Measurable fun ω => (h ω).cPsiSq) (hhc : Measurable fun ω => (h ω).cPsiCube)
    (τ σ : Symbol) :
    Measurable fun ω => structureGroupMap (structureGroupInv (g ω) * h ω) (basis τ) σ := by
  refine measurable_structureGroupMap_basis (fun ω => structureGroupInv (g ω) * h ω) ?_ ?_ ?_ ?_ ?_
    τ σ
  · intro i
    simp only [structureGroupMul_shift, structureGroupInv, Pi.add_apply, Pi.neg_apply]
    exact (hgx i).neg.add (hhx i)
  · simp only [structureGroupMul_cPsi, structureGroupInv, Pi.neg_apply]
    refine ((hgp.neg.add (Finset.measurable_sum _ fun i _ => (hgx i.succ).mul (hgg i))).add
      hhp).add (Finset.measurable_sum _ fun i _ => ?_)
    exact (hgx i.succ).neg.mul (hhg i)
  · intro i
    simp only [structureGroupMul_cPsiGrad, structureGroupInv, Pi.add_apply, Pi.neg_apply]
    exact (hgg i).neg.add (hhg i)
  · simp only [structureGroupInv]
    exact hgs.neg.add hhs
  · simp only [structureGroupInv]
    exact hgc.neg.add hhc

end RegularityStructures.Phi43

end
