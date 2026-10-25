/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.LargeG
public import RegularityStructures.Abstract.Singular.KGamma.MeasReconG
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# Singular `𝒦_γ`: the large-scale form of the series on the time slab, weighted models

Weighted (`_growth`) version. `Model.polyUS_eq_large_growth`
(`RegularityStructures.Abstract.Singular.KGamma.LargeG`) assumes that the lattice approximations of
the shell derivatives `D^k K_n(z - ·)` converge for *every* centre `z`. Here we only use the two
centres `x` and `y`, and discharge the convergence for centres in the time slab from the weighted
layer setting (`Model.tendsto_latticeApprox_lineIter_scaledShell_growth`): this is
`Model.polyUS_eq_large_of_slab_growth`.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {h : ParabolicSpace → ℝ} {N : ℕ}
  {γ CPi CGam p qG Rw : ℝ} {ρP ρG : ParabolicSpace → ℝ}

/-- `latticeRecon` of the Taylor kernel, given convergence of the lattice approximations of the
shell derivatives at the two centres `x` and `y` only. -/
theorem latticeRecon_dTaylorKernel_of_conv_growth (hh : ShellProfile h N)
    {f : ParabolicSpace → ι → ℝ} (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (Gm : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (x y : ParabolicSpace)
    (hcy : ∀ k n, Tendsto (M.latticeApprox f
      (fun w => lineIter (multiDirs k) (scaledShell h n) (y - w))) atTop
      (𝓝 (M.latticeRecon f (fun w => lineIter (multiDirs k) (scaledShell h n) (y - w)))))
    (hcx : ∀ k n, Tendsto (M.latticeApprox f
      (fun w => lineIter (multiDirs k) (scaledShell h n) (x - w))) atTop
      (𝓝 (M.latticeRecon f (fun w => lineIter (multiDirs k) (scaledShell h n) (x - w)))))
    (k : Fin 4 →₀ ℕ) (n : ℕ) (σ : ℝ) :
    M.latticeRecon f (dTaylorKernel h k n σ x y) =
      M.latticeRecon f (fun w => lineIter (multiDirs k) (scaledShell h n) (y - w)) -
        ∑ l ∈ taylorIdx σ, coeffT (parabolicCoords (y - x)) l *
          M.latticeRecon f (fun w => lineIter (multiDirs (k + l)) (scaledShell h n) (x - w)) := by
  classical
  obtain ⟨C, -, hC⟩ := exists_isScaledTest_lineIter_multiDirs_scaledShell hh k
  choose C' hC' using fun l : Fin 4 →₀ ℕ => exists_isScaledTest_lineIter_multiDirs_scaledShell hh
    (k + l)
  set G : Option (Fin 4 →₀ ℕ) → ParabolicSpace → ℝ := fun o =>
    o.elim (fun w => lineIter (multiDirs k) (scaledShell h n) (y - w))
      (fun l w => lineIter (multiDirs (k + l)) (scaledShell h n) (x - w)) with hG
  set zc : Option (Fin 4 →₀ ℕ) → ParabolicSpace := fun o => o.elim y fun _ => x with hzc
  set c : Option (Fin 4 →₀ ℕ) → ℝ := fun o =>
    o.elim (1 : ℝ) fun l => -coeffT (parabolicCoords (y - x)) l with hc
  set L : Option (Fin 4 →₀ ℕ) → ℝ := fun o => c o * M.latticeRecon f (G o) with hL
  have hsc' : ∀ o, ∃ A, IsScaledTest (G o) (zc o) (((2 : ℝ) ^ n)⁻¹) A := fun o => by
    cases o with
    | none => exact ⟨_, hC n y⟩
    | some l => exact ⟨_, (hC' l).2 n x⟩
  choose A hsc using hsc'
  have hconvG : ∀ o, Tendsto (M.latticeApprox f (G o)) atTop (𝓝 (M.latticeRecon f (G o))) :=
    fun o => by
      cases o with
      | none => exact hcy k n
      | some l => exact hcx (k + l) n
  have hT := M.tendsto_latticeApprox_finset_sum_growth hf Gm hdeg
    (Finset.insertNone (taylorIdx σ)) (fun o => c o • G o) zc (fun _ => ((2 : ℝ) ^ n)⁻¹)
    (fun o _ => by exact (hsc o).contDiff.const_smul (c o))
    (fun o _ w hw => by simp [(hsc o).supp w hw]) L
    (fun o _ => M.tendsto_latticeApprox_smul_growth hf Gm hdeg (hsc o).contDiff
      (hsc o).supp (c o) (hconvG o))
  have e : dTaylorKernel h k n σ x y = ∑ o ∈ Finset.insertNone (taylorIdx σ), c o • G o := by
    funext w
    rw [dTaylorKernel_eq_sub_sum]
    simp only [Finset.sum_apply, Finset.sum_insertNone, hc, hG, Pi.smul_apply, smul_eq_mul,
      Option.elim_none, Option.elim_some, one_mul, neg_mul, Finset.sum_neg_distrib]
    ring
  rw [e]
  unfold latticeRecon
  rw [hT.limUnder_eq]
  simp only [hL, hc, hG, Finset.sum_insertNone, Option.elim_none, Option.elim_some, one_mul,
    neg_mul, Finset.sum_neg_distrib]
  unfold latticeRecon
  ring

end Model

end RegularityStructures

end
