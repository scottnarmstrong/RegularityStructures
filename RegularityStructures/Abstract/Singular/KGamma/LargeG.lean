/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.Large
public import RegularityStructures.Abstract.Singular.KGamma.PairingG
public import RegularityStructures.Abstract.Singular.Kernel.LinearG
public import RegularityStructures.Abstract.Singular.Kernel.Shell
public import RegularityStructures.Analysis.Heat.Schauder.DTaylorDeriv
public import RegularityStructures.Analysis.Heat.Schauder.TaylorSum
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# Singular `𝒦_γ`: the large-scale form of the series, weighted models

Weighted (`_growth`) version of `RegularityStructures.Abstract.Singular.KGamma.Large`
(`dTaylorKernel_eq_sub_sum` is model-free and reused).

Singular analogue of the large-scale form of the series in the proof of [Hai14, Theorem 5.12]: for
every `n`,

  `polyUS n = ⟨Rf − Π_x f(x), K^{k,γ}_{n;yx}⟩ − ∑_{i : |k| ≥ deg i + 2} τ_i ⟨Π_y e_i, D^k K_n(y−·)⟩`,

where `⟨Rf − Π_x f(x), g⟩ = latticeRecon f g − ⟨Π_x f(x), g⟩`, `K^{k,γ}_{n;yx}` is
`dTaylorKernel h k n (γ + 2 − |k|) x y`, and `τ = f(y) − Γ_{yx} f(x)` ([Hai14, (5.48)]).
Linearity of the lattice reconstruction (`RegularityStructures.Abstract.Singular.Kernel.LinearG`)
is used under the
hypothesis `hconv` that the lattice approximations converge on the shell derivatives.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {h : ParabolicSpace → ℝ} {N : ℕ} {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}

/-- `⟨Π_x τ, K^{k,σ}_{n;yx}⟩ = ⟨Π_x τ, D^kK_n(y−·)⟩ − ∑_l c_l ⟨Π_x τ, D^{k+l}K_n(x−·)⟩`. -/
theorem pairing_regPi_dTaylorKernel_growth (hh : ShellProfile h N)
    (Gm : M.GrowthModel γ CPi CGam ρP ρG p qG) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {τ : ι → ℝ} (hτ : τ ∈ lowerSubspace 𝒯.deg γ)
    (x y : ParabolicSpace) (k : Fin 4 →₀ ℕ) (n : ℕ) (σ : ℝ) :
    parabolicSemigroup.pairing (M.regPi x τ) (dTaylorKernel h k n σ x y) =
      parabolicSemigroup.pairing (M.regPi x τ)
          (fun w => lineIter (multiDirs k) (scaledShell h n) (y - w)) -
        ∑ l ∈ taylorIdx σ, coeffT (parabolicCoords (y - x)) l *
          parabolicSemigroup.pairing (M.regPi x τ)
            (fun w => lineIter (multiDirs (k + l)) (scaledShell h n) (x - w)) := by
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
  have hsc' : ∀ o, ∃ A, IsScaledTest (G o) (zc o) (((2 : ℝ) ^ n)⁻¹) A := fun o => by
    cases o with
    | none => exact ⟨_, hC n y⟩
    | some l => exact ⟨_, (hC' l).2 n x⟩
  choose A hsc using hsc'
  have e : dTaylorKernel h k n σ x y =
      fun w => ∑ o ∈ Finset.insertNone (taylorIdx σ), c o * G o w := by
    funext w
    rw [dTaylorKernel_eq_sub_sum]
    simp only [Finset.sum_insertNone, hc, hG, Option.elim_none, Option.elim_some, one_mul,
      neg_mul, Finset.sum_neg_distrib]
    ring
  rw [e, M.pairing_regPi_sum_mul_of_scaled_centres_growth Gm hdeg hτ x c G _ zc _ A
    fun o _ => hsc o]
  simp only [Finset.sum_insertNone, hc, hG, Option.elim_none, Option.elim_some, one_mul,
    neg_mul, Finset.sum_neg_distrib]
  ring

end Model

end RegularityStructures

end
