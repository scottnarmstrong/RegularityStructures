/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.ModelLocal
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Heat.Annihilating.Decomposition
public import RegularityStructures.Analysis.Heat.Annihilating.KernelSupport
public import RegularityStructures.Analysis.Heat.Schauder.Derivative
public import RegularityStructures.Analysis.Heat.Schauder.DerivativePairing

/-!
# Coefficients of Hairer's map `J(x)`

Hairer's map [Hai14, (5.11)] is
`J(x) e_i = ∑_{|k|_𝔰 < deg i + β} X^k/k! ∑_n ⟨Π_x e_i, D₁^k K_n(x, ·)⟩` (here `β = 2`).  We define the
coefficient `jCoeff M N x i k = ∑_n ⟨Π_x e_i, D^k annShell N n (x - ·)⟩` for the annihilating
decomposition `annShell N n`, and show it converges absolutely with
`|jCoeff M N x i k| ≤ c C_Π max(C_Γ, 1)` for `|k|_𝔰 < deg i + 2`
(`summable_jCoeff_terms`, `abs_jCoeff_le`).  The pairing is that of `Q`-families
(`RegularisingSemigroup.pairing`), and `Π_x e_i` is of local order `deg i` at `x`
(`Model.isLocalOrder_regPi_single`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- `jCoeff M N x i k = ∑ₙ ⟨Π_x e_i, D^k (annShell N n)(x - ·)⟩`. -/
def jCoeff (M : Model 𝒯 parabolicSemigroup) (N : ℕ) (x : ParabolicSpace) (i : ι)
    (k : Fin 4 →₀ ℕ) : ℝ :=
  ∑' n : ℕ, parabolicSemigroup.pairing (fun t y => M.regPi x (Pi.single i 1) t y)
    (fun y => lineIter (multiDirs k) (annShell N n) (x - y))

/-- The constant of the `J`-coefficient bound (depends on `𝒯, γ, i, N, k`, not on the model). -/
def jCoeffConst (𝒯 : RegularityStructure ι) (γ : ℝ) (N : ℕ) (i : ι) (k : Fin 4 →₀ ℕ) : ℝ :=
  derivShellConst (annKernel0 N) k (𝒯.degreesBelowLe γ (𝒯.deg i)) /
    (1 - derivShellRatio k (𝒯.deg i)) * Fintype.card ι

end RegularityStructures

end

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

theorem jCoeff_eq_tsum_derivShellPairing (M : Model 𝒯 parabolicSemigroup) (N : ℕ)
    (x : ParabolicSpace) (i : ι) (k : Fin 4 →₀ ℕ) :
    jCoeff M N x i k = ∑' n, derivShellPairing (fun t y => M.regPi x (Pi.single i 1) t y)
      (annKernel0 N) k x n := rfl

/-- The exponent set condition: all degrees `a ≤ deg i` below `γ` exceed `-4`. -/
theorem degreesBelowLe_bounds (𝒯 : RegularityStructure ι) {γ : ℝ}
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) (i : ι) :
    ∀ a ∈ 𝒯.degreesBelowLe γ (𝒯.deg i), -4 < a ∧ a ≤ 𝒯.deg i := by
  intro a ha
  rw [RegularityStructure.degreesBelowLe, Finset.mem_filter] at ha
  obtain ⟨j, hj, rfl⟩ := (𝒯.mem_degreesBelow).1 ha.1
  exact ⟨hdeg j hj, ha.2⟩

section
variable (M : Model 𝒯 parabolicSemigroup) {γ CPi CGam : ℝ} (N : ℕ) (x : ParabolicSpace) (i : ι)
  (k : Fin 4 →₀ ℕ)

theorem summable_jCoeff_terms (hPi : M.PiBoundOn γ CPi univ) (hGam : M.GammaBoundOn γ CGam univ)
    (hCPi : 0 ≤ CPi) (hi : 𝒯.deg i < γ) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (hk : (multiDeg k : ℝ) < 𝒯.deg i + 2) :
    Summable fun n : ℕ => parabolicSemigroup.pairing
      (fun t y => M.regPi x (Pi.single i 1) t y)
      (fun y => lineIter (multiDirs k) (annShell N n) (x - y)) :=
  summable_pairing_lineIter_scaledShell (M.regPi_mem x _)
    (fun _ hu => M.measurable_regPi x _ hu) (contDiff_annKernel0 N) (fun _ hz => annKernel0_eq_zero N hz) k
    (degreesBelowLe_bounds 𝒯 hdeg i)
    (mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_right _ _)) hCPi) (Nat.cast_nonneg _))
    (M.isLocalOrder_regPi_single hPi hGam hCPi hi x) hk

theorem abs_jCoeff_le (hPi : M.PiBoundOn γ CPi univ) (hGam : M.GammaBoundOn γ CGam univ)
    (hCPi : 0 ≤ CPi) (hi : 𝒯.deg i < γ) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (hk : (multiDeg k : ℝ) < 𝒯.deg i + 2) :
    |jCoeff M N x i k| ≤ jCoeffConst 𝒯 γ N i k * CPi * max CGam 1 := by
  have hC : 0 ≤ max CGam 1 * CPi * Fintype.card ι :=
    mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_right _ _)) hCPi) (Nat.cast_nonneg _)
  have h := abs_tsum_pairing_lineIter_scaledShell_le (M.regPi_mem x _)
    (fun _ hu => M.measurable_regPi x _ hu) (contDiff_annKernel0 N) (fun _ hz => annKernel0_eq_zero N hz) k
    (degreesBelowLe_bounds 𝒯 hdeg i) hC (M.isLocalOrder_regPi_single hPi hGam hCPi hi x) hk
  rw [jCoeff_eq_tsum_derivShellPairing]
  refine h.trans (le_of_eq ?_)
  rw [jCoeffConst]
  ring

theorem jCoeffConst_nonneg (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    (hk : (multiDeg k : ℝ) < 𝒯.deg i + 2) : 0 ≤ jCoeffConst 𝒯 γ N i k := by
  refine mul_nonneg (div_nonneg (derivShellConst_nonneg _ _ (degreesBelowLe_bounds 𝒯 hdeg i))
    (sub_nonneg.2 (derivShellRatio_lt_one hk).le)) (Nat.cast_nonneg _)

end

end RegularityStructures

end
