/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.JMap
public import RegularityStructures.Abstract.TestFunctionBound
public import RegularityStructures.Abstract.Integration.JMapDef

/-!
# Hairer's polynomial correction `N_γ f`

[Hai14, (5.16)]: `(N_γ f)(x) = ∑_{|k|_𝔰 < γ + β} X^k / k! ∫ D₁^k K(x, y) (Rf − Π_x f(x))(dy)`,
β = 2. With the decomposition `K = ∑_n K_n` (`annShell N n`), the coefficient of `X^k / k!` is

  `nCoeff M N f x k = ∑_n ⟨Rf − Π_x f(x), D^k K_n(x − ·)⟩`.

Since `Rf − Π_x f(x)` is of local order `γ` at `x` (`Model.isLocalOrder_reconstructSubAt`), the
derivative-shell bound gives convergence and `|nCoeff| ≤ c C_Π C_f` whenever `|k|_𝔰 < γ + 2`
(`summable_nCoeff_terms`, `abs_nCoeff_le`); this is the statement after (5.16) in [Hai14] that
"this expression is indeed well-defined for all `f ∈ D^γ`".

Source: [Hai14, (5.16) and the proof of Theorem 5.12].
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- The coefficient of `X^k / k!` in `N_γ f(x)`:
`∑_n ⟨Rf − Π_x f(x), D^k K_n(x − ·)⟩`. -/
def nCoeff (M : Model 𝒯 parabolicSemigroup) (N : ℕ) (f : ParabolicSpace → ι → ℝ)
    (x : ParabolicSpace) (k : Fin 4 →₀ ℕ) : ℝ :=
  ∑' n : ℕ, derivShellPairing (M.reconstructSubAt f x) (annKernel0 N) k x n

/-- The constant of the `N_γ` coefficient bound (independent of the model and of `f`). -/
def nCoeffConst (𝒯 : RegularityStructure ι) (γ : ℝ) (N : ℕ) (k : Fin 4 →₀ ℕ) : ℝ :=
  derivShellConst (annKernel0 N) k (insert γ (𝒯.degreesBelow γ)) /
    (1 - derivShellRatio k γ) *
    (modelReconstructionConst 𝒯 parabolicSemigroup γ + Fintype.card ι)

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

theorem exponents_reconstructSubAt {γ : ℝ} (hγ : 0 < γ)
    (hdeg : ∀ i, 𝒯.deg i < γ → -4 < 𝒯.deg i) :
    ∀ a ∈ insert γ (𝒯.degreesBelow γ), -4 < a ∧ a ≤ γ := by
  intro a ha
  rcases Finset.mem_insert.1 ha with rfl | ha
  · exact ⟨by linarith, le_rfl⟩
  · obtain ⟨i, hi, rfl⟩ := (𝒯.mem_degreesBelow).1 ha
    exact ⟨hdeg i hi, hi.le⟩

section

variable (M : Model 𝒯 parabolicSemigroup) {γ CPi Cf : ℝ} (hγ : 0 < γ)
  (hPi : M.PiBoundOn γ CPi univ) (hCPi : 0 ≤ CPi) {f : ParabolicSpace → ι → ℝ}
  (hf : f ∈ M.modelledDistributions γ) (hfb : M.ModelledBoundOn γ Cf univ f) (hCf : 0 ≤ Cf)
  (hdeg : ∀ i, 𝒯.deg i < γ → -4 < 𝒯.deg i) (N : ℕ) (x : ParabolicSpace) {k : Fin 4 →₀ ℕ}
  (hk : (multiDeg k : ℝ) < γ + 2)

include hγ hPi hCPi hf hfb hCf hdeg hk

/-- The series defining `nCoeff` converges for `|k|_𝔰 < γ + 2`. -/
theorem summable_nCoeff_terms :
    Summable (derivShellPairing (M.reconstructSubAt f x) (annKernel0 N) k x) :=
  summable_pairing_lineIter_scaledShell (M.reconstructSubAt_mem hγ hPi hCPi hf hfb hCf x)
    (fun _ hu => M.measurable_reconstructSubAt hγ hPi hCPi hf hfb hCf x hu)
    (contDiff_annKernel0 N) (fun _ hz => annKernel0_eq_zero N hz) k
    (exponents_reconstructSubAt hγ hdeg)
    (mul_nonneg (mul_nonneg (add_nonneg (modelReconstructionConst_nonneg 𝒯 _ hγ.le)
      (Nat.cast_nonneg _)) hCPi) hCf)
    (M.isLocalOrder_reconstructSubAt hγ hPi hCPi hf hfb hCf x) hk

/-- `|nCoeff M N f x k| ≤ c C_Π C_f` for `|k|_𝔰 < γ + 2`, with `c = nCoeffConst 𝒯 γ N k`. -/
theorem abs_nCoeff_le : |nCoeff M N f x k| ≤ nCoeffConst 𝒯 γ N k * CPi * Cf := by
  have h := abs_tsum_pairing_lineIter_scaledShell_le
    (M.reconstructSubAt_mem hγ hPi hCPi hf hfb hCf x)
    (fun _ hu => M.measurable_reconstructSubAt hγ hPi hCPi hf hfb hCf x hu)
    (contDiff_annKernel0 N) (fun _ hz => annKernel0_eq_zero N hz) k
    (exponents_reconstructSubAt hγ hdeg)
    (mul_nonneg (mul_nonneg (add_nonneg (modelReconstructionConst_nonneg 𝒯 _ hγ.le)
      (Nat.cast_nonneg _)) hCPi) hCf)
    (M.isLocalOrder_reconstructSubAt hγ hPi hCPi hf hfb hCf x) hk
  refine h.trans (le_of_eq ?_)
  rw [nCoeffConst]
  ring

end

end RegularityStructures

end
