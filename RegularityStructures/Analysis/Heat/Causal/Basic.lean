/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Annihilating.Decomposition
public import RegularityStructures.Analysis.Heat.Causal.Bump
public import RegularityStructures.Analysis.Heat.Annihilating.Scaled

/-!
# Causal polynomial-annihilating modification of the heat shells

The construction of `Analysis/Heat/Annihilating` with the correcting bump `ψ = annBumpC N`
supported in `{t > 0}` (`exists_moment_bump_causal`), so that every shell
`annShellC N n` and the remainder `annRemainderC N` are non-anticipative.  Contains the
decomposition `G = ∑ₙ annShellC N n + annRemainderC N` away from `0`
(`heatKernelR4_eq_tsum_annShellC`) and Assumption 5.1 with `β = 2`
(`isRegularisingDecomposition_annShellC`).

Source: Hairer, arXiv:1303.5113v4, proof of Lemma 5.5 and Section 7.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace RegularityStructures

theorem exists_annBumpC (N : ℕ) :
    ∃ ψ : ParabolicSpace → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ z, 1 < parabolicNorm z → ψ z = 0) ∧
      (∀ z, z.1 ≤ 0 → ψ z = 0) ∧
      ∀ k : PolyIndex N, ∫ z, evalParabolic (MvPolynomial.monomial k.1 1) z * ψ z = annMoment k :=
  exists_moment_bump_causal N annMoment

/-- The causal correcting bump `ψ`. -/
def annBumpC (N : ℕ) : ParabolicSpace → ℝ := Classical.choose (exists_annBumpC N)

/-- The base kernel `K₀ = heatShell 0 - ψ + 2³ ψ(S² ·)` with the causal bump. -/
def annKernel0C (N : ℕ) (z : ParabolicSpace) : ℝ :=
  heatShell 0 z - annBumpC N z + 2 ^ 3 * annBumpC N (parabolicDilate 2 z)

/-- The `n`-th causal polynomial-annihilating shell `(2^n)^3 K₀(S^{2^n} z)`. -/
def annShellC (N n : ℕ) (z : ParabolicSpace) : ℝ := scaledShell (annKernel0C N) n z

/-- The smooth causal remainder `R = heatRemainder + ψ`. -/
def annRemainderC (N : ℕ) (z : ParabolicSpace) : ℝ := heatRemainder z + annBumpC N z

end RegularityStructures

end

public section

open scoped ContDiff

namespace RegularityStructures

theorem contDiff_annBumpC (N : ℕ) : ContDiff ℝ ∞ (annBumpC N) :=
  (Classical.choose_spec (exists_annBumpC N)).1

theorem annBumpC_eq_zero {N : ℕ} {z : ParabolicSpace} (hz : 1 < parabolicNorm z) :
    annBumpC N z = 0 :=
  (Classical.choose_spec (exists_annBumpC N)).2.1 z hz

theorem annBumpC_eq_zero_of_nonpos {N : ℕ} {z : ParabolicSpace} (hz : z.1 ≤ 0) :
    annBumpC N z = 0 :=
  (Classical.choose_spec (exists_annBumpC N)).2.2.1 z hz

theorem integral_monomial_mul_annBumpC {N : ℕ} (k : PolyIndex N) :
    ∫ z, evalParabolic (MvPolynomial.monomial k.1 1) z * annBumpC N z = annMoment k :=
  (Classical.choose_spec (exists_annBumpC N)).2.2.2 k

theorem contDiff_annKernel0C (N : ℕ) : ContDiff ℝ ∞ (annKernel0C N) := by
  unfold annKernel0C
  exact ((contDiff_heatShell 0).sub (contDiff_annBumpC N)).add
    (contDiff_const.mul ((contDiff_annBumpC N).comp (parabolicDilateCLM 2).contDiff))

theorem annKernel0C_eq_zero (N : ℕ) {z : ParabolicSpace} (hz : 1 < parabolicNorm z) :
    annKernel0C N z = 0 := by
  have h1 : heatShell 0 z = 0 := heatShell_eq_zero (by simpa using hz)
  have h2 : 1 < parabolicNorm (parabolicDilate 2 z) := by
    rw [parabolicNorm_parabolicDilate (by norm_num)]
    linarith [parabolicNorm_nonneg z]
  simp [annKernel0C, h1, annBumpC_eq_zero hz, annBumpC_eq_zero h2]

theorem contDiff_annShellC (N n : ℕ) : ContDiff ℝ ∞ (annShellC N n) :=
  contDiff_scaledShell (contDiff_annKernel0C N) n

theorem annShellC_eq_zero {N n : ℕ} {z : ParabolicSpace} (hz : (2 : ℝ)⁻¹ ^ n < parabolicNorm z) :
    annShellC N n z = 0 :=
  scaledShell_eq_zero (fun _ hz => annKernel0C_eq_zero N hz) hz

theorem contDiff_annRemainderC (N : ℕ) : ContDiff ℝ ∞ (annRemainderC N) :=
  contDiff_heatRemainder.add (contDiff_annBumpC N)

/-- Each shell is the heat shell, minus the `n`-th rescaling of `ψ`, plus its `(n+1)`-st. -/
theorem annShellC_eq (N n : ℕ) (z : ParabolicSpace) :
    annShellC N n z = heatShell n z - scaledShell (annBumpC N) n z +
      scaledShell (annBumpC N) (n + 1) z := by
  unfold annShellC scaledShell annKernel0C
  have hd : parabolicDilate (2 ^ (n + 1)) z = parabolicDilate 2 (parabolicDilate (2 ^ n) z) := by
    rw [pow_succ, mul_comm, parabolicDilate_mul]
  rw [heatShell_eq_scale n z, hd]
  ring

/-- Telescoping of the partial sums. -/
theorem sum_range_annShellC (N M : ℕ) (z : ParabolicSpace) :
    ∑ n ∈ Finset.range M, annShellC N n z =
      ∑ n ∈ Finset.range M, heatShell n z - annBumpC N z + scaledShell (annBumpC N) M z := by
  induction M with
  | zero => simp [scaledShell_zero]
  | succ M ih => rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, annShellC_eq]; ring

theorem heatKernelR4_eq_tsum_annShellC {N : ℕ} {z : ParabolicSpace} (hz : z ≠ 0) :
    heatKernelR4 z = (∑' n : ℕ, annShellC N n z) + annRemainderC N z := by
  obtain ⟨M, hM⟩ := exists_inv_pow_lt hz
  have hvan : ∀ m, M ≤ m → (2 : ℝ)⁻¹ ^ m < parabolicNorm z := fun m hm =>
    lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) hm) hM
  have hA : ∑' n : ℕ, annShellC N n z = ∑ n ∈ Finset.range M, annShellC N n z :=
    tsum_eq_sum fun n hn => annShellC_eq_zero (hvan n (not_lt.1 (by simpa using hn)))
  have hH : ∑' n : ℕ, heatShell n z = ∑ n ∈ Finset.range M, heatShell n z :=
    tsum_eq_sum fun n hn => heatShell_eq_zero (hvan n (not_lt.1 (by simpa using hn)))
  have hS : scaledShell (annBumpC N) M z = 0 :=
    scaledShell_eq_zero (fun _ hz => annBumpC_eq_zero hz) hM
  have := heatKernelR4_eq_tsum hz
  rw [hH] at this
  rw [hA, sum_range_annShellC, hS, annRemainderC, this]
  ring

end RegularityStructures

end
