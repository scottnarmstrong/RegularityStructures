/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Remainder.Words
public import RegularityStructures.Analysis.Heat.Decay

/-!
# Spatial decay of the derivatives of the smooth remainder, with uniform constants

`RemDecay G n τ₀ B` says `‖D^i G(u)‖ ≤ B (1 + |u'|²)^{-3}` for all `i ≤ n` and `u₀ ≤ τ₀`.
For `G = D^k R`, `R = annRemainderC N`, such a bound holds for every `n` and `τ₀`
(`exists_remDecay_lineIter_annRemainderC`); this is the base case for all kernels below.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The spatial decay weight `(1 + |u'|²)^{-3}`. -/
def remWt (a : Fin 3 → ℝ) : ℝ := (1 + sqNorm3 a)⁻¹ ^ 3

/-- Uniform decay of the derivatives of order `≤ n` for times `≤ τ₀`. -/
def RemDecay (G : ParabolicSpace → ℝ) (n : ℕ) (τ₀ B : ℝ) : Prop :=
  ∀ i ≤ n, ∀ u : ParabolicSpace, u.1 ≤ τ₀ → ‖iteratedFDeriv ℝ i G u‖ ≤ B * remWt u.2

end RegularityStructures

end

public section

open scoped ContDiff

namespace RegularityStructures

theorem remWt_nonneg (a : Fin 3 → ℝ) : 0 ≤ remWt a := by
  have := sqNorm3_nonneg a
  unfold remWt; positivity

/-- For every `k`, `n` and `τ₀`, the derivatives of `D^k R` of order `≤ n` decay uniformly. -/
theorem exists_remDecay_lineIter_annRemainderC (N : ℕ) (k : Fin 4 →₀ ℕ) (n : ℕ) (τ₀ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ RemDecay (lineIter (multiDirs k) (annRemainderC N)) n τ₀ B := by
  have hC : ∀ p : (Σ i : Fin (n + 1), (Fin i → Fin 4)), ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ParabolicSpace, z.1 ≤ τ₀ →
        |lineIter (List.ofFn (fun i => coordDir (p.2 i)) ++ multiDirs k) (annRemainderC N) z| ≤
          C * remWt z.2 := fun p => by
    obtain ⟨C, hC0, hC⟩ := exists_abs_lineIter_annRemainderC_le_of_list N
      (List.ofFn (fun i => coordDir (p.2 i)) ++ multiDirs k) 3 (T₀ := τ₀)
    exact ⟨C, hC0, hC⟩
  choose C hC0 hC using hC
  set B₀ : ℝ := ∑ p, C p with hB₀
  have hB₀0 : 0 ≤ B₀ := Finset.sum_nonneg fun p _ => hC0 p
  refine ⟨4 ^ n * B₀, by positivity, fun i hi u hu => ?_⟩
  have hg : ContDiff ℝ ∞ (lineIter (multiDirs k) (annRemainderC N)) :=
    contDiff_lineIter (contDiff_annRemainderC N) _
  have hb0 : 0 ≤ B₀ * remWt u.2 := mul_nonneg hB₀0 (remWt_nonneg _)
  have h1 := norm_iteratedFDeriv_le_of_words hg i u hb0 fun r => by
    rw [← lineIter_append]
    have := hC ⟨⟨i, Nat.lt_succ_of_le hi⟩, r⟩ u hu
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (remWt_nonneg _))
    exact Finset.single_le_sum (f := C) (fun p _ => hC0 p) (Finset.mem_univ _)
  refine h1.trans ?_
  have : (4 : ℝ) ^ i ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hi
  calc (4 : ℝ) ^ i * (B₀ * remWt u.2) ≤ 4 ^ n * (B₀ * remWt u.2) :=
        mul_le_mul_of_nonneg_right this hb0
    _ = _ := by ring

end RegularityStructures

end
