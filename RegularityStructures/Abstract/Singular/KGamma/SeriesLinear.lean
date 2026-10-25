/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SeriesZero

/-!
# The Taylor kernel: linearity of the model pairing and the choice of the exponent
* `Model.pairing_regPi_dTaylor_eq_sum`: `⟨Π_x τ, K^{k,σ}_{n;yx}⟩ = ∑_i τ_i ⟨Π_x e_i, K^{k,σ}_{n;yx}⟩`
  for all scales `n ≥ 0` (`n ≥ 1`: the kernel is a scaled test function at `x`; `n = 0`: it lives
  in `B(x, 2)`);
* `taylorIdx_ceil`, `dTaylorKernel_ceil`: `taylorIdx ⌈σ⌉ = taylorIdx σ`, hence the Taylor kernel for
  the exponent `σ` equals the one for `⌈σ⌉`;
* `lt_ceil_of_forall_multiDeg_ne`: if no `|l|_𝔰` equals `σ > 0`, then `σ < ⌈σ⌉`.
-/

public section

open Set Filter
open scoped Topology ContDiff

namespace RegularityStructures

theorem exists_multiDeg_eq (m : ℕ) : ∃ l : Fin 4 →₀ ℕ, multiDeg l = m := by
  refine ⟨Finsupp.single 1 m, ?_⟩
  simp [multiDeg, Finsupp.weight_apply, Finsupp.sum_single_index, parabolicWeight]

theorem taylorIdx_ceil (σ : ℝ) : taylorIdx (⌈σ⌉ : ℝ) = taylorIdx σ := by
  ext l
  rw [mem_taylorIdx_iff, mem_taylorIdx_iff]
  have := Int.lt_ceil (a := σ) (z := (multiDeg l : ℤ))
  have e : ((multiDeg l : ℕ) : ℝ) < (⌈σ⌉ : ℝ) ↔ (multiDeg l : ℤ) < ⌈σ⌉ := by
    exact_mod_cast Iff.rfl
  rw [e, this]
  norm_cast

theorem dTaylorKernel_ceil (h : ParabolicSpace → ℝ) (k : Fin 4 →₀ ℕ) (n : ℕ) (σ : ℝ)
    (x y : ParabolicSpace) :
    dTaylorKernel h k n (⌈σ⌉ : ℝ) x y = dTaylorKernel h k n σ x y := by
  unfold dTaylorKernel
  rw [taylorIdx_ceil]

/-- If no `|l|_𝔰` equals `σ > 0` then `σ < ⌈σ⌉` (`σ` is not an integer). -/
theorem lt_ceil_of_forall_multiDeg_ne {σ : ℝ} (hσ : 0 < σ)
    (hne : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) ≠ σ) : σ < (⌈σ⌉ : ℝ) := by
  rcases (Int.le_ceil σ).lt_or_eq with h | h
  · exact h
  · exfalso
    have hc : (0 : ℤ) ≤ ⌈σ⌉ := Int.ceil_nonneg hσ.le
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hc
    obtain ⟨l, hl⟩ := exists_multiDeg_eq m
    refine hne l ?_
    rw [hl, h, hm]
    simp

end RegularityStructures

end
