/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorDeriv
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# Taylor remainders of the derivative kernels `D^k K_n`

Hairer's kernel `K^{k,α}_{n;xy}` [Hai14, proof of Lemma 5.18]:

  `D^k K_n(y - w) - ∑_{|l|_𝔰 < σ} (y - x)^l/l! · D^{k+l} K_n(x - w)`, `σ = α + 2 - |k|_𝔰`.

Since `D^k (scaledShell h n) = (2^n)^{|k|_𝔰} scaledShell (D^k h) n`, it equals
`(2^n)^{|k|_𝔰} · taylorKernel (D^k h) n σ x y` (`dTaylorKernel_eq`), and the Taylor estimate for
`D^k h` gives `exists_abs_pairing_dTaylorKernel_le`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- `D^k K_n(y - w) - ∑_{|l|_𝔰 < σ} (y - x)^l/l! D^{k+l} K_n(x - w)`, `K_n = scaledShell h n`. -/
def dTaylorKernel (h : ParabolicSpace → ℝ) (k : Fin 4 →₀ ℕ) (n : ℕ) (σ : ℝ)
    (x y w : ParabolicSpace) : ℝ :=
  lineIter (multiDirs k) (scaledShell h n) (y - w) - ∑ l ∈ taylorIdx σ,
    (evalParabolic (MvPolynomial.monomial l 1) (y - x) / multiFact l) *
      lineIter (multiDirs (k + l)) (scaledShell h n) (x - w)

end RegularityStructures

end

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

theorem multiDirs_add_perm (k l : Fin 4 →₀ ℕ) :
    (multiDirs (k + l)).Perm (multiDirs l ++ multiDirs k) := by
  rw [← Multiset.coe_eq_coe, coe_multiDirs, ← Multiset.coe_add, coe_multiDirs, coe_multiDirs,
    Finsupp.toMultiset_add, Multiset.map_add, add_comm]

theorem dTaylorKernel_eq {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h) (k : Fin 4 →₀ ℕ) (n : ℕ)
    (σ : ℝ) (x y : ParabolicSpace) :
    dTaylorKernel h k n σ x y = fun w => ((2 : ℝ) ^ n) ^ multiDeg k *
      taylorKernel (lineIter (multiDirs k) h) n σ x y w := by
  funext w
  have hh' : ContDiff ℝ ∞ (lineIter (multiDirs k) h) := contDiff_lineIter h0 _
  have hg' := contDiff_scaledShell hh' n
  have hDk := lineIter_multiDirs_scaledShell h0 k n
  have hl : ∀ l : Fin 4 →₀ ℕ, lineIter (multiDirs (k + l)) (scaledShell h n) =
      fun w => ((2 : ℝ) ^ n) ^ multiDeg k *
        lineIter (multiDirs l) (scaledShell (lineIter (multiDirs k) h) n) w := by
    intro l
    rw [lineIter_perm (contDiff_scaledShell h0 n) (multiDirs_add_perm k l), lineIter_append, hDk]
    exact lineIter_const_mul hg' _ _
  unfold dTaylorKernel taylorKernel
  rw [hDk]
  simp only [hl]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

end RegularityStructures

end
