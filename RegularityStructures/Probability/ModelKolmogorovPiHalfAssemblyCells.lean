/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyDyadic
public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyMoments
public import Mathlib.Order.CompletePartialOrder

/-!
# Union bound over dyadic levels and cells

`piHalfRandomSup` is the supremum, over dyadic levels `j`, symbols `i` and cells `c < n j`, of the
rescaled random remainders `R j i c · s_j^{-deg i/ℓ}`.  If `n j ≤ A · 2^{5 ⌊j/4⌋}` and
`E (R j i c)^q ≤ (K C s_j^{(deg i + κ)/ℓ})^q` with `q κ ≥ 12`, then
`E (piHalfRandomSup)^q ≤ 2 · |ι| · A · (K C)^q`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

/-- Summability of the cell counts against the decay of the moments. -/
theorem cell_count_mul_scale_le (j nj : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hn : (nj : ℝ) ≤ A * (2 : ℝ) ^ (5 * (j / 4))) {x : ℝ} (hx : 3 ≤ x) :
    (nj : ℝ) * piHalfScale j ^ x ≤ A * (1 / 2 : ℝ) ^ j := by
  have hs0 := piHalfScale_pos j
  have hs1 : piHalfScale j ≤ 1 := by
    unfold piHalfScale; exact pow_le_one₀ (by norm_num) (by norm_num)
  have h1 : piHalfScale j ^ x ≤ piHalfScale j ^ 3 := by
    rw [show piHalfScale j ^ 3 = piHalfScale j ^ ((3 : ℕ) : ℝ) from (Real.rpow_natCast _ _).symm]
    exact Real.rpow_le_rpow_of_exponent_ge hs0 hs1 (by exact_mod_cast hx)
  have h2 : (nj : ℝ) * piHalfScale j ^ x ≤ A * (2 : ℝ) ^ (5 * (j / 4)) * piHalfScale j ^ 3 :=
    mul_le_mul hn h1 (Real.rpow_nonneg hs0.le _) (mul_nonneg hA (by positivity))
  refine h2.trans ?_
  have hb : 3 * (j + 2) = 5 * (j / 4) + (3 * (j + 2) - 5 * (j / 4)) := by omega
  have hj : j ≤ 3 * (j + 2) - 5 * (j / 4) := by omega
  have h3 : ((1 / 2 : ℝ) ^ (j + 2)) ^ 3 = (1 / 2 : ℝ) ^ (5 * (j / 4)) *
      (1 / 2 : ℝ) ^ (3 * (j + 2) - 5 * (j / 4)) := by
    rw [← pow_mul, mul_comm (j + 2) 3, ← pow_add, ← hb]
  have h4 : (2 : ℝ) ^ (5 * (j / 4)) * (1 / 2 : ℝ) ^ (5 * (j / 4)) = 1 := by
    rw [← mul_pow]; norm_num
  have h5 : (1 / 2 : ℝ) ^ (3 * (j + 2) - 5 * (j / 4)) ≤ (1 / 2 : ℝ) ^ j :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
  unfold piHalfScale
  rw [h3, ← mul_assoc, mul_assoc A, mul_assoc A, h4, one_mul]
  exact mul_le_mul_of_nonneg_left h5 hA

/-- Moment of a rescaled remainder. -/
theorem lintegral_rescaled_pow_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {R : Ω → ℝ≥0∞} {s e κ' K C : ℝ} (hs : 0 < s) (hK : 0 ≤ K) (hC : 0 ≤ C) (q : ℕ)
    (h : ∫⁻ ω, R ω ^ q ∂P ≤ ENNReal.ofReal (K * C * s ^ (e + κ')) ^ q) :
    ∫⁻ ω, (R ω * ENNReal.ofReal (s ^ (-e))) ^ q ∂P ≤
      ENNReal.ofReal ((K * C) ^ q * s ^ (κ' * q)) := by
  simp only [mul_pow]
  rw [lintegral_mul_const' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  refine (mul_le_mul' h le_rfl).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (Real.rpow_nonneg hs.le _),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have e1 : (s ^ (e + κ')) ^ q = s ^ ((e + κ') * q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
  have e2 : (s ^ (-e)) ^ q = s ^ (-e * q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
  rw [mul_pow, e1, e2, mul_assoc, ← Real.rpow_add hs]
  have : (e + κ') * (q : ℝ) + -e * q = κ' * q := by ring
  rw [this, mul_pow]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
/-- The supremum over levels, symbols and cells of the rescaled random remainders. -/
@[expose] noncomputable def piHalfRandomSup (𝒯 : RegularityStructure ι) (γ : ℝ) (Dπ : Set ι)
    (n : ℕ → ℕ) {Ω : Type*} (R : ℕ → ι → ℕ → Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ⨆ x : (Σ j : ℕ, ι × Fin (n j)),
    if x.2.1 ∉ Dπ ∧ 𝒯.deg x.2.1 < γ then
      R x.1 x.2.1 x.2.2 ω *
        ENNReal.ofReal (piHalfScale x.1 ^ (-(𝒯.deg x.2.1 / parabolicSemigroup.order)))
    else 0

end RegularityStructures

end
