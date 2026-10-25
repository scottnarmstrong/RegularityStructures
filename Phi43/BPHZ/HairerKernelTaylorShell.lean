/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.HairerKernelTaylorBase
import Mathlib.Tactic

/-!
# Spatial gradient kernel and Taylor remainder of the dyadic shells

`hairerKernelGrad N i = ∑ₙ ∂ᵢ (annShellC N n)` is the spatial gradient of `hairerKernel N`
(a locally finite sum away from the origin).  For the `n`-th shell `S_n = (2ⁿ)³ K₀(S^{2ⁿ} ·)`:

* `∂ᵢ S_n = (2ⁿ)⁴ (∂ᵢ K₀)(S^{2ⁿ} ·)`;
* `|S_n (u + h) - S_n u - ∑ᵢ ∂ᵢ S_n u hᵢ| ≤ L (2ⁿ)^(4+θ) ‖h‖^(1+θ)` for `θ ∈ [0, 1]`;
* `|∂ᵢ S_n| ≤ B (2ⁿ)⁴` and `|∂ᵢ S_n (u + h) - ∂ᵢ S_n u| ≤ L (2ⁿ)⁵ ‖h‖`.

We also record the dyadic index `m` (the shells with `n ≥ m` vanish at `u` and `u + h`) and the
geometric sums.
-/

@[expose] public section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The spatial gradient of Hairer's kernel: `∂ᵢ K_N = ∑ₙ ∂ᵢ S_n`. -/
noncomputable def hairerKernelGrad (N : ℕ) (i : Fin 3) (z : ParabolicSpace) : ℝ :=
  ∑' n : ℕ, lineIter [spaceDir i] (annShellC N n) z

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem ksh_dilate_add (c : ℝ) (z h : ParabolicSpace) :
    parabolicDilate c (z + h) = parabolicDilate c z + parabolicDilate c h := by
  simp [parabolicDilate, mul_add, smul_add]

/-- Derivative scaling of the shells. -/
theorem lineIter_spaceDir_annShellC (N n : ℕ) (i : Fin 3) (z : ParabolicSpace) :
    lineIter [spaceDir i] (annShellC N n) z =
      ((2 : ℝ) ^ n) ^ 4 * lineIter [spaceDir i] (annKernel0C N) (parabolicDilate (2 ^ n) z) := by
  have h := lineIter_coordDir_scaledShell (contDiff_annKernel0C N) n [i.succ] z
  have hw : indexWeight [i.succ] = 1 := by
    fin_cases i <;> simp [indexWeight_cons, indexWeight_nil, parabolicWeight]
  have e : annShellC N n = scaledShell (annKernel0C N) n := rfl
  rw [e]
  simpa [coordDir_succ, hw] using h

/-- The profile gradient vanishes outside the unit ball. -/
theorem lineIter_spaceDir_annKernel0C_eq_zero (N : ℕ) (i : Fin 3) {z : ParabolicSpace}
    (hz : 1 < parabolicNorm z) : lineIter [spaceDir i] (annKernel0C N) z = 0 :=
  lineIter_eq_zero_of_lt (fun _ hz => annKernel0C_eq_zero N hz) _ hz

/-- The gradient of the `n`-th shell vanishes where the shell does. -/
theorem lineIter_spaceDir_annShellC_eq_zero (N n : ℕ) (i : Fin 3) {z : ParabolicSpace}
    (hz : (2 : ℝ)⁻¹ ^ n < parabolicNorm z) :
    lineIter [spaceDir i] (annShellC N n) z = 0 := by
  have hc : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  rw [lineIter_spaceDir_annShellC, lineIter_spaceDir_annKernel0C_eq_zero N i, mul_zero]
  rw [parabolicNorm_parabolicDilate hc.le, inv_pow, inv_lt_iff_one_lt_mul₀ hc] at *
  linarith

/-- Uniform bound of the gradient of the base profile. -/
theorem annKernel0C_lineIter_abs_le (N : ℕ) (i : Fin 3) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z, |lineIter [spaceDir i] (annKernel0C N) z| ≤ B :=
  hairerKernelTaylor_exists_abs_le (contDiff_lineIter (contDiff_annKernel0C N) _)
    (fun _ hz => lineIter_spaceDir_annKernel0C_eq_zero N i hz)

/-- Gradient bound of a single shell. -/
theorem annShellC_lineIter_abs_le (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (i : Fin 3) (n : ℕ) (z : ParabolicSpace),
      |lineIter [spaceDir i] (annShellC N n) z| ≤ B * ((2 : ℝ) ^ n) ^ 4 := by
  have hb : ∀ i : Fin 3, ∃ B : ℝ, 0 ≤ B ∧ ∀ z, |lineIter [spaceDir i] (annKernel0C N) z| ≤ B :=
    annKernel0C_lineIter_abs_le N
  choose Bi hBi0 hBi using hb
  refine ⟨∑ i, Bi i, Finset.sum_nonneg fun i _ => hBi0 i, fun i n z => ?_⟩
  rw [lineIter_spaceDir_annShellC, abs_mul, abs_of_nonneg (by positivity)]
  have := (hBi i (parabolicDilate (2 ^ n) z)).trans
    (Finset.single_le_sum (f := Bi) (fun j _ => hBi0 j) (Finset.mem_univ i))
  nlinarith [pow_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n) 4]

/-- Gradient increment of a single shell. -/
theorem annShellC_lineIter_sub_abs_le (N : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (i : Fin 3) (n : ℕ) (z h : ParabolicSpace),
      |lineIter [spaceDir i] (annShellC N n) (z + h) - lineIter [spaceDir i] (annShellC N n) z| ≤
        L * ((2 : ℝ) ^ n) ^ 5 * parabolicNorm h := by
  have hb : ∀ i : Fin 3, ∃ L : ℝ, 0 ≤ L ∧ ∀ w k : ParabolicSpace,
      |lineIter [spaceDir i] (annKernel0C N) (w + k) - lineIter [spaceDir i] (annKernel0C N) w| ≤
        L * parabolicNorm k := fun i =>
    hairerKernelTaylor_abs_sub_le (contDiff_lineIter (contDiff_annKernel0C N) _)
      (fun _ hz => lineIter_spaceDir_annKernel0C_eq_zero N i hz)
  choose Li hLi0 hLi using hb
  refine ⟨∑ i, Li i, Finset.sum_nonneg fun i _ => hLi0 i, fun i n z h => ?_⟩
  have hc : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have h1 := hLi i (parabolicDilate (2 ^ n) z) (parabolicDilate (2 ^ n) h)
  rw [parabolicNorm_parabolicDilate hc.le] at h1
  have hL : Li i ≤ ∑ i, Li i := Finset.single_le_sum (f := Li) (fun j _ => hLi0 j)
    (Finset.mem_univ i)
  rw [lineIter_spaceDir_annShellC, lineIter_spaceDir_annShellC, ← mul_sub, ksh_dilate_add,
    abs_mul, abs_of_nonneg (by positivity)]
  have hs0 := parabolicNorm_nonneg h
  calc ((2 : ℝ) ^ n) ^ 4 * |lineIter [spaceDir i] (annKernel0C N) (parabolicDilate (2 ^ n) z +
          parabolicDilate (2 ^ n) h) - lineIter [spaceDir i] (annKernel0C N)
            (parabolicDilate (2 ^ n) z)|
      ≤ ((2 : ℝ) ^ n) ^ 4 * (Li i * (2 ^ n * parabolicNorm h)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ ((2 : ℝ) ^ n) ^ 4 * ((∑ i, Li i) * (2 ^ n * parabolicNorm h)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hL (by positivity)
    _ = (∑ i, Li i) * ((2 : ℝ) ^ n) ^ 5 * parabolicNorm h := by ring

/-- **Taylor remainder of a single shell**, with the spatial gradient only. -/
theorem annShellC_taylor_abs_le (N : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {θ : ℝ}, 0 ≤ θ → θ ≤ 1 → ∀ (n : ℕ) (u h : ParabolicSpace),
      |annShellC N n (u + h) - annShellC N n u -
          ∑ i : Fin 3, lineIter [spaceDir i] (annShellC N n) u * h.2 i| ≤
        L * ((2 : ℝ) ^ n) ^ (4 + θ) * parabolicNorm h ^ (1 + θ) := by
  obtain ⟨L, hL, hT⟩ := hairerKernelTaylor_remainder_abs_le (contDiff_annKernel0C N)
    (fun _ hz => annKernel0C_eq_zero N hz)
  refine ⟨L, hL, fun {θ} hθ0 hθ1 n u h => ?_⟩
  have hc : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have h1 := hT hθ0 hθ1 (parabolicDilate (2 ^ n) u) (parabolicDilate (2 ^ n) h)
  rw [parabolicNorm_parabolicDilate hc.le] at h1
  have e : annShellC N n (u + h) - annShellC N n u -
      ∑ i : Fin 3, lineIter [spaceDir i] (annShellC N n) u * h.2 i =
      ((2 : ℝ) ^ n) ^ 3 * (annKernel0C N (parabolicDilate (2 ^ n) u + parabolicDilate (2 ^ n) h) -
        annKernel0C N (parabolicDilate (2 ^ n) u) - ∑ i : Fin 3,
          lineIter [spaceDir i] (annKernel0C N) (parabolicDilate (2 ^ n) u) *
            (parabolicDilate (2 ^ n) h).2 i) := by
    simp only [annShellC, scaledShell, ksh_dilate_add, lineIter_spaceDir_annShellC, mul_sub,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [parabolicDilate, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, abs_mul, abs_of_nonneg (by positivity)]
  have hpow : ((2 : ℝ) ^ n) ^ 3 * (2 ^ n) ^ (1 + θ) = ((2 : ℝ) ^ n) ^ (4 + θ) := by
    have h3 : ((2 : ℝ) ^ n) ^ (3 : ℝ) = ((2 : ℝ) ^ n) ^ 3 := by
      exact_mod_cast Real.rpow_natCast ((2 : ℝ) ^ n) 3
    rw [show (4 + θ) = (3 : ℝ) + (1 + θ) by ring, Real.rpow_add hc (3 : ℝ) (1 + θ), h3]
  calc ((2 : ℝ) ^ n) ^ 3 * |annKernel0C N (parabolicDilate (2 ^ n) u + parabolicDilate (2 ^ n) h) -
          annKernel0C N (parabolicDilate (2 ^ n) u) - ∑ i : Fin 3,
          lineIter [spaceDir i] (annKernel0C N) (parabolicDilate (2 ^ n) u) *
            (parabolicDilate (2 ^ n) h).2 i|
      ≤ ((2 : ℝ) ^ n) ^ 3 * (L * (2 ^ n * parabolicNorm h) ^ (1 + θ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = L * (((2 : ℝ) ^ n) ^ 3 * (2 ^ n) ^ (1 + θ)) * parabolicNorm h ^ (1 + θ) := by
        rw [Real.mul_rpow hc.le (parabolicNorm_nonneg h)]
        ring
    _ = L * ((2 : ℝ) ^ n) ^ (4 + θ) * parabolicNorm h ^ (1 + θ) := by rw [hpow]

/-- The dyadic index: `m` with `(1/2)^m < r` and `r ≤ (1/2)^j` for `j < m`. -/
theorem hairerKernelTaylor_exists_index {r : ℝ} (hr : 0 < r) :
    ∃ m : ℕ, (2 : ℝ)⁻¹ ^ m < r ∧ ∀ j < m, r ≤ (2 : ℝ)⁻¹ ^ j := by
  have hex : ∃ m : ℕ, (2 : ℝ)⁻¹ ^ m < r := exists_pow_lt_of_lt_one hr (by norm_num)
  exact ⟨Nat.find hex, Nat.find_spec hex, fun j hj => not_lt.1 (Nat.find_min hex hj)⟩

/-- Geometric sum `∑_{n<m} (2ⁿ)^β ≤ 2 r^{-β}` for `β ≥ 4` and `r ≤ (1/2)^j` for `j < m`. -/
theorem hairerKernelTaylor_geom_sum_le {β r : ℝ} (hβ : 4 ≤ β) (hr : 0 < r) {m : ℕ}
    (hm : ∀ j < m, r ≤ (2 : ℝ)⁻¹ ^ j) :
    ∑ n ∈ Finset.range m, ((2 : ℝ) ^ n) ^ β ≤ 2 * (r ^ β)⁻¹ := by
  set q : ℝ := (2 : ℝ) ^ β with hq
  have hq16 : 16 ≤ q := by
    have : (2 : ℝ) ^ (4 : ℝ) ≤ 2 ^ β := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ
    have e : (2 : ℝ) ^ (4 : ℝ) = 16 := by norm_num
    linarith
  have hpow : ∀ n : ℕ, ((2 : ℝ) ^ n) ^ β = q ^ n := fun n => by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num), mul_comm]
  simp_rw [hpow]
  cases m with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; positivity
  | succ j =>
    have h1 : r ≤ (2 : ℝ)⁻¹ ^ j := hm j (Nat.lt_succ_self j)
    have h2 : (2 : ℝ) ^ j ≤ r⁻¹ := by
      rw [le_inv_comm₀ (by positivity) hr, ← inv_pow]
      exact h1
    have h3 : q ^ j ≤ (r ^ β)⁻¹ := by
      rw [← hpow, ← Real.inv_rpow hr.le]
      exact Real.rpow_le_rpow (by positivity) h2 (by linarith)
    have hgeom : (∑ n ∈ Finset.range (j + 1), q ^ n) * (q - 1) = q ^ (j + 1) - 1 := by
      exact geom_sum_mul q (j + 1)
    have hq1 : 0 < q - 1 := by linarith
    have hS : ∑ n ∈ Finset.range (j + 1), q ^ n ≤ q ^ (j + 1) / (q - 1) := by
      rw [le_div_iff₀ hq1, hgeom]; linarith
    refine hS.trans ?_
    rw [pow_succ, div_le_iff₀ hq1]
    have hqj : 0 ≤ q ^ j := by positivity
    have h4 : q ^ j * q ≤ q ^ j * (2 * (q - 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) hqj
    have h5 : q ^ j * (2 * (q - 1)) ≤ (r ^ β)⁻¹ * (2 * (q - 1)) :=
      mul_le_mul_of_nonneg_right h3 (by linarith)
    linarith

end RegularityStructures.Phi43

end
