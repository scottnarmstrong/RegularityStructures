/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Remainder.TimeTaylorQuant
public import RegularityStructures.Abstract.Singular.Kernel.TimeTaylorScaled
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.WeightedSingularDefs
public import RegularityStructures.Abstract.Singular.Remainder.Kernel

/-!
# The sup bound for `⟨R f, D^k R(x − ·)⟩` with vanishing

Hairer, arXiv:1303.5113v4, Lemma 7.7 (smooth part): for `x ∈ (0, T] × ℝ³`, `T ≤ 1`,

  `|⟨R f, D^k R(x − ·)⟩| ≤ C K₀ Cf w(x)^{α∧η + 2 − |k|_𝔰}`, `w(x) = ‖x‖_P = min 1 |x₀|^{1/2}`

(`exists_abs_remPairing_le_weight`).  If the exponent is positive the bound uses the time-Taylor
remainder at `x̄ = (0, x')` of order `m` with `2m ≥ α∧η + 2 − |k|`: the subtracted terms are
supported in `{y₀ < 0}` where the reconstruction of `f` vanishes (`remSumm_remPairing_eq_of_eq_of_nonneg`).
-/

public section

open scoped ContDiff
open Filter Topology

namespace RegularityStructures

theorem exists_isRemKernel_timeTaylorRem (m : ℕ) :
    ∃ (n : ℕ) (c : ℝ), 0 ≤ c ∧ ∀ {G : ParabolicSpace → ℝ} {B : ℝ}, ContDiff ℝ ∞ G → 0 ≤ B →
      RemDecay G n 7 B → ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
      IsRemKernel (fun u => timeTaylorRem τ m G (u - τ • timeDir)) (c * B * τ ^ m) := by
  obtain ⟨n, c, hc0, hdec⟩ := exists_remDecay_timeTaylorRem m
  refine ⟨n, c, hc0, fun {G B} hG hB hD τ hτ0 hτ1 => ⟨?_, by positivity, fun i hi u hu => ?_⟩⟩
  · exact (contDiff_timeTaylorRem hG τ m).comp (contDiff_id.sub contDiff_const)
  · have e : (fun u => timeTaylorRem τ m G (u - τ • timeDir)) =
        fun u => timeTaylorRem τ m G (u + -(τ • timeDir)) := by
      funext u; rw [sub_eq_add_neg]
    rw [e, iteratedFDeriv_comp_add_right]
    have h1 : (u + -(τ • timeDir)).1 + 4 ≤ 7 := by
      simp only [Prod.fst_add, Prod.fst_neg, Prod.smul_fst, timeDir, smul_eq_mul, mul_one]
      linarith
    have h2 := hdec hG hB hD τ (by rw [abs_of_nonneg hτ0]; exact hτ1) i hi _ h1
    rw [abs_of_nonneg hτ0] at h2
    have h3 : (u + -(τ • timeDir)).2 = u.2 := by simp [timeDir]
    rw [h3] at h2
    exact h2

theorem pow_le_singularWeight_rpow {x : ParabolicSpace} {T : ℝ} (hT : T ≤ 1)
    (hx : x ∈ timeSlab T) (e : ℝ) (m : ℕ) (he : e ≤ 2 * m) :
    x.1 ^ m ≤ singularWeight timeZeroDist x ^ e := by
  obtain ⟨hx0, hxT⟩ := hx
  have hsq : Real.sqrt |x.1| ≤ 1 := by
    rw [abs_of_pos hx0]; exact Real.sqrt_le_one.2 (hxT.trans hT)
  have hw : singularWeight timeZeroDist x = Real.sqrt x.1 := by
    unfold singularWeight timeZeroDist
    rw [abs_of_pos hx0]
    exact min_eq_right (by rwa [abs_of_pos hx0] at hsq)
  rw [hw]
  have hpos : 0 < Real.sqrt x.1 := Real.sqrt_pos.2 hx0
  have hle : Real.sqrt x.1 ≤ 1 := by rwa [abs_of_pos hx0] at hsq
  calc x.1 ^ m = (Real.sqrt x.1) ^ (2 * m) := by
        rw [pow_mul, Real.sq_sqrt hx0.le]
    _ = (Real.sqrt x.1) ^ ((2 * m : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (Real.sqrt x.1) ^ e := by
        refine Real.rpow_le_rpow_of_exponent_ge hpos hle ?_
        push_cast; exact he

end RegularityStructures

end
