/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.BlockEnvelope.Weight

/-!
# Moments of the block envelope

For `a ≥ 0` and `a + 1 < n`, `E^n_s(z) ‖z‖_𝔰^a` is integrable with integral `≤ M s^{a/4}`.
The threshold `a + 1 < n` is sharp: integrability of the spatial factors needs `n - a > 1`.
The proof bounds `‖z‖^a ≤ 4^a (|z₀|^{a/2} + ∑ₖ |zₖ|^a)` (`parabolicNorm_rpow_le`) and dominates
each of the four terms by `s^{a/4}` times a `envelopeWeight` with lowered exponents.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The weight with lowered exponents for the time moment `|z₀|^{a/2}`. -/
def blockTimeTerm (n : ℕ) (a s : ℝ) : ParabolicSpace → ℝ :=
  envelopeWeight s ((n : ℝ) - a / 2) (fun i => (n : ℝ) - (0 : Fin 3 → ℝ) i)

/-- The weight with lowered exponents for the space moment `|zₖ|^a`. -/
def blockSpaceTerm (n : ℕ) (a s : ℝ) (k : Fin 3) : ParabolicSpace → ℝ :=
  envelopeWeight s ((n : ℝ) - 0) (fun i => (n : ℝ) - (Pi.single k a : Fin 3 → ℝ) i)

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem measurable_blockBracket (m l : ℝ) : Measurable (blockBracket m l) := by
  unfold blockBracket
  fun_prop

theorem measurable_envelopeWeight (s m₀ : ℝ) (m : Fin 3 → ℝ) : Measurable (envelopeWeight s m₀ m) := by
  unfold envelopeWeight
  refine Measurable.mul (((measurable_blockBracket _ _).comp measurable_fst).const_mul _)
    (Finset.measurable_prod _ fun i _ => ?_)
  exact ((measurable_blockBracket _ _).comp ((measurable_pi_apply i).comp measurable_snd)).const_mul _

theorem one_lt_sub_single {n a : ℝ} (ha : 0 ≤ a) (hn : a + 1 < n) (k i : Fin 3) :
    1 < n - (Pi.single k a : Fin 3 → ℝ) i := by
  rw [Pi.single_apply]
  split_ifs <;> linarith

theorem integrable_blockTimeTerm {n : ℕ} {a : ℝ} (ha : 0 ≤ a) (hn : a + 1 < n) {s : ℝ}
    (hs : 0 < s) : Integrable (blockTimeTerm n a s) :=
  integrable_envelopeWeight hs (by linarith) fun i => by rw [Pi.zero_apply, sub_zero]; linarith

theorem integrable_blockSpaceTerm {n : ℕ} {a : ℝ} (ha : 0 ≤ a) (hn : a + 1 < n) {s : ℝ}
    (hs : 0 < s) (k : Fin 3) : Integrable (blockSpaceTerm n a s k) :=
  integrable_envelopeWeight hs (by rw [sub_zero]; linarith) (one_lt_sub_single ha hn k)

theorem integral_blockTimeTerm {s : ℝ} (hs : 0 < s) (n : ℕ) (a : ℝ) :
    ∫ z, blockTimeTerm n a s z =
      bracketConst ((n : ℝ) - a / 2) * ∏ i, bracketConst ((n : ℝ) - (0 : Fin 3 → ℝ) i) :=
  integral_envelopeWeight hs _ _

theorem integral_blockSpaceTerm {s : ℝ} (hs : 0 < s) (n : ℕ) (a : ℝ) (k : Fin 3) :
    ∫ z, blockSpaceTerm n a s k z =
      bracketConst ((n : ℝ) - 0) * ∏ i, bracketConst ((n : ℝ) - (Pi.single k a : Fin 3 → ℝ) i) :=
  integral_envelopeWeight hs _ _

/-- The four-term pointwise domination of `E^n_s(z) ‖z‖^a`. -/
theorem kernelBlockEnvelope_mul_norm_le (n : ℕ) {a : ℝ} (ha : 0 ≤ a) {s : ℝ} (hs : 0 < s)
    (z : ParabolicSpace) :
    kernelBlockEnvelope n s z * parabolicNorm z ^ a ≤
      (4 : ℝ) ^ a * (s ^ (a / 4) * (blockTimeTerm n a s z + ∑ k, blockSpaceTerm n a s k z)) := by
  have hE := kernelBlockEnvelope_nonneg n hs z
  have hEw := kernelBlockEnvelope_eq_envelopeWeight n hs z
  have hpf : ∀ θ : ℝ, 0 ≤ θ → (s ^ (1 / 4 : ℝ)) ^ θ = s ^ (θ / 4) := fun θ _ => by
    rw [← Real.rpow_mul hs.le]; congr 1; ring
  -- time term
  have t0 : kernelBlockEnvelope n s z * |z.1| ^ (a / 2) ≤ s ^ (a / 4) * blockTimeTerm n a s z := by
    have h := envelopeWeight_mul_rpow_le hs (n : ℝ) (fun _ => (n : ℝ)) (p₀ := a / 2) (by positivity)
      (p := 0) (fun i => le_rfl) z
    simp only [Pi.zero_apply, Real.rpow_zero, Finset.prod_const_one, mul_one] at h
    rw [hEw]
    refine h.trans (le_of_eq ?_)
    have : (s ^ (1 / 2 : ℝ)) ^ (a / 2) = s ^ (a / 4) := by
      rw [← Real.rpow_mul hs.le]; congr 1; ring
    rw [this, blockTimeTerm]
    simp
  have t1 : ∀ k : Fin 3, kernelBlockEnvelope n s z * |z.2 k| ^ a ≤
      s ^ (a / 4) * blockSpaceTerm n a s k z := fun k => by
    have h := envelopeWeight_mul_rpow_le hs (n : ℝ) (fun _ => (n : ℝ)) (p₀ := 0) le_rfl
      (p := Pi.single k a) (fun i => by rw [Pi.single_apply]; split_ifs <;> simp [ha]) z
    have e1 : ∏ i, |z.2 i| ^ (Pi.single k a : Fin 3 → ℝ) i = |z.2 k| ^ a := by
      rw [Finset.prod_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
      simp
    have e2 : ∏ i, (s ^ (1 / 4 : ℝ)) ^ (Pi.single k a : Fin 3 → ℝ) i = s ^ (a / 4) := by
      rw [Finset.prod_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
      simp only [Pi.single_eq_same]
      exact hpf a ha
    rw [e1, e2] at h
    rw [hEw]
    simpa [blockSpaceTerm] using h
  have hn := parabolicNorm_rpow_le z ha
  have hsum : ∑ k, kernelBlockEnvelope n s z * |z.2 k| ^ a ≤
      ∑ k, s ^ (a / 4) * blockSpaceTerm n a s k z := Finset.sum_le_sum fun k _ => t1 k
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have h3 : ∑ k : Fin 3, |z.2 k| ^ a = |z.2 0| ^ a + |z.2 1| ^ a + |z.2 2| ^ a := by
    rw [Fin.sum_univ_three]
  calc kernelBlockEnvelope n s z * parabolicNorm z ^ a
      ≤ kernelBlockEnvelope n s z * ((4 : ℝ) ^ a *
        (|z.1| ^ (a / 2) + ∑ k : Fin 3, |z.2 k| ^ a)) := by
        refine mul_le_mul_of_nonneg_left (hn.trans (le_of_eq ?_)) hE
        rw [h3]; ring
    _ = (4 : ℝ) ^ a * (kernelBlockEnvelope n s z * |z.1| ^ (a / 2) +
        kernelBlockEnvelope n s z * ∑ k : Fin 3, |z.2 k| ^ a) := by ring
    _ ≤ (4 : ℝ) ^ a * (s ^ (a / 4) * blockTimeTerm n a s z +
        s ^ (a / 4) * ∑ k, blockSpaceTerm n a s k z) := by
        refine mul_le_mul_of_nonneg_left (add_le_add t0 ?_) (Real.rpow_nonneg (by norm_num) _)
        exact hsum
    _ = _ := by ring

theorem integrable_kernelBlockEnvelope_mul_rpow {n : ℕ} {a : ℝ} (ha : 0 ≤ a) (hn : a + 1 < n)
    {s : ℝ} (hs : 0 < s) :
    Integrable (fun z => kernelBlockEnvelope n s z * parabolicNorm z ^ a) := by
  have hI : Integrable (fun z => (4 : ℝ) ^ a * (s ^ (a / 4) *
      (blockTimeTerm n a s z + ∑ k, blockSpaceTerm n a s k z))) :=
    (((integrable_blockTimeTerm ha hn hs).add (integrable_finsetSum _ fun k _ =>
      integrable_blockSpaceTerm ha hn hs k)).const_mul _).const_mul _
  refine hI.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · have hm : Measurable (kernelBlockEnvelope n s) := by
      have : kernelBlockEnvelope n s = envelopeWeight s n (fun _ => n) :=
        funext (kernelBlockEnvelope_eq_envelopeWeight n hs)
      rw [this]
      exact measurable_envelopeWeight _ _ _
    exact (hm.mul (continuous_parabolicNorm.measurable.pow_const a)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (kernelBlockEnvelope_nonneg n hs z)
      (Real.rpow_nonneg (parabolicNorm_nonneg z) a))]
    exact kernelBlockEnvelope_mul_norm_le n ha hs z

theorem exists_integral_kernelBlockEnvelope_mul_rpow_le {n : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (hn : a + 1 < n) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, 0 < s →
      ∫ z, kernelBlockEnvelope n s z * parabolicNorm z ^ a ≤ M * s ^ (a / 4) := by
  set M : ℝ := (4 : ℝ) ^ a * (bracketConst ((n : ℝ) - a / 2) *
      ∏ i, bracketConst ((n : ℝ) - (0 : Fin 3 → ℝ) i) +
    ∑ k : Fin 3, bracketConst ((n : ℝ) - 0) *
      ∏ i, bracketConst ((n : ℝ) - (Pi.single k a : Fin 3 → ℝ) i)) with hM
  refine ⟨M, ?_, fun s hs => ?_⟩
  · rw [hM]
    refine mul_nonneg (Real.rpow_nonneg (by norm_num) _) (add_nonneg
      (mul_nonneg (bracketConst_nonneg _) (Finset.prod_nonneg fun i _ => bracketConst_nonneg _))
      (Finset.sum_nonneg fun k _ => mul_nonneg (bracketConst_nonneg _)
        (Finset.prod_nonneg fun i _ => bracketConst_nonneg _)))
  · have hint := integrable_kernelBlockEnvelope_mul_rpow ha hn hs
    have hI0 : Integrable (fun z => blockTimeTerm n a s z + ∑ k, blockSpaceTerm n a s k z) :=
      (integrable_blockTimeTerm ha hn hs).add (integrable_finsetSum _ fun k _ =>
        integrable_blockSpaceTerm ha hn hs k)
    have hI : Integrable (fun z => (4 : ℝ) ^ a * (s ^ (a / 4) *
        (blockTimeTerm n a s z + ∑ k, blockSpaceTerm n a s k z))) :=
      (hI0.const_mul _).const_mul _
    calc ∫ z, kernelBlockEnvelope n s z * parabolicNorm z ^ a
        ≤ ∫ z, (4 : ℝ) ^ a * (s ^ (a / 4) *
          (blockTimeTerm n a s z + ∑ k, blockSpaceTerm n a s k z)) :=
          integral_mono hint hI fun z => kernelBlockEnvelope_mul_norm_le n ha hs z
      _ = M * s ^ (a / 4) := by
          rw [integral_const_mul, integral_const_mul, integral_add (integrable_blockTimeTerm ha hn hs)
            (integrable_finsetSum _ fun k _ => integrable_blockSpaceTerm ha hn hs k),
            integral_finsetSum _ fun k _ => integrable_blockSpaceTerm ha hn hs k,
            integral_blockTimeTerm hs]
          simp only [integral_blockSpaceTerm hs, hM]
          ring

end RegularityStructures

end
