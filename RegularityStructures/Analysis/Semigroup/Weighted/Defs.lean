/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Basic

/-!
# Weights, weighted germs and weighted coherence

Weighted germs and weighted coherence, following [Hos25, Definitions 2.1, 3.2, 3.5] with `p = ∞`. We
write the weight as a growth function `ρ = 1 / w ≥ 1`; polynomial moderateness
`ρ z ≤ ρ y (1 + d(z, y))^p` replaces the condition `w(x + y) ≤ w*(x) w(y)`. Stationary random models
have `sup_x |(Q_t Π_x τ)(x)| = ∞` but are bounded by `ρ(x) t^{deg/ℓ}` for a polynomial `ρ`, which is
why the reconstruction must allow growth.

* `IsModerateWeight ρ p`: `ρ ≥ 1` measurable, `ρ z ≤ ρ y (1 + d(z, y))^p`;
* `IsWeightedGerm F ρ`, `IsWeightedCoherent F ρ γ A C`: weighted versions of `IsGerm`,
  `IsCoherent` (the case `ρ = 1`, `p = 0` is the unweighted one);
* `weightConst`, `weightedCoherenceConst`, `weightedReconstructionConst`: explicit constants;
* `IsModerateWeight.le_mul`: `ρ z ≤ ρ y 2^p (1 + d(z, y)^p)`, the form used with the moments.

Source: [Hos25] = arXiv:2310.07396v2, Theorem 4.1.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

/-- A polynomially moderate weight: `ρ ≥ 1` measurable, `ρ z ≤ ρ y * (1 + d(z, y))^p`. -/
structure IsModerateWeight (ρ : E → ℝ) (p : ℝ) : Prop where
  one_le : ∀ x, 1 ≤ ρ x
  measurable : Measurable ρ
  nonneg_exp : 0 ≤ p
  le : ∀ y z, ρ z ≤ ρ y * (1 + K.scaleDist z y) ^ p

/-- The weighted operator constant `2^p (M₀ + M_p τ^{p/ℓ})`:
`∫ |Q_τ(x, y)| ρ(y) dy ≤ ρ(x) · weightConst p τ`. -/
def weightConst (p τ : ℝ) : ℝ :=
  (2 : ℝ) ^ p * (K.momentConst 0 + K.momentConst p * τ ^ (p / K.order))

end RegularityStructures.RegularisingSemigroup

end

public section

open MeasureTheory Filter Set

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

theorem one_add_rpow_le {d p : ℝ} (hd : 0 ≤ d) (hp : 0 ≤ p) :
    (1 + d) ^ p ≤ (2 : ℝ) ^ p * (1 + d ^ p) := by
  have hdp : 0 ≤ d ^ p := Real.rpow_nonneg hd p
  have h2p : 0 ≤ (2 : ℝ) ^ p := Real.rpow_nonneg (by norm_num) p
  rcases le_total d 1 with h | h
  · calc (1 + d) ^ p ≤ (2 : ℝ) ^ p := Real.rpow_le_rpow (by linarith) (by linarith) hp
      _ ≤ (2 : ℝ) ^ p * (1 + d ^ p) := le_mul_of_one_le_right h2p (by linarith)
  · calc (1 + d) ^ p ≤ (2 * d) ^ p := Real.rpow_le_rpow (by linarith) (by linarith) hp
      _ = (2 : ℝ) ^ p * d ^ p := Real.mul_rpow (by norm_num) hd
      _ ≤ (2 : ℝ) ^ p * (1 + d ^ p) := mul_le_mul_of_nonneg_left (by linarith) h2p

variable {K}

theorem IsModerateWeight.le_mul {ρ : E → ℝ} {p : ℝ} (hρ : K.IsModerateWeight ρ p) (y z : E) :
    ρ z ≤ ρ y * ((2 : ℝ) ^ p * (1 + K.scaleDist z y ^ p)) :=
  (hρ.le y z).trans (mul_le_mul_of_nonneg_left
    (one_add_rpow_le (K.scaleDist_nonneg z y) hρ.nonneg_exp)
    (zero_le_one.trans (hρ.one_le y)))

theorem IsModerateWeight.pos {ρ : E → ℝ} {p : ℝ} (hρ : K.IsModerateWeight ρ p) (x : E) :
    0 < ρ x :=
  zero_lt_one.trans_le (hρ.one_le x)

theorem isModerateWeight_one : K.IsModerateWeight (fun _ => (1 : ℝ)) 0 where
  one_le _ := le_rfl
  measurable := measurable_const
  nonneg_exp := le_rfl
  le _ _ := by simp

variable (K)

theorem weightConst_mono {p a b : ℝ} (hp : 0 ≤ p) (ha : 0 ≤ a) (hab : a ≤ b) :
    K.weightConst p a ≤ K.weightConst p b := by
  unfold weightConst
  have h := Real.rpow_le_rpow ha hab (div_nonneg hp K.order_pos.le)
  have := K.momentConst_nonneg p
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ p := Real.rpow_nonneg (by norm_num) _
  exact mul_le_mul_of_nonneg_left (by gcongr) h2

end RegularityStructures.RegularisingSemigroup

end
