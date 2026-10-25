/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.BlockEnvelope.Envelope
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Product weights built from brackets

`envelopeWeight s m₀ m z = (s^{-1/2} (1 + |z₀|/s^{1/2})^{-m₀}) ∏ᵢ (s^{-1/4} (1 + |zᵢ|/s^{1/4})^{-mᵢ})`
is integrable with integral `c(m₀) ∏ᵢ c(mᵢ)` as soon as all exponents exceed `1`, where
`c(m) = ∫ (1 + |u|)^{-m} du`. The block envelope is `envelopeWeight s n (fun _ => n)`, and
`E^n_s(z) |z₀|^{p₀} ∏ |zᵢ|^{pᵢ}` is dominated by `s^{p₀/2 + ∑ pᵢ/4}` times `envelopeWeight` with
lowered exponents.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The constant `c(m) = ∫ (1 + |u|)^{-m} du`. -/
def bracketConst (m : ℝ) : ℝ := ∫ u, blockBracket m 1 u

/-- The product weight of brackets of exponents `m₀`, `m i` at the scales `s^{1/2}`, `s^{1/4}`,
normalised by `s^{-1/2}` and `s^{-1/4}` per factor. -/
def envelopeWeight (s m₀ : ℝ) (m : Fin 3 → ℝ) (z : ParabolicSpace) : ℝ :=
  (s ^ (-(1 / 2 : ℝ)) * blockBracket m₀ (s ^ (1 / 2 : ℝ)) z.1) *
    ∏ i, (s ^ (-(1 / 4 : ℝ)) * blockBracket (m i) (s ^ (1 / 4 : ℝ)) (z.2 i))

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem blockBracket_scale_eq {m : ℝ} {l : ℝ} (hl : 0 < l) (u : ℝ) :
    blockBracket m l u = blockBracket m 1 (l⁻¹ * u) := by
  unfold blockBracket
  rw [abs_mul, abs_of_pos (inv_pos.2 hl), div_one, div_eq_inv_mul]

theorem integrable_blockBracket_one {m : ℝ} (hm : 1 < m) : Integrable (blockBracket m 1) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := m) (by simpa using hm)
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [blockBracket]

theorem integrable_blockBracket {m : ℝ} (hm : 1 < m) {l : ℝ} (hl : 0 < l) :
    Integrable (blockBracket m l) := by
  have := (integrable_blockBracket_one hm).comp_mul_left' (inv_pos.2 hl).ne'
  exact this.congr (Filter.Eventually.of_forall fun u => (blockBracket_scale_eq hl u).symm)

theorem integral_blockBracket (m : ℝ) {l : ℝ} (hl : 0 < l) :
    ∫ u, blockBracket m l u = l * bracketConst m := by
  simp_rw [blockBracket_scale_eq (m := m) hl]
  rw [Measure.integral_comp_mul_left (blockBracket m 1) l⁻¹, smul_eq_mul, inv_inv,
    abs_of_pos hl]
  rfl

theorem bracketConst_nonneg (m : ℝ) : 0 ≤ bracketConst m :=
  integral_nonneg fun u => blockBracket_nonneg m one_pos u

theorem kernelBlockEnvelope_eq_envelopeWeight (n : ℕ) {s : ℝ} (hs : 0 < s) (z : ParabolicSpace) :
    kernelBlockEnvelope n s z = envelopeWeight s n (fun _ => n) z :=
  kernelBlockEnvelope_eq_prod n hs z

theorem integrable_envelopeWeight {s : ℝ} (hs : 0 < s) {m₀ : ℝ} (h₀ : 1 < m₀) {m : Fin 3 → ℝ}
    (hm : ∀ i, 1 < m i) : Integrable (envelopeWeight s m₀ m) := by
  have h1 : Integrable (fun x : ℝ => s ^ (-(1 / 2 : ℝ)) * blockBracket m₀ (s ^ (1 / 2 : ℝ)) x) :=
    (integrable_blockBracket h₀ (Real.rpow_pos_of_pos hs _)).const_mul _
  have h2 : Integrable (fun y : Fin 3 → ℝ =>
      ∏ i, (s ^ (-(1 / 4 : ℝ)) * blockBracket (m i) (s ^ (1 / 4 : ℝ)) (y i))) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun i b =>
      s ^ (-(1 / 4 : ℝ)) * blockBracket (m i) (s ^ (1 / 4 : ℝ)) b)
      fun i => (integrable_blockBracket (hm i) (Real.rpow_pos_of_pos hs _)).const_mul _
  rw [Measure.volume_eq_prod]
  exact h1.mul_prod h2

theorem integral_envelopeWeight {s : ℝ} (hs : 0 < s) (m₀ : ℝ) (m : Fin 3 → ℝ) :
    ∫ z, envelopeWeight s m₀ m z = bracketConst m₀ * ∏ i, bracketConst (m i) := by
  have hl1 : 0 < s ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
  have hl2 : 0 < s ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hs _
  have e1 : s ^ (-(1 / 2 : ℝ)) * s ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hs]; norm_num
  have e2 : s ^ (-(1 / 4 : ℝ)) * s ^ (1 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add hs]; norm_num
  have h : ∫ z : ParabolicSpace, envelopeWeight s m₀ m z =
      (∫ x, s ^ (-(1 / 2 : ℝ)) * blockBracket m₀ (s ^ (1 / 2 : ℝ)) x) *
        ∫ y : Fin 3 → ℝ, ∏ i, (s ^ (-(1 / 4 : ℝ)) * blockBracket (m i) (s ^ (1 / 4 : ℝ)) (y i)) := by
    rw [Measure.volume_eq_prod]
    exact integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin 3 → ℝ)))
      (fun x => s ^ (-(1 / 2 : ℝ)) * blockBracket m₀ (s ^ (1 / 2 : ℝ)) x)
      (fun y : Fin 3 → ℝ =>
        ∏ i, (s ^ (-(1 / 4 : ℝ)) * blockBracket (m i) (s ^ (1 / 4 : ℝ)) (y i)))
  rw [h, volume_pi, integral_fintype_prod_eq_prod
    (f := fun i b => s ^ (-(1 / 4 : ℝ)) * blockBracket (m i) (s ^ (1 / 4 : ℝ)) b),
    integral_const_mul, integral_blockBracket _ hl1]
  simp only [integral_const_mul, integral_blockBracket _ hl2]
  rw [← mul_assoc, e1, one_mul]
  simp only [← mul_assoc, e2, one_mul]

/-- Pointwise domination of `E^n_s(z) |z₀|^{p₀} ∏ |zᵢ|^{pᵢ}`. -/
theorem envelopeWeight_mul_rpow_le {s : ℝ} (hs : 0 < s) (m₀ : ℝ) (m : Fin 3 → ℝ) {p₀ : ℝ}
    (hp₀ : 0 ≤ p₀) {p : Fin 3 → ℝ} (hp : ∀ i, 0 ≤ p i) (z : ParabolicSpace) :
    envelopeWeight s m₀ m z * (|z.1| ^ p₀ * ∏ i, |z.2 i| ^ p i) ≤
      ((s ^ (1 / 2 : ℝ)) ^ p₀ * ∏ i, (s ^ (1 / 4 : ℝ)) ^ p i) *
        envelopeWeight s (m₀ - p₀) (fun i => m i - p i) z := by
  have hs1 : 0 < s ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hs _
  have hs2 : 0 < s ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hs _
  have hl1 : 0 < s ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
  have hl2 : 0 < s ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hs _
  have f0 : (s ^ (-(1 / 2 : ℝ)) * blockBracket m₀ (s ^ (1 / 2 : ℝ)) z.1) * |z.1| ^ p₀ ≤
      (s ^ (1 / 2 : ℝ)) ^ p₀ * (s ^ (-(1 / 2 : ℝ)) *
        blockBracket (m₀ - p₀) (s ^ (1 / 2 : ℝ)) z.1) := by
    have := mul_le_mul_of_nonneg_left (blockBracket_mul_rpow_le m₀ hl1 hp₀ z.1) hs1.le
    calc _ = s ^ (-(1 / 2 : ℝ)) * (blockBracket m₀ (s ^ (1 / 2 : ℝ)) z.1 * |z.1| ^ p₀) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have fi : ∀ i : Fin 3, (s ^ (-(1 / 4 : ℝ)) * blockBracket (m i) (s ^ (1 / 4 : ℝ)) (z.2 i)) *
      |z.2 i| ^ p i ≤ (s ^ (1 / 4 : ℝ)) ^ p i * (s ^ (-(1 / 4 : ℝ)) *
        blockBracket (m i - p i) (s ^ (1 / 4 : ℝ)) (z.2 i)) := fun i => by
    have := mul_le_mul_of_nonneg_left (blockBracket_mul_rpow_le (m i) hl2 (hp i) (z.2 i)) hs2.le
    calc _ = s ^ (-(1 / 4 : ℝ)) * (blockBracket (m i) (s ^ (1 / 4 : ℝ)) (z.2 i) *
          |z.2 i| ^ p i) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have hb : ∀ (θ m u : ℝ), 0 ≤ blockBracket m (s ^ θ) u := fun θ m u =>
    blockBracket_nonneg m (Real.rpow_pos_of_pos hs θ) u
  have hprod : ∏ i, ((s ^ (-(1 / 4 : ℝ)) * blockBracket (m i) (s ^ (1 / 4 : ℝ)) (z.2 i)) *
      |z.2 i| ^ p i) ≤ ∏ i, ((s ^ (1 / 4 : ℝ)) ^ p i * (s ^ (-(1 / 4 : ℝ)) *
        blockBracket (m i - p i) (s ^ (1 / 4 : ℝ)) (z.2 i))) :=
    Finset.prod_le_prod₀ (fun i _ => mul_nonneg (mul_nonneg hs2.le (hb _ _ _))
      (Real.rpow_nonneg (abs_nonneg _) _)) fun i _ => fi i
  unfold envelopeWeight
  have hL : ((s ^ (-(1 / 2 : ℝ)) * blockBracket m₀ (s ^ (1 / 2 : ℝ)) z.1) *
        (∏ i, (s ^ (-(1 / 4 : ℝ)) * blockBracket (m i) (s ^ (1 / 4 : ℝ)) (z.2 i)))) *
      (|z.1| ^ p₀ * ∏ i, |z.2 i| ^ p i) =
      ((s ^ (-(1 / 2 : ℝ)) * blockBracket m₀ (s ^ (1 / 2 : ℝ)) z.1) * |z.1| ^ p₀) *
        ∏ i, ((s ^ (-(1 / 4 : ℝ)) * blockBracket (m i) (s ^ (1 / 4 : ℝ)) (z.2 i)) *
          |z.2 i| ^ p i) := by
    rw [Finset.prod_mul_distrib (f := fun i => s ^ (-(1 / 4 : ℝ)) *
      blockBracket (m i) (s ^ (1 / 4 : ℝ)) (z.2 i)) (g := fun i => |z.2 i| ^ p i)]
    ring
  have hR : ((s ^ (1 / 2 : ℝ)) ^ p₀ * ∏ i, (s ^ (1 / 4 : ℝ)) ^ p i) *
      ((s ^ (-(1 / 2 : ℝ)) * blockBracket (m₀ - p₀) (s ^ (1 / 2 : ℝ)) z.1) *
        ∏ i, (s ^ (-(1 / 4 : ℝ)) * blockBracket (m i - p i) (s ^ (1 / 4 : ℝ)) (z.2 i))) =
      ((s ^ (1 / 2 : ℝ)) ^ p₀ * (s ^ (-(1 / 2 : ℝ)) *
          blockBracket (m₀ - p₀) (s ^ (1 / 2 : ℝ)) z.1)) *
        ∏ i, ((s ^ (1 / 4 : ℝ)) ^ p i * (s ^ (-(1 / 4 : ℝ)) *
          blockBracket (m i - p i) (s ^ (1 / 4 : ℝ)) (z.2 i))) := by
    rw [Finset.prod_mul_distrib (f := fun i => (s ^ (1 / 4 : ℝ)) ^ p i)]; ring
  beta_reduce
  rw [hL, hR]
  exact mul_le_mul f0 hprod (Finset.prod_nonneg fun i _ => mul_nonneg
      (mul_nonneg hs2.le (hb _ _ _)) (Real.rpow_nonneg (abs_nonneg _) _))
    (mul_nonneg (Real.rpow_nonneg hl1.le _) (mul_nonneg hs1.le (hb _ _ _)))

end RegularityStructures

end
