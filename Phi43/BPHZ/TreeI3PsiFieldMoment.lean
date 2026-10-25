/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianWickBlocksFour
public import RegularityStructures.BPHZ.GaussianWickMonomialSpecial
public import RegularityStructures.Probability.Isserlis

/-!
# Moment bounds for `:X_a³: X_b :X_c³: X_d` on a Gaussian vector

For a centred Gaussian vector `X` with covariance `C` whose diagonal is bounded by `D`, every
entry satisfies `|C i j| ≤ D`, the product `:X_a³: X_b :X_c³: X_d` is integrable, and
`E|:X_a³: X_b :X_c³: X_d| ≤ 42 D⁴`.  Integrability and the bound come from
`|p q| ≤ (p² + q²) / 2` together with the block formula `integral_wick_three_mul_X_mul_wick_three_mul_X`
at `(a, b, a, b)`.
-/

public section

open MeasureTheory

namespace RegularityStructures

namespace IsCentredGaussianVector

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ}
  {C : Fin n → Fin n → ℝ}

/-- The entries of the covariance of a Gaussian vector are bounded by a bound on its diagonal. -/
theorem abs_apply_le_of_diag_le (h : IsCentredGaussianVector P X C) {D : ℝ}
    (hD : ∀ i, C i i ≤ D) (i j : Fin n) : |C i j| ≤ D := by
  have := h.isProbabilityMeasure
  have hij := h.integrable_mul i j
  have hii := h.integrable_mul i i
  have hjj := h.integrable_mul j j
  have hmaj : Integrable (fun ω => (X ω i * X ω i + X ω j * X ω j) / 2) P :=
    (hii.add hjj).div_const 2
  have hint : ∫ ω, (X ω i * X ω i + X ω j * X ω j) / 2 ∂P = (C i i + C j j) / 2 := by
    rw [integral_div, integral_add hii hjj, h.integral_mul, h.integral_mul]
  have h1 : C i j ≤ (C i i + C j j) / 2 := by
    rw [← hint, ← h.integral_mul i j]
    exact integral_mono hij hmaj fun ω => by nlinarith [sq_nonneg (X ω i - X ω j)]
  have h2 : -C i j ≤ (C i i + C j j) / 2 := by
    rw [← hint, ← h.integral_mul i j, ← integral_neg]
    exact integral_mono hij.neg hmaj fun ω => by
      nlinarith [sq_nonneg (X ω i + X ω j)]
  rw [abs_le]
  constructor <;> linarith [hD i, hD j]

/-- Each coordinate is a.e. measurable. -/
theorem aemeasurable_apply (h : IsCentredGaussianVector P X C) (i : Fin n) :
    AEMeasurable (fun ω => X ω i) P :=
  (measurable_pi_apply i).comp_aemeasurable h.1

/-- The product of two polynomial blocks `(X_a³ - 3 s X_a) X_b` is integrable, as is its square. -/
theorem integrable_cube_pair (h : IsCentredGaussianVector P X C) (s t : ℝ) (a b c d : Fin n) :
    Integrable (fun ω => ((X ω a ^ 3 - 3 * s * X ω a) * X ω b) *
      ((X ω c ^ 3 - 3 * t * X ω c) * X ω d)) P := by
  have := h.isProbabilityMeasure
  have hsq : ∀ (s : ℝ) (a b : Fin n),
      Integrable (fun ω => ((X ω a ^ 3 - 3 * s * X ω a) * X ω b) ^ 2) P := by
    intro s a b
    have e : (fun ω => ((X ω a ^ 3 - 3 * s * X ω a) * X ω b) ^ 2) =
        fun ω => X ω a ^ 6 * X ω b ^ 2 - (6 * s) * (X ω a ^ 4 * X ω b ^ 2) +
          (9 * s ^ 2) * (X ω a ^ 2 * X ω b ^ 2) := by
      funext ω
      ring
    rw [e]
    exact ((h.integrable_pow_mul_pow a b 6 2).sub
      ((h.integrable_pow_mul_pow a b 4 2).const_mul _)).add
      ((h.integrable_pow_mul_pow a b 2 2).const_mul _)
  have hmaj := ((hsq s a b).add (hsq t c d)).div_const 2
  refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · have ha := h.aemeasurable_apply a
    have hb := h.aemeasurable_apply b
    have hc := h.aemeasurable_apply c
    have hd := h.aemeasurable_apply d
    exact ((((ha.pow_const 3).sub (ha.const_mul _)).mul hb).mul
      (((hc.pow_const 3).sub (hc.const_mul _)).mul hd)).aestronglyMeasurable
  · simp only [Pi.add_apply, Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg ((X ω a ^ 3 - 3 * s * X ω a) * X ω b -
      (X ω c ^ 3 - 3 * t * X ω c) * X ω d), sq_nonneg ((X ω a ^ 3 - 3 * s * X ω a) * X ω b +
      (X ω c ^ 3 - 3 * t * X ω c) * X ω d)]

/-- The second moment of `:X_a³: X_b` is at most `42 D⁴`. -/
theorem integral_wick_three_mul_X_sq_le (h : IsCentredGaussianVector P X C) {D : ℝ}
    (hD : ∀ i, C i i ≤ D) (a b : Fin n) :
    ∫ ω, wickMonomial C (List.replicate 3 a) (X ω) * X ω b *
        (wickMonomial C (List.replicate 3 a) (X ω) * X ω b) ∂P ≤ 42 * D ^ 4 := by
  have hf := integral_wick_three_mul_X_mul_wick_three_mul_X h a b a b
  have e : (fun ω => wickMonomial C (List.replicate 3 a) (X ω) * X ω b *
        (wickMonomial C (List.replicate 3 a) (X ω) * X ω b)) =
      fun ω => wickMonomial C (List.replicate 3 a) (X ω) * X ω b *
        wickMonomial C (List.replicate 3 a) (X ω) * X ω b := by
    funext ω
    ring
  rw [e, hf]
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (h.abs_apply_le_of_diag_le hD a a)
  have hab := h.abs_apply_le_of_diag_le hD a b
  have hba := h.abs_apply_le_of_diag_le hD b a
  have haa := h.abs_apply_le_of_diag_le hD a a
  have hbb := h.abs_apply_le_of_diag_le hD b b
  have m4 : ∀ u v w z : ℝ, |u| ≤ D → |v| ≤ D → |w| ≤ D → |z| ≤ D →
      u * v * w * z ≤ D ^ 4 := by
    intro u v w z hu hv hw hz
    have : |u * v * w * z| ≤ D * D * D * D := by
      rw [abs_mul, abs_mul, abs_mul]
      gcongr
    calc u * v * w * z ≤ |u * v * w * z| := le_abs_self _
      _ ≤ D * D * D * D := this
      _ = D ^ 4 := by ring
  have t1 := m4 (C a b) (C a a) (C a a) (C a b) hab haa haa hab
  have t2 := m4 (C a a) (C a a) (C a a) (C b b) haa haa haa hbb
  have t3 := m4 (C a a) (C a a) (C a b) (C b a) haa haa hab hba
  nlinarith [t1, t2, t3]

/-- **Moment bound for `:X_a³: X_b :X_c³: X_d`.** -/
theorem integrable_and_abs_integral_wick_three_le (h : IsCentredGaussianVector P X C) {D : ℝ}
    (hD : ∀ i, C i i ≤ D) (a b c d : Fin n) :
    Integrable (fun ω => wickMonomial C (List.replicate 3 a) (X ω) * X ω b *
        wickMonomial C (List.replicate 3 c) (X ω) * X ω d) P ∧
      ∫ ω, |wickMonomial C (List.replicate 3 a) (X ω) * X ω b *
        wickMonomial C (List.replicate 3 c) (X ω) * X ω d| ∂P ≤ 42 * D ^ 4 := by
  have := h.isProbabilityMeasure
  have hw : ∀ (a : Fin n) (ω : Ω), wickMonomial C (List.replicate 3 a) (X ω) =
      X ω a ^ 3 - 3 * C a a * X ω a := fun a ω => wickMonomial_triple_self C a (X ω)
  have hi : ∀ a b c d : Fin n, Integrable (fun ω =>
      wickMonomial C (List.replicate 3 a) (X ω) * X ω b *
        (wickMonomial C (List.replicate 3 c) (X ω) * X ω d)) P := by
    intro a b c d
    simp only [hw]
    exact h.integrable_cube_pair _ _ a b c d
  have hpq := hi a b c d
  have hpp := hi a b a b
  have hqq := hi c d c d
  have e : ∀ ω, wickMonomial C (List.replicate 3 a) (X ω) * X ω b *
        wickMonomial C (List.replicate 3 c) (X ω) * X ω d =
      wickMonomial C (List.replicate 3 a) (X ω) * X ω b *
        (wickMonomial C (List.replicate 3 c) (X ω) * X ω d) := fun ω => by ring
  simp only [e]
  refine ⟨hpq, ?_⟩
  have hmaj := (hpp.add hqq).div_const 2
  calc ∫ ω, |wickMonomial C (List.replicate 3 a) (X ω) * X ω b *
          (wickMonomial C (List.replicate 3 c) (X ω) * X ω d)| ∂P
      ≤ ∫ ω, (wickMonomial C (List.replicate 3 a) (X ω) * X ω b *
            (wickMonomial C (List.replicate 3 a) (X ω) * X ω b) +
          wickMonomial C (List.replicate 3 c) (X ω) * X ω d *
            (wickMonomial C (List.replicate 3 c) (X ω) * X ω d)) / 2 ∂P := by
        refine integral_mono hpq.abs hmaj fun ω => ?_
        simp only
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg (wickMonomial C (List.replicate 3 a) (X ω) * X ω b -
          wickMonomial C (List.replicate 3 c) (X ω) * X ω d),
          sq_nonneg (wickMonomial C (List.replicate 3 a) (X ω) * X ω b +
          wickMonomial C (List.replicate 3 c) (X ω) * X ω d)]
    _ = (∫ ω, wickMonomial C (List.replicate 3 a) (X ω) * X ω b *
            (wickMonomial C (List.replicate 3 a) (X ω) * X ω b) ∂P +
          ∫ ω, wickMonomial C (List.replicate 3 c) (X ω) * X ω d *
            (wickMonomial C (List.replicate 3 c) (X ω) * X ω d) ∂P) / 2 := by
        rw [integral_div, integral_add hpp hqq]
    _ ≤ (42 * D ^ 4 + 42 * D ^ 4) / 2 := by
        gcongr
        · exact h.integral_wick_three_mul_X_sq_le hD a b
        · exact h.integral_wick_three_mul_X_sq_le hD c d
    _ = 42 * D ^ 4 := by ring

end IsCentredGaussianVector

end RegularityStructures

end
