/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI2Psi2Coupled
public import Phi43.BPHZ.SemigroupTestTreesI2Psi2Single2
public import Phi43.BPHZ.TreeI3Psi2TestedSize

/-!
# Integral bounds for nonnegative functions on `ℝ⁴ × ℝ⁴`, and merging of centred powers

* `I2Psi2DiffIntBd M I`: `M` is integrable on `SpaceTime × SpaceTime` with integral at most `I`;
  it is stable under sums and nonnegative multiples, and dominates an integrand
  (`I2Psi2DiffIntBd.abs_integral_le`).
* `i2Psi2Diff_ind_merge`: `1_S (s₃(p₁) + s₃(p₂)) s_a(e) ≤ 1_S (s_{3+a}(p₁) + s_{3+a}(p₂) +
  2 s_{3+a}(e))` for `a ≥ 0`.
* `i2Psi2Diff_size_swap`: `s(a - b) = s(b - a)`.
-/

@[expose] public section

open MeasureTheory

namespace RegularityStructures

/-- `M` is integrable on `SpaceTime × SpaceTime` with integral at most `I`. -/
def I2Psi2DiffIntBd (M : SpaceTime × SpaceTime → ℝ) (I : ℝ) : Prop :=
  Integrable M (volume : Measure (SpaceTime × SpaceTime)) ∧
    ∫ q, M q ∂(volume : Measure (SpaceTime × SpaceTime)) ≤ I

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem i2Psi2Diff_size_swap (a b : SpaceTime) : torusParabolicSize (a - b) =
    torusParabolicSize (b - a) := by
  refine le_antisymm ?_ ?_
  · have := torusParabolicSize_neg_le_self (b - a)
    rwa [neg_sub] at this
  · have := torusParabolicSize_neg_le_self (a - b)
    rwa [neg_sub] at this

namespace I2Psi2DiffIntBd

variable {M N : SpaceTime × SpaceTime → ℝ} {I J : ℝ}

theorem add (hM : I2Psi2DiffIntBd M I) (hN : I2Psi2DiffIntBd N J) :
    I2Psi2DiffIntBd (fun q => M q + N q) (I + J) :=
  ⟨hM.1.add hN.1, by rw [integral_add hM.1 hN.1]; exact add_le_add hM.2 hN.2⟩

theorem const_mul (hM : I2Psi2DiffIntBd M I) {c : ℝ} (hc : 0 ≤ c) :
    I2Psi2DiffIntBd (fun q => c * M q) (c * I) :=
  ⟨hM.1.const_mul c, by
    rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hM.2 hc⟩

theorem mul_const (hM : I2Psi2DiffIntBd M I) {c : ℝ} (hc : 0 ≤ c) :
    I2Psi2DiffIntBd (fun q => M q * c) (I * c) := by
  have := hM.const_mul hc
  refine ⟨(hM.1.mul_const c), ?_⟩
  rw [integral_mul_const]; exact mul_le_mul_of_nonneg_right hM.2 hc

theorem mono_right (hM : I2Psi2DiffIntBd M I) (h : I ≤ J) : I2Psi2DiffIntBd M J :=
  ⟨hM.1, hM.2.trans h⟩

/-- A function dominated by `c M` is integrable with absolute integral at most `c I`. -/
theorem abs_integral_le (hM : I2Psi2DiffIntBd M I) {f : SpaceTime × SpaceTime → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hf : AEStronglyMeasurable f volume)
    (hle : ∀ᵐ q : SpaceTime × SpaceTime ∂volume, |f q| ≤ c * M q) :
    Integrable f ∧ |∫ q, f q| ≤ c * I := by
  have hI : Integrable f := (hM.1.const_mul c).mono' hf
    (hle.mono fun q hq => by rwa [Real.norm_eq_abs])
  refine ⟨hI, ?_⟩
  have h1 := norm_integral_le_of_norm_le (hM.1.const_mul c) (hle.mono fun q hq => by
    rwa [Real.norm_eq_abs])
  rw [Real.norm_eq_abs, integral_const_mul] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left hM.2 hc)

end I2Psi2DiffIntBd

/-- Merging of the slab-restricted increment weight with a further centred power. -/
theorem i2Psi2Diff_ind_merge (S : Set SpaceTime) {a : ℝ} (ha : 0 ≤ a) {p₁ p₂ e w : SpaceTime}
    (h1 : 0 < torusParabolicSize (p₁ - w)) (h2 : 0 < torusParabolicSize (p₂ - w))
    (h3 : 0 < torusParabolicSize (e - w)) :
    Set.indicator S (fun w => singularPow 3 p₁ w + singularPow 3 p₂ w) w * singularPow a e w ≤
      Set.indicator S (fun w => ∑ i, (![1, 1, 2] : Fin 3 → ℝ) i *
        singularPow (3 + a) (![p₁, p₂, e] i) w) w := by
  by_cases hw : w ∈ S
  · simp only [Set.indicator_of_mem hw, Fin.sum_univ_three]
    have e1 := singularPow_mul_le (a := 3) (b := a) (by norm_num) ha h1 h3
    have e2 := singularPow_mul_le (a := 3) (b := a) (by norm_num) ha h2 h3
    rw [add_mul]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linarith
  · simp [Set.indicator_of_notMem hw]

end RegularityStructures

end
