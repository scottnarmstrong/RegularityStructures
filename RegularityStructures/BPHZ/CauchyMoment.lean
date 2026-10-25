/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.CauchyInProbabilityDyadic

/-!
# First-moment bounds with a rate, and their consequences

`MomentBound P D θ C` says that the distances `D ε ε'` are a.e. measurable with first moment at most
`C * max ε ε' ^ θ` on `(0, 1]²`, and `SizeMoment P S C` that the sizes `S ε` are a.e. measurable with
first moment at most `C`.  Both are closed under sums, and they give convergence in probability
(`tendsto_measure_lt_of_momentBound`), tightness (`exists_measure_lt_le_of_sizeMoment`) and the
dyadic almost-sure statements (`ae_dyadic_of_momentBound`).
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace RegularityStructures

/-- Rate-`θ` first-moment bound for a two-scale family of `ℝ≥0∞`-valued functionals. -/
def MomentBound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : ℝ → ℝ → Ω → ℝ≥0∞)
    (θ C : ℝ) : Prop :=
  ∀ ε ε' : ℝ, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
    AEMeasurable (D ε ε') P ∧ ∫⁻ ω, D ε ε' ω ∂P ≤ ENNReal.ofReal (C * max ε ε' ^ θ)

/-- Uniform first-moment bound for a one-scale family. -/
def SizeMoment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (S : ℝ → Ω → ℝ≥0∞) (C : ℝ) :
    Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → AEMeasurable (S ε) P ∧ ∫⁻ ω, S ε ω ∂P ≤ ENNReal.ofReal C

end RegularityStructures

end

public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem MomentBound.add {D₁ D₂ : ℝ → ℝ → Ω → ℝ≥0∞} {θ₁ θ₂ C₁ C₂ : ℝ} (h₁ : MomentBound P D₁ θ₁ C₁)
    (h₂ : MomentBound P D₂ θ₂ C₂) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    MomentBound P (fun ε ε' ω => D₁ ε ε' ω + D₂ ε ε' ω) (min θ₁ θ₂) (C₁ + C₂) := by
  intro ε ε' h0 h1 h0' h1'
  obtain ⟨m₁, b₁⟩ := h₁ ε ε' h0 h1 h0' h1'
  obtain ⟨m₂, b₂⟩ := h₂ ε ε' h0 h1 h0' h1'
  have hm0 : 0 < max ε ε' := lt_max_of_lt_left h0
  have hm1 : max ε ε' ≤ 1 := max_le h1 h1'
  refine ⟨m₁.add m₂, ?_⟩
  rw [lintegral_add_left' m₁]
  refine (add_le_add b₁ b₂).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e₁ : max ε ε' ^ θ₁ ≤ max ε ε' ^ min θ₁ θ₂ :=
    Real.rpow_le_rpow_of_exponent_ge hm0 hm1 (min_le_left _ _)
  have e₂ : max ε ε' ^ θ₂ ≤ max ε ε' ^ min θ₁ θ₂ :=
    Real.rpow_le_rpow_of_exponent_ge hm0 hm1 (min_le_right _ _)
  nlinarith [mul_le_mul_of_nonneg_left e₁ hC₁, mul_le_mul_of_nonneg_left e₂ hC₂]

theorem SizeMoment.add {S₁ S₂ : ℝ → Ω → ℝ≥0∞} {C₁ C₂ : ℝ} (h₁ : SizeMoment P S₁ C₁)
    (h₂ : SizeMoment P S₂ C₂) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    SizeMoment P (fun ε ω => S₁ ε ω + S₂ ε ω) (C₁ + C₂) := by
  intro ε h0 h1
  obtain ⟨m₁, b₁⟩ := h₁ ε h0 h1
  obtain ⟨m₂, b₂⟩ := h₂ ε h0 h1
  refine ⟨m₁.add m₂, ?_⟩
  rw [lintegral_add_left' m₁, ENNReal.ofReal_add hC₁ hC₂]
  exact add_le_add b₁ b₂

/-- Convergence in probability from a rate-`θ` first-moment bound. -/
theorem tendsto_measure_lt_of_momentBound {D : ℝ → ℝ → Ω → ℝ≥0∞} {θ C : ℝ} (hθ : 0 < θ)
    (hC : 0 ≤ C) (h : MomentBound P D θ C) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun e : ℝ × ℝ => P {ω | ENNReal.ofReal δ < D e.1 e.2 ω})
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine tendsto_measure_lt_cauchy_of_lintegral_rpow_le (D := D) (D' := D) (θ := θ) (p := 1)
    (C := C) hθ one_pos (fun _ _ _ _ _ _ => Filter.EventuallyEq.rfl.le)
    (fun ε ε' h0 h1 h0' h1' => (h ε ε' h0 h1 h0' h1').1) (fun ε ε' h0 h1 h0' h1' => ?_) hδ
  have := (h ε ε' h0 h1 h0' h1').2
  have hm : 0 ≤ max ε ε' := (lt_max_of_lt_left h0).le
  simp only [ENNReal.rpow_one]
  rw [mul_one, ENNReal.ofReal_rpow_of_nonneg hm hθ.le, ← ENNReal.ofReal_mul hC]
  exact this

/-- Tightness from a uniform first-moment bound. -/
theorem exists_measure_lt_le_of_sizeMoment {S : ℝ → Ω → ℝ≥0∞} {C : ℝ} (h : SizeMoment P S C)
    {ϑ : ℝ} (hϑ : 0 < ϑ) :
    ∃ B : ℝ, ∀ ε, 0 < ε → ε ≤ 1 → P {ω | ENNReal.ofReal B < S ε ω} ≤ ENNReal.ofReal ϑ :=
  exists_measure_lt_le_of_lintegral_rpow_le (S := S) (S' := S) (p := 1) (C := C) one_pos
    (fun _ _ _ => Filter.EventuallyEq.rfl.le) (fun ε h0 h1 => (h ε h0 h1).1)
    (fun ε h0 h1 => by simpa using (h ε h0 h1).2) hϑ

private theorem max_inv_two_pow (n m : ℕ) :
    max ((2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ m) = (2⁻¹ : ℝ) ^ (min n m) := by
  rcases le_total n m with h | h
  · rw [min_eq_left h, max_eq_left]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  · rw [min_eq_right h, max_eq_right]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h

/-- **Dyadic almost-sure Cauchy property and boundedness from first-moment bounds.** -/
theorem ae_dyadic_of_momentBound {D : ℝ → ℝ → Ω → ℝ≥0∞} {S : ℝ → Ω → ℝ≥0∞} {θ C Cs : ℝ}
    (hθ : 0 < θ) (hC : 0 ≤ C) (hD : MomentBound P D θ C)
    (hS : SizeMoment P S Cs)
    (hsymm : ∀ᵐ ω ∂P, ∀ n m : ℕ,
      D ((2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ m) ω = D ((2⁻¹ : ℝ) ^ m) ((2⁻¹ : ℝ) ^ n) ω)
    (hdiag : ∀ᵐ ω ∂P, ∀ n : ℕ, D ((2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ n) ω = 0)
    (htri : ∀ᵐ ω ∂P, ∀ n k m : ℕ, D ((2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ m) ω ≤
      D ((2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ k) ω + D ((2⁻¹ : ℝ) ^ k) ((2⁻¹ : ℝ) ^ m) ω)
    (hSD : ∀ᵐ ω ∂P, ∀ n : ℕ, S ((2⁻¹ : ℝ) ^ n) ω ≤
      S ((2⁻¹ : ℝ) ^ 0) ω + D ((2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ 0) ω) :
    ∀ᵐ ω ∂P,
      (∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀,
        D ((2⁻¹ : ℝ) ^ n) ((2⁻¹ : ℝ) ^ m) ω ≤ ENNReal.ofReal δ) ∧
      ∃ B : ℝ, ∀ n : ℕ, S ((2⁻¹ : ℝ) ^ n) ω ≤ ENNReal.ofReal B := by
  have hpos : ∀ n : ℕ, 0 < (2⁻¹ : ℝ) ^ n := fun n => by positivity
  have hle : ∀ n : ℕ, (2⁻¹ : ℝ) ^ n ≤ 1 := fun n => pow_le_one₀ (by norm_num) (by norm_num)
  refine ae_cauchy_and_bounded_of_dyadic_lintegral_rpow_le (D := D) (D' := D) (S := S)
    (S' := fun n => S ((2⁻¹ : ℝ) ^ n)) (θ := θ) (p := 1) (C := max C Cs) hθ one_pos
    (le_max_of_le_left hC) (fun _ _ => Filter.EventuallyEq.rfl.le)
    (fun n m => (hD _ _ (hpos n) (hle n) (hpos m) (hle m)).1) (fun n m => ?_)
    (fun _ => Filter.EventuallyEq.rfl.le) (fun n => (hS _ (hpos n) (hle n)).1) (fun n => ?_)
    hsymm hdiag htri hSD
  · have := (hD _ _ (hpos n) (hle n) (hpos m) (hle m)).2
    rw [max_inv_two_pow] at this
    have e : ((2⁻¹ : ℝ) ^ (min n m)) ^ θ = (2⁻¹ : ℝ) ^ (θ * 1 * ((min n m : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast (2⁻¹ : ℝ) (min n m), ← Real.rpow_mul (by norm_num)]
      congr 1; ring
    rw [e] at this
    simp only [ENNReal.rpow_one]
    refine this.trans ?_
    rw [ENNReal.ofReal_mul hC]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _
  · simpa using ((hS _ (hpos n) (hle n)).2.trans
      (ENNReal.ofReal_le_ofReal (le_max_right C Cs)))

end RegularityStructures
