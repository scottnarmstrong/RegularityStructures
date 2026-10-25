/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Pairing.Moment
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic
public import RegularityStructures.Analysis.Semigroup.Pairing.LocalOrder

/-!
# Standing hypotheses for the pairing

`LocalData`: a `Q`-distribution `Λ` of local order `γ` at `x₀` with exponents `A ≤ γ` and constant
`C ≥ 0`, and the uniform bound on `∫ |Q_v(y, z)| |Λ_s(z)| dz`.
-/

public section

open MeasureTheory

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

/-- The standing hypotheses on a `Q`-distribution `Λ` of local order `γ` at `x₀` with exponents
`A ≤ γ` and constant `C ≥ 0`. -/
structure LocalData (Λ : ℝ → E → ℝ) (x₀ : E) (γ : ℝ) (A : Finset ℝ) (C : ℝ) : Prop where
  mem : Λ ∈ K.distributions
  meas : ∀ u, 0 < u → Measurable (Λ u)
  nonneg : 0 ≤ C
  le : ∀ a ∈ A, a ≤ γ
  loc : K.IsLocalOrder Λ x₀ γ A C

variable {K}

theorem LocalData.abs_le {Λ : ℝ → E → ℝ} {x₀ : E} {γ : ℝ} {A : Finset ℝ} {C : ℝ}
    (hΛ : K.LocalData Λ x₀ γ A C) {u : ℝ} (hu : u ∈ Set.Ioc (0 : ℝ) 1) {y : E} {lam : ℝ}
    (hy : K.scaleDist y x₀ ≤ lam) :
    |Λ u y| ≤ C * ∑ a ∈ A, u ^ (a / K.order) * lam ^ (γ - a) := by
  refine (hΛ.loc u hu y).trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a ha => ?_)
    hΛ.nonneg)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (K.scaleDist_nonneg _ _) hy
    (sub_nonneg.2 (hΛ.le a ha))) (Real.rpow_nonneg hu.1.le _)

/-- Uniform bound for `∫ |Q_v(y, z)| |Λ_s(z)| dz`, `v ≤ h₀`, `d(y, x₀) ≤ λ`. -/
theorem LocalData.exists_integral_abs_kernel_mul_le (hd : K.IsMetricScale) {Λ : ℝ → E → ℝ}
    {x₀ : E} {γ : ℝ} {A : Finset ℝ} {C : ℝ} (hΛ : K.LocalData Λ x₀ γ A C) {s : ℝ}
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (h₀ lam : ℝ) :
    ∃ W : ℝ, ∀ v ∈ Set.Ioc (0 : ℝ) h₀, ∀ y, K.scaleDist y x₀ ≤ lam →
      ∫ z, |K.kernel v y z| * |Λ s z| ∂μ ≤ W := by
  set c : ℝ → ℝ := fun a => C * s ^ (a / K.order) * 2 ^ (γ - a) with hc
  have hc0 : ∀ a, 0 ≤ c a := fun a => by
    exact mul_nonneg (mul_nonneg hΛ.nonneg (Real.rpow_nonneg hs.1.le _))
      (Real.rpow_nonneg (by norm_num) _)
  refine ⟨∑ a ∈ A, c a * (K.momentConst (γ - a) * h₀ ^ ((γ - a) / K.order) +
    lam ^ (γ - a) * K.momentConst 0), ?_⟩
  intro v hv y hy
  have hv0 : 0 < v := hv.1
  have hpt : ∀ z, |K.kernel v y z| * |Λ s z| ≤ ∑ a ∈ A, (c a * (|K.kernel v y z| *
      K.scaleDist z y ^ (γ - a)) + (c a * K.scaleDist y x₀ ^ (γ - a)) * |K.kernel v y z|) := by
    intro z
    calc |K.kernel v y z| * |Λ s z|
        ≤ |K.kernel v y z| * (C * ∑ a ∈ A, s ^ (a / K.order) * K.scaleDist z x₀ ^ (γ - a)) :=
          mul_le_mul_of_nonneg_left (hΛ.loc s hs z) (abs_nonneg _)
      _ = ∑ a ∈ A, |K.kernel v y z| * (C * (s ^ (a / K.order) * K.scaleDist z x₀ ^ (γ - a))) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun a ha => by
          have hr : 0 ≤ γ - a := sub_nonneg.2 (hΛ.le a ha)
          have h1 : K.scaleDist z x₀ ^ (γ - a) ≤
              2 ^ (γ - a) * (K.scaleDist z y ^ (γ - a) + K.scaleDist y x₀ ^ (γ - a)) :=
            (Real.rpow_le_rpow (K.scaleDist_nonneg _ _) (hd.triangle z y x₀) hr).trans
              (rpow_add_le_mul (K.scaleDist_nonneg _ _) (K.scaleDist_nonneg _ _) hr)
          have h2 : |K.kernel v y z| * (C * (s ^ (a / K.order) * K.scaleDist z x₀ ^ (γ - a))) ≤
              |K.kernel v y z| * (C * (s ^ (a / K.order) *
                (2 ^ (γ - a) * (K.scaleDist z y ^ (γ - a) + K.scaleDist y x₀ ^ (γ - a))))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hs.1.le _)) hΛ.nonneg)
              (abs_nonneg _)
          refine h2.trans (le_of_eq ?_)
          simp only [hc]; ring
  have hf : Integrable (fun z => |K.kernel v y z|) μ := (K.integrable_kernel hv0 y).abs
  have hg : ∀ a ∈ A, Integrable (fun z => |K.kernel v y z| * K.scaleDist z y ^ (γ - a)) μ :=
    fun a ha => K.integrable_moment hv0 (sub_nonneg.2 (hΛ.le a ha)) y
  have hD : Integrable (fun z => ∑ a ∈ A, (c a * (|K.kernel v y z| *
      K.scaleDist z y ^ (γ - a)) + (c a * K.scaleDist y x₀ ^ (γ - a)) * |K.kernel v y z|)) μ :=
    integrable_finsetSum _ fun a ha => ((hg a ha).const_mul _).add (hf.const_mul _)
  have hle := integral_mono_of_nonneg (Filter.Eventually.of_forall fun z =>
    mul_nonneg (abs_nonneg _) (abs_nonneg _)) hD (Filter.Eventually.of_forall hpt)
  refine hle.trans ?_
  have hint : ∀ a ∈ A, Integrable (fun z => c a * (|K.kernel v y z| *
      K.scaleDist z y ^ (γ - a)) + (c a * K.scaleDist y x₀ ^ (γ - a)) * |K.kernel v y z|) μ :=
    fun a ha => ((hg a ha).const_mul _).add (hf.const_mul _)
  rw [integral_finsetSum _ hint]
  refine Finset.sum_le_sum fun a ha => ?_
  have hr : 0 ≤ γ - a := sub_nonneg.2 (hΛ.le a ha)
  rw [integral_add ((hg a ha).const_mul _) (hf.const_mul _), integral_const_mul,
    integral_const_mul]
  have e1 : ∫ z, |K.kernel v y z| * K.scaleDist z y ^ (γ - a) ∂μ ≤
      K.momentConst (γ - a) * h₀ ^ ((γ - a) / K.order) :=
    (K.moment_le hv0 hr y).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hv0.le hv.2
      (div_nonneg hr K.order_pos.le)) (K.momentConst_nonneg _))
  have e2 : ∫ z, |K.kernel v y z| ∂μ ≤ K.momentConst 0 := K.integral_abs_kernel_le hv0 y
  have e3 : K.scaleDist y x₀ ^ (γ - a) ≤ lam ^ (γ - a) :=
    Real.rpow_le_rpow (K.scaleDist_nonneg _ _) hy hr
  have e4 : 0 ≤ ∫ z, |K.kernel v y z| ∂μ := integral_nonneg fun _ => abs_nonneg _
  have h5 : c a * K.scaleDist y x₀ ^ (γ - a) * ∫ z, |K.kernel v y z| ∂μ ≤
      c a * lam ^ (γ - a) * K.momentConst 0 :=
    mul_le_mul (mul_le_mul_of_nonneg_left e3 (hc0 a)) e2 e4
      (mul_nonneg (hc0 a) ((Real.rpow_nonneg (K.scaleDist_nonneg _ _) _).trans e3))
  have h6 := mul_le_mul_of_nonneg_left e1 (hc0 a)
  linarith [h5, h6]

end RegularityStructures.RegularisingSemigroup

end
