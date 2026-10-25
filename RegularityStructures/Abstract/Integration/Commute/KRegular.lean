/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Commute.KConv
public import RegularityStructures.Abstract.Integration.Commute.KConvShell
public import RegularityStructures.Abstract.Polynomial.Model.Growth

/-!
# Regular distributions: measurability and polynomial growth of `K ∗ Λ`

`KRegular Λ x` records that `Λ` is a measurable `Q`-family of local order `α` at `x` with
exponents in `(-2, α]` (the situation of `Π_x e_i` when all homogeneities below `γ` exceed `-2`).
For such `Λ`, `kConv N Λ` is measurable (`KRegular.measurable_kConv`; the pointwise limit of the
parametric integrals `z ↦ ∫ Λ_s(w) K_n(z - w) dw`, as in the measurability of the germ) and has
polynomial growth (`KRegular.polyBounded_kConv`), by `summable_and_abs_kConv_le`.
-/

@[expose] public section

namespace RegularityStructures

/-- `Λ` is a measurable `Q`-family of local order `α` at `x` with exponents in `(-2, α]`. -/
def KRegular (Λ : ℝ → ParabolicSpace → ℝ) (x : ParabolicSpace) : Prop :=
  Λ ∈ parabolicSemigroup.distributions ∧ (∀ u, 0 < u → Measurable (Λ u)) ∧
    ∃ (α C : ℝ) (A : Finset ℝ), (∀ a ∈ A, -2 < a ∧ a ≤ α) ∧ 0 ≤ C ∧
      parabolicSemigroup.IsLocalOrder Λ x α A C

end RegularityStructures

end

public section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace RegularityStructures

namespace KRegular

variable {Λ : ℝ → ParabolicSpace → ℝ} {x : ParabolicSpace}

theorem summable_pairing (hΛ : KRegular Λ x) (N : ℕ) (z : ParabolicSpace) :
    Summable (fun n : ℕ => parabolicSemigroup.pairing Λ (fun w => annShell N n (z - w))) := by
  obtain ⟨h1, h2, α, C, A, hA, hC, hloc⟩ := hΛ
  exact summable_pairing_annShell h1 h2 N hA hC hloc z

theorem measurable_pairing_annShell (hΛ : KRegular Λ x) (N n : ℕ) :
    Measurable fun z => parabolicSemigroup.pairing Λ (fun w => annShell N n (z - w)) := by
  obtain ⟨h1, h2, α, C, A, hA, hC, hloc⟩ := hΛ
  have hA' : ∀ a ∈ A, -4 < a ∧ a ≤ α := fun a ha => ⟨by linarith [(hA a ha).1], (hA a ha).2⟩
  have hg := contDiff_scaledShell (contDiff_annKernel0 N) n
  have hF : ∀ m : ℕ, Measurable fun z => ∫ w, Λ (1 / ((m : ℝ) + 1)) w * annShell N n (z - w) := by
    intro m
    have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hm : Measurable fun p : ParabolicSpace × ParabolicSpace =>
        Λ (1 / ((m : ℝ) + 1)) p.2 * annShell N n (p.1 - p.2) :=
      ((h2 _ hpos).comp measurable_snd).mul
        (hg.continuous.comp (continuous_fst.sub continuous_snd)).measurable
    exact (hm.stronglyMeasurable.integral_prod_right (ν := volume)).measurable
  refine measurable_of_tendsto_metrizable hF (tendsto_pi_nhds.2 fun z => ?_)
  have hseq : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun m => by
        show (0 : ℝ) < 1 / ((m : ℝ) + 1)
        positivity⟩
  have key := (tendsto_and_abs_pairing_scaledShell_centre_le h1 h2 (contDiff_annKernel0 N)
    (fun _ hz => annKernel0_eq_zero N hz) (y := z) hA' hC hloc n).1
  exact key.comp hseq

theorem measurable_kConv (hΛ : KRegular Λ x) (N : ℕ) : Measurable (kConv N Λ) := by
  have hlim : Tendsto (fun (m : ℕ) (z : ParabolicSpace) => ∑ n ∈ Finset.range m,
      parabolicSemigroup.pairing Λ (fun w => annShell N n (z - w))) atTop (𝓝 (kConv N Λ)) :=
    tendsto_pi_nhds.2 fun z => (hΛ.summable_pairing N z).hasSum.tendsto_sum_nat
  exact measurable_of_tendsto_metrizable
    (fun m => Finset.measurable_sum _ fun n _ => hΛ.measurable_pairing_annShell N n) hlim

theorem polyBounded_kConv (hΛ : KRegular Λ x) (N : ℕ) : PolyBounded (kConv N Λ) := by
  refine ⟨hΛ.measurable_kConv N, ?_⟩
  obtain ⟨h1, h2, α, C, A, hA, hC, hloc⟩ := hΛ
  obtain ⟨p, hp⟩ : ∃ p : ℕ, ∀ a ∈ A, α - a ≤ p :=
    ⟨⌈∑ b ∈ A, |α - b|⌉₊, fun a ha => (le_abs_self _).trans
      ((Finset.single_le_sum (f := fun b => |α - b|) (fun _ _ => abs_nonneg _) ha).trans
        (Nat.le_ceil _))⟩
  set c := (((∫ w, |annKernel0 N w|) + ∫ w, |parabolicGenerator (annKernel0 N) w|) *
      kConvRate A) * C with hc
  have hc0 : 0 ≤ c := by
    refine mul_nonneg (mul_nonneg (add_nonneg (integral_nonneg fun _ => abs_nonneg _)
      (integral_nonneg fun _ => abs_nonneg _)) (kConvRate_nonneg fun a ha => (hA a ha).1)) hC
  refine ⟨c * (1 + parabolicNorm x) ^ p, p, fun z => ?_⟩
  have hb := (summable_and_abs_kConv_le h1 h2 N hA hC hloc hp z).2
  have h3 : 1 + parabolicNorm (z - x) ≤ (1 + parabolicNorm x) * (1 + parabolicNorm z) := by
    have := one_add_parabolicNorm_le (z - x) (-x)
    rwa [parabolicNorm_neg, sub_neg_eq_add, sub_add_cancel] at this
  refine hb.trans ?_
  calc c * (1 + parabolicNorm (z - x)) ^ p
      ≤ c * ((1 + parabolicNorm x) * (1 + parabolicNorm z)) ^ p :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [parabolicNorm_nonneg (z - x)])
          h3 p) hc0
    _ = _ := by rw [mul_pow]; ring

end KRegular

end RegularityStructures

end
