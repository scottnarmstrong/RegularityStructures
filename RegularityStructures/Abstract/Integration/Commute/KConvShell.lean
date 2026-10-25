/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Commute.KConv
public import RegularityStructures.Analysis.Heat.Schauder.TaylorSmall
public import RegularityStructures.Analysis.Heat.Annihilating.Decomposition
public import RegularityStructures.Analysis.Heat.Annihilating.KernelSupport

/-!
# The convolution `K ∗ Λ` with the annihilating shells

`kConv N Λ z = ∑_n ⟨Λ, K_n(z - ·)⟩` with `K_n = annShell N n`, the per-shell bound
(`abs_pairing_annShell_le`), and absolute convergence of the series with a polynomial growth bound
for `Λ` of local order `α` (`summable_and_abs_kConv_le`).

Source: [Hai14, Section 5, proof of Theorem 5.12].
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- `K ∗ Λ (z) = ∑_n ⟨Λ, K_n(z - ·)⟩`, `K_n = annShell N n`. -/
def kConv (N : ℕ) (Λ : ℝ → ParabolicSpace → ℝ) (z : ParabolicSpace) : ℝ :=
  ∑' n : ℕ, parabolicSemigroup.pairing Λ (fun w => annShell N n (z - w))

end RegularityStructures

end

public section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace RegularityStructures

/-- Per-shell bound on `⟨Λ, K_n(z - ·)⟩`, with the polynomial factor `(1 + d(z, x))^p`. -/
theorem abs_pairing_annShell_le {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    (N : ℕ) {x z : ParabolicSpace} {α C : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -2 < a ∧ a ≤ α)
    (hC : 0 ≤ C) (hloc : parabolicSemigroup.IsLocalOrder Λ x α A C) {p : ℕ}
    (hp : ∀ a ∈ A, α - a ≤ p) (n : ℕ) :
    |parabolicSemigroup.pairing Λ (fun w => annShell N n (z - w))| ≤
      ((∫ w, |annKernel0 N w|) + ∫ w, |parabolicGenerator (annKernel0 N) w|) * C *
        (1 + parabolicNorm (z - x)) ^ p *
        ∑ a ∈ A, pairingWeight a * ((2 : ℝ) ^ (-(a + 2))) ^ n := by
  have h := abs_pairing_scaledShell_centre_le hΛ hΛm (contDiff_annKernel0 N)
    (fun _ hz => annKernel0_eq_zero N hz) (x := x) (y := z) (A := A)
    (fun a ha => ⟨by linarith [(hA a ha).1], (hA a ha).2⟩) hC hloc n
  have hd0 : 0 ≤ parabolicNorm (z - x) := parabolicNorm_nonneg _
  have hB : 0 ≤ ((∫ w, |annKernel0 N w|) + ∫ w, |parabolicGenerator (annKernel0 N) w|) * C :=
    mul_nonneg (add_nonneg (integral_nonneg fun _ => abs_nonneg _)
      (integral_nonneg fun _ => abs_nonneg _)) hC
  have hS : ∑ a ∈ A, pairingWeight a * ((2 : ℝ) ^ (-(a + 2) * n) *
      ((2 : ℝ)⁻¹ ^ n + parabolicNorm (z - x)) ^ (α - a)) ≤
      (1 + parabolicNorm (z - x)) ^ p *
        ∑ a ∈ A, pairingWeight a * ((2 : ℝ) ^ (-(a + 2))) ^ n := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a ha => ?_
    have hκ := pairingWeight_nonneg (a := a) (by linarith [(hA a ha).1])
    have h1 : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h2 : ((2 : ℝ)⁻¹ ^ n + parabolicNorm (z - x)) ^ (α - a) ≤
        (1 + parabolicNorm (z - x)) ^ p := by
      calc _ ≤ (1 + parabolicNorm (z - x)) ^ (α - a) :=
            Real.rpow_le_rpow (add_nonneg (pow_nonneg (by norm_num) _) (parabolicNorm_nonneg _))
              (by linarith) (by linarith [(hA a ha).2])
        _ ≤ (1 + parabolicNorm (z - x)) ^ (p : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (hp a ha)
        _ = _ := Real.rpow_natCast _ _
    rw [two_rpow_neg_pow]
    have hr : 0 ≤ ((2 : ℝ) ^ (-(a + 2))) ^ n :=
      pow_nonneg (Real.rpow_nonneg (by norm_num) _) n
    calc pairingWeight a * (((2 : ℝ) ^ (-(a + 2))) ^ n *
          ((2 : ℝ)⁻¹ ^ n + parabolicNorm (z - x)) ^ (α - a))
        ≤ pairingWeight a * (((2 : ℝ) ^ (-(a + 2))) ^ n * (1 + parabolicNorm (z - x)) ^ p) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hr) hκ
      _ = _ := by ring
  refine h.trans ?_
  calc _ ≤ ((∫ w, |annKernel0 N w|) + ∫ w, |parabolicGenerator (annKernel0 N) w|) * C *
        ((1 + parabolicNorm (z - x)) ^ p *
          ∑ a ∈ A, pairingWeight a * ((2 : ℝ) ^ (-(a + 2))) ^ n) :=
        mul_le_mul_of_nonneg_left hS hB
    _ = _ := by ring

/-- **Convergence and growth of `K ∗ Λ`**: for `Λ` of local order `α` at `x` with exponents in
`(-2, α]`, the series defining `kConv N Λ z` converges absolutely and
`|kConv N Λ z| ≤ c C (1 + d(z, x))^p`, `p ≥ α - a` for all `a ∈ A`. -/
theorem summable_and_abs_kConv_le {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    (N : ℕ) {x : ParabolicSpace} {α C : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -2 < a ∧ a ≤ α)
    (hC : 0 ≤ C) (hloc : parabolicSemigroup.IsLocalOrder Λ x α A C) {p : ℕ}
    (hp : ∀ a ∈ A, α - a ≤ p) (z : ParabolicSpace) :
    Summable (fun n : ℕ => |parabolicSemigroup.pairing Λ (fun w => annShell N n (z - w))|) ∧
    |kConv N Λ z| ≤ (((∫ w, |annKernel0 N w|) + ∫ w, |parabolicGenerator (annKernel0 N) w|) *
      kConvRate A) * C * (1 + parabolicNorm (z - x)) ^ p := by
  set B := ((∫ w, |annKernel0 N w|) + ∫ w, |parabolicGenerator (annKernel0 N) w|) * C *
    (1 + parabolicNorm (z - x)) ^ p with hB
  have hb := hasSum_annShell_bound A (fun a ha => (hA a ha).1) B
  have hle := abs_pairing_annShell_le hΛ hΛm N hA hC hloc hp (z := z)
  have hs : Summable (fun n : ℕ => |parabolicSemigroup.pairing Λ
      (fun w => annShell N n (z - w))|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => hle n) hb.summable
  refine ⟨hs, ?_⟩
  have hs' : Summable (fun n : ℕ => ‖parabolicSemigroup.pairing Λ
      (fun w => annShell N n (z - w))‖) := hs
  unfold kConv
  calc |∑' n : ℕ, parabolicSemigroup.pairing Λ (fun w => annShell N n (z - w))|
      ≤ ∑' n : ℕ, |parabolicSemigroup.pairing Λ (fun w => annShell N n (z - w))| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs'
    _ ≤ B * kConvRate A := by
        rw [← hb.tsum_eq]
        exact hs.tsum_le_tsum (fun n => hle n) hb.summable
    _ = _ := by rw [hB]; ring

theorem summable_pairing_annShell {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    (N : ℕ) {x : ParabolicSpace} {α C : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -2 < a ∧ a ≤ α)
    (hC : 0 ≤ C) (hloc : parabolicSemigroup.IsLocalOrder Λ x α A C) (z : ParabolicSpace) :
    Summable (fun n : ℕ => parabolicSemigroup.pairing Λ (fun w => annShell N n (z - w))) := by
  obtain ⟨p, hp⟩ : ∃ p : ℕ, ∀ a ∈ A, α - a ≤ p :=
    ⟨⌈∑ b ∈ A, |α - b|⌉₊, fun a ha => (le_abs_self _).trans
      ((Finset.single_le_sum (f := fun b => |α - b|) (fun _ _ => abs_nonneg _) ha).trans
        (Nat.le_ceil _))⟩
  exact (summable_and_abs_kConv_le hΛ hΛm N hA hC hloc hp z).1.of_abs

end RegularityStructures

end
