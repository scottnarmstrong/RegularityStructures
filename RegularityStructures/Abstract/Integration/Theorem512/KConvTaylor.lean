/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Commute
public import RegularityStructures.Analysis.Heat.Schauder.TaylorDyadicSum
public import RegularityStructures.Abstract.Integration.Commute.Lemma516Integral

/-!
# `K ∗ Λ` minus its Taylor polynomial, for `Λ` of local order `γ`

For `Λ` a measurable `Q`-family of local order `γ` at `x` with exponents in `(-2, γ]`:

  `kConv N Λ z − ∑_{|k|_𝔰 < γ + 2} (z − x)^k/k! · ∑_n ⟨Λ, D^k K_n(x − ·)⟩
     = ∑_n ⟨Λ, K^γ_{n;xz}⟩`  (`kConv_sub_taylor_eq`),

so that, if `γ + 2 ∉ ℕ[𝔰]`, its modulus is `≤ c C ‖z − x‖_𝔰^{γ+2}` with `c` independent of `Λ`
(`exists_abs_kConv_sub_taylor_le`).  This is the function
`z ↦ ∑_n ⟨Rf − Π_x f(x), K^γ_{n;xz}⟩` in [Hai14, proof of Theorem 5.12] (cf. (5.14), (5.17)).
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

theorem kConv_sub_taylor_eq {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    {x : ParabolicSpace} {γ C : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -2 < a ∧ a ≤ γ) (hC : 0 ≤ C)
    (hloc : parabolicSemigroup.IsLocalOrder Λ x γ A C) (N : ℕ) (z : ParabolicSpace) :
    kConv N Λ z - ∑ k ∈ taylorIdx (γ + 2),
        (evalParabolic (MvPolynomial.monomial k 1) (z - x) / multiFact k) *
          ∑' n, derivShellPairing Λ (annKernel0 N) k x n =
      ∑' n, parabolicSemigroup.pairing Λ (taylorKernel (annKernel0 N) n (γ + 2) x z) := by
  have hA4 : ∀ a ∈ A, -4 < a ∧ a ≤ γ := fun a ha => ⟨by linarith [(hA a ha).1], (hA a ha).2⟩
  have hterm : ∀ n : ℕ, parabolicSemigroup.pairing Λ
      (taylorKernel (annKernel0 N) n (γ + 2) x z) =
      parabolicSemigroup.pairing Λ (fun w => annShell N n (z - w)) -
      ∑ k ∈ taylorIdx (γ + 2),
        (evalParabolic (MvPolynomial.monomial k 1) (z - x) / multiFact k) *
          derivShellPairing Λ (annKernel0 N) k x n := fun n =>
    pairing_taylorKernel_eq hΛ hΛm (contDiff_annKernel0 N)
      (fun _ hz => annKernel0_eq_zero N hz) hA4 hC hloc (γ + 2) n
  have hs1 : Summable fun n : ℕ => parabolicSemigroup.pairing Λ (fun w => annShell N n (z - w)) :=
    summable_pairing_annShell hΛ hΛm N hA hC hloc z
  have hsk : ∀ k ∈ taylorIdx (γ + 2), Summable fun n : ℕ =>
      (evalParabolic (MvPolynomial.monomial k 1) (z - x) / multiFact k) *
        derivShellPairing Λ (annKernel0 N) k x n := fun k hk =>
    (summable_pairing_lineIter_scaledShell hΛ hΛm (contDiff_annKernel0 N)
      (fun _ hz => annKernel0_eq_zero N hz) k hA4 hC hloc
      ((mem_taylorIdx_iff k).1 hk)).mul_left _
  simp only [hterm]
  unfold kConv
  rw [Summable.tsum_sub hs1 (summable_sum hsk), Summable.tsum_finsetSum hsk]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tsum_mul_left]

theorem exists_abs_kConv_sub_taylor_le (N : ℕ) {γ : ℝ} {A : Finset ℝ}
    (hA : ∀ a ∈ A, -2 < a ∧ a ≤ γ) (hγ : -2 < γ)
    (hnat : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) ≠ γ + 2) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {Λ : ℝ → ParabolicSpace → ℝ} {C : ℝ} {x : ParabolicSpace},
      Λ ∈ parabolicSemigroup.distributions → (∀ u, 0 < u → Measurable (Λ u)) → 0 ≤ C →
      parabolicSemigroup.IsLocalOrder Λ x γ A C → ∀ z : ParabolicSpace,
      |kConv N Λ z - ∑ k ∈ taylorIdx (γ + 2),
        (evalParabolic (MvPolynomial.monomial k 1) (z - x) / multiFact k) *
          ∑' n, derivShellPairing Λ (annKernel0 N) k x n| ≤
        c * C * parabolicNorm (z - x) ^ (γ + 2) := by
  obtain ⟨c, hc0, hc⟩ := exists_tsum_abs_pairing_taylorKernel_le (contDiff_annKernel0 N)
    (fun _ hz => annKernel0_eq_zero N hz) hA hγ hnat
  refine ⟨c, hc0, @fun Λ C x hΛ hΛm hC hloc z => ?_⟩
  obtain ⟨hs, hb⟩ := hc (y := z) hΛ hΛm hC hloc
  rw [kConv_sub_taylor_eq hΛ hΛm hA hC hloc N z]
  have h := norm_tsum_le_tsum_norm (f := fun n : ℕ =>
    parabolicSemigroup.pairing Λ (taylorKernel (annKernel0 N) n (γ + 2) x z))
    (by simpa only [Real.norm_eq_abs] using hs)
  simp only [Real.norm_eq_abs] at h
  exact h.trans hb

end RegularityStructures

end
