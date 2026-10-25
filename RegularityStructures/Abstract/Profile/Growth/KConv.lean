/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Growth.KConv
public import RegularityStructures.Abstract.Integration.Commute.KConv
public import RegularityStructures.Abstract.Polynomial.Model.Growth
public import RegularityStructures.Abstract.Profile.KConv
public import RegularityStructures.Analysis.Heat.Annihilating.Scaled

/-!
# The function `K ∗ Λ` for a distribution of local order with growth, for a general shell profile

Profile-generic version of `RegularityStructures.Abstract.Integration.Growth.KConv`. For `Λ` that is
`KRegularG` at `x` (the definition does not involve the kernel and is reused), and a profile `h`
(`ShellProfile h N`) with shells `K_n = scaledShell h n`, the series `kConvP h Λ z` converges
(`KRegularG.summable_pairing_growthP`), `|kConvP h Λ z| ≤ c C (2 + d(z, x))^q (1 + d(z, x))^p`
(`summable_and_abs_kConv_le_growthPP`), `kConvP h Λ` is measurable with polynomial growth
(`KRegularG.polyBounded_kConv_growthP_growthP`) and `Λ ↦ kConvP h Λ` is linear on finitely many such
families (`kConv_finset_sum_growthP`). Input of the weighted [Hai14, Lemma 5.16].
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace RegularityStructures

variable {h : ParabolicSpace → ℝ} {N : ℕ}

/-- Per-shell bound on `⟨Λ, K_n(z - ·)⟩` for `Λ` of local order with growth `q`, with the
polynomial factors `(2 + d(z, x))^q (1 + d(z, x))^p`. -/
theorem abs_pairing_shell_le_growthP {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    (hh : ShellProfile h N) {x z : ParabolicSpace} {α C q : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -2 < a ∧ a ≤ α)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hloc : parabolicSemigroup.IsLocalOrderGrowth Λ x α A C q) {p : ℕ}
    (hp : ∀ a ∈ A, α - a ≤ p) (n : ℕ) :
    |parabolicSemigroup.pairing Λ (fun w => scaledShell h n (z - w))| ≤
      ((∫ w, |h w|) + ∫ w, |parabolicGenerator (h) w|) *
        (C * (2 + parabolicNorm (z - x)) ^ q) * (1 + parabolicNorm (z - x)) ^ p *
        ∑ a ∈ A, pairingWeight a * ((2 : ℝ) ^ (-(a + 2))) ^ n := by
  have hmain := abs_pairing_scaledShell_centre_le_growth hΛ hΛm hh.contDiff
    hh.eq_zero (x := x) (y := z) (A := A)
    (fun a ha => ⟨by linarith [(hA a ha).1], (hA a ha).2⟩) hC hq hloc n
  have hd0 : 0 ≤ parabolicNorm (z - x) := parabolicNorm_nonneg _
  have h2q : 0 ≤ (2 + parabolicNorm (z - x)) ^ q := Real.rpow_nonneg (by linarith) _
  have hB : 0 ≤ ((∫ w, |h w|) + ∫ w, |parabolicGenerator (h) w|) *
      (C * (2 + parabolicNorm (z - x)) ^ q) :=
    mul_nonneg (add_nonneg (integral_nonneg fun _ => abs_nonneg _)
      (integral_nonneg fun _ => abs_nonneg _)) (mul_nonneg hC h2q)
  have hmono : C * (1 + ((2 : ℝ)⁻¹ ^ n + parabolicNorm (z - x))) ^ q ≤
      C * (2 + parabolicNorm (z - x)) ^ q := by
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith [pow_nonneg (show (0 : ℝ) ≤ 2⁻¹ by norm_num) n]) ?_ hq) hC
    have : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
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
  have hI0 : 0 ≤ (∫ w, |h w|) + ∫ w, |parabolicGenerator (h) w| :=
    add_nonneg (integral_nonneg fun _ => abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _)
  have hS0 : 0 ≤ ∑ a ∈ A, pairingWeight a * ((2 : ℝ) ^ (-(a + 2) * n) *
      ((2 : ℝ)⁻¹ ^ n + parabolicNorm (z - x)) ^ (α - a)) :=
    Finset.sum_nonneg fun a ha => mul_nonneg (pairingWeight_nonneg (by linarith [(hA a ha).1]))
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.rpow_nonneg (add_nonneg (pow_nonneg (by norm_num) _) hd0) _))
  refine hmain.trans ?_
  calc _ ≤ ((∫ w, |h w|) + ∫ w, |parabolicGenerator (h) w|) *
        (C * (2 + parabolicNorm (z - x)) ^ q) *
        ∑ a ∈ A, pairingWeight a * ((2 : ℝ) ^ (-(a + 2) * n) *
          ((2 : ℝ)⁻¹ ^ n + parabolicNorm (z - x)) ^ (α - a)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hI0) hS0
    _ ≤ ((∫ w, |h w|) + ∫ w, |parabolicGenerator (h) w|) *
        (C * (2 + parabolicNorm (z - x)) ^ q) *
        ((1 + parabolicNorm (z - x)) ^ p *
          ∑ a ∈ A, pairingWeight a * ((2 : ℝ) ^ (-(a + 2))) ^ n) :=
        mul_le_mul_of_nonneg_left hS hB
    _ = _ := by ring

/-- **Convergence and growth of `K ∗ Λ`** for `Λ` of local order `α` at `x` with growth `q` and
exponents in `(-2, α]`: the series defining `kConvP h Λ z` converges absolutely and
`|kConvP h Λ z| ≤ c C (2 + d(z, x))^q (1 + d(z, x))^p`, `p ≥ α - a` for all `a ∈ A`. -/
theorem summable_and_abs_kConv_le_growthP {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    (hh : ShellProfile h N) {x : ParabolicSpace} {α C q : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -2 < a ∧ a ≤ α)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hloc : parabolicSemigroup.IsLocalOrderGrowth Λ x α A C q) {p : ℕ}
    (hp : ∀ a ∈ A, α - a ≤ p) (z : ParabolicSpace) :
    Summable (fun n : ℕ => |parabolicSemigroup.pairing Λ (fun w => scaledShell h n (z - w))|) ∧
    |kConvP h Λ z| ≤ (((∫ w, |h w|) + ∫ w, |parabolicGenerator (h) w|) *
      kConvRate A) * (C * (2 + parabolicNorm (z - x)) ^ q) * (1 + parabolicNorm (z - x)) ^ p := by
  set B := ((∫ w, |h w|) + ∫ w, |parabolicGenerator (h) w|) *
    (C * (2 + parabolicNorm (z - x)) ^ q) * (1 + parabolicNorm (z - x)) ^ p with hB
  have hb := hasSum_annShell_bound A (fun a ha => (hA a ha).1) B
  have hle := abs_pairing_shell_le_growthP hΛ hΛm hh hA hC hq hloc hp (z := z)
  have hs : Summable (fun n : ℕ => |parabolicSemigroup.pairing Λ
      (fun w => scaledShell h n (z - w))|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => hle n) hb.summable
  refine ⟨hs, ?_⟩
  have hs' : Summable (fun n : ℕ => ‖parabolicSemigroup.pairing Λ
      (fun w => scaledShell h n (z - w))‖) := hs
  unfold kConvP
  calc |∑' n : ℕ, parabolicSemigroup.pairing Λ (fun w => scaledShell h n (z - w))|
      ≤ ∑' n : ℕ, |parabolicSemigroup.pairing Λ (fun w => scaledShell h n (z - w))| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs'
    _ ≤ B * kConvRate A := by
        rw [← hb.tsum_eq]
        exact hs.tsum_le_tsum (fun n => hle n) hb.summable
    _ = _ := by rw [hB]; ring

theorem summable_pairing_shell_growthP {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    (hh : ShellProfile h N) {x : ParabolicSpace} {α C q : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -2 < a ∧ a ≤ α)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hloc : parabolicSemigroup.IsLocalOrderGrowth Λ x α A C q) (z : ParabolicSpace) :
    Summable (fun n : ℕ => parabolicSemigroup.pairing Λ (fun w => scaledShell h n (z - w))) := by
  obtain ⟨p, hp⟩ : ∃ p : ℕ, ∀ a ∈ A, α - a ≤ p :=
    ⟨⌈∑ b ∈ A, |α - b|⌉₊, fun a ha => (le_abs_self _).trans
      ((Finset.single_le_sum (f := fun b => |α - b|) (fun _ _ => abs_nonneg _) ha).trans
        (Nat.le_ceil _))⟩
  exact (summable_and_abs_kConv_le_growthP hΛ hΛm hh hA hC hq hloc hp z).1.of_abs

namespace KRegularG

variable {Λ : ℝ → ParabolicSpace → ℝ} {x : ParabolicSpace}

theorem summable_pairing_growthP (hΛ : KRegularG Λ x) (hh : ShellProfile h N) (z : ParabolicSpace) :
    Summable (fun n : ℕ => parabolicSemigroup.pairing Λ (fun w => scaledShell h n (z - w))) := by
  obtain ⟨h1, h2, α, C, q, A, hA, hC, hq, hloc⟩ := hΛ
  exact summable_pairing_shell_growthP h1 h2 hh hA hC hq hloc z

theorem measurable_pairing_shell_growthP (hΛ : KRegularG Λ x) (hh : ShellProfile h N) (n : ℕ) :
    Measurable fun z => parabolicSemigroup.pairing Λ (fun w => scaledShell h n (z - w)) := by
  obtain ⟨h1, h2, α, C, q, A, hA, hC, hq, hloc⟩ := hΛ
  have hA' : ∀ a ∈ A, -4 < a ∧ a ≤ α := fun a ha => ⟨by linarith [(hA a ha).1], (hA a ha).2⟩
  have hg := contDiff_scaledShell hh.contDiff n
  have hF : ∀ m : ℕ, Measurable fun z => ∫ w, Λ (1 / ((m : ℝ) + 1)) w * scaledShell h n (z - w) := by
    intro m
    have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hm : Measurable fun p : ParabolicSpace × ParabolicSpace =>
        Λ (1 / ((m : ℝ) + 1)) p.2 * scaledShell h n (p.1 - p.2) :=
      ((h2 _ hpos).comp measurable_snd).mul
        (hg.continuous.comp (continuous_fst.sub continuous_snd)).measurable
    exact (hm.stronglyMeasurable.integral_prod_right (ν := volume)).measurable
  refine measurable_of_tendsto_metrizable hF (tendsto_pi_nhds.2 fun z => ?_)
  have hseq : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun m => by
        show (0 : ℝ) < 1 / ((m : ℝ) + 1)
        positivity⟩
  have key := (tendsto_and_abs_pairing_scaledShell_centre_le_growth h1 h2 hh.contDiff
    hh.eq_zero (y := z) hA' hC hq hloc n).1
  exact key.comp hseq

theorem measurable_kConv_growthP (hΛ : KRegularG Λ x) (hh : ShellProfile h N) : Measurable (kConvP h Λ) := by
  have hlim : Tendsto (fun (m : ℕ) (z : ParabolicSpace) => ∑ n ∈ Finset.range m,
      parabolicSemigroup.pairing Λ (fun w => scaledShell h n (z - w))) atTop (𝓝 (kConvP h Λ)) :=
    tendsto_pi_nhds.2 fun z => (hΛ.summable_pairing_growthP hh z).hasSum.tendsto_sum_nat
  exact measurable_of_tendsto_metrizable
    (fun m => Finset.measurable_sum _ fun n _ => hΛ.measurable_pairing_shell_growthP hh n) hlim

theorem polyBounded_kConv_growthP (hΛ : KRegularG Λ x) (hh : ShellProfile h N) : PolyBounded (kConvP h Λ) := by
  refine ⟨hΛ.measurable_kConv_growthP hh, ?_⟩
  obtain ⟨h1, h2, α, C, q, A, hA, hC, hq, hloc⟩ := hΛ
  obtain ⟨p, hp⟩ : ∃ p : ℕ, ∀ a ∈ A, α - a ≤ p :=
    ⟨⌈∑ b ∈ A, |α - b|⌉₊, fun a ha => (le_abs_self _).trans
      ((Finset.single_le_sum (f := fun b => |α - b|) (fun _ _ => abs_nonneg _) ha).trans
        (Nat.le_ceil _))⟩
  set c := (((∫ w, |h w|) + ∫ w, |parabolicGenerator (h) w|) *
      kConvRate A) * (C * 2 ^ q) with hc
  have hc0 : 0 ≤ c := by
    refine mul_nonneg (mul_nonneg (add_nonneg (integral_nonneg fun _ => abs_nonneg _)
      (integral_nonneg fun _ => abs_nonneg _)) (kConvRate_nonneg fun a ha => (hA a ha).1))
      (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _))
  refine ⟨c * (1 + parabolicNorm x) ^ (p + ⌈q⌉₊), p + ⌈q⌉₊, fun z => ?_⟩
  have hb := (summable_and_abs_kConv_le_growthP h1 h2 hh hA hC hq hloc hp z).2
  have hd0 : 0 ≤ parabolicNorm (z - x) := parabolicNorm_nonneg _
  have h3 : 1 + parabolicNorm (z - x) ≤ (1 + parabolicNorm x) * (1 + parabolicNorm z) := by
    have := one_add_parabolicNorm_le (z - x) (-x)
    rwa [parabolicNorm_neg, sub_neg_eq_add, sub_add_cancel] at this
  have hb1 : 1 ≤ 1 + parabolicNorm (z - x) := by linarith
  have h2q : (2 + parabolicNorm (z - x)) ^ q ≤ 2 ^ q * (1 + parabolicNorm (z - x)) ^ ⌈q⌉₊ := by
    calc (2 + parabolicNorm (z - x)) ^ q ≤ (2 * (1 + parabolicNorm (z - x))) ^ q :=
          Real.rpow_le_rpow (by linarith) (by linarith) hq
      _ = 2 ^ q * (1 + parabolicNorm (z - x)) ^ q := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 2 ^ q * (1 + parabolicNorm (z - x)) ^ (⌈q⌉₊ : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hb1 (Nat.le_ceil q))
            (Real.rpow_nonneg (by norm_num) _)
      _ = _ := by rw [Real.rpow_natCast]
  have hcd : 0 ≤ ((∫ w, |h w|) + ∫ w, |parabolicGenerator (h) w|) *
      kConvRate A * C :=
    mul_nonneg (mul_nonneg (add_nonneg (integral_nonneg fun _ => abs_nonneg _)
      (integral_nonneg fun _ => abs_nonneg _)) (kConvRate_nonneg fun a ha => (hA a ha).1)) hC
  calc |kConvP h Λ z| ≤ ((∫ w, |h w|) + ∫ w, |parabolicGenerator (h) w|) *
        kConvRate A * (C * (2 + parabolicNorm (z - x)) ^ q) * (1 + parabolicNorm (z - x)) ^ p := hb
    _ ≤ ((∫ w, |h w|) + ∫ w, |parabolicGenerator (h) w|) *
        kConvRate A * (C * (2 ^ q * (1 + parabolicNorm (z - x)) ^ ⌈q⌉₊)) *
          (1 + parabolicNorm (z - x)) ^ p := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h2q hC) (mul_nonneg (add_nonneg
            (integral_nonneg fun _ => abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _))
            (kConvRate_nonneg fun a ha => (hA a ha).1))) (pow_nonneg (by linarith) _)
    _ = c * (1 + parabolicNorm (z - x)) ^ (p + ⌈q⌉₊) := by rw [hc, pow_add]; ring
    _ ≤ c * ((1 + parabolicNorm x) * (1 + parabolicNorm z)) ^ (p + ⌈q⌉₊) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h3 _) hc0
    _ = _ := by rw [mul_pow]; ring

end KRegularG

namespace KRegularG

variable {Λ : ℝ → ParabolicSpace → ℝ} {x : ParabolicSpace}

theorem integrable_mul_shell_growthP (hΛ : KRegularG Λ x) (hh : ShellProfile h N) (n : ℕ) (z : ParabolicSpace) {s : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    Integrable (fun w => Λ s w * scaledShell h n (z - w)) := by
  obtain ⟨h1, h2, α, C, qg, A, hA, hC, hqg, hloc⟩ := hΛ
  have hg := contDiff_scaledShell hh.contDiff n
  set q : ℝ := (2 : ℝ)⁻¹ ^ n with hq
  have hq0 : 0 < q := by positivity
  set d : ℝ := parabolicNorm (z - x) with hd
  have hc1 : Continuous fun w => scaledShell h n (z - w) :=
    hg.continuous.comp (continuous_const.sub continuous_id)
  have hsupp : ∀ w, q < parabolicNorm (w - z) → scaledShell h n (z - w) = 0 := fun w hw => by
    refine scaledShell_eq_zero hh.eq_zero ?_
    rwa [parabolicNorm_sub_comm]
  have hcs : HasCompactSupport fun w => scaledShell h n (z - w) :=
    hasCompactSupport_of_eq_zero (c := q) hq0 z hsupp
  exact integrable_mul_of_growth h1 h2 hC hqg (fun a ha => (hA a ha).2) hloc hs
    (lam := q + d) (add_nonneg hq0.le (parabolicNorm_nonneg _)) ⟨hc1.measurable,
    hc1.integrable_of_hasCompactSupport hcs, fun w hw => by
      have h3 : parabolicNorm (w - x) ≤ parabolicNorm (w - z) + parabolicNorm (z - x) := by
        simpa using parabolicNorm_add_le (w - z) (z - x)
      refine hsupp w ?_
      change q + d < parabolicNorm (w - x) at hw
      linarith⟩

end KRegularG

variable {J : Type*} {x : ParabolicSpace}

/-- Linearity of the pairing with a shell on finitely many regular families. -/
theorem pairing_shell_finset_sum_growthP (s : Finset J) (Λj : J → ℝ → ParabolicSpace → ℝ) (c : J → ℝ)
    (hΛ : ∀ j ∈ s, KRegularG (Λj j) x) (hh : ShellProfile h N) (n : ℕ) (z : ParabolicSpace) :
    parabolicSemigroup.pairing (fun t w => ∑ j ∈ s, c j * Λj j t w)
        (fun w => scaledShell h n (z - w)) =
      ∑ j ∈ s, c j * parabolicSemigroup.pairing (Λj j) (fun w => scaledShell h n (z - w)) := by
  have hT : ∀ j ∈ s, Tendsto (fun r => ∫ w, Λj j r w * scaledShell h n (z - w))
      (𝓝[>] 0) (𝓝 (parabolicSemigroup.pairing (Λj j) (fun w => scaledShell h n (z - w)))) := by
    intro j hj
    obtain ⟨h1, h2, α, C, qg, A, hA, hC, hq, hloc⟩ := hΛ j hj
    exact (tendsto_and_abs_pairing_scaledShell_centre_le_growth h1 h2 hh.contDiff
      hh.eq_zero (y := z) (A := A)
      (fun a ha => ⟨by linarith [(hA a ha).1], (hA a ha).2⟩) hC hq hloc n).1
  refine parabolicSemigroup.pairing_eq_of_tendsto ((tendsto_finsetSum s fun j hj =>
    (hT j hj).const_mul (c j)).congr' ?_)
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with r hr
  have hr' : r ∈ Ioc (0 : ℝ) 1 := ⟨hr.1, hr.2.le⟩
  simp only [← integral_const_mul]
  rw [← integral_finsetSum]
  · refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · intro j hj
    exact ((hΛ j hj).integrable_mul_shell_growthP hh n z hr').const_mul (c j)

/-- **Linearity of `kConv`** on finitely many regular families. -/
theorem kConv_finset_sum_growthP (s : Finset J) (Λj : J → ℝ → ParabolicSpace → ℝ) (c : J → ℝ)
    (hΛ : ∀ j ∈ s, KRegularG (Λj j) x) (hh : ShellProfile h N) (z : ParabolicSpace) :
    kConvP h (fun t w => ∑ j ∈ s, c j * Λj j t w) z = ∑ j ∈ s, c j * kConvP h (Λj j) z := by
  unfold kConvP
  simp only [pairing_shell_finset_sum_growthP s Λj c hΛ hh _ z]
  rw [Summable.tsum_finsetSum]
  · exact Finset.sum_congr rfl fun j _ => tsum_mul_left
  · intro j hj
    exact ((hΛ j hj).summable_pairing_growthP hh z).mul_left (c j)

end RegularityStructures

end
