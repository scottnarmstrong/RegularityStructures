/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorEstimate
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernelBound

/-!
# The Taylor-regime estimate with the index set decoupled from the local order

`exists_abs_pairing_taylorKernel_le_sigma` is `exists_abs_pairing_taylorKernel_le` with the Taylor
index set `{|k|_𝔰 < σ}` and the local order `γ` of `Λ` independent: for `‖y - x‖ ≤ 2^{-n}`,
`|⟨Λ, K^σ_{n;xy}⟩| ≤ C ∑_ℓ κ_ℓ d^{|ℓ|} 2^{(|ℓ| - γ - 2) n}`, `|ℓ| ≥ σ`.  Used for the kernels
`D^k K_n`, which are `2^{|k| n}` times shells (`σ = γ + 2 - |k|`) in [Hai14, Theorem 5.12].
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

theorem exists_abs_pairing_taylorKernel_le_sigma {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h)
    (hs : ∀ z, 1 < parabolicNorm z → h z = 0) {γ : ℝ} (σ : ℝ) {A : Finset ℝ}
    (hA : ∀ a ∈ A, -4 < a ∧ a ≤ γ) :
    ∃ (𝔈 : List (List (Fin 4))) (κ : List (Fin 4) → ℝ), (∀ ℓ, 0 ≤ κ ℓ) ∧
      (∀ ℓ ∈ 𝔈, σ ≤ (indexWeight ℓ : ℝ) ∧
        ((∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) ≠ σ) → σ < (indexWeight ℓ : ℝ))) ∧
      ∀ {Λ : ℝ → ParabolicSpace → ℝ} {C : ℝ} {x y : ParabolicSpace},
        Λ ∈ parabolicSemigroup.distributions → (∀ u, 0 < u → Measurable (Λ u)) → 0 ≤ C →
        parabolicSemigroup.IsLocalOrder Λ x γ A C → ∀ n : ℕ,
        parabolicNorm (y - x) ≤ (2 : ℝ)⁻¹ ^ n →
        Filter.Tendsto (fun s => ∫ w, Λ s w * taylorKernel h n σ x y w) (nhdsWithin 0 (Ioi 0))
          (nhds (parabolicSemigroup.pairing Λ (taylorKernel h n σ x y))) ∧
        |parabolicSemigroup.pairing Λ (taylorKernel h n σ x y)| ≤
          C * (𝔈.map fun ℓ => κ ℓ * (parabolicNorm (y - x) ^ indexWeight ℓ *
            (2 : ℝ) ^ (((indexWeight ℓ : ℝ) - γ - 2) * n))).sum := by
  classical
  obtain ⟨E, hEprop, hEb⟩ := exists_integral_abs_remJ_le (fun _ : Fin 4 => ⌈σ⌉₊) (List.finRange 4)
  have hE : RemBound (fun _ : Fin 4 => ⌈σ⌉₊) (List.finRange 4) E :=
    remBound_intro fun s d hd hs' _ hφ hc => hEb s d hd hs' hφ hc
  set Out : List (List (Fin 4)) := (taylorOut σ).toList.map fun k => (Finsupp.toMultiset k).toList
    with hOut
  set wI : List (Fin 4) → ℝ := fun ℓ => ∫ w, |lineIter (ℓ.map coordDir) h w| with hwI
  set wI' : List (Fin 4) → ℝ := fun ℓ =>
    ∫ w, |lineIter (ℓ.map coordDir) (parabolicGenerator h) w| with hwI'
  set Pw : ℝ := ∑ a ∈ A, pairingWeight a with hPw
  have hPw0 : 0 ≤ Pw := Finset.sum_nonneg fun a ha => pairingWeight_nonneg (hA a ha).1
  refine ⟨E ++ Out, fun ℓ => 16 * Pw * 2 ^ |γ| * (wI ℓ + wI' ℓ), ?_, ?_, ?_⟩
  · intro ℓ
    have h1 : 0 ≤ wI ℓ := integral_nonneg fun _ => abs_nonneg _
    have h2 : 0 ≤ wI' ℓ := integral_nonneg fun _ => abs_nonneg _
    have h3 : (0 : ℝ) ≤ 2 ^ |γ| := Real.rpow_nonneg (by norm_num) _
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hPw0) h3) (add_nonneg h1 h2)
  · intro ℓ hℓ
    rcases List.mem_append.1 hℓ with hE' | hO
    · obtain ⟨j, -, hj⟩ := hEprop ℓ hE'
      have h1 := count_le_indexWeight j ℓ
      have h2 : σ ≤ ⌈σ⌉₊ := Nat.le_ceil σ
      have h3 : (⌈σ⌉₊ : ℝ) + 1 ≤ (indexWeight ℓ : ℝ) := by exact_mod_cast hj.trans h1
      exact ⟨by linarith, fun _ => by linarith⟩
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hO
      have hk' := (Finset.mem_toList.1 hk)
      have : ¬ (multiDeg k : ℝ) < σ := by
        unfold taylorOut at hk'
        exact (Finset.mem_filter.1 hk').2
      rw [indexWeight_toList]
      exact ⟨not_lt.1 this, fun hne => lt_of_le_of_ne (not_lt.1 this) (hne k).symm⟩
  · intro Λ C x y hΛ hΛm hC hloc n hdq
    set z : ParabolicSpace := y - x with hz
    set d : ℝ := parabolicNorm z with hd
    set q : ℝ := (2 : ℝ)⁻¹ ^ n with hq
    have hd0 : 0 ≤ d := parabolicNorm_nonneg _
    have hq0 : 0 < q := by positivity
    have hq1 : q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    set g := scaledShell h n with hg
    have hgs : ContDiff ℝ ∞ g := contDiff_scaledShell h0 n
    have hgc : HasCompactSupport g := hasCompactSupport_scaledShell hs n
    have hzc : ∀ i, |parabolicCoords z i| ≤ d ^ parabolicWeight i := fun i =>
      abs_parabolicCoords_le i
    obtain ⟨hL0, hL1⟩ := taylorProfile_L1 hE hgs hgc hd0 hzc
    -- convert the sums over `taylorOut` into sums over `Out`
    have hconv : ∀ F : List (Fin 4) → ℝ,
        ∑ k ∈ taylorOut σ, F ((Finsupp.toMultiset k).toList) = (Out.map F).sum := by
      intro F
      rw [hOut, List.map_map]
      exact (Finset.sum_map_toList (taylorOut σ)
        (fun k => F ((Finsupp.toMultiset k).toList))).symm
    have hH0 : ∫ u, |taylorProfile g σ z u| ≤ ((E ++ Out).map fun ℓ => d ^ indexWeight ℓ *
        (((2 : ℝ) ^ n) ^ indexWeight ℓ * ((((2 : ℝ) ^ n)⁻¹ ^ 2) * wI ℓ))).sum := by
      refine hL0.trans (le_of_eq ?_)
      rw [List.map_append, List.sum_append]
      congr 1
      · congr 1
        refine List.map_congr_left fun ℓ _ => ?_
        rw [hg, integral_abs_word_scaledShell h0]
      · rw [← hconv]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← indexWeight_toList k]
        have := integral_abs_word_scaledShell h0 ((Finsupp.toMultiset k).toList) n
        rw [multiDirs_eq_map, hg, this]
    have hH1 : ∫ u, |parabolicGenerator (taylorProfile g σ z) u| ≤
        ((E ++ Out).map fun ℓ => d ^ indexWeight ℓ *
          (((2 : ℝ) ^ n) ^ indexWeight ℓ * (((2 : ℝ) ^ n) ^ 2 * wI' ℓ))).sum := by
      refine hL1.trans (le_of_eq ?_)
      rw [List.map_append, List.sum_append]
      congr 1
      · congr 1
        refine List.map_congr_left fun ℓ _ => ?_
        rw [hg, integral_abs_gen_word_scaledShell h0]
      · rw [← hconv]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← indexWeight_toList k]
        have := integral_abs_gen_word_scaledShell h0 ((Finsupp.toMultiset k).toList) n
        rw [multiDirs_eq_map, hg, this]
    have hlam0 : 0 < q + d := by linarith
    have hlam2 : q + d ≤ 2 := by linarith
    have hsupp : ∀ u, q + d < parabolicNorm u → taylorProfile g σ z u = 0 := fun u hu =>
      taylorProfile_eq_zero hs n σ hu
    have hrp : (q + d) ^ (-(4 : ℝ)) = ((q + d) ^ 4)⁻¹ := by
      rw [show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hlam0.le, Real.rpow_natCast]
    have hP1 : 0 ≤ ((E ++ Out).map fun ℓ => d ^ indexWeight ℓ *
          (((2 : ℝ) ^ n) ^ indexWeight ℓ * (((2 : ℝ) ^ n) ^ 2 * wI' ℓ))).sum := by
      refine List.sum_nonneg fun x hx => ?_
      obtain ⟨ℓ, -, rfl⟩ := List.mem_map.1 hx
      have : 0 ≤ wI' ℓ := integral_nonneg fun _ => abs_nonneg _
      positivity
    have key := tendsto_and_abs_pairing_reflect_le_centre hΛ hΛm hA hC hloc (contDiff_taylorProfile hgs σ z)
      hlam0 hlam2 hsupp (c := x)
      (B₀ := ((E ++ Out).map fun ℓ => d ^ indexWeight ℓ *
        (((2 : ℝ) ^ n) ^ indexWeight ℓ * ((((2 : ℝ) ^ n)⁻¹ ^ 2) * wI ℓ))).sum)
      (B₁ := ((E ++ Out).map fun ℓ => d ^ indexWeight ℓ *
          (((2 : ℝ) ^ n) ^ indexWeight ℓ * (((2 : ℝ) ^ n) ^ 2 * wI' ℓ))).sum * (q + d) ^ 4)
      hH0
      (by
        rw [hrp, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
        exact hH1)
    have hker : taylorKernel h n σ x y = fun w => taylorProfile g σ z (x - w) :=
      funext fun w => taylorKernel_eq_profile h n σ x y w
    rw [hker]
    refine ⟨key.1, key.2.trans ?_⟩
    rw [sub_self, parabolicNorm_zero, add_zero]
    have hsum : ∑ a ∈ A, pairingWeight a * ((q + d) ^ a * (q + d) ^ (γ - a)) =
        Pw * (q + d) ^ γ := by
      rw [hPw, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Real.rpow_add hlam0]; congr 2; ring
    rw [hsum]
    exact taylor_estimate_alg (E ++ Out) wI wI' (fun ℓ => integral_nonneg fun _ => abs_nonneg _)
      (fun ℓ => integral_nonneg fun _ => abs_nonneg _) hd0 hq0 hdq n hq γ C Pw hC hPw0

end RegularityStructures

end
