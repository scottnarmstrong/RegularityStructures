/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorEstimate
public import RegularityStructures.Analysis.Heat.Schauder.TaylorL1
public import RegularityStructures.Analysis.Heat.Schauder.Derivative
public import RegularityStructures.Analysis.Heat.Schauder.DerivativePairing

/-!
# The Taylor kernel bound

`exists_abs_pairing_taylorKernel_le`: the pairing of a distribution of local order `γ` at `x` with the
Taylor kernel `K^γ_{n;xy}` at the scales `2^{-n} ≥ ‖y - x‖`.

Source: [Hai14, (5.16), proof of Lemma 5.19].
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

theorem lam_rpow_le {q d : ℝ} (hq : 0 < q) (hd : 0 ≤ d) (hdq : d ≤ q) (γ : ℝ) :
    (q + d) ^ γ ≤ (2 : ℝ) ^ |γ| * q ^ γ := by
  have h2 : (1 : ℝ) ≤ 2 ^ |γ| := Real.one_le_rpow (by norm_num) (abs_nonneg _)
  have hqγ : 0 < q ^ γ := Real.rpow_pos_of_pos hq _
  rcases le_total 0 γ with hγ | hγ
  · have : (q + d) ^ γ ≤ (2 * q) ^ γ :=
      Real.rpow_le_rpow (by linarith) (by linarith) hγ
    rw [Real.mul_rpow (by norm_num) hq.le] at this
    refine this.trans ?_
    refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) hqγ.le
    rw [abs_of_nonneg hγ]
  · have : (q + d) ^ γ ≤ q ^ γ := Real.rpow_le_rpow_of_nonpos hq (by linarith) hγ
    calc (q + d) ^ γ ≤ q ^ γ := this
      _ = 1 * q ^ γ := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 hqγ.le

theorem taylor_estimate_alg (L : List (List (Fin 4))) (wI wI' : List (Fin 4) → ℝ)
    (hI : ∀ ℓ, 0 ≤ wI ℓ) (hI' : ∀ ℓ, 0 ≤ wI' ℓ) {d q : ℝ} (hd : 0 ≤ d) (hq : 0 < q) (hdq : d ≤ q)
    (n : ℕ) (hqn : q = (2 : ℝ)⁻¹ ^ n) (γ C Pw : ℝ) (hC : 0 ≤ C) (hPw : 0 ≤ Pw) :
    C * (Pw * (q + d) ^ γ) *
        ((L.map fun ℓ => d ^ indexWeight ℓ * (((2 : ℝ) ^ n) ^ indexWeight ℓ *
            ((((2 : ℝ) ^ n)⁻¹ ^ 2) * wI ℓ))).sum +
          (L.map fun ℓ => d ^ indexWeight ℓ * (((2 : ℝ) ^ n) ^ indexWeight ℓ *
            (((2 : ℝ) ^ n) ^ 2 * wI' ℓ))).sum * (q + d) ^ 4) ≤
      C * (L.map fun ℓ => (16 * Pw * (2 : ℝ) ^ |γ| * (wI ℓ + wI' ℓ)) *
        (d ^ indexWeight ℓ * (2 : ℝ) ^ (((indexWeight ℓ : ℝ) - γ - 2) * n))).sum := by
  have hN : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hqN : q = ((2 : ℝ) ^ n)⁻¹ := by rw [hqn, inv_pow]
  have hlam4 : (q + d) ^ 4 ≤ 16 * (((2 : ℝ) ^ n)⁻¹) ^ 4 := by
    have : q + d ≤ 2 * ((2 : ℝ) ^ n)⁻¹ := by rw [← hqN]; linarith
    calc (q + d) ^ 4 ≤ (2 * ((2 : ℝ) ^ n)⁻¹) ^ 4 :=
          pow_le_pow_left₀ (by linarith) this 4
      _ = _ := by ring
  have hγ := lam_rpow_le hq hd hdq γ
  have hrewrite : (L.map fun ℓ => d ^ indexWeight ℓ * (((2 : ℝ) ^ n) ^ indexWeight ℓ *
            ((((2 : ℝ) ^ n)⁻¹ ^ 2) * wI ℓ))).sum +
          (L.map fun ℓ => d ^ indexWeight ℓ * (((2 : ℝ) ^ n) ^ indexWeight ℓ *
            (((2 : ℝ) ^ n) ^ 2 * wI' ℓ))).sum * (q + d) ^ 4 ≤
      (L.map fun ℓ => 16 * (d ^ indexWeight ℓ * (((2 : ℝ) ^ n) ^ indexWeight ℓ *
            ((((2 : ℝ) ^ n)⁻¹ ^ 2) * (wI ℓ + wI' ℓ))))).sum := by
    rw [← List.sum_map_mul_right, ← List.sum_map_add]
    refine List.sum_le_sum fun ℓ _ => ?_
    have h1 := hI ℓ
    have h2 := hI' ℓ
    have hT : 0 ≤ d ^ indexWeight ℓ * ((2 : ℝ) ^ n) ^ indexWeight ℓ := by positivity
    have hlam : (q + d) ^ 4 ≤ 16 * (((2 : ℝ) ^ n) ^ 2)⁻¹ ^ 2 := by
      refine hlam4.trans (le_of_eq ?_)
      ring
    have e : (d ^ indexWeight ℓ * (((2 : ℝ) ^ n) ^ indexWeight ℓ * (((2 : ℝ) ^ n) ^ 2 * wI' ℓ))) *
        (q + d) ^ 4 ≤ (d ^ indexWeight ℓ * ((2 : ℝ) ^ n) ^ indexWeight ℓ) *
          (((2 : ℝ) ^ n) ^ 2 * wI' ℓ) * (16 * (((2 : ℝ) ^ n) ^ 2)⁻¹ ^ 2) := by
      have : (d ^ indexWeight ℓ * (((2 : ℝ) ^ n) ^ indexWeight ℓ * (((2 : ℝ) ^ n) ^ 2 * wI' ℓ))) =
          (d ^ indexWeight ℓ * ((2 : ℝ) ^ n) ^ indexWeight ℓ) * (((2 : ℝ) ^ n) ^ 2 * wI' ℓ) := by
        ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hlam (by positivity)
    have e2 : (d ^ indexWeight ℓ * ((2 : ℝ) ^ n) ^ indexWeight ℓ) *
          (((2 : ℝ) ^ n) ^ 2 * wI' ℓ) * (16 * (((2 : ℝ) ^ n) ^ 2)⁻¹ ^ 2) =
        16 * (d ^ indexWeight ℓ * (((2 : ℝ) ^ n) ^ indexWeight ℓ *
          ((((2 : ℝ) ^ n)⁻¹ ^ 2) * wI' ℓ))) := by
      field_simp
    have e3 : 0 ≤ d ^ indexWeight ℓ * (((2 : ℝ) ^ n) ^ indexWeight ℓ *
          ((((2 : ℝ) ^ n)⁻¹ ^ 2) * wI ℓ)) := by positivity
    have e4 : 0 ≤ d ^ indexWeight ℓ * (((2 : ℝ) ^ n) ^ indexWeight ℓ *
          ((((2 : ℝ) ^ n)⁻¹ ^ 2) * wI' ℓ)) := by positivity
    linarith [e, e2]
  have hT0 : 0 ≤ (L.map fun ℓ => 16 * (d ^ indexWeight ℓ * (((2 : ℝ) ^ n) ^ indexWeight ℓ *
      ((((2 : ℝ) ^ n)⁻¹ ^ 2) * (wI ℓ + wI' ℓ))))).sum := by
    refine List.sum_nonneg fun x hx => ?_
    obtain ⟨ℓ, -, rfl⟩ := List.mem_map.1 hx
    have := hI ℓ
    have := hI' ℓ
    positivity
  have hq0 : 0 ≤ q ^ γ := Real.rpow_nonneg hq.le _
  have hlam0 : 0 ≤ (q + d) ^ γ := Real.rpow_nonneg (by linarith) _
  have hPq : Pw * (q + d) ^ γ ≤ Pw * ((2 : ℝ) ^ |γ| * q ^ γ) :=
    mul_le_mul_of_nonneg_left hγ hPw
  calc _ ≤ C * (Pw * (q + d) ^ γ) * (L.map fun ℓ => 16 * (d ^ indexWeight ℓ *
          (((2 : ℝ) ^ n) ^ indexWeight ℓ * ((((2 : ℝ) ^ n)⁻¹ ^ 2) * (wI ℓ + wI' ℓ))))).sum :=
        mul_le_mul_of_nonneg_left hrewrite (by positivity)
    _ ≤ C * (Pw * ((2 : ℝ) ^ |γ| * q ^ γ)) * (L.map fun ℓ => 16 * (d ^ indexWeight ℓ *
          (((2 : ℝ) ^ n) ^ indexWeight ℓ * ((((2 : ℝ) ^ n)⁻¹ ^ 2) * (wI ℓ + wI' ℓ))))).sum :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPq hC) hT0
    _ = _ := by
        rw [mul_assoc, ← List.sum_map_mul_left]
        congr 1
        congr 1
        refine List.map_congr_left fun ℓ _ => ?_
        rw [two_rpow_deg_eq, ← hqn]
        ring

theorem exists_abs_pairing_taylorKernel_le {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h)
    (hs : ∀ z, 1 < parabolicNorm z → h z = 0) {γ : ℝ} {A : Finset ℝ}
    (hA : ∀ a ∈ A, -4 < a ∧ a ≤ γ) :
    ∃ (𝔈 : List (List (Fin 4))) (κ : List (Fin 4) → ℝ), (∀ ℓ, 0 ≤ κ ℓ) ∧
      (∀ ℓ ∈ 𝔈, γ + 2 ≤ (indexWeight ℓ : ℝ) ∧
        ((∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) ≠ γ + 2) → γ + 2 < (indexWeight ℓ : ℝ))) ∧
      ∀ {Λ : ℝ → ParabolicSpace → ℝ} {C : ℝ} {x y : ParabolicSpace},
        Λ ∈ parabolicSemigroup.distributions → (∀ u, 0 < u → Measurable (Λ u)) → 0 ≤ C →
        parabolicSemigroup.IsLocalOrder Λ x γ A C → ∀ n : ℕ,
        parabolicNorm (y - x) ≤ (2 : ℝ)⁻¹ ^ n →
        |parabolicSemigroup.pairing Λ (taylorKernel h n (γ + 2) x y)| ≤
          C * (𝔈.map fun ℓ => κ ℓ * (parabolicNorm (y - x) ^ indexWeight ℓ *
            (2 : ℝ) ^ (((indexWeight ℓ : ℝ) - γ - 2) * n))).sum := by
  classical
  set σ : ℝ := γ + 2 with hσ
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
    have key := abs_pairing_reflect_le_centre hΛ hΛm hA hC hloc (contDiff_taylorProfile hgs σ z)
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
    refine key.trans ?_
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
