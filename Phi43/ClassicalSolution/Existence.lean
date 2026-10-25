/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.ClassicalSolution.ExistenceBounds

/-!
# Existence of classical solutions (W4, existence half)

Definition 2.6 and item (W4) of Lemma 4.1 of the statement: for `f` smooth on `ℝ × T³`, `c ∈ ℝ` and `u₀`
smooth on `T³`, the equation `∂_t u = Δu - u³ + c u + f`, `u(0) = u₀`, has a classical solution
(`classicalSolution_exists`).

## Proof

For `N ∈ ℕ` let `B_N` bound `|f|` on `[0, N] × T³` (made monotone in `N`), let
`L_N = ‖u₀‖ + |c| + B_N + 1` and `K_N = L_N + 1`. The truncated equation with nonlinearity
`χ_{K_N}(u)(-u³ + c u) + f` has a globally Lipschitz smooth nonlinearity, so it has a continuous
mild solution `U_N` on `[0, N]` (`exists_isMildSolution`), which is smooth and classical on
`(0, N) × T³` (`contDiffOn_of_isMildSolution`, `hasDerivAt_of_isMildSolution`). The maximum
principle gives `|U_M| < L_N` on `[0, N)` for `M ≥ N` (`abs_lt_of_isMildSolution_cutoff`), so the
truncation is inactive and, by uniqueness of mild solutions, `U_M = U_N` on `[0, N - 1]`. The
solution is `u(t) = U_{⌈t⌉₊ + 1}(t)`; near any time `t₀ ≥ 0` it coincides with `U_{⌈t₀⌉₊ + 2}`.
-/

open scoped ContDiff

public section

namespace RegularityStructures.Phi43

open RegularityStructures.PDE Set Filter Topology

theorem exists_abs_le_of_isSmoothOnSpaceTime {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    (T : ℝ) : ∃ B, ∀ t ∈ Icc 0 T, ∀ x, |f (t, x)| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (isCompact_univ (X := Torus3))).exists_bound_of_continuousOn
    (continuous_of_isSmoothOnSpaceTime hf).continuousOn
  exact ⟨B, fun t ht x => by simpa using hB (t, x) ⟨ht, mem_univ _⟩⟩

/-- Second partial derivatives along coordinate lines. -/
theorem deriv_deriv_update_eq {g : C(Torus3, ℝ)} {Dg : C(Torus3, Fin 3 → ℝ)}
    {D2g : C(Torus3, Fin 3 → Fin 3 → ℝ)} (hg : HasTorusDeriv g Dg)
    (hDg : HasTorusDeriv (E := Fin 3 → ℝ) Dg D2g) (y : Fin 3 → ℝ) (i : Fin 3) :
    deriv (deriv fun r => g (torusProj (Function.update y i r))) (y i) =
      D2g (torusProj y) i i := by
  have hφ' : deriv (fun r => g (torusProj (Function.update y i r))) =
      fun r => Dg (torusProj (Function.update y i r)) i :=
    funext fun r => (hasDerivAt_update_of_hasTorusDeriv hg y i r).deriv
  rw [hφ']
  have h := hasDerivAt_update_of_hasTorusDeriv (E := Fin 3 → ℝ) hDg y i (y i)
  simp only [Function.update_eq_self] at h
  exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp_hasDerivAt
    (y i) h).deriv

/-- **Existence of classical solutions** (item (W4) of Lemma 4.1 of the statement, existence half): for `f`
smooth on `ℝ × T³`, `c ∈ ℝ` and `u₀` smooth on `T³`, the equation `∂_t u = Δu - u³ + c u + f`
with `u(0) = u₀` has a classical solution in the sense of Definition 2.6. -/
theorem classicalSolution_exists (c : ℝ) {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    {u₀ : C(Torus3, ℝ)} (hu₀ : IsSmoothOnTorus u₀) :
    ∃ u : ℝ → C(Torus3, ℝ), IsClassicalSolution c f u₀ u := by
  -- monotone bounds on the forcing
  choose B hB using fun N : ℕ => exists_abs_le_of_isSmoothOnSpaceTime hf (N : ℝ)
  set Bm : ℕ → ℝ := fun N => ∑ k ∈ Finset.range (N + 1), |B k| with hBmdef
  have hBm0 : ∀ N, 0 ≤ Bm N := fun N => Finset.sum_nonneg fun k _ => abs_nonneg (B k)
  have hBm : ∀ N : ℕ, ∀ t ∈ Icc 0 (N : ℝ), ∀ x, |f (t, x)| ≤ Bm N := fun N t ht x =>
    (hB N t ht x).trans ((le_abs_self _).trans (Finset.single_le_sum
      (f := fun k => |B k|) (fun k _ => abs_nonneg (B k)) (Finset.self_mem_range_succ N)))
  have hBmono : Monotone Bm := fun N M hNM => Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.2 (by omega)) fun _ _ _ => abs_nonneg _
  -- levels and truncation radii
  set L : ℕ → ℝ := fun N => ‖u₀‖ + (|c| + Bm N + 1) with hLdef
  set K : ℕ → ℝ := fun N => L N + 1 with hKdef
  have hLR : ∀ N, |c| + Bm N + 1 ≤ L N := fun N => le_add_of_nonneg_left (norm_nonneg _)
  have hLmono : Monotone L := fun N M hNM => by
    simp only [hLdef]
    linarith [hBmono hNM]
  have hu₀L : ∀ N x, |u₀ x| < L N := fun N x => by
    have h1 : |u₀ x| ≤ ‖u₀‖ := by rw [← Real.norm_eq_abs]; exact u₀.norm_coe_le_norm x
    have h2 := hBm0 N
    simp only [hLdef]
    linarith [abs_nonneg c]
  have hKpos : ∀ N, 0 < K N := fun N => by
    have := (abs_nonneg (u₀ 0)).trans_lt (hu₀L N 0)
    simp only [hKdef]
    linarith
  -- the truncated solutions
  have hex : ∀ N : ℕ, ∃ U : ℝ → C(Torus3, ℝ), Continuous U ∧
      IsMildSolution (cutoffNonlin c (K N) (hKpos N) hf) u₀ N U := fun N => by
    obtain ⟨Lip, hLip⟩ := exists_lipschitzWith_cutoffNonlin c (K N) (hKpos N) hf
    exact exists_isMildSolution _ u₀ (Nat.cast_nonneg N) fun s _ x => hLip s x
  choose U hUc hUm using hex
  -- a priori bounds
  have hbound : ∀ N M : ℕ, N ≤ M → ∀ t : ℝ, 0 ≤ t → t < N → ∀ x, |U M t x| < L N := by
    intro N M hNM t ht0 htN x
    have hLK : L N ≤ K M := by
      simp only [hKdef]
      linarith [hLmono hNM]
    exact abs_lt_of_isMildSolution_cutoff (hKpos M) hf hu₀ (Nat.cast_nonneg M) (hUc M) (hUm M)
      hLK (hLR N) (hu₀L N) (fun s hs x => hBm N s ⟨hs.1, hs.2.trans htN.le⟩ x)
      (htN.trans_le (Nat.cast_le.2 hNM)) t ⟨ht0, le_rfl⟩ x
  -- agreement of the truncated solutions
  have hagree : ∀ N M : ℕ, N ≤ M → ∀ t ∈ Icc 0 ((N : ℝ) - 1), U N t = U M t := by
    intro N M hNM
    have hNM' : (N : ℝ) ≤ M := Nat.cast_le.2 hNM
    refine eqOn_of_isMildSolution_cutoff (hKpos N) (hKpos M) hf (hUc N) (hUc M) (hUm N) (hUm M)
      (by linarith) (by linarith) fun t ht x => ?_
    have h := (hbound N M hNM t ht.1 (by linarith [ht.2]) x).le
    have h1 : L N ≤ K N := by simp only [hKdef]; linarith
    have h2 : L N ≤ K M := by simp only [hKdef]; linarith [hLmono hNM]
    exact le_min (h.trans h1) (h.trans h2)
  -- the glued solution
  set u : ℝ → C(Torus3, ℝ) := fun t => U (⌈t⌉₊ + 1) t with hudef
  have hlocal : ∀ t₀ t : ℝ, 0 ≤ t → t < t₀ + 1 → u t = U (⌈t₀⌉₊ + 2) t := by
    intro t₀ t ht0 ht
    have hle : ⌈t⌉₊ + 1 ≤ ⌈t₀⌉₊ + 2 := by
      have h1 : ⌈t⌉₊ ≤ ⌈t₀ + 1⌉₊ := Nat.ceil_le_ceil ht.le
      have h2 : ⌈t₀ + 1⌉₊ ≤ ⌈t₀⌉₊ + ⌈(1 : ℝ)⌉₊ := Nat.ceil_add_le t₀ 1
      simp only [Nat.ceil_one] at h2
      omega
    refine hagree _ _ hle t ⟨ht0, ?_⟩
    push_cast
    linarith [Nat.le_ceil t]
  have hlt : ∀ t₀ : ℝ, t₀ < ((⌈t₀⌉₊ + 2 : ℕ) : ℝ) := fun t₀ => by
    push_cast
    linarith [Nat.le_ceil t₀]
  refine ⟨u, ⟨?_, ?_, ?_, ?_⟩⟩
  · -- continuity on `[0, ∞) × T³`
    intro z hz
    set N₁ := ⌈z.1⌉₊ + 2
    have hcont : Continuous fun z : ℝ × Torus3 => U N₁ z.1 z.2 :=
      continuous_eval.comp (((hUc N₁).comp continuous_fst).prodMk continuous_snd)
    refine hcont.continuousAt.continuousWithinAt.congr_of_eventuallyEq ?_
      (congrArg (fun g : C(Torus3, ℝ) => g z.2) (hlocal z.1 z.1 hz.1 (lt_add_one _)))
    have hnhds : {z' : ℝ × Torus3 | z'.1 < z.1 + 1} ∈ 𝓝 z :=
      continuous_fst.continuousAt.preimage_mem_nhds (Iio_mem_nhds (lt_add_one z.1))
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hnhds] with z' hz' hz''
    exact congrArg (fun g : C(Torus3, ℝ) => g z'.2) (hlocal z.1 z'.1 hz'.1 hz'')
  · -- the initial condition
    show U (⌈(0 : ℝ)⌉₊ + 1) 0 = u₀
    rw [hUm _ 0 ⟨le_rfl, Nat.cast_nonneg _⟩, heatOp_zero_left, duhamel_zero, add_zero]
  · -- smoothness on `(0, ∞) × T³`
    intro p hp
    set N₁ := ⌈p.1⌉₊ + 2
    have hsm := contDiffOn_of_isMildSolution (contDiff_nonlinLift_cutoffNonlin c (K N₁)
      (hKpos N₁) hf) hu₀ (Nat.cast_nonneg N₁) (hUc N₁) (hUm N₁)
    have hpΩ : p ∈ Ioo 0 (N₁ : ℝ) ×ˢ (univ : Set (Fin 3 → ℝ)) := ⟨⟨hp.1, hlt p.1⟩, mem_univ _⟩
    have hat := hsm.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hpΩ)
    refine (hat.congr_of_eventuallyEq ?_).contDiffWithinAt
    have hnhds : Ioo 0 (p.1 + 1) ×ˢ (univ : Set (Fin 3 → ℝ)) ∈ 𝓝 p :=
      (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨hp.1, lt_add_one _⟩, mem_univ _⟩
    filter_upwards [hnhds] with q hq
    exact congrArg (fun g : C(Torus3, ℝ) => g (torusProj q.2))
      (hlocal p.1 q.1 hq.1.1.le hq.1.2)
  · -- the equation
    intro t ht y
    set N₁ := ⌈t⌉₊ + 2
    obtain ⟨w, w2, -, -, hdw, hdw2, hdt⟩ := hasDerivAt_of_isMildSolution
      (contDiff_nonlinLift_cutoffNonlin c (K N₁) (hKpos N₁) hf) hu₀ (Nat.cast_nonneg N₁)
      (hUc N₁) (hUm N₁)
    have htI : t ∈ Ioo 0 (N₁ : ℝ) := ⟨ht, hlt t⟩
    have hut : u t = U N₁ t := hlocal t t ht.le (lt_add_one t)
    -- the time derivative
    have hev : (fun s => u s (torusProj y)) =ᶠ[𝓝 t] fun s => U N₁ s (torusProj y) := by
      filter_upwards [Ioo_mem_nhds ht (lt_add_one t)] with s hs
      exact congrArg (fun g : C(Torus3, ℝ) => g (torusProj y)) (hlocal t s hs.1.le hs.2)
    rw [hev.deriv_eq, (hdt t htI (torusProj y)).deriv, hut, cutoffNonlin_apply]
    -- the truncation is inactive
    have hvb : |U N₁ t (torusProj y)| ≤ K N₁ := by
      have := hbound N₁ N₁ le_rfl t ht.le (hlt t) (torusProj y)
      simp only [hKdef]
      linarith
    rw [truncCubic_eq (hKpos N₁) hvb]
    -- the spatial second derivatives
    have hsum : ∑ i, deriv (deriv fun r => U N₁ t (torusProj (Function.update y i r))) (y i) =
        torusLap (w2 t) (torusProj y) := by
      rw [torusLap_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hI : t ∈ Icc 0 (N₁ : ℝ) := Ioo_subset_Icc_self htI
      exact deriv_deriv_update_eq (hdw t hI) (hdw2 t hI) y i
    rw [hsum]
    ring

end RegularityStructures.Phi43

end
