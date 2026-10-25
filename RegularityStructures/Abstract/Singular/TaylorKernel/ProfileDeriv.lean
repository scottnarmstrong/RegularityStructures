/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TaylorKernel.ProfileSup
public import RegularityStructures.Abstract.Singular.TaylorKernel.IterDeriv
public import RegularityStructures.Analysis.Heat.Schauder.TaylorRegime

/-!
# Derivative bounds for the Taylor remainder profile

For `G` smooth with compact support, `0 < σ` and `‖s‖_𝔰 ≤ 1`, the derivatives of order `j ≤ 4`
of `taylorProfile G σ s` are bounded by `C ‖s‖_𝔰^σ`, with `C` independent of `s`
(`exists_norm_iteratedFDeriv_taylorProfile_le`). The key point is that directional derivatives
commute with the remainder (`lineIter_taylorProfile`), so the bound of
`exists_abs_taylorProfile_le_sup` applies to `D^L G`.

Source: [Hai14] = arXiv:1303.5113v4, proof of Lemma 5.18.
-/

public section

open scoped ContDiff

namespace RegularityStructures

theorem norm_coordDir (i : Fin 4) : ‖coordDir i‖ = 1 := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [coordDir, norm_timeDir]
  · simp [coordDir, norm_spaceDir]

theorem lineIter_lineIter_comm {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g)
    (L K : List ParabolicSpace) : lineIter L (lineIter K g) = lineIter K (lineIter L g) := by
  rw [← lineIter_append, ← lineIter_append]
  exact lineIter_perm hg (List.perm_append_comm)

theorem lineIter_taylorProfile {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g) (σ : ℝ)
    (z : ParabolicSpace) (L : List ParabolicSpace) :
    lineIter L (taylorProfile g σ z) = taylorProfile (lineIter L g) σ z := by
  have hs : ContDiff ℝ ∞ fun u => g (u + z) := hg.comp (contDiff_id.add contDiff_const)
  have hsum : ∀ k ∈ taylorIdx σ, ContDiff ℝ ∞ fun u =>
      (evalParabolic (MvPolynomial.monomial k 1) z / multiFact k) * lineIter (multiDirs k) g u :=
    fun k _ => contDiff_const.mul (contDiff_lineIter hg _)
  unfold taylorProfile
  rw [lineIter_sub hs (ContDiff.sum hsum), lineIter_shift,
    lineIter_finset_sum _ hsum]
  funext u
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [lineIter_const_mul (contDiff_lineIter hg _), lineIter_lineIter_comm hg]

theorem exists_norm_iteratedFDeriv_taylorProfile_le {G : ParabolicSpace → ℝ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ParabolicSpace), parabolicNorm s ≤ 1 → ∀ j ≤ 4,
      ∀ u : ParabolicSpace,
        ‖iteratedFDeriv ℝ j (taylorProfile G σ s) u‖ ≤ C * parabolicNorm s ^ σ := by
  obtain ⟨E, hEσ, hE⟩ := exists_abs_taylorProfile_le_sup σ
  have hS : ∀ N : ℕ, ∃ B : ℝ, ∀ u, ‖iteratedFDeriv ℝ N G u‖ ≤ B := fun N => by
    obtain ⟨B, hB⟩ := (hG.continuous_iteratedFDeriv (m := N)
      (by exact_mod_cast le_top)).norm.bounded_above_of_compact_support (hc.iteratedFDeriv N).norm
    exact ⟨B, fun u => by simpa using hB u⟩
  choose S hS using hS
  have hS0 : ∀ N, 0 ≤ S N := fun N => (norm_nonneg _).trans (hS N 0)
  set T : ℕ → ℝ := fun j => (E.map fun ℓ => S (ℓ.length + j)).sum with hT
  have hT0 : ∀ j, 0 ≤ T j := fun j =>
    List.sum_nonneg fun x hx => by
      obtain ⟨ℓ, -, rfl⟩ := List.mem_map.1 hx
      exact hS0 _
  refine ⟨∑ j ∈ Finset.range 5, T j, Finset.sum_nonneg fun j _ => hT0 j, ?_⟩
  intro s hs j hj u
  set d : ℝ := parabolicNorm s with hd
  have hd0 : 0 ≤ d := parabolicNorm_nonneg _
  have hTj : T j ≤ ∑ j ∈ Finset.range 5, T j :=
    Finset.single_le_sum (f := T) (fun j _ => hT0 j) (Finset.mem_range.2 (by omega))
  have hC0 : 0 ≤ ∑ j ∈ Finset.range 5, T j := Finset.sum_nonneg fun j _ => hT0 j
  have hdσ : 0 ≤ d ^ σ := Real.rpow_nonneg hd0 _
  refine norm_iteratedFDeriv_le_of_lineIter (contDiff_taylorProfile hG σ s) j u
    (mul_nonneg hC0 hdσ) fun L hL hL1 => ?_
  rw [lineIter_taylorProfile hG]
  have hLG : ContDiff ℝ ∞ (lineIter L G) := contDiff_lineIter hG L
  refine (hE hLG (fun ℓ => S (ℓ.length + j)) (fun ℓ v => ?_) s u d hd0
    (fun i => abs_parabolicCoords_le i)).trans ?_
  · rw [← lineIter_append]
    refine (abs_lineIter_le_norm_iteratedFDeriv hG _ ?_ v).trans ?_
    · intro e he
      rcases List.mem_append.1 he with h | h
      · obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
        exact (norm_coordDir i).le
      · exact hL1 e h
    · have : (ℓ.map coordDir ++ L).length = ℓ.length + j := by simp [hL]
      rw [this]
      exact hS _ v
  · have h1 : ∀ ℓ ∈ E, d ^ indexWeight ℓ ≤ d ^ σ := fun ℓ hℓ => by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge' hd0 hs hσ.le (hEσ ℓ hℓ)
    calc (E.map fun ℓ => d ^ indexWeight ℓ * S (ℓ.length + j)).sum
        ≤ (E.map fun ℓ => d ^ σ * S (ℓ.length + j)).sum := by
          refine List.sum_le_sum fun ℓ hℓ => ?_
          exact mul_le_mul_of_nonneg_right (h1 ℓ hℓ) (hS0 _)
      _ = d ^ σ * T j := by rw [hT, List.sum_map_mul_left]
      _ ≤ d ^ σ * ∑ j ∈ Finset.range 5, T j := mul_le_mul_of_nonneg_left hTj hdσ
      _ = _ := mul_comm _ _

end RegularityStructures

end
