/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Remainder.Cutoff
public import RegularityStructures.Abstract.Singular.TaylorKernel.ProfileDeriv
public import RegularityStructures.Analysis.Kernel.GeneratorLip
public import RegularityStructures.Analysis.Heat.Schauder.TaylorRegime

/-!
# Decay of the derivatives of the parabolic Taylor remainder profile

Quantitative form of `exists_norm_iteratedFDeriv_taylorProfile_le`: the constant only depends on
`σ` and on a bound `S` for the derivatives of `G` up to a fixed order
(`exists_norm_iteratedFDeriv_taylorProfile_le_of_sup`).  Combined with the cutoff localisation
this gives the decay bound `C B ‖s‖^σ (1 + |u'|²)^{-3}` for the derivatives of
`taylorProfile G σ s` at `u`, if `G` has `RemDecay` (`exists_remDecay_taylorProfile`).
-/

public section

open scoped ContDiff
open Filter Topology

namespace RegularityStructures

theorem norm_le_one_of_parabolicNorm_le_one {s : ParabolicSpace} (hs : parabolicNorm s ≤ 1) :
    ‖s‖ ≤ 1 := by
  have h1 : |s.1| ≤ 1 := by
    have h2 : Real.sqrt |s.1| ≤ 1 := by
      have : 0 ≤ ∑ i, |s.2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      unfold parabolicNorm at hs; linarith
    have := (Real.sqrt_le_iff.1 h2).2
    simpa using this
  exact (norm_le_parabolicNorm h1).trans hs

theorem exists_norm_iteratedFDeriv_taylorProfile_le_of_sup {σ : ℝ} (hσ : 0 < σ) :
    ∃ (K : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ {G : ParabolicSpace → ℝ}, ContDiff ℝ ∞ G → HasCompactSupport G →
      ∀ {S : ℝ}, 0 ≤ S → (∀ N ≤ K, ∀ u, ‖iteratedFDeriv ℝ N G u‖ ≤ S) →
      ∀ s : ParabolicSpace, parabolicNorm s ≤ 1 → ∀ j ≤ 4, ∀ u : ParabolicSpace,
        ‖iteratedFDeriv ℝ j (taylorProfile G σ s) u‖ ≤ C * S * parabolicNorm s ^ σ := by
  obtain ⟨E, hEσ, hE⟩ := exists_abs_taylorProfile_le_sup σ
  refine ⟨(E.map List.length).sum + 4, 5 * E.length, by positivity,
    fun {G} hG hGc {S} hS0 hS s hs j hj u => ?_⟩
  set d : ℝ := parabolicNorm s with hd
  have hd0 : 0 ≤ d := parabolicNorm_nonneg _
  have hdσ : 0 ≤ d ^ σ := Real.rpow_nonneg hd0 _
  have hbd : ∀ N : ℕ, ∃ S' : ℝ, ∀ u, ‖iteratedFDeriv ℝ N G u‖ ≤ S' := fun N => by
    obtain ⟨S', -, h⟩ := hGc.exists_bound_iteratedFDeriv hG N
    exact ⟨S', fun u => h N le_rfl u⟩
  choose Sb hSb using hbd
  set Bf : List (Fin 4) → ℝ := fun ℓ =>
    if ℓ.length + j ≤ (E.map List.length).sum + 4 then S else Sb (ℓ.length + j) with hBf
  refine norm_iteratedFDeriv_le_of_lineIter (contDiff_taylorProfile hG σ s) j u
    (by positivity) fun L hL hL1 => ?_
  rw [lineIter_taylorProfile hG]
  have hLG : ContDiff ℝ ∞ (lineIter L G) := contDiff_lineIter hG L
  refine (hE hLG Bf (fun ℓ v => ?_) s u d hd0 (fun i => abs_parabolicCoords_le i)).trans ?_
  · rw [← lineIter_append]
    refine (abs_lineIter_le_norm_iteratedFDeriv hG _ ?_ v).trans ?_
    · intro e he
      rcases List.mem_append.1 he with h | h
      · obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
        exact (norm_coordDir i).le
      · exact hL1 e h
    · have hlen : (ℓ.map coordDir ++ L).length = ℓ.length + j := by simp [hL]
      rw [hlen, hBf]
      simp only
      split_ifs with hif
      · exact hS _ hif v
      · exact hSb _ v
  · have h1 : ∀ ℓ ∈ E, d ^ indexWeight ℓ * Bf ℓ ≤ d ^ σ * S := fun ℓ hℓ => by
      have hle : ℓ.length ≤ (E.map List.length).sum :=
        List.le_sum_of_mem (List.mem_map.2 ⟨ℓ, hℓ, rfl⟩)
      have hB : Bf ℓ = S := by
        have hl : ℓ.length + j ≤ (E.map List.length).sum + 4 := by omega
        simp [hBf, hl]
      rw [hB]
      refine mul_le_mul_of_nonneg_right ?_ hS0
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge' hd0 hs hσ.le (hEσ ℓ hℓ)
    calc (E.map fun ℓ => d ^ indexWeight ℓ * Bf ℓ).sum
        ≤ (E.map fun _ => d ^ σ * S).sum := by
          refine List.sum_le_sum fun ℓ hℓ => ?_
          exact h1 ℓ hℓ
      _ = E.length * (d ^ σ * S) := by simp
      _ ≤ 5 * E.length * S * d ^ σ := by
        have : (0 : ℝ) ≤ E.length * (d ^ σ * S) := by positivity
        nlinarith

/-- Decay of the derivatives of the parabolic Taylor remainder profile of a decaying function. -/
theorem exists_remDecay_taylorProfile {σ : ℝ} (hσ : 0 < σ) :
    ∃ (n : ℕ) (c : ℝ), 0 ≤ c ∧ ∀ {G : ParabolicSpace → ℝ} {B τ₀ : ℝ}, ContDiff ℝ ∞ G → 0 ≤ B →
      RemDecay G n τ₀ B → ∀ s : ParabolicSpace, parabolicNorm s ≤ 1 → ∀ j ≤ 4,
      ∀ u : ParabolicSpace, u.1 + 4 ≤ τ₀ →
        ‖iteratedFDeriv ℝ j (taylorProfile G σ s) u‖ ≤ c * B * parabolicNorm s ^ σ * remWt u.2 := by
  obtain ⟨K, C, hC0, hC⟩ := exists_norm_iteratedFDeriv_taylorProfile_le_of_sup hσ
  obtain ⟨c₁, hc₁, hloc⟩ := exists_localize K
  refine ⟨K, C * c₁, by positivity, fun {G B τ₀} hG hB hD s hs j hj u hu => ?_⟩
  obtain ⟨G', hG', hGc, heq, hbd⟩ := hloc hG hB hD u hu
  have hs1 := norm_le_one_of_parabolicNorm_le_one hs
  have hprof : taylorProfile G σ s =ᶠ[𝓝 u] taylorProfile G' σ s := by
    refine Filter.eventuallyEq_of_mem (IsOpen.mem_nhds
      (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const :
        IsOpen {w : ParabolicSpace | ‖w - u‖ < 1}) (by simp)) fun w hw => ?_
    have hw' : ‖w - u‖ < 1 := hw
    have h1 : ‖w + s - u‖ < 3 := by
      have := norm_add_le (w - u) s
      rw [show w + s - u = (w - u) + s by abel]
      linarith
    have h0 : ‖w - u‖ < 3 := by linarith
    have hU : IsOpen {v : ParabolicSpace | ‖v - u‖ < 3} :=
      isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
    unfold taylorProfile
    rw [heq (w + s) h1]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [lineIter_congr_of_isOpen hU (fun v hv => heq v hv) (multiDirs k) w h0]
  rw [(hprof.iteratedFDeriv ℝ j).self_of_nhds]
  have hS0 : 0 ≤ c₁ * B * remWt u.2 := by have := remWt_nonneg u.2; positivity
  have := hC hG' hGc hS0 hbd s hs j hj u
  refine this.trans (le_of_eq ?_)
  ring

end RegularityStructures

end
