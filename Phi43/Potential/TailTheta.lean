/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.TailLattice
public import Phi43.Potential.PairingSum

/-!
# The spatial cell function `θ(v) = bump3 (8 v₂ + 1)` on parabolic space

`θ` is smooth, bounded with all its derivatives of order `≤ 4` (`potThetaConst`), and vanishes
(with all derivatives) when some `|v₂ᵢ| > 1/8` (`iteratedFDeriv_theta_eq_zero`).  The cell `k` of the
spatial partition of unity at spacing `1/8` is `y ↦ θ(y - ((k+1)/8))`-shifted: indeed
`bump3 (8 y₂ - k) = θ (y - z')` for `z' = (·, (k + 1)/8)`.
-/

open scoped ContDiff

public section

open Set

namespace RegularityStructures.Potential

/-- `θ(v) = bump3 (8 v₂ + 1)`, supported in `{|v₂ᵢ| ≤ 1/8}`. -/
@[expose] noncomputable def potTheta (v : ParabolicSpace) : ℝ :=
  bump3 (fun i => 8 * v.2 i + 1)

theorem contDiff_bump3 : ContDiff ℝ ∞ bump3 := by
  unfold bump3
  exact contDiff_prod fun i _ => contDiff_latticeBump.comp (contDiff_apply ℝ ℝ i)

/-- `Θ₁(u) = bump3 (u + 1)`, supported in the closed cube of radius `1` around `0`. -/
@[expose] noncomputable def potTheta1 (u : Fin 3 → ℝ) : ℝ := bump3 (fun i => u i + 1)

theorem contDiff_potTheta1 : ContDiff ℝ ∞ potTheta1 :=
  contDiff_bump3.comp (contDiff_pi.2 fun i => (contDiff_apply ℝ ℝ i).add contDiff_const)

theorem hasCompactSupport_potTheta1 : HasCompactSupport potTheta1 := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin 3 → ℝ) 1) fun u hu => ?_
  by_contra hne
  apply hu
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  obtain ⟨h1, h2⟩ := bump3_ne_zero hne i
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

theorem exists_bound_potTheta1 :
    ∃ M : ℝ, 0 < M ∧ ∀ k ≤ 4, ∀ u, ‖iteratedFDeriv ℝ k potTheta1 u‖ ≤ M := by
  have hb : ∀ k : ℕ, ∃ C : ℝ, ∀ u, ‖iteratedFDeriv ℝ k potTheta1 u‖ ≤ C := by
    intro k
    have hc := (contDiff_potTheta1.continuous_iteratedFDeriv (m := k)
      (by exact_mod_cast le_top)).norm
    obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support
      (hasCompactSupport_potTheta1.iteratedFDeriv k).norm
    exact ⟨C, fun u => by simpa using hC u⟩
  choose C hC using hb
  refine ⟨1 + ∑ k ∈ Finset.range 5, |C k|, ?_, fun k hk u => ?_⟩
  · have := Finset.sum_nonneg (s := Finset.range 5) (f := fun k => |C k|) fun _ _ => abs_nonneg _
    linarith
  · have h1 : |C k| ≤ ∑ k ∈ Finset.range 5, |C k| :=
      Finset.single_le_sum (f := fun k => |C k|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
    linarith [(hC k u).trans (le_abs_self (C k))]

/-- The constant bounding the derivatives of `θ` of order `≤ 4`. -/
@[expose] noncomputable def potThetaConst : ℝ :=
  Classical.choose exists_bound_potTheta1 * 8 ^ 4

theorem potThetaConst_pos : 0 < potThetaConst := by
  unfold potThetaConst
  have := (Classical.choose_spec exists_bound_potTheta1).1
  positivity

theorem potTheta_eq_comp : potTheta =
    potTheta1 ∘ ((8 : ℝ) • ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ)) := by
  funext v
  simp [potTheta, potTheta1]

theorem contDiff_potTheta : ContDiff ℝ ∞ potTheta := by
  rw [potTheta_eq_comp]
  exact contDiff_potTheta1.comp ((8 : ℝ) • ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ)).contDiff

theorem norm_iteratedFDeriv_potTheta_le {k : ℕ} (hk : k ≤ 4) (v : ParabolicSpace) :
    ‖iteratedFDeriv ℝ k potTheta v‖ ≤ potThetaConst := by
  obtain ⟨hM0, hM⟩ := Classical.choose_spec exists_bound_potTheta1
  set L : ParabolicSpace →L[ℝ] (Fin 3 → ℝ) := (8 : ℝ) • ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ)
  rw [potTheta_eq_comp, ContinuousLinearMap.iteratedFDeriv_comp_right (n := k) L
    (contDiff_potTheta1.of_le (by exact_mod_cast le_top)) v (by exact_mod_cast le_refl k)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hL : ‖L‖ ≤ 8 := by
    refine (ContinuousLinearMap.opNorm_smul_le (8 : ℝ) _).trans ?_
    have := ContinuousLinearMap.norm_snd_le ℝ ℝ (Fin 3 → ℝ)
    rw [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
    nlinarith
  have hp : ∏ _i : Fin k, ‖L‖ ≤ 8 ^ 4 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc ‖L‖ ^ k ≤ 8 ^ k := pow_le_pow_left₀ (norm_nonneg _) hL k
      _ ≤ 8 ^ 4 := pow_le_pow_right₀ (by norm_num) hk
  calc _ ≤ ‖iteratedFDeriv ℝ k potTheta1 (L v)‖ * ∏ _i : Fin k, ‖L‖ := by gcongr
    _ ≤ Classical.choose exists_bound_potTheta1 * 8 ^ 4 := by
        gcongr
        exact hM k hk _
    _ = potThetaConst := rfl

theorem potTheta_eq_zero_of_lt {v : ParabolicSpace} {i : Fin 3} (h : 1 / 8 < |v.2 i|) :
    potTheta v = 0 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := bump3_ne_zero hne i
  have := abs_lt.2 (⟨by linarith, by linarith⟩ : -(1 / 8 : ℝ) < v.2 i ∧ v.2 i < 1 / 8)
  linarith

theorem iteratedFDeriv_potTheta_eq_zero (k : ℕ) {v : ParabolicSpace} {i : Fin 3}
    (h : 1 / 8 < |v.2 i|) : iteratedFDeriv ℝ k potTheta v = 0 := by
  have hs : tsupport potTheta ⊆ {w : ParabolicSpace | ∀ i, |w.2 i| ≤ 1 / 8} := by
    refine closure_minimal (fun w hw => ?_) ?_
    · intro i
      by_contra hc
      exact hw (potTheta_eq_zero_of_lt (not_le.1 hc))
    · have : {w : ParabolicSpace | ∀ i, |w.2 i| ≤ 1 / 8} =
          ⋂ i : Fin 3, {w : ParabolicSpace | |w.2 i| ≤ 1 / 8} := by
        ext; simp
      rw [this]
      exact isClosed_iInter fun i => isClosed_le
        (continuous_abs.comp ((continuous_apply i).comp continuous_snd)) continuous_const
  by_contra hne
  have := hs (support_iteratedFDeriv_subset (𝕜 := ℝ) (n := k) hne) i
  linarith

end RegularityStructures.Potential

end
