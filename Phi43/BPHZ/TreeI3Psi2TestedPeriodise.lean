/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.ClassicalSolution.PeriodiseRegularity
public import Phi43.Torus.KernelBoundsMollifier
public import Phi43.Torus.KernelBoundsCovariance
public import RegularityStructures.PDE.TorusLift
public import RegularityStructures.PDE.SmoothDense

/-!
# A uniform Lipschitz bound for the periodised mollifier

For a mollifier `ρ`, `|ρ_ε^♯(z + h) - ρ_ε^♯(z)| ≤ C ε⁻⁶ s(h)` for `ε ∈ (0, 1]`, all `z, h`, where
`s = torusParabolicSize`.  Both `ρ_ε^♯(z + h)` and `ρ_ε^♯(z)` are lattice sums, and after the shift
of the lattice index by an integer vector the two sums have corresponding terms at spatial
arguments differing by the centred representative of `h.2`.
-/

public section

open scoped ContDiff

namespace RegularityStructures.Phi43

open RegularityStructures

/-- Lipschitz bound for `rescale ρ ε` for increments with `|Δt| ≤ ε δ`, `|Δy_i| ≤ δ`. -/
private theorem abs_rescale_sub_le {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {L : NNReal}
    (hL : LipschitzWith L ρ) {ε : ℝ} (hε : 0 < ε) {t t' : ℝ} {y y' : Fin 3 → ℝ} {δ : ℝ}
    (ht : |t' - t| ≤ ε * δ) (hy : ∀ i, |y' i - y i| ≤ δ) :
    |rescale ρ ε (t', y') - rescale ρ ε (t, y)| ≤ (L : ℝ) * ε ^ (-6 : ℤ) * δ := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hy 0)
  have hd : dist ((ε ^ (-2 : ℤ) * t', ε⁻¹ • y') : ℝ × (Fin 3 → ℝ))
      (ε ^ (-2 : ℤ) * t, ε⁻¹ • y) ≤ δ / ε := by
    rw [Prod.dist_eq]
    refine max_le ?_ ?_
    · rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (zpow_pos hε _)]
      calc ε ^ (-2 : ℤ) * |t' - t| ≤ ε ^ (-2 : ℤ) * (ε * δ) :=
            mul_le_mul_of_nonneg_left ht (zpow_pos hε _).le
        _ = δ / ε := by
          rw [zpow_neg, zpow_two]
          field_simp
    · refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
      rw [Real.dist_eq]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hε)]
      calc ε⁻¹ * |y' i - y i| ≤ ε⁻¹ * δ := mul_le_mul_of_nonneg_left (hy i) (inv_pos.2 hε).le
        _ = δ / ε := by rw [div_eq_inv_mul]
  have h1 := hL.dist_le_mul ((ε ^ (-2 : ℤ) * t', ε⁻¹ • y') : ℝ × (Fin 3 → ℝ))
    (ε ^ (-2 : ℤ) * t, ε⁻¹ • y)
  rw [Real.dist_eq] at h1
  unfold rescale
  simp only
  rw [← mul_sub, abs_mul, abs_of_pos (zpow_pos hε _)]
  have h2 : ε ^ (-5 : ℤ) * |ρ (ε ^ (-2 : ℤ) * t', ε⁻¹ • y') - ρ (ε ^ (-2 : ℤ) * t, ε⁻¹ • y)| ≤
      ε ^ (-5 : ℤ) * (L * (δ / ε)) :=
    mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left hd L.2)) (zpow_pos hε _).le
  refine h2.trans (le_of_eq ?_)
  rw [show (-6 : ℤ) = -5 + -1 by norm_num, zpow_add₀ hε.ne', zpow_neg_one]
  field_simp

/-- A finite box of lattice indices outside which all the lattice terms vanish. -/
private theorem exists_box_rescale_eq_zero {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) :
    ∃ S : Finset (Fin 3 → ℤ), ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      (∀ i, |y i| ≤ 2) → ∀ k ∉ S, rescale ρ ε (t, y + fun i => (k i : ℝ)) = 0 := by
  obtain ⟨R, hR, hbox⟩ := exists_mollifier_support_box ρ hρ
  let N : ℤ := ⌈R + 2⌉
  have hN : R + 2 ≤ (N : ℝ) := by exact_mod_cast Int.le_ceil (R + 2)
  refine ⟨Fintype.piFinset fun _ => Finset.Icc (-N) N, ?_⟩
  intro ε hε hε1 t y hy k hk
  by_contra hne
  have harg : (ε ^ (-2 : ℤ) * t, ε⁻¹ • (y + fun i => (k i : ℝ))) ∈ tsupport ρ := by
    by_contra hnot
    apply hne
    unfold rescale
    rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]
  apply hk
  rw [Fintype.mem_piFinset]
  intro i
  have h1 := (hbox _ harg).2 i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] at h1
  have h2 : |y i + (k i : ℝ)| ≤ R := by
    have : |y i + (k i : ℝ)| = ε * |ε⁻¹ * (y i + (k i : ℝ))| := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hε), ← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]
    rw [this]
    calc ε * |ε⁻¹ * (y i + (k i : ℝ))| ≤ 1 * R :=
          mul_le_mul hε1 h1 (abs_nonneg _) zero_le_one
      _ = R := one_mul R
  have h3 := abs_le.1 h2
  have h4 := abs_le.1 (hy i)
  rw [Finset.mem_Icc]
  constructor
  · have : (-(N : ℝ)) ≤ (k i : ℝ) := by linarith
    exact_mod_cast this
  · have : (k i : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast this

private theorem abs_centered_add_rep_le (x η : Torus3) (i : Fin 3) :
    |(torusRep x + torusCenteredRep η) i| ≤ 2 := by
  have h1 := torusRep_mem_Ico x i
  have h2 := torusCenteredRep_mem_Ico η i
  simp only [Pi.add_apply]
  exact abs_le.2 ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩

private theorem abs_torusRep_le_two (x : Torus3) (i : Fin 3) : |torusRep x i| ≤ 2 := by
  have h1 := torusRep_mem_Ico x i
  exact abs_le.2 ⟨by linarith [h1.1], by linarith [h1.2]⟩

/-- Reindexing of the lattice sum of `ρ_ε^♯(z + h)`. -/
private theorem periodise_add_eq_tsum (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (t τ : ℝ)
    (x η : Torus3) :
    periodise ρ ε (t + τ, x + η) =
      ∑' k : Fin 3 → ℤ, rescale ρ ε (t + τ,
        torusRep x + torusCenteredRep η + fun i => (k i : ℝ)) := by
  have hp : torusProj (torusRep x + torusCenteredRep η) = torusProj (torusRep (x + η)) := by
    funext i
    simp only [torusProj, Pi.add_apply, AddCircle.coe_add]
    have h1 := congrFun (PDE.torusProj_torusRep x) i
    have h2 := congrFun (torusProj_torusCenteredRep η) i
    have h3 := congrFun (PDE.torusProj_torusRep (x + η)) i
    simp only [torusProj] at h1 h2 h3
    rw [h1, h2, h3]
    rfl
  choose m hm using fun i => PDE.exists_int_of_torusProj_eq hp i
  unfold periodise
  rw [← (Equiv.addRight m).tsum_eq (fun k : Fin 3 → ℤ => rescale ρ ε (t + τ,
    torusRep x + torusCenteredRep η + fun i => (k i : ℝ)))]
  refine tsum_congr fun k => ?_
  congr 2
  funext i
  simp only [Equiv.coe_addRight, Pi.add_apply, Int.cast_add, hm i]
  ring

/-- **Uniform Lipschitz bound for the periodised mollifier.** -/
theorem periodise_sub_abs_le_uniform (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ z h : SpaceTime,
      |periodise ρ ε (z + h) - periodise ρ ε z| ≤ C * ε ^ (-6 : ℤ) * torusParabolicSize h := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hρ.hasCompactSupport
    hρ.contDiff (by simp)
  obtain ⟨S, hS⟩ := exists_box_rescale_eq_zero hρ
  obtain ⟨D, hD, hDb⟩ := periodise_uniform_bound ρ hρ
  refine ⟨max ((S.card : ℝ) * L) (2 * D), by positivity, ?_⟩
  intro ε hε hε1 z h
  obtain ⟨t, x⟩ := z
  obtain ⟨τ, η⟩ := h
  set s := torusParabolicSize (τ, η) with hs
  have hs0 : 0 ≤ s := torusParabolicSize_nonneg _
  have hε6 : 0 < ε ^ (-6 : ℤ) := zpow_pos hε _
  have hε5 : ε ^ (-5 : ℤ) = ε ^ (-6 : ℤ) * ε := by
    rw [show (-5 : ℤ) = -6 + 1 by norm_num, zpow_add₀ hε.ne', zpow_one]
  by_cases hsε : s ≤ ε
  · -- small increment: Lipschitz termwise
    have hsq : |τ| ≤ ε * s := by
      have : √|τ| ≤ s := by
        rw [hs]; unfold torusParabolicSize
        simp only
        linarith [torusSpatialNorm_nonneg η]
      have h2 : |τ| ≤ s ^ 2 := by
        calc |τ| = √|τ| ^ 2 := (Real.sq_sqrt (abs_nonneg _)).symm
          _ ≤ s ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) this 2
      calc |τ| ≤ s ^ 2 := h2
        _ = s * s := sq s
        _ ≤ s * ε := mul_le_mul_of_nonneg_left hsε hs0
        _ = ε * s := mul_comm _ _
    have hcoord : ∀ i, |torusCenteredRep η i| ≤ s := by
      intro i
      refine torusSpatialNorm_coord_le η s ?_ i
      rw [hs]; unfold torusParabolicSize
      simp only
      linarith [Real.sqrt_nonneg |τ|]
    rw [show (t, x) + (τ, η) = (t + τ, x + η) from rfl, periodise_add_eq_tsum]
    unfold periodise
    have hsum1 : ∑' k : Fin 3 → ℤ, rescale ρ ε (t + τ,
        torusRep x + torusCenteredRep η + fun i => (k i : ℝ)) =
        ∑ k ∈ S, rescale ρ ε (t + τ,
          torusRep x + torusCenteredRep η + fun i => (k i : ℝ)) :=
      tsum_eq_sum fun k hk => hS hε hε1 _ _ (abs_centered_add_rep_le x η) k hk
    have hsum0 : ∑' k : Fin 3 → ℤ, rescale ρ ε (t, torusRep x + fun i => (k i : ℝ)) =
        ∑ k ∈ S, rescale ρ ε (t, torusRep x + fun i => (k i : ℝ)) :=
      tsum_eq_sum fun k hk => hS hε hε1 _ _ (abs_torusRep_le_two x) k hk
    rw [hsum1, hsum0, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ k ∈ S, |rescale ρ ε (t + τ,
        torusRep x + torusCenteredRep η + fun i => (k i : ℝ)) -
        rescale ρ ε (t, torusRep x + fun i => (k i : ℝ))| ≤ (L : ℝ) * ε ^ (-6 : ℤ) * s := by
      intro k _
      refine abs_rescale_sub_le hL hε (δ := s) ?_ ?_
      · simpa using hsq
      · intro i
        simp only [Pi.add_apply]
        rw [show torusRep x i + torusCenteredRep η i + (k i : ℝ) - (torusRep x i + (k i : ℝ)) =
          torusCenteredRep η i by ring]
        exact hcoord i
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    calc (S.card : ℝ) * ((L : ℝ) * ε ^ (-6 : ℤ) * s)
        = ((S.card : ℝ) * L) * ε ^ (-6 : ℤ) * s := by ring
      _ ≤ max ((S.card : ℝ) * L) (2 * D) * ε ^ (-6 : ℤ) * s := by
        gcongr
        exact le_max_left _ _
  · -- large increment: trivial bound
    have hsε' : ε < s := lt_of_not_ge hsε
    have h1 := hDb hε hε1 (t + τ, x + η)
    have h2 := hDb hε hε1 (t, x)
    have h3 : |periodise ρ ε ((t, x) + (τ, η)) - periodise ρ ε (t, x)| ≤
        2 * D * ε ^ (-5 : ℤ) := by
      refine (abs_sub _ _).trans ?_
      have : (t, x) + (τ, η) = (t + τ, x + η) := rfl
      rw [this]
      linarith
    refine h3.trans ?_
    rw [hε5]
    calc 2 * D * (ε ^ (-6 : ℤ) * ε) = (2 * D) * ε ^ (-6 : ℤ) * ε := by ring
      _ ≤ max ((S.card : ℝ) * L) (2 * D) * ε ^ (-6 : ℤ) * s := by
        gcongr
        exact le_max_right _ _

end RegularityStructures.Phi43

end
