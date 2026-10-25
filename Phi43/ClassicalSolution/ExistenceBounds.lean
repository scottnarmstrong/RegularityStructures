/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.ClassicalSolution.ExistenceCutoff
public import RegularityStructures.PDE.MaxPrinciple

/-!
# A priori bounds for the truncated equation

Let `u` be a continuous mild solution of `∂_t u = Δu + χ_K(u)(-u³ + c u) + f` on `[0, T]` with
smooth data. If `|u₀| < L ≤ K` and `L ≥ |c| + B + 1`, where `|f| ≤ B` on `[0, T'] × T³` with
`T' < T`, then `|u| < L` on `[0, T'] × T³` (`abs_lt_of_isMildSolution_cutoff`). The truncation is
then inactive, so `u` solves the cubic equation. Two such solutions with different truncation
levels agree as long as both stay below the smaller level (`eqOn_of_isMildSolution_cutoff`).
-/

open scoped ContDiff

public section

namespace RegularityStructures.Phi43

open RegularityStructures.PDE Set Filter Topology

theorem torusLap_neg (D2g : C(Torus3, Fin 3 → Fin 3 → ℝ)) : torusLap (-D2g) = -torusLap D2g := by
  ext x
  simp [torusLap_apply, Finset.sum_neg_distrib]

/-- **A priori bound** for the truncated equation, from the maximum principle. -/
theorem abs_lt_of_isMildSolution_cutoff {c K B L T T' : ℝ} (hK : 0 < K) {f : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) {u₀ : C(Torus3, ℝ)} (hu₀ : IsSmoothOnTorus u₀) (hT : 0 ≤ T)
    {u : ℝ → C(Torus3, ℝ)} (hu : Continuous u)
    (hmild : IsMildSolution (cutoffNonlin c K hK hf) u₀ T u) (hLK : L ≤ K)
    (hLR : |c| + B + 1 ≤ L) (hu₀L : ∀ x, |u₀ x| < L)
    (hB : ∀ t ∈ Icc 0 T', ∀ x, |f (t, x)| ≤ B) (hT' : T' < T) :
    ∀ t ∈ Icc 0 T', ∀ x, |u t x| < L := by
  obtain ⟨w, w2, -, -, hdw, hdw2, hdt⟩ := hasDerivAt_of_isMildSolution
    (contDiff_nonlinLift_cutoffNonlin c K hK hf) hu₀ hT hu hmild
  have hu0 : u 0 = u₀ := by
    rw [hmild 0 ⟨le_rfl, hT⟩, heatOp_zero_left, duhamel_zero, add_zero]
  have hIoc : ∀ t ∈ Ioc 0 T', t ∈ Ioo 0 T := fun t ht => ⟨ht.1, ht.2.trans_lt hT'⟩
  have hIcc : ∀ t ∈ Ioc 0 T', t ∈ Icc 0 T := fun t ht => Ioo_subset_Icc_self (hIoc t ht)
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hu₀L 0).le
  -- upper bound
  have hupper := lt_of_maxPrinciple (u := u) (w := w) (w2 := w2) (L := L) (T := T')
    (D := fun t x => torusLap (w2 t) x + cutoffNonlin c K hK hf (t, x, u t x)) hu
    (fun x => by rw [hu0]; exact (le_abs_self _).trans_lt (hu₀L x))
    (fun t ht => hdw t (hIcc t ht)) (fun t ht => hdw2 t (hIcc t ht))
    (fun t ht x => hdt t (hIoc t ht) x) (fun t ht x hx => by
      rw [add_sub_cancel_left, cutoffNonlin_apply, hx,
        truncCubic_eq hK ((abs_of_nonneg hL0).trans_le hLK)]
      exact cubic_add_neg (hB t (Ioc_subset_Icc_self ht) x) hLR)
  -- lower bound, from the maximum principle for `-u`
  have hlower := lt_of_maxPrinciple (u := fun t => -u t) (w := fun t => -w t)
    (w2 := fun t => -w2 t) (L := L) (T := T')
    (D := fun t x => -(torusLap (w2 t) x + cutoffNonlin c K hK hf (t, x, u t x)))
    (continuous_neg.comp hu)
    (fun x => by
      simp only [ContinuousMap.neg_apply, hu0]
      exact (neg_le_abs _).trans_lt (hu₀L x))
    (fun t ht => (hdw t (hIcc t ht)).neg) (fun t ht => (hdw2 t (hIcc t ht)).neg)
    (fun t ht x => by simpa using (hdt t (hIoc t ht) x).fun_neg)
    (fun t ht x hx => by
      simp only [ContinuousMap.neg_apply] at hx
      have hux : u t x = -L := by linarith
      rw [torusLap_neg, ContinuousMap.neg_apply, cutoffNonlin_apply, hux,
        truncCubic_eq hK (by rw [abs_neg, abs_of_nonneg hL0]; exact hLK)]
      have := cubic_add_pos (c := c) (v := -L) (hB t (Ioc_subset_Icc_self ht) x) (by linarith)
      linarith)
  intro t ht x
  have h1 := hupper t ht x
  have h2 := hlower t ht x
  simp only [ContinuousMap.neg_apply] at h2
  exact abs_lt.2 ⟨by linarith, h1⟩

/-- Two truncated solutions agree as long as the second stays below both truncation levels. -/
theorem eqOn_of_isMildSolution_cutoff {c K₁ K₂ T₁ T₂ T' : ℝ} (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) {u₀ : C(Torus3, ℝ)}
    {u₁ u₂ : ℝ → C(Torus3, ℝ)} (hu₁ : Continuous u₁) (hu₂ : Continuous u₂)
    (hm₁ : IsMildSolution (cutoffNonlin c K₁ hK₁ hf) u₀ T₁ u₁)
    (hm₂ : IsMildSolution (cutoffNonlin c K₂ hK₂ hf) u₀ T₂ u₂) (hT₁ : T' ≤ T₁) (hT₂ : T' ≤ T₂)
    (hb : ∀ t ∈ Icc 0 T', ∀ x, |u₂ t x| ≤ min K₁ K₂) : ∀ t ∈ Icc 0 T', u₁ t = u₂ t := by
  obtain ⟨L, hL⟩ := exists_lipschitzWith_cutoffNonlin c K₁ hK₁ hf
  have hm₂' : IsMildSolution (cutoffNonlin c K₁ hK₁ hf) u₀ T' u₂ := by
    intro t ht
    rw [hm₂ t ⟨ht.1, ht.2.trans hT₂⟩]
    congr 1
    refine duhamel_congr ht.1 fun s hs => ?_
    ext x
    have hs' : s ∈ Icc 0 T' := ⟨hs.1, hs.2.trans ht.2⟩
    simp only [nemytskii_apply, cutoffNonlin_apply]
    rw [truncCubic_eq hK₂ ((hb s hs' x).trans (min_le_right _ _)),
      truncCubic_eq hK₁ ((hb s hs' x).trans (min_le_left _ _))]
  have hm₁' : IsMildSolution (cutoffNonlin c K₁ hK₁ hf) u₀ T' u₁ :=
    fun t ht => hm₁ t ⟨ht.1, ht.2.trans hT₁⟩
  exact IsMildSolution.eqOn (fun s _ x => hL s x) hu₁ hu₂ hm₁' hm₂'

end RegularityStructures.Phi43

end
