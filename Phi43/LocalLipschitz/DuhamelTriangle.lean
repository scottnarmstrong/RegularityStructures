/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Fubini on the triangle

For a jointly continuous `K : ℝ → ℝ → E` into a Banach space and `0 ≤ t`,
`∫_0^t ∫_0^r K r q dq dr = ∫_0^t ∫_q^t K r q dr dq` (`intervalIntegral_triangle_swap`).
-/

public section

open MeasureTheory Set

namespace RegularityStructures.Phi43.LocalLipschitz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Fubini on the triangle** `0 ≤ q ≤ r ≤ t`. -/
theorem intervalIntegral_triangle_swap {K : ℝ → ℝ → E} (hK : Continuous (Function.uncurry K))
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ r in (0 : ℝ)..t, ∫ q in (0 : ℝ)..r, K r q =
      ∫ q in (0 : ℝ)..t, ∫ r in q..t, K r q := by
  classical
  set F : ℝ → ℝ → E := fun r q => if q ≤ r then K r q else 0 with hF
  have hint : IntegrableOn (Function.uncurry F) (uIoc 0 t ×ˢ uIoc 0 t) := by
    have h1 : IntegrableOn (Function.uncurry K) (Icc 0 t ×ˢ Icc 0 t) :=
      hK.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have h2 : IntegrableOn (Function.uncurry K) (uIoc 0 t ×ˢ uIoc 0 t) := by
      refine h1.mono_set (prod_mono ?_ ?_) <;>
        · rw [uIoc_of_le ht]; exact Ioc_subset_Icc_self
    have h3 : IntegrableOn (Set.indicator {p : ℝ × ℝ | p.2 ≤ p.1} (Function.uncurry K))
        (uIoc 0 t ×ˢ uIoc 0 t) volume :=
      Integrable.indicator h2 (measurableSet_le measurable_snd measurable_fst)
    have e : Function.uncurry F = Set.indicator {p : ℝ × ℝ | p.2 ≤ p.1} (Function.uncurry K) := by
      ext ⟨r, q⟩
      simp [hF, Set.indicator]
    rw [e]
    exact h3
  have hswap := intervalIntegral_intervalIntegral_swap hint
  have hKq : ∀ r, Continuous (K r) := fun r => hK.comp (Continuous.prodMk_right r)
  have hKr : ∀ q, Continuous (fun r => K r q) := fun q => hK.comp (Continuous.prodMk_left q)
  have hFq : ∀ r, IntervalIntegrable (F r) volume 0 t := fun r => by
    have e : F r = Set.indicator (Iic r) (K r) := by
      ext q; simp [hF, Set.indicator]
    rw [e, intervalIntegrable_iff, uIoc_of_le ht]
    have h : IntegrableOn (K r) (Ioc 0 t) volume :=
      ((hKq r).integrableOn_Icc (a := 0) (b := t)).mono_set Ioc_subset_Icc_self
    exact Integrable.indicator h measurableSet_Iic
  have hFr : ∀ q, IntervalIntegrable (fun r => F r q) volume 0 t := fun q => by
    have e : (fun r => F r q) = Set.indicator (Ici q) (fun r => K r q) := by
      ext r; simp [hF, Set.indicator]
    rw [e, intervalIntegrable_iff, uIoc_of_le ht]
    have h : IntegrableOn (fun r => K r q) (Ioc 0 t) volume :=
      ((hKr q).integrableOn_Icc (a := 0) (b := t)).mono_set Ioc_subset_Icc_self
    exact Integrable.indicator h measurableSet_Ici
  have hL : ∀ r ∈ Icc (0 : ℝ) t, ∫ q in (0 : ℝ)..t, F r q = ∫ q in (0 : ℝ)..r, K r q := by
    intro r hr
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := r)
      (f := fun q => F r q)]
    · have e1 : ∫ q in (0 : ℝ)..r, F r q = ∫ q in (0 : ℝ)..r, K r q := by
        refine intervalIntegral.integral_congr fun q hq => ?_
        rw [uIcc_of_le hr.1] at hq
        simp [hF, hq.2]
      have e2 : ∫ q in r..t, F r q = 0 := by
        have : ∫ q in r..t, F r q = ∫ q in r..t, (0 : E) := by
          refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun q hq => ?_)
          rw [uIoc_of_le hr.2] at hq
          simp [hF, not_le.2 hq.1]
        simpa using this
      rw [e1, e2, add_zero]
    · exact (hFq r).mono_set (by rw [uIcc_of_le hr.1, uIcc_of_le ht]; exact Icc_subset_Icc_right hr.2)
    · exact (hFq r).mono_set (by rw [uIcc_of_le hr.2, uIcc_of_le ht]; exact Icc_subset_Icc_left hr.1)
  have hR : ∀ q ∈ Icc (0 : ℝ) t, ∫ r in (0 : ℝ)..t, F r q = ∫ r in q..t, K r q := by
    intro q hq
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := q)
      (f := fun r => F r q)]
    · have e1 : ∫ r in q..t, F r q = ∫ r in q..t, K r q := by
        refine intervalIntegral.integral_congr fun r hr => ?_
        rw [uIcc_of_le hq.2] at hr
        simp [hF, hr.1]
      have e2 : ∫ r in (0 : ℝ)..q, F r q = 0 := by
        have : ∫ r in (0 : ℝ)..q, F r q = ∫ r in (0 : ℝ)..q, (0 : E) := by
          refine intervalIntegral.integral_congr_ae ?_
          have hne : ∀ᵐ r : ℝ, r ≠ q := (Set.countable_singleton q).ae_notMem _
          filter_upwards [hne] with r hr hmem
          rw [uIoc_of_le hq.1] at hmem
          simp [hF, not_le.2 (lt_of_le_of_ne hmem.2 hr)]
        simpa using this
      rw [e1, e2, zero_add]
    · exact (hFr q).mono_set (by rw [uIcc_of_le hq.1, uIcc_of_le ht]; exact Icc_subset_Icc_right hq.2)
    · exact (hFr q).mono_set (by rw [uIcc_of_le hq.2, uIcc_of_le ht]; exact Icc_subset_Icc_left hq.1)
  calc ∫ r in (0 : ℝ)..t, ∫ q in (0 : ℝ)..r, K r q
      = ∫ r in (0 : ℝ)..t, ∫ q in (0 : ℝ)..t, F r q :=
        intervalIntegral.integral_congr fun r hr => by
          rw [uIcc_of_le ht] at hr; exact (hL r hr).symm
    _ = ∫ q in (0 : ℝ)..t, ∫ r in (0 : ℝ)..t, F r q := by
        simpa [uIoc_of_le ht] using hswap
    _ = ∫ q in (0 : ℝ)..t, ∫ r in q..t, K r q :=
        intervalIntegral.integral_congr fun q hq => by
          rw [uIcc_of_le ht] at hq; exact hR q hq

end RegularityStructures.Phi43.LocalLipschitz

end
