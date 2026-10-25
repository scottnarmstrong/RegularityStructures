/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesCoupled

/-!
# The coupled diagram with a general gain exponent

Generalisation of `coupled_sum_integral` (which needs `β + k = 5` and gains `δ`) to
`β + k + δ = 5 + η`: for an integrand dominated by
`Λ m(w) s_k(w; v) n(v)` with `m = 1_S ∑ c_i s_α(q_i; ·)`, `n = 1_{S'} ∑ c'_j s_β(q'_j; ·)`, and
`s(w - v) ≤ D` on `S × S'`,
`|∫∫ F| ≤ C Λ D^δ (∑ c)(∑ c') (80/(5 - (α + η)) + 2 T)`.
This is the version used for the global cross-difference bounds of `I(Ψ²) Ψ²`, where one of the
covariance exponents is raised by `2θ`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

theorem i2Psi2Diff_coupled_sum_integral {α β k δ η : ℝ} (hα : 0 < α) (hβ : 0 < β) (hk : 0 < k)
    (hδ : 0 < δ) (hη : 0 < η) (hβ5 : β < 5) (hkδ : k + δ < 5) (hβk : β + k + δ = 5 + η)
    (hαη : α + η < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : SpaceTime → SpaceTime → ℝ} {Λ τ τ' T T' D : ℝ}
      {c c' : Fin 3 → ℝ} {q q' : Fin 3 → SpaceTime}, 0 ≤ Λ → 0 ≤ T → 0 ≤ T' → 0 ≤ D →
      (∀ i, 0 ≤ c i) → (∀ j, 0 ≤ c' j) →
      AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) →
      (∀ w v : SpaceTime, |w.1 - τ| ≤ T → |v.1 - τ'| ≤ T' → torusParabolicSize (w - v) ≤ D) →
      (∀ᵐ w : SpaceTime ∂volume, ∀ᵐ v : SpaceTime ∂volume, |F w v| ≤
        Λ * (Set.indicator {w : SpaceTime | |w.1 - τ| ≤ T}
            (fun w => ∑ i, c i * singularPow α (q i) w) w *
          (singularPow k w v * Set.indicator {v : SpaceTime | |v.1 - τ'| ≤ T'}
            (fun v => ∑ j, c' j * singularPow β (q' j) v) v))) →
      Integrable (Function.uncurry F) (volume.prod volume) ∧
        |∫ w, ∫ v, F w v| ≤ C * Λ * D ^ δ * ((∑ i, c i) * (∑ j, c' j)) *
          (80 / (5 - (α + η)) + 2 * T) := by
  obtain ⟨C1, hC1, h1⟩ := singularIntLe_mul_two (a := β) (b := k + δ) (η := η) hβ hβ5
    (by linarith) hkδ hη (by linarith)
  refine ⟨C1 * 2, by positivity, ?_⟩
  intro F Λ τ τ' T T' D c c' q q' hΛ hT hT' hD hc hc' hmeas hDw hFG
  set S : Set SpaceTime := {w : SpaceTime | |w.1 - τ| ≤ T} with hS
  set S' : Set SpaceTime := {v : SpaceTime | |v.1 - τ'| ≤ T'} with hS'
  have nn : ∀ (a : ℝ) (cc : Fin 3 → ℝ) (qq : Fin 3 → SpaceTime), (∀ i, 0 ≤ cc i) →
      ∀ w, 0 ≤ ∑ i, cc i * singularPow a (qq i) w := fun a cc qq hcc w =>
    Finset.sum_nonneg fun i _ => mul_nonneg (hcc i) (singularPow_nonneg _ _ _)
  set m : SpaceTime → ℝ := Set.indicator S (fun w => ∑ i, c i * singularPow α (q i) w) with hm
  set n : SpaceTime → ℝ := Set.indicator S' (fun v => ∑ j, c' j * singularPow β (q' j) v)
    with hn
  have hm0 : ∀ w, 0 ≤ m w := fun w => Set.indicator_nonneg (fun w _ => nn α c q hc w) w
  have hn0 : ∀ v, 0 ≤ n v := fun v => Set.indicator_nonneg (fun v _ => nn β c' q' hc' v) v
  set Hn : SpaceTime → ℝ := fun w => ∑ j, c' j * (C1 * singularPow η (q' j) w) with hHn
  have hin : ∀ᵐ w : SpaceTime ∂volume,
      SingularIntLe (fun v => singularPow (k + δ) w v * n v) (Hn w) := by
    have hae : ∀ᵐ w : SpaceTime ∂volume, ∀ j, 0 < torusParabolicSize (q' j - w) := by
      rw [ae_all_iff]
      exact fun j => ae_torusParabolicSize_sub_pos (q' j)
    filter_upwards [hae] with w hw
    have hs := SingularIntLe.finset_sum (Finset.univ : Finset (Fin 3))
      (f := fun j v => c' j * (singularPow β (q' j) v * singularPow (k + δ) w v))
      (X := fun j => c' j * (C1 * torusParabolicSize (q' j - w) ^ (-η)))
      (fun j _ => (h1 (q' j) w (hw j)).const_mul (hc' j))
    refine (hs.mono_right (le_of_eq ?_)).of_le ?_ ?_ ?_
    · simp only [hHn, singularPow]
    · exact ((measurable_singularPow (k + δ) w).mul (Measurable.indicator
        (Finset.measurable_sum _ fun j _ => measurable_const.mul (measurable_singularPow β (q' j)))
        (measurableSet_abs_fst_sub_le τ' T'))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun v => mul_nonneg (singularPow_nonneg _ _ _) (hn0 v)
    · refine Filter.Eventually.of_forall fun v => ?_
      by_cases hv : v ∈ S'
      · simp only [hn, Set.indicator_of_mem hv, Finset.mul_sum]
        refine Finset.sum_le_sum fun j _ => le_of_eq ?_
        ring
      · simp only [hn, Set.indicator_of_notMem hv, mul_zero]
        exact Finset.sum_nonneg fun j _ => mul_nonneg (hc' j) (mul_nonneg (singularPow_nonneg _ _ _)
          (singularPow_nonneg _ _ _))
  have hout : SingularIntLe (fun w => m w * Hn w)
      (C1 * 2 * ((∑ i, c i) * (∑ j, c' j)) * (80 / (5 - (α + η)) + 2 * T)) := by
    have hsl : ∀ i j, SingularIntLe (Set.indicator S
        (fun w => singularPow α (q i) w * singularPow η (q' j) w))
        (2 * (80 / (5 - (α + η)) + 2 * T)) := fun i j =>
      singularIntLe_slabAt_mul_two τ hα hη hαη hT (q i) (q' j)
    have hs := SingularIntLe.finset_sum (Finset.univ : Finset (Fin 3))
      (f := fun i w => c i * ∑ j, c' j * (C1 * Set.indicator S
        (fun w => singularPow α (q i) w * singularPow η (q' j) w) w))
      (X := fun i => c i * ∑ j, c' j * (C1 * (2 * (80 / (5 - (α + η)) + 2 * T))))
      (fun i _ => (SingularIntLe.finset_sum (Finset.univ : Finset (Fin 3))
        (f := fun j w => c' j * (C1 * Set.indicator S
          (fun w => singularPow α (q i) w * singularPow η (q' j) w) w))
        (X := fun j => c' j * (C1 * (2 * (80 / (5 - (α + η)) + 2 * T))))
        (fun j _ => ((hsl i j).const_mul hC1).const_mul (hc' j))).const_mul (hc i))
    refine (hs.mono_right (le_of_eq ?_)).of_le ?_ ?_ ?_
    · simp only [← Finset.sum_mul]
      ring
    · exact ((Measurable.indicator
        (Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_singularPow α (q i)))
        (measurableSet_abs_fst_sub_le τ T)).mul (Finset.measurable_sum _ fun j _ =>
          measurable_const.mul (measurable_const.mul (measurable_singularPow η (q' j))))
        ).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun w => mul_nonneg (hm0 w)
        (Finset.sum_nonneg fun j _ => mul_nonneg (hc' j) (mul_nonneg hC1
          (singularPow_nonneg _ _ _)))
    · refine Filter.Eventually.of_forall fun w => ?_
      by_cases hw : w ∈ S
      · simp only [hm, hHn, Set.indicator_of_mem hw]
        refine le_of_eq ?_
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      · simp [hm, hw]
  have := coupled_two_level (F := F) (Λ := Λ) (D := D) (k := k) (δ := δ) hΛ hD hδ.le
    hm0 hn0 (S := S) (S' := S') (fun w hw => by simp [hm, hw]) (fun v hv => by simp [hn, hv])
    (fun w hw v hv => hDw w v hw hv) hin hout hmeas hFG
  refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
  ring

end RegularityStructures

end
