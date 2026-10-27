/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Probability.L2IndicatorApproximation
public import GlobalPhi43.Probability.NoiseInsideOutside
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Real-time exterior cutoffs and their L2 approximation. Boundary hyperplanes
are removed only modulo space-time volume, never by a pointwise noise identity. -/

public noncomputable section

open MeasureTheory Set Filter RegularityStructures
open scoped Topology

namespace GlobalPhi43.Probability

@[expose] def germWidth (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem germWidth_pos (n : ℕ) : 0 < germWidth n := by
  unfold germWidth
  positivity

theorem germWidth_antitone : Antitone germWidth := by
  intro m n hmn
  unfold germWidth
  apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (m : ℝ) + 1)
  exact_mod_cast Nat.add_le_add_right hmn 1

theorem germWidth_tendsto : Tendsto germWidth atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

@[expose] def exteriorStrip (s t δ : ℝ) : Set SpaceTime :=
  {z | z.1 < s - δ ∨ t + δ < z.1}

theorem exteriorStrip_eq_compl (s t δ : ℝ) :
    exteriorStrip s t δ = (Icc (s - δ) (t + δ) ×ˢ (univ : Set Torus3))ᶜ := by
  ext z
  simp only [exteriorStrip, mem_ofPred_eq, mem_compl_iff, mem_prod, mem_Icc, mem_univ,
    and_true, not_and_or, not_le]

theorem exteriorStrip_measurable (s t δ : ℝ) : MeasurableSet (exteriorStrip s t δ) := by
  rw [exteriorStrip_eq_compl]
  exact (measurableSet_Icc.prod MeasurableSet.univ).compl

theorem exteriorStrip_mono_width (s t : ℝ) {δ δ' : ℝ} (hle : δ' ≤ δ) :
    exteriorStrip s t δ ⊆ exteriorStrip s t δ' := by
  intro z hz
  rcases hz with hz | hz
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

theorem exteriorStrip_germ_mono (s t : ℝ) : Monotone (fun n => exteriorStrip s t (germWidth n)) :=
  fun _ _ hmn => exteriorStrip_mono_width s t (germWidth_antitone hmn)

theorem exteriorStrip_subset_compl_Ioc_prod (s t : ℝ) (n : ℕ) :
    exteriorStrip s t (germWidth n) ⊆ (Ioc s t ×ˢ (univ : Set Torus3))ᶜ := by
  intro z hz hmem
  have hp := germWidth_pos n
  have ht := hmem.1
  rcases hz with hz | hz <;> linarith [ht.1, ht.2]

theorem ae_ne_time_faces (s t : ℝ) :
    ∀ᵐ z : SpaceTime, z.1 ≠ s ∧ z.1 ≠ t := by
  have he : {z : SpaceTime | z.1 = s ∨ z.1 = t} =
      (({s} ∪ {t}) : Set ℝ) ×ˢ (univ : Set Torus3) := by ext z; simp [or_comm]
  have hzero : volume {z : SpaceTime | z.1 = s ∨ z.1 = t} = 0 := by
    rw [he, Measure.volume_eq_prod, Measure.prod_prod]
    have hnull : volume (({s} ∪ {t}) : Set ℝ) = 0 := measure_union_null (by simp) (by simp)
    rw [hnull, zero_mul]
  rw [ae_iff]
  simpa only [not_and_or, not_not] using hzero

theorem eventually_mem_exteriorStrip (s t : ℝ) {z : SpaceTime} (hz : z.1 < s ∨ t < z.1) :
    ∀ᶠ n in atTop, z ∈ exteriorStrip s t (germWidth n) := by
  rcases hz with hz | hz
  · have hw := (tendsto_order.mp germWidth_tendsto).2 (s - z.1) (sub_pos.mpr hz)
    filter_upwards [hw] with n hn
    exact Or.inl (by linarith)
  · have hw := (tendsto_order.mp germWidth_tendsto).2 (z.1 - t) (sub_pos.mpr hz)
    filter_upwards [hw] with n hn
    exact Or.inr (by linarith)

theorem exterior_indicator_tendsto {h : SpaceTime → ℝ} (s t : ℝ)
    (hs : Function.support h ⊆ (Ioc s t ×ˢ (univ : Set Torus3))ᶜ) :
    ∀ᵐ z : SpaceTime, Tendsto (fun n => (exteriorStrip s t (germWidth n)).indicator h z)
      atTop (𝓝 (h z)) := by
  filter_upwards [ae_ne_time_faces s t] with z hz
  by_cases hzero : h z = 0
  · have hfn (n : ℕ) : (exteriorStrip s t (germWidth n)).indicator h z = 0 := by
      by_cases hn : z ∈ exteriorStrip s t (germWidth n)
      · rw [Set.indicator_of_mem hn, hzero]
      · exact Set.indicator_of_notMem hn h
    simpa only [hfn, hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · have hnot : ¬ (s < z.1 ∧ z.1 ≤ t) := fun ht => hs (Function.mem_support.mpr hzero) ⟨ht, trivial⟩
    have hout : z.1 < s ∨ t < z.1 := by
      rcases not_and_or.mp hnot with hl | hr
      · rcases lt_or_eq_of_le (le_of_not_gt hl) with hlt | heq
        · exact Or.inl hlt
        · exact False.elim (hz.1 heq)
      · exact Or.inr (lt_of_not_ge hr)
    have he : (fun n => (exteriorStrip s t (germWidth n)).indicator h z) =ᶠ[atTop]
        (fun _ => h z) := (eventually_mem_exteriorStrip s t hout).mono fun n hn =>
      Set.indicator_of_mem hn h
    exact Tendsto.congr' he.symm tendsto_const_nhds

theorem exterior_toLp_tendsto {h : SpaceTime → ℝ} (hh : MemLp h 2) (s t : ℝ)
    (hs : Function.support h ⊆ (Ioc s t ×ˢ (univ : Set Torus3))ᶜ) :
    Tendsto (fun n => (hh.indicator (exteriorStrip_measurable s t (germWidth n))).toLp
      ((exteriorStrip s t (germWidth n)).indicator h)) atTop (𝓝 (hh.toLp h)) :=
  indicator_toLp_tendsto hh _ (fun n => exteriorStrip_measurable s t (germWidth n))
    (exterior_indicator_tendsto s t hs)

end GlobalPhi43.Probability
