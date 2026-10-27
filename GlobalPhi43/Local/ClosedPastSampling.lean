/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.SourceSectionSmooth

/-! Smoothness near the whole closed past testing box, including its top
face, follows from the actual source domain and compact kernel support. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 MeasureTheory Set Filter Topology
open scoped ContDiff

 theorem closed_past_sample_mem_source {r d L T : ℝ} {x y w : ParabolicSpace}
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hLT : L + T ≤ d)
    (hx : x ∈ cylinderInterior r d) (hy : pdist x y ≤ L) (hyt : y.1 ≤ x.1)
    (hw : pdist 0 w ≤ T) (hwt : w.1 ≤ 0) : y + w ∈ sourceCylinder r := by
  have hd : 0 ≤ d := by linarith
  have hdist : pdist x (y + w) ≤ d := by
    apply (pdist_triangle x y (y + w)).trans
    have hh : pdist y (y + w) ≤ T := by simpa only [pdist_add_right] using hw
    linarith
  have ht : |x.1 - (y + w).1| ≤ d ^ 2 :=
    (Real.sqrt_le_left hd).mp ((le_max_left _ _).trans hdist)
  have hs : ‖x.2 - (y + w).2‖ ≤ d := (le_max_right _ _).trans hdist
  refine ⟨?_, ?_, fun i => ?_⟩
  · have := le_abs_self (x.1 - (y + w).1)
    linarith [hx.1]
  · change y.1 + w.1 < 1
    linarith [hx.2.1]
  · have hi : |x.2 i - (y + w).2 i| ≤ d := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using
        (norm_le_pi_norm (x.2 - (y + w).2) i).trans hs
    rw [abs_lt]
    obtain ⟨hl, hu⟩ := hx.2.2 i
    have hh := abs_le.mp hi
    constructor <;> linarith [hh.1, hh.2]

 theorem exists_source_smoothing_closed_past_neighbourhood
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (U : GermPoint → ℝ) {r d L T : ℝ} (hr : 0 ≤ r)
    (hT : 0 < T) (hT₁ : T ≤ 1) (hL : 0 ≤ L) (hLT : L + T ≤ d)
    (hU : ∃ O : Set GermPoint, IsOpen O ∧
      closure (sourceCylinder r) ×ˢ closure (sourceCylinder r) ⊆ O ∧ ContDiffOn ℝ ∞ U O)
    {x : ParabolicSpace} (hx : x ∈ cylinderInterior r d) :
    ∃ O : Set ParabolicSpace, IsOpen O ∧
      {y | pdist x y ≤ L ∧ y.1 ≤ x.1} ⊆ O ∧
      ContDiffOn ℝ ∞ (fun z => ∫ w, U (x, z + w) ∂infiniteKernelMeasure Φ hΦ T hT) O := by
  let K := tsupport (infiniteKernel Φ hΦ T hT)
  have hK : IsCompact K := (infiniteKernel_hasCompactSupport Φ hΦ hT hT₁).isCompact
  let O := {z : ParabolicSpace | ∀ w ∈ K, z + w ∈ sourceCylinder r}
  have hO : IsOpen O := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    apply hK.eventually_forall_of_forall_eventually
    intro w hw
    exact (continuous_fst.add continuous_snd).continuousAt.preimage_mem_nhds
      ((isOpen_sourceCylinder r).mem_nhds (hz w hw))
  refine ⟨O, hO, ?_, ?_⟩
  · intro y hy w hw
    obtain ⟨hwt, hwd⟩ := infiniteKernel_tsupport_closedPast Φ hΦ hT hT₁ hw
    exact closed_past_sample_mem_source hL hT.le hLT hx hy.1 hy.2 hwd hwt
  · have := infiniteKernelMeasure_probability Φ hΦ hT hT₁
    have hxD := subset_closure (cylinderInterior_mem_domain (by linarith : 0 ≤ d) hx)
    have htest : ∀ᵐ w ∂infiniteKernelMeasure Φ hΦ T hT,
        ∀ z ∈ O, z + w ∈ closure (sourceCylinder r) := by
      filter_upwards [infiniteKernelMeasure_ae_tsupport Φ hΦ hT] with w hw
      exact fun z hz => subset_closure (hz w hw)
    intro z hz
    exact (contDiffAt_average_on_open_infty _ (fun q => U (x, q))
      (isCompact_closure_sourceCylinder hr) hO
      (fun q hq => source_section_contDiffAt_infty U hU hxD hq) htest hz).contDiffWithinAt

end GlobalPhi43.Local
