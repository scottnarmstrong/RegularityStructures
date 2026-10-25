/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.PairingGrowth.Bound
public import RegularityStructures.Analysis.Semigroup.Pairing.Tendsto

/-!
# Existence of the pairing (`LocalBall` version)
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {K : RegularisingSemigroup E μ}
  {lam : ℝ}

theorem LocalBall.exists_tendsto_integral [SFinite μ] (hK : K.IsSymmetric)
    (hJ : K.IsJointMeasurable) {Λ : ℝ → E → ℝ} {x₀ : E} {γ : ℝ} {A : Finset ℝ} {C : ℝ}
    (hΛ : K.LocalBall Λ x₀ γ A C lam) (hA : ∀ a ∈ A, -K.order < a) {φ ψ : E → ℝ} {B₁ : ℝ}
    (hlam : 0 < lam) (hB₁ : 0 ≤ B₁) (hφ : K.IsSupported φ x₀ lam) (hψ : K.IsSupported ψ x₀ lam)
    (hgen : K.IsGeneratorPair φ ψ) (hψ1 : ∫ y, |ψ y| ∂μ ≤ B₁ * lam ^ (-K.order)) :
    ∃ L : ℝ, Tendsto (fun s => ∫ y, Λ s y * φ y ∂μ) (𝓝[>] 0) (𝓝 L) := by
  refine cauchy_map_iff_exists_tendsto.1 ?_
  rw [Metric.cauchy_iff]
  refine ⟨inferInstance, fun ε hε => ?_⟩
  have hP := tendsto_incrBound hA γ lam (C * (B₁ * lam ^ (-K.order)))
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      K.incrBound A γ lam (C * (B₁ * lam ^ (-K.order))) δ < ε ∧ δ ≤ 1 :=
    (hP.eventually (gt_mem_nhds hε)).and
      (Filter.mem_of_superset (Ioo_mem_nhdsGT one_pos) fun δ hδ => hδ.2.le)
  obtain ⟨δ0, hδ0, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨_, image_mem_map (Ioo_mem_nhdsGT hδ0), ?_⟩
  rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
  rw [Real.dist_eq]
  rcases lt_trichotomy s s' with h | h | h
  · rw [abs_sub_comm]
    exact (hΛ.abs_integral_sub_le hK hJ hA hlam hB₁ hφ hψ hgen hψ1 hs.1 h (hsub hs').2).trans_lt
      (hsub hs').1
  · subst h; simpa using hε
  · exact (hΛ.abs_integral_sub_le hK hJ hA hlam hB₁ hφ hψ hgen hψ1 hs'.1 h (hsub hs).2).trans_lt
      (hsub hs).1

end RegularityStructures.RegularisingSemigroup

end
