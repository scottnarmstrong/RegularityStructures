/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyCover
public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyLower
public import Mathlib.Order.CompletePartialOrder

/-!
# `piHalfStmt_of_unitBox`: the unit-box `Π` half implies the `Π` half on every compact set

Given the `Π` half (`PiHalfStmt`) for every compact subset of the unit box with constants `qPi`,
`KPi`, it holds for every compact `S` with the same `qPi` and the constant `m * KPi`, where `m` is
the size of a finite cover of `S` by closed balls of radius `1/2` (each contained in a translate of
the unit box).  Measurability is inherited from `IsContinuousRandomModelWithFieldsOn` on `S`.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace RegularityStructures

universe u

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem piHalfStmt_of_unitBox (𝒯 : RegularityStructure ι) (γ κbar θ : ℝ) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (S : Set ParabolicSpace) (hS : IsCompact S) (p : ℕ) (hp : 1 ≤ p)
    (hbox : ∀ T : Set ParabolicSpace, IsCompact T → T ⊆ piHalfUnitBox →
      ∃ qPi : ℕ, p ≤ qPi ∧ ∃ KPi : ℝ → ℝ, (∀ C, 0 ≤ KPi C) ∧
        PiHalfStmt.{u, _} 𝒯 γ κbar θ Dπ DΓ T p qPi KPi) :
    ∃ qPi : ℕ, p ≤ qPi ∧ ∃ KPi : ℝ → ℝ, (∀ C, 0 ≤ KPi C) ∧
      PiHalfStmt.{u, _} 𝒯 γ κbar θ Dπ DΓ S p qPi KPi := by
  obtain ⟨s, hcov⟩ := exists_finset_cover_closedBall_half hS
  -- the pieces
  let a : ParabolicSpace → ParabolicSpace := fun z =>
    z - ((1 / 2 : ℝ), fun _ : Fin 3 => (1 / 2 : ℝ))
  let T : ParabolicSpace → Set ParabolicSpace := fun z =>
    (fun y => y + a z) ⁻¹' (S ∩ closedBall z (1 / 2))
  have hTimg : ∀ z, (fun y => y + a z) '' T z = S ∩ closedBall z (1 / 2) := fun z =>
    Set.image_preimage_eq _ fun y => ⟨y - a z, sub_add_cancel y (a z)⟩
  have hTcpt : ∀ z, IsCompact (T z) := fun z =>
    (Homeomorph.addRight (a z)).isCompact_preimage.2 (hS.inter_right isClosed_closedBall)
  have hTbox : ∀ z, T z ⊆ piHalfUnitBox := fun z =>
    (preimage_mono inter_subset_right).trans (piHalfPiece_subset_unitBox z)
  have hSubS : ∀ z, (fun y => y + a z) '' T z ⊆ S := fun z => by
    rw [hTimg]; exact inter_subset_left
  choose! qz hqz KPz hKPz hst using fun z => hbox (T z) (hTcpt z) (hTbox z)
  set qPi : ℕ := max p (s.sup qz) with hqPi
  refine ⟨qPi, le_max_left _ _, fun Cbar => ∑ z ∈ s, KPz z Cbar, fun C => ?_, ?_⟩
  · exact Finset.sum_nonneg fun z _ => hKPz z C
  unfold PiHalfStmt
  intro Cbar Ω _ P _ Z₁ Z₂ C ε hC hCb hε hZ₁ hZ₂ h1 h2 h3 h4 h5 h6 h7 h8
  have hprem : PiHalfPrem 𝒯 γ κbar θ Dπ DΓ qPi P Z₁ Z₂ C ε :=
    ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hV₁ : ∀ z, IsContinuousRandomModelWithFieldsOn
      (fun ω => (Z₁ ω).translate (a z)) (T z) := fun z =>
    (hZ₁.mono (hSubS z)).translate (a z)
  have hV₂ : ∀ z, IsContinuousRandomModelWithFieldsOn
      (fun ω => (Z₂ ω).translate (a z)) (T z) := fun z =>
    (hZ₂.mono (hSubS z)).translate (a z)
  have hpz : ∀ z ∈ s, PiHalfPrem 𝒯 γ κbar θ Dπ DΓ (qz z) P (fun ω => (Z₁ ω).translate (a z))
      (fun ω => (Z₂ ω).translate (a z)) C ε := fun z hz =>
    (hprem.translate (a z)).lower (hV₁ z) (hV₂ z) (le_trans hp (hqz z))
      (le_trans (Finset.le_sup (f := qz) hz) (le_max_right _ _))
  have key := fun z (hz : z ∈ s) => hst z Cbar P
    (fun ω => (Z₁ ω).translate (a z)) (fun ω => (Z₂ ω).translate (a z)) C ε hC hCb hε
    (hV₁ z) (hV₂ z) (hpz z hz).detPi (hpz z hz).detPiDiff
    (hpz z hz).detGamma (hpz z hz).detGammaDiff
    (hpz z hz).momPi (hpz z hz).momPiDiff
    (hpz z hz).momGamma (hpz z hz).momGammaDiff
  have hcov' : S ⊆ ⋃ z ∈ s, (fun y => y + a z) '' T z := fun x hx => by
    have := hcov hx
    simp only [mem_iUnion] at this ⊢
    obtain ⟨z, hz, hxz⟩ := this
    exact ⟨z, hz, by rw [hTimg]; exact ⟨hx, hxz⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro Z hZ
    have hZV : IsContinuousRandomModelWithFieldsOn Z S := by
      rcases hZ with rfl | hZ
      · exact hZ₁
      · rw [mem_singleton_iff] at hZ; exact hZ ▸ hZ₂
    have hmem : ∀ z, (fun ω => (Z ω).translate (a z)) ∈
        ({fun ω => (Z₁ ω).translate (a z), fun ω => (Z₂ ω).translate (a z)} :
          Set (Ω → Model 𝒯 parabolicSemigroup)) := by
      intro z
      rcases hZ with rfl | hZ
      · exact Or.inl rfl
      · rw [mem_singleton_iff] at hZ
        subst hZ
        exact Or.inr rfl
    refine ⟨(hZV.measurable_piNormOn γ).aemeasurable, ?_⟩
    have hpt : ∀ ω, (Z ω).piNormOn γ S ≤
        s.sup fun z => ((fun ω => (Z ω).translate (a z)) ω).piNormOn γ (T z) := fun ω => by
      refine ((Z ω).piNormOn_mono γ hcov').trans
        ((Z ω).piNormOn_biUnion_le γ s _) |>.trans ?_
      refine Finset.sup_le fun z hz => ?_
      exact (le_of_eq (Model.piNormOn_translate (Z ω) (a z) γ (T z)).symm).trans
        (Finset.le_sup (f := fun z =>
          ((fun ω => (Z ω).translate (a z)) ω).piNormOn γ (T z)) hz)
    calc ∫⁻ ω, (Z ω).piNormOn γ S ^ p ∂P
        ≤ ∫⁻ ω, ∑ z ∈ s, ((fun ω => (Z ω).translate (a z)) ω).piNormOn γ (T z) ^ p ∂P :=
          lintegral_mono fun ω => by
            exact (pow_le_pow_left' (hpt ω) p).trans (ennreal_finset_sup_pow_le_sum _ _ hp)
      _ = ∑ z ∈ s, ∫⁻ ω, ((fun ω => (Z ω).translate (a z)) ω).piNormOn γ (T z) ^ p ∂P :=
          lintegral_finsetSum' s fun z hz => ((key z hz).1 _ (hmem z)).1.pow_const p
      _ ≤ ∑ z ∈ s, ENNReal.ofReal (KPz z Cbar * C ^ p) :=
          Finset.sum_le_sum fun z hz => ((key z hz).1 _ (hmem z)).2
      _ = ENNReal.ofReal ((∑ z ∈ s, KPz z Cbar) * C ^ p) := by
          rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun z _ =>
            mul_nonneg (hKPz z Cbar) (pow_nonneg hC p)]
  · exact (hZ₁.measurable_piDiffNormOn hZ₂ γ).aemeasurable
  · have hpt : ∀ ω, (Z₁ ω).piDiffNormOn (Z₂ ω) γ S ≤
        s.sup fun z => ((fun ω => (Z₁ ω).translate (a z)) ω).piDiffNormOn
          ((fun ω => (Z₂ ω).translate (a z)) ω) γ (T z) := fun ω => by
      refine ((Z₁ ω).piDiffNormOn_mono (Z₂ ω) γ hcov').trans
        ((Z₁ ω).piDiffNormOn_biUnion_le (Z₂ ω) γ s _) |>.trans ?_
      refine Finset.sup_le fun z hz => ?_
      exact (le_of_eq (Model.piDiffNormOn_translate (Z₁ ω) (Z₂ ω) (a z) γ (T z)).symm).trans
        (Finset.le_sup (f := fun z => ((fun ω => (Z₁ ω).translate (a z)) ω).piDiffNormOn
          ((fun ω => (Z₂ ω).translate (a z)) ω) γ (T z)) hz)
    calc ∫⁻ ω, (Z₁ ω).piDiffNormOn (Z₂ ω) γ S ^ p ∂P
        ≤ ∫⁻ ω, ∑ z ∈ s, ((fun ω => (Z₁ ω).translate (a z)) ω).piDiffNormOn
            ((fun ω => (Z₂ ω).translate (a z)) ω) γ (T z) ^ p ∂P :=
          lintegral_mono fun ω => by
            exact (pow_le_pow_left' (hpt ω) p).trans (ennreal_finset_sup_pow_le_sum _ _ hp)
      _ = ∑ z ∈ s, ∫⁻ ω, ((fun ω => (Z₁ ω).translate (a z)) ω).piDiffNormOn
            ((fun ω => (Z₂ ω).translate (a z)) ω) γ (T z) ^ p ∂P :=
          lintegral_finsetSum' s fun z hz => (key z hz).2.1.pow_const p
      _ ≤ ∑ z ∈ s, ENNReal.ofReal (KPz z Cbar * (C * ε ^ θ) ^ p) :=
          Finset.sum_le_sum fun z hz => (key z hz).2.2
      _ = ENNReal.ofReal ((∑ z ∈ s, KPz z Cbar) * (C * ε ^ θ) ^ p) := by
          have hε' : 0 ≤ C * ε ^ θ := mul_nonneg hC (Real.rpow_nonneg hε _)
          rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun z _ =>
            mul_nonneg (hKPz z Cbar) (pow_nonneg hε' p)]

end RegularityStructures

end
