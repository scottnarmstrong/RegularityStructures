module

public import GlobalPhi43.Attachment.CoverTerminal

/-! Local-to-global application of the normalized Moinat–Weber bound,
with the normalized estimate as an explicit hypothesis. -/

public noncomputable section

open Set RegularityStructures

namespace GlobalPhi43.Attachment

/-- Positive physical times contain the entire pulled-back closed inset. -/
theorem cover_innerClosure_positive {t : ℝ} (ht : 0 < t) (s : ℝ) (x₀ : Fin 3 → ℝ) :
    MapsTo (coverMap s t x₀) (closure (mwInnerCylinder (1 / 2))) {z | s < z.1} := by
  intro z hz
  rw [closure_mwInnerCylinder_half] at hz
  have hz0 : 0 ≤ z.1 := by linarith [hz.1.1]
  have hprod := mul_nonneg (sq_nonneg (coverScale t)) hz0
  change s < s + t - coverScale t ^ 2 + coverScale t ^ 2 * z.1
  nlinarith [coverScale_sq ht.le]

/-- Cover bound assuming the normalized estimate and the tree/defect scaling identities. -/
theorem cover_bound_of_normalized_row {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (s : ℝ)
    (v : ParabolicSpace → ℝ) (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hv : ContinuousOn v {z | s < z.1})
    (hMW : ∀ x₀ ∈ coverGrid (coverScale t), ∀ z ∈ mwInnerCylinder (1 / 2),
      coverScale t * |v (coverMap s t x₀ z)| ≤ C * max 2 (coverScale t * M))
    (x : Fin 3 → ℝ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    Real.sqrt t * |v (s + t, x)| ≤ 2 * C * max 2 M := by
  have hc := coverScale_pos ht.1
  have hscale : coverScale t ≤ 1 := (coverScale_le_half ht).trans (by norm_num)
  have hmax : max 2 (coverScale t * M) ≤ max 2 M := by
    apply max_le (le_max_left _ _)
    exact (by nlinarith : coverScale t * M ≤ M).trans (le_max_right _ _)
  have hint : ∀ x₀ ∈ coverGrid (coverScale t), ∀ z ∈ mwInnerCylinder (1 / 2),
      |v (coverMap s t x₀ z)| ≤ (C * max 2 (coverScale t * M)) / coverScale t := by
    intro x₀ hx₀ z hz
    exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hMW x₀ hx₀ z hz)
  have hpatch (x₀ : Fin 3 → ℝ) (_ : x₀ ∈ coverGrid (coverScale t)) :
      ContinuousOn (fun z => v (coverMap s t x₀ z)) (closure (mwInnerCylinder (1 / 2))) :=
    hv.comp (coverMap_contDiff s t x₀).continuous.continuousOn
      (cover_innerClosure_positive ht.1 s x₀)
  have h := cover_grid_terminal_bound ht.1 s v _ hpatch hint x hx
  have hmul := mul_le_mul_of_nonneg_left h hc.le
  have he : coverScale t * ((C * max 2 (coverScale t * M)) / coverScale t) =
      C * max 2 (coverScale t * M) := by field_simp
  rw [he] at hmul
  have hpoly := mul_le_mul_of_nonneg_left hmax hC
  unfold coverScale at hmul
  have hh := hmul.trans hpoly
  nlinarith only [hh]

end GlobalPhi43.Attachment
