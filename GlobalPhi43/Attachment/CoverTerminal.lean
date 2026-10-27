module

public import GlobalPhi43.Attachment.CoverCylinder
public import GlobalPhi43.Attachment.CoverGrid
public import GlobalPhi43.MW20.Setting.MWInnerCylinder
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-! The open upper face is passed through closure before applying the closed grid cover. -/

public noncomputable section

open Set Metric RegularityStructures

namespace GlobalPhi43.Attachment

/-- Closing the actual half-inset cylinder includes the whole terminal closed cube. -/
theorem closure_mwInnerCylinder_half :
    closure (mwInnerCylinder (1 / 2)) =
      Icc (1 / 4 : ℝ) 1 ×ˢ closedBall (0 : Fin 3 → ℝ) (1 / 2) := by
  have he : mwInnerCylinder (1 / 2) =
      Ioo (1 / 4 : ℝ) 1 ×ˢ ball (0 : Fin 3 → ℝ) (1 / 2) := by
    ext z
    simp only [mwInnerCylinder, mem_prod, mem_Ioo, mem_ofPred_eq, mem_ball, dist_zero_right]
    norm_num
  rw [he, closure_prod_eq, closure_Ioo (by norm_num : (1 / 4 : ℝ) ≠ 1),
    closure_ball (0 : Fin 3 → ℝ) (by norm_num : (1 / 2 : ℝ) ≠ 0)]

theorem coverMap_top (s t : ℝ) (x₀ y : Fin 3 → ℝ) :
    coverMap s t x₀ (1, y) = (s + t, x₀ + coverScale t • y) := by
  apply Prod.ext
  · change s + t - coverScale t ^ 2 + coverScale t ^ 2 * 1 = s + t
    ring
  · rfl

/-- The terminal bound is derived by continuity from an interior bound; no top-face
point is incorrectly treated as belonging to the open cylinder. -/
theorem cover_terminal_bound (s t : ℝ) (x₀ : Fin 3 → ℝ) (v : ParabolicSpace → ℝ)
    (B : ℝ) (hv : ContinuousOn (fun z => v (coverMap s t x₀ z))
      (closure (mwInnerCylinder (1 / 2))))
    (hb : ∀ z ∈ mwInnerCylinder (1 / 2), |v (coverMap s t x₀ z)| ≤ B)
    (y : Fin 3 → ℝ) (hy : ‖y‖ ≤ 1 / 2) :
    |v (s + t, x₀ + coverScale t • y)| ≤ B := by
  have hp : (1, y) ∈ closure (mwInnerCylinder (1 / 2)) := by
    rw [closure_mwInnerCylinder_half]
    exact ⟨⟨by norm_num, le_rfl⟩, by simpa only [mem_closedBall, dist_zero_right] using hy⟩
  have h := le_on_closure hb hv.abs continuousOn_const hp
  rwa [coverMap_top] at h

/-- Every closed-grid cube has an actual normalized terminal-face preimage. -/
theorem cover_terminal_preimage {t : ℝ} (ht : 0 < t) (s : ℝ) (x₀ x : Fin 3 → ℝ)
    (hx : ∀ i, |x i - x₀ i| ≤ coverScale t / 2) :
    ∃ y : Fin 3 → ℝ, ‖y‖ ≤ 1 / 2 ∧ coverMap s t x₀ (1, y) = (s + t, x) := by
  have hc := coverScale_pos ht
  let y : Fin 3 → ℝ := fun i => (x i - x₀ i) / coverScale t
  refine ⟨y, (pi_norm_le_iff_of_nonneg (by norm_num)).mpr ?_, ?_⟩
  · intro i
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hc]
    exact (div_le_iff₀ hc).mpr (by linarith [hx i])
  · rw [coverMap_top]
    congr 1
    funext i
    change x₀ i + coverScale t * ((x i - x₀ i) / coverScale t) = x i
    field_simp
    ring

/-- Concrete grid and terminal-face preimage for every point of the closed unit cell. -/
theorem exists_cover_terminal_patch {t : ℝ} (ht : 0 < t) (s : ℝ) (x : Fin 3 → ℝ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    ∃ x₀ ∈ coverGrid (coverScale t), ∃ y : Fin 3 → ℝ,
      ‖y‖ ≤ 1 / 2 ∧ coverMap s t x₀ (1, y) = (s + t, x) := by
  obtain ⟨x₀, hx₀, hdist⟩ := exists_coverGrid_point (coverScale_pos ht) x hx
  obtain ⟨y, hy, he⟩ := cover_terminal_preimage ht s x₀ x hdist
  exact ⟨x₀, hx₀, y, hy, he⟩

/-- Uniform interior bounds pass to every point of the closed fundamental cell. -/
theorem cover_grid_terminal_bound {t : ℝ} (ht : 0 < t) (s : ℝ)
    (v : ParabolicSpace → ℝ) (B : ℝ)
    (hv : ∀ x₀ ∈ coverGrid (coverScale t),
      ContinuousOn (fun z => v (coverMap s t x₀ z)) (closure (mwInnerCylinder (1 / 2))))
    (hb : ∀ x₀ ∈ coverGrid (coverScale t), ∀ z ∈ mwInnerCylinder (1 / 2),
      |v (coverMap s t x₀ z)| ≤ B)
    (x : Fin 3 → ℝ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) : |v (s + t, x)| ≤ B := by
  obtain ⟨x₀, hx₀, y, hy, he⟩ := exists_cover_terminal_patch ht s x hx
  have h := cover_terminal_bound s t x₀ v B (hv x₀ hx₀) (hb x₀ hx₀) y hy
  rwa [← coverMap_top, he] at h

end GlobalPhi43.Attachment
