module

public import GlobalPhi43.Local.DataScaling

public section

namespace GlobalPhi43.Local

open RegularityStructures Set
open scoped ContDiff

/-- Translated receiving adapter for a normalized local-data application.
Original PDEs live on D/E; genuine image containments and an actual smooth
neighbourhood of sigma(closure(P)) are supplied by the covering geometry. -/
theorem isMWLocalData_parabolicPullback
    (u ζ J Y Z e₁ e₂ e₃ : ParabolicSpace → ℝ) (C₁ C₂ : ℝ)
    (b : ParabolicSpace) (ℓ : ℝ) (O D E : Set ParabolicSpace)
    (hO : IsOpen O) (huO : ContDiffOn ℝ ∞ u O)
    (hKO : parabolicMap b ℓ '' closure mwCylinder ⊆ O)
    (hPD : parabolicMap b ℓ '' mwCylinder ⊆ D)
    (hPE : parabolicMap b ℓ '' parabolicClosedNbhd mwCylinder 1 ⊆ E)
    (hζ : ContDiff ℝ ∞ ζ) (hJ : ContDiff ℝ ∞ J) (hY : ContDiff ℝ ∞ Y)
    (hZ : ContDiff ℝ ∞ Z) (he₁ : ContDiff ℝ ∞ e₁) (he₂ : ContDiff ℝ ∞ e₂)
    (he₃ : ContDiff ℝ ∞ e₃)
    (hu : ∀ z ∈ D, heatOperator u z = -u z^3+ζ z+(3*C₁-9*C₂)*u z)
    (hTrees : ∀ z ∈ E,
      heatOperator J z = ζ z+e₁ z ∧ heatOperator Y z = J z^2-C₁+e₂ z ∧
      heatOperator Z z = J z^3-3*C₁*J z+e₃ z) :
    IsMWLocalData (parabolicPullback ℓ u b ℓ) (parabolicPullback (ℓ^3) ζ b ℓ)
      (parabolicPullback ℓ J b ℓ) (parabolicPullback 1 Y b ℓ)
      (parabolicPullback ℓ Z b ℓ) (parabolicPullback (ℓ^3) e₁ b ℓ)
      (parabolicPullback (ℓ^2) e₂ b ℓ) (parabolicPullback (ℓ^3) e₃ b ℓ)
      (ℓ^2*C₁) (ℓ^2*C₂) := by
  have hm : Continuous (parabolicMap b ℓ) := by
    unfold parabolicMap parabolicDilate
    fun_prop
  refine ⟨⟨parabolicMap b ℓ ⁻¹' O,hO.preimage hm,?_,parabolicPullback_contDiffOn ℓ u b ℓ huO⟩,
    parabolicPullback_contDiff _ _ _ _ hζ,parabolicPullback_contDiff _ _ _ _ hJ,
    parabolicPullback_contDiff _ _ _ _ hY,parabolicPullback_contDiff _ _ _ _ hZ,
    parabolicPullback_contDiff _ _ _ _ he₁,parabolicPullback_contDiff _ _ _ _ he₂,
    parabolicPullback_contDiff _ _ _ _ he₃,?_,?_⟩
  · intro x hx
    exact hKO ⟨x,hx,rfl⟩
  · intro x hx
    have hxO := hKO ⟨x,subset_closure hx,rfl⟩
    have hxD := hPD ⟨x,hx,rfl⟩
    rw [heatOperator_parabolicPullback ℓ u b ℓ hO huO x hxO,hu _ hxD]
    simp only [parabolicPullback]
    ring
  · intro x hx
    obtain ⟨hj,hy,hz⟩ := hTrees _ (hPE ⟨x,hx,rfl⟩)
    refine ⟨?_,?_,?_⟩
    · rw [heatOperator_parabolicPullback_global ℓ J b ℓ hJ,hj]
      simp only [parabolicPullback]
      ring
    · rw [heatOperator_parabolicPullback_global 1 Y b ℓ hY,hy]
      simp only [parabolicPullback]
      ring
    · rw [heatOperator_parabolicPullback_global ℓ Z b ℓ hZ,hz]
      simp only [parabolicPullback]
      ring

end GlobalPhi43.Local
