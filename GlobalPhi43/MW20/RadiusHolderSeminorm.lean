module

public import GlobalPhi43.MW20.AffineSeminorm

/-! Actual radius-local Holder seminorms in the max parabolic
metric, for scalar fields and spatial coefficient fields alike. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set
open scoped ENNReal

/-- Radius-local, two-sided source Holder supremum. -/
@[expose] noncomputable def radiusHolderSeminorm {E : Type*} [SeminormedAddCommGroup E]
    (f : ParabolicSpace → E) (D : Set ParabolicSpace) (α L : ℝ) : ℝ≥0∞ :=
  ⨆ x ∈ D, ⨆ y ∈ D, ⨆ (_ : pdist x y ≤ L ∧ y ≠ x),
    ENNReal.ofReal (‖f x - f y‖ / pdist x y ^ α)

/-- Increment extraction with exactly the source radius restriction. -/
theorem radiusHolderSeminorm_increment_bound {E : Type*} [SeminormedAddCommGroup E]
    (f : ParabolicSpace → E) (D : Set ParabolicSpace) (α L : ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hnorm : radiusHolderSeminorm f D α L ≤ ENNReal.ofReal C)
    {x y : ParabolicSpace} (hx : x ∈ D) (hy : y ∈ D) (hxy : pdist x y ≤ L) :
    ‖f x - f y‖ ≤ C * pdist x y ^ α := by
  by_cases he : y = x
  · subst y
    simpa only [sub_self, norm_zero] using mul_nonneg hC (Real.rpow_nonneg (pdist_nonneg x x) α)
  · have hall : ∀ x ∈ D, ∀ y ∈ D, ∀ (_ : pdist x y ≤ L ∧ y ≠ x),
        ENNReal.ofReal (‖f x - f y‖ / pdist x y ^ α) ≤ ENNReal.ofReal C := by
      simpa only [radiusHolderSeminorm, iSup_le_iff] using hnorm
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (pdist_pos_of_ne he) _)).mp
      ((ENNReal.ofReal_le_ofReal_iff hC).mp (hall x hx y hy ⟨hxy, he⟩))

/-- Restricting both the point domain and the testing radius decreases the
actual truncated norm. -/
theorem radiusHolderSeminorm_mono {E : Type*} [SeminormedAddCommGroup E]
    (f : ParabolicSpace → E) {D₁ D₂ : Set ParabolicSpace} {α L₁ L₂ : ℝ}
    (hD : D₁ ⊆ D₂) (hL : L₁ ≤ L₂) :
    radiusHolderSeminorm f D₁ α L₁ ≤ radiusHolderSeminorm f D₂ α L₂ := by
  have hall : ∀ x ∈ D₂, ∀ y ∈ D₂, ∀ (_ : pdist x y ≤ L₂ ∧ y ≠ x),
      ENNReal.ofReal (‖f x - f y‖ / pdist x y ^ α) ≤ radiusHolderSeminorm f D₂ α L₂ := by
    simpa only [radiusHolderSeminorm, iSup_le_iff] using
      (le_rfl : radiusHolderSeminorm f D₂ α L₂ ≤ radiusHolderSeminorm f D₂ α L₂)
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  apply iSup_le
  intro hh
  exact hall x (hD hx) y (hD hy) ⟨hh.1.trans hL, hh.2⟩

end GlobalPhi43.MW20
