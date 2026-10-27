module

public import GlobalPhi43.MW20.CoordinateSeminorm

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set
open scoped ENNReal

/-- Pure cutoff monotonicity for the actual testing supremum. -/
theorem localTestSeminorm_mono_scales (K : ℝ → Measure ParabolicSpace)
    (D : Set ParabolicSpace) {I J : Set ℝ} (hIJ : I ⊆ J) (α : ℝ)
    (G : ParabolicSpace → ParabolicSpace → ℝ) :
    localTestSeminorm K D I α G ≤ localTestSeminorm K D J α G := by
  unfold localTestSeminorm
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun t => iSup_le fun ht => ?_
  exact le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le t (le_iSup_of_le (hIJ ht) le_rfl)))

/-- For covering scales at most one, ordinary truncated norms use the original
source unit-scale norm; the endpoint at one is kept. -/
theorem localTestSeminorm_Ioc_scale_le (K : ℝ → Measure ParabolicSpace)
    (D : Set ParabolicSpace) {ℓ : ℝ} (hℓ : ℓ ≤ 1) (α : ℝ)
    (G : ParabolicSpace → ParabolicSpace → ℝ) :
    localTestSeminorm K D (Ioc 0 ℓ) α G ≤ localTestSeminorm K D (Ioc 0 1) α G :=
  localTestSeminorm_mono_scales K D (I := Ioc 0 ℓ) (J := Ioc 0 1)
    (fun _ ht => ⟨ht.1,ht.2.trans hℓ⟩) α G

theorem localTestSeminorm_Ioo_scale_le (K : ℝ → Measure ParabolicSpace)
    (D : Set ParabolicSpace) {ℓ : ℝ} (hℓ : ℓ ≤ 1) (α : ℝ)
    (G : ParabolicSpace → ParabolicSpace → ℝ) :
    localTestSeminorm K D (Ioo 0 ℓ) α G ≤ localTestSeminorm K D (Ioo 0 1) α G :=
  localTestSeminorm_mono_scales K D (I := Ioo 0 ℓ) (J := Ioo 0 1)
    (fun _ ht => ⟨ht.1,ht.2.trans_le hℓ⟩) α G

/-- The same pure cutoff comparison for the actual vector XV test. -/
theorem coordinateTree_truncated_le (K : ℝ → Measure ParabolicSpace)
    (D : Set ParabolicSpace) {ℓ : ℝ} (hℓ : ℓ ≤ 1) (κ : ℝ) (V : ParabolicSpace → ℝ) :
    (⨆ x ∈ D, ⨆ t ∈ Ioo (0 : ℝ) ℓ,
      ENNReal.ofReal (t^(2*κ)*‖coordinateTreeTest K V t x‖)) ≤ recenteredXVSeminorm K D κ V := by
  unfold recenteredXVSeminorm
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun t => iSup_le fun ht => ?_
  exact le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le t
    (le_iSup_of_le (show t ∈ Ioo (0 : ℝ) 1 from ⟨ht.1,ht.2.trans_le hℓ⟩) le_rfl)))

end GlobalPhi43.MW20
