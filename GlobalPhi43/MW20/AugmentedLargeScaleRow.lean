module

public import GlobalPhi43.MW20.AugmentedUnsmoothedMaximum
public import GlobalPhi43.MW20.SourceCommutatorRoot

/-!
# The augmented large-scale row MW20 (4.31)
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures

/-- Replacing the actual commutator root retains the separate defect cost. -/
theorem augmented_commutator_replacement {E q A B C D P F : ℝ}
    (hq : 0 ≤ q) (hD : D ≤ 2 * P) :
    46 * max E (max q (max (max (max A B) (max C D)) F)) ≤
      92 * max (max q E) (max P (max A (max B (max C F)))) := by
  let K := max (max q E) (max P (max A (max B (max C F))))
  have hqK : q ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hEK : E ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have hPK : P ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hAK : A ≤ K := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hBK : B ≤ K := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hCK : C ≤ K := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hFK : F ≤ K := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hK : 0 ≤ K := hq.trans hqK
  have hmax : max E (max q (max (max (max A B) (max C D)) F)) ≤ 2 * K :=
    max_le (by linarith) (max_le (by linarith)
      (max_le (max_le (max_le (by linarith) (by linarith))
        (max_le (by linarith) (by linarith))) (by linarith)))
  change _ ≤ 92 * K
  nlinarith

/-- MW20 (4.31), retaining the exact smoothing, commutator and three forcing
norm powers, with the universal numerical constant 92 and the original defect root. -/
theorem mw20_augmented_row_4_31 (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {v J V W e : ParabolicSpace → ℝ} (hv : SourceCubicRegularity v)
    (hJ : ContinuousOn J sourceClosedCylinder) (hV : ContinuousOn V sourceClosedCylinder)
    (hW : ContinuousOn W sourceClosedCylinder)
    (he : ContinuousOn e sourceClosedCylinder) (C₂ : ℝ)
    (hPDE : ∀ z ∈ sourceCylinder 0,
      sourceHeat v z = -v z ^ 3 - 3 * (v z ^ 2 * J z) - 3 * (v z * V z) -
        W z - 9 * C₂ * (v z + J z) - e z)
    {T S R α E₁ : ℝ}
    (he₁ : ∀ z ∈ sourceCylinder 0, |e z| ≤ E₁) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hT : 0 < T) (hTS : T < S) (hSR : S < R) (hR : R ≤ 1 / 2) :
    let μ := infiniteKernelMeasure Φ hΦ T hT
    let A := pastSmooth μ (fun z => v z ^ 2 * J z)
    let B := fun z => pastSmooth μ (fun y => v y * V y) z +
      3 * C₂ * (pastSmooth μ v z + pastSmooth μ J z)
    let C := pastSmooth μ W
    sourceSup v R ≤ 92 * max
      (max (1 / (R - S)) (sourceHolder v α (R - T) (2 * T) * T ^ α))
      (max (cubicCommutatorScale (sourceSup v (S - T))
        (sourceHolder v α (S - T) (2 * T)) T α)
        (max (sourceSup A S ^ (1 / 3 : ℝ))
          (max (sourceSup B S ^ (1 / 3 : ℝ)) (max (sourceSup C S ^ (1 / 3 : ℝ)) (E₁ ^ (1 / 3 : ℝ)))))) := by
  have h29 := mw20_augmented_row_4_29 Φ hΦ hv hJ hV hW he C₂ hPDE he₁ hα0 hα1 hT hTS hSR hR
  have hroot := source_cubic_commutator_root Φ hΦ hv hT hTS (hSR.le.trans hR) hα0 hα1
  dsimp only at h29 ⊢
  unfold fourForcingRoot at h29
  simp only [pastSmooth] at h29 ⊢
  exact h29.trans (augmented_commutator_replacement
    (by positivity : 0 ≤ 1 / (R - S)) hroot)

end GlobalPhi43.MW20
