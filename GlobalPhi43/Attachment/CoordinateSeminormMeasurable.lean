module

public import GlobalPhi43.Attachment.CoordinateTestMeasurable

/-! Measurability of MW20's actual vector XV seminorm. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures MW20 Set

def unitCoordinateSeminorm (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (S : Set ParabolicSpace) (ε : ℝ) (V : ParabolicSpace → ℝ) : ENNReal :=
  ⨆ p : S × Ioo (0 : ℝ) 1,
    ENNReal.ofReal (p.2.1 ^ (2*ε) * ‖unitCoordinateTest Φ hΦ V (p.1.1, p.2.1)‖)

theorem recenteredXVSeminorm_eq_unit (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (S : Set ParabolicSpace) (ε : ℝ) (V : ParabolicSpace → ℝ) (hV : Continuous V) :
    recenteredXVSeminorm (mw20TestingKernel Φ hΦ) S ε V = unitCoordinateSeminorm Φ hΦ S ε V := by
  let H (p : S × Ioo (0 : ℝ) 1) : ENNReal :=
    ENNReal.ofReal (p.2.1 ^ (2 * ε) * ‖unitCoordinateTest Φ hΦ V (p.1.1, p.2.1)‖)
  change recenteredXVSeminorm (mw20TestingKernel Φ hΦ) S ε V = ⨆ p, H p
  apply le_antisymm
  · refine iSup₂_le fun x hx => iSup₂_le fun t ht => ?_
    change ENNReal.ofReal (t ^ (2 * ε) *
      ‖coordinateTreeTest (mw20TestingKernel Φ hΦ) V t x‖) ≤ _
    rw [coordinateTreeTest_eq_unit Φ hΦ V hV x ht.1 ht.2.le]
    exact le_iSup_of_le (⟨x, hx⟩, ⟨t, ht⟩) le_rfl
  · refine iSup_le fun p => ?_
    refine le_iSup₂_of_le p.1.1 p.1.2 (le_iSup₂_of_le p.2.1 p.2.2 ?_)
    change H p ≤ ENNReal.ofReal (p.2.1 ^ (2 * ε) *
      ‖coordinateTreeTest (mw20TestingKernel Φ hΦ) V p.2.1 p.1.1‖)
    rw [coordinateTreeTest_eq_unit Φ hΦ V hV p.1.1 p.2.2.1 p.2.2.2.le]

theorem unitCoordinateGauge_measurable {Ω : Type*} [MeasurableSpace Ω]
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (ε : ℝ)
    (V : Ω → ParabolicSpace → ℝ) (hc : ∀ ω, Continuous (V ω))
    (hm : ∀ x, Measurable (fun ω => V ω x)) (p : ParabolicSpace × ℝ) :
    Measurable (fun ω => ENNReal.ofReal (p.2 ^ (2*ε) * ‖unitCoordinateTest Φ hΦ (V ω) p‖)) :=
  (measurable_const.mul (unitCoordinateTest_measurable Φ hΦ V hc hm p).norm).ennreal_ofReal

theorem unitCoordinateGauge_continuous (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (S : Set ParabolicSpace) (ε : ℝ) (V : ParabolicSpace → ℝ) (hV : Continuous V) :
    Continuous (fun p : S × Ioo (0 : ℝ) 1 =>
      ENNReal.ofReal (p.2.1 ^ (2*ε) * ‖unitCoordinateTest Φ hΦ V (p.1.1, p.2.1)‖)) := by
  have hparam : Continuous (fun p : S × Ioo (0 : ℝ) 1 => (p.1.1, p.2.1)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  have hp : Continuous (fun p : S × Ioo (0 : ℝ) 1 => p.2.1 ^ (2 * ε)) :=
    (continuous_subtype_val.comp continuous_snd).rpow_const (fun p => Or.inl p.2.2.1.ne')
  exact ENNReal.continuous_ofReal.comp
    (hp.mul (((unitCoordinateTest_continuous Φ hΦ V hV).comp hparam).norm))

theorem unitCoordinateSeminorm_measurable {Ω : Type*} [MeasurableSpace Ω]
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (S : Set ParabolicSpace) (ε : ℝ)
    (V : Ω → ParabolicSpace → ℝ) (hc : ∀ ω, Continuous (V ω))
    (hm : ∀ x, Measurable (fun ω => V ω x)) :
    Measurable (fun ω => unitCoordinateSeminorm Φ hΦ S ε (V ω)) := by
  let H (p : S × Ioo (0 : ℝ) 1) (ω : Ω) : ENNReal :=
    ENNReal.ofReal (p.2.1 ^ (2*ε) * ‖unitCoordinateTest Φ hΦ (V ω) (p.1.1, p.2.1)‖)
  have hefun : (fun ω => unitCoordinateSeminorm Φ hΦ S ε (V ω)) =
      (⨆ p : S × Ioo (0 : ℝ) 1, H p) := by
    funext ω
    simp only [iSup_apply]
    rfl
  rw [hefun]
  exact measurable_iSup_of_lowerSemicontinuous
    (fun p => unitCoordinateGauge_measurable Φ hΦ ε V hc hm (p.1.1, p.2.1))
    (fun ω => (unitCoordinateGauge_continuous Φ hΦ S ε (V ω) (hc ω)).lowerSemicontinuous)

/-- The genuine vector supremum is measurable, retaining the open scale interval. -/
theorem recenteredXVSeminorm_measurable {Ω : Type*} [MeasurableSpace Ω]
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (S : Set ParabolicSpace) (ε : ℝ)
    (V : Ω → ParabolicSpace → ℝ) (hc : ∀ ω, Continuous (V ω))
    (hm : ∀ x, Measurable (fun ω => V ω x)) :
    Measurable (fun ω => recenteredXVSeminorm (mw20TestingKernel Φ hΦ) S ε (V ω)) := by
  have he : (fun ω => recenteredXVSeminorm (mw20TestingKernel Φ hΦ) S ε (V ω)) =
      (fun ω => unitCoordinateSeminorm Φ hΦ S ε (V ω)) :=
    funext fun ω => recenteredXVSeminorm_eq_unit Φ hΦ S ε (V ω) (hc ω)
  rw [he]
  exact unitCoordinateSeminorm_measurable Φ hΦ S ε V hc hm

end GlobalPhi43.Attachment
