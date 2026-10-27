module

public import GlobalPhi43.Attachment.StartedRemainder
public import GlobalPhi43.Attachment.CoverTorusNorm
public import GlobalPhi43.Attachment.CoverFunctional
public import GlobalPhi43.Attachment.TreeFunctionalFiniteness
public import GlobalPhi43.Attachment.MajorantPolynomial
public import GlobalPhi43.Flow.MajorantLaterState

/-! Physical majorant bounds from the normalized scaling estimate and the
time-slice estimate at the same regularity and loss exponents. -/

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43 GlobalPhi43.MW20
open scoped ENNReal NNReal

namespace GlobalPhi43.Attachment

/-- Normalized bound for u-minus-J and the original nine-tree/three-defect
functional, uniformly over all smooth data. -/
@[expose] def NormalizedCoverRow (N : ℕ) (κ : Kappa) (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) (C : ℝ≥0) : Prop :=
  ∀ (a : Flow.LiftData N κ) (s : ℝ), 0 ≤ s →
    ∀ (q : C(Torus3, ℝ)) (hq : IsSmoothOnTorus q) (t : ℝ), t ∈ Ioc (0 : ℝ) 1 →
    ∀ x₀ ∈ coverGrid (coverScale t), ∀ z ∈ mwInnerCylinder (1/2),
      coverScale t * |startedRemainder a s q hq (coverMap 0 t x₀ z).1
        (torusProj (coverMap 0 t x₀ z).2)| ≤
      (C : ℝ) * max 2 (coverScale t *
        (attachmentFunctional N κ Φ hΦ a.forcing a.constants (Flow.coverRegion s)).toReal)

/-- Time-slice bound at the same regularity and loss exponents on the majorant region. -/
@[expose] def ActualSliceRow (N : ℕ) (κ : Kappa) (H : ℝ≥0) : Prop :=
  ∀ (a : Flow.LiftData N κ) (s : ℝ), 0 ≤ s → ∀ t ∈ Ioc (0 : ℝ) 1,
    ENNReal.ofReal (Real.sqrt t) * holderBesovENorm (Flow.lossExponent κ)
      (smoothNoiseJ N ⟨a.forcing, Flow.smooth_of_moderateLift a.moderate⟩ (s+t)) ≤
      (H : ℝ≥0∞) * (Flow.unitPotentialSize (Flow.lossExponent κ) s a.potential +
        (1+a.model.normOn (gamma κ) (Flow.majorantRegion s))^3)

/-- One finite coefficient works for every lift sequence, outcome, index, start
and initial datum. The normalized scaling and slice estimates are hypotheses;
the functional bound follows from the tree seminorm estimates. -/
theorem everyStartMajorant_of_normalized_cover_and_slice (N : ℕ) (κ : Kappa)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (C H : ℝ≥0)
    (hcover : NormalizedCoverRow N κ Φ hΦ C) (hslice : ActualSliceRow N κ H) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ A : ℕ → Flow.LiftData N κ, Flow.EveryStartMajorant c A := by
  obtain ⟨K, hK⟩ := cover_functional_bound N κ Φ hΦ
  refine ⟨(majorantCoefficient C K H : ℝ), (majorantCoefficient C K H).coe_nonneg, ?_⟩
  intro A n s hs q hq t ht
  let a := A n
  let M := attachmentFunctional N κ Φ hΦ a.forcing a.constants (Flow.coverRegion s)
  have hM : M ≠ ⊤ := attachmentFunctional_ne_top N κ Φ hΦ
    (Flow.smooth_of_moderateLift a.moderate) a.constants _ (isCompact_coverRegion s)
  have hv := cover_torus_norm_of_normalized_row ht 0 (startedRemainder a s q hq)
    (C : ℝ) M.toReal C.coe_nonneg ENNReal.toReal_nonneg
    (startedRemainder_continuousOn a s q hq) (hcover a s hs q hq t ht)
  simp only [zero_add, ENNReal.ofReal_toReal hM, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
    ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal] at hv
  have hη : (Flow.lossExponent κ : ℝ) ≤ 0 := (Flow.lossExponent κ).2.le
  have hb := majorant_norm_of_rows (Flow.lossExponent κ) hη C K H
    (Flow.smoothSolution (3*a.constants.1-9*a.constants.2)
      (shiftForcing s a.forcing) (a.shiftSmooth s) q hq t)
    (smoothNoiseJ N ⟨a.forcing, Flow.smooth_of_moderateLift a.moderate⟩ (s+t))
    (ENNReal.ofReal (Real.sqrt t)) M
    (a.model.normOn (gamma κ) (Flow.majorantRegion s))
    (Flow.unitPotentialSize (Flow.lossExponent κ) s a.potential)
    hv (hK a s) (hslice a s hs t ht)
  simpa only [Flow.windowMajorantRhs, ENNReal.ofReal_coe_nnreal] using hb

end GlobalPhi43.Attachment
