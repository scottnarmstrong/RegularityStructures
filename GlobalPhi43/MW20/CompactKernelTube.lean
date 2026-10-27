module

public import GlobalPhi43.MW20.CylinderTesting
public import GlobalPhi43.MW20.SourceHolderBound
public import Mathlib.Topology.Compactness.Compact

/-!
# Compact interior testing neighbourhoods for the actual source kernel
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Filter Topology Set

/-- The source inset cylinder is open. -/
theorem isOpen_sourceCylinder (R : ℝ) : IsOpen (sourceCylinder R) := by
  have hs : ∀ i : Fin 3, IsOpen {z : ParabolicSpace | |z.2 i| < 1 - R} := fun i =>
    isOpen_lt ((continuous_apply i).comp continuous_snd).abs continuous_const
  simpa only [sourceCylinder, ofPred_and, ofPred_forall] using
    (isOpen_lt (continuous_const : Continuous (fun _ : ParabolicSpace => R ^ 2))
      continuous_fst).inter
      ((isOpen_lt continuous_fst (continuous_const : Continuous (fun _ : ParabolicSpace => (1 : ℝ)))).inter (isOpen_iInter_of_finite hs))

/-- The topological support also lies in the exact closed past ball. -/
theorem infiniteKernel_tsupport_closedPast (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) :
    tsupport (infiniteKernel Φ hΦ T hT) ⊆
      {y | y.1 ≤ 0 ∧ Local.pdist 0 y ≤ T} := by
  have hd : Continuous (fun y : ParabolicSpace => Local.pdist 0 y) := by
    unfold Local.pdist; fun_prop
  apply closure_minimal
  · intro y hy
    exact infiniteKernel_closedPast_support Φ hΦ hT hT1 hy
  · exact (isClosed_le continuous_fst continuous_const).inter
      (isClosed_le hd continuous_const)

/-- The actual infinite measure is concentrated on the topological support
of its constructed density. -/
theorem infiniteKernelMeasure_ae_tsupport (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ y ∂infiniteKernelMeasure Φ hΦ T hT, y ∈ tsupport (infiniteKernel Φ hΦ T hT) := by
  unfold infiniteKernelMeasure
  apply (ae_withDensity_iff
    (infiniteKernel Φ hΦ T hT).continuous.measurable.ennreal_ofReal).2
  apply ae_of_all
  intro y hy
  apply subset_tsupport
  intro he
  simp [he] at hy

/-- Every strictly interior source test admits a whole compact testing tube.
The radius and the compact inset are constructed from the actual support,
not added as hypotheses of the later differentiation theorem. -/
theorem exists_compact_kernel_testing_tube (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T R : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (hTR : T < R)
    {x : ParabolicSpace} (hx : x ∈ sourceCylinder R) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧
      ∀ᵐ y ∂infiniteKernelMeasure Φ hΦ T hT,
        ∀ z ∈ Metric.ball x δ, z + y ∈ sourceClosedInset r := by
  let r := (R - T) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hcompact := infiniteKernel_hasCompactSupport Φ hΦ hT hT1
  have hpoint : ∀ y ∈ tsupport (infiniteKernel Φ hΦ T hT),
      x + y ∈ sourceCylinder r := by
    intro y hy
    have hs := infiniteKernel_tsupport_closedPast Φ hΦ hT hT1 hy
    have hrs : r ≤ R - T := by dsimp [r]; linarith
    exact sourceCylinder_antitone hr.le hrs
      (sourceCylinder_add_closedPast hT.le hTR.le hx hs.1 hs.2)
  have hevent : ∀ᶠ z in 𝓝 x,
      ∀ y ∈ tsupport (infiniteKernel Φ hΦ T hT), z + y ∈ sourceCylinder r := by
    apply hcompact.isCompact.eventually_forall_of_forall_eventually
    intro y hy
    exact (continuous_fst.add continuous_snd).continuousAt.preimage_mem_nhds
      ((isOpen_sourceCylinder r).mem_nhds (hpoint y hy))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨r, δ, hr, hδ, ?_⟩
  filter_upwards [infiniteKernelMeasure_ae_tsupport Φ hΦ hT] with y hy
  intro z hz
  exact sourceCylinder_subset_closedInset r (hball hz y hy)

end GlobalPhi43.MW20
