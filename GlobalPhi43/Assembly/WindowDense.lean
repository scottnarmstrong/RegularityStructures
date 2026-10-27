module

public import GlobalPhi43.Flow.SmoothDensity
public import GlobalPhi43.Invariant.DenseSup
public import GlobalPhi43Statements.Defs.WindowSup
public import GlobalPhi43Statements.Defs.IsContinuousMeasurableFlow
public import Mathlib.Topology.Instances.Rat

/-! # Dense smooth data and rational observation times for the weighted window supremum -/

@[expose] public noncomputable section

open MeasureTheory RegularityStructures Set Filter Topology
open scoped ENNReal

namespace GlobalPhi43.Assembly

/-- The smooth data sequence is selected using only the state carrier, before any noise space. -/
theorem exists_dense_smooth_seq (η : NegExponent) :
    ∃ d : ℕ → C(Torus3, ℝ), (∀ i, IsSmoothOnTorus (d i)) ∧
      DenseRange (fun i => toHolderBesov η (d i)) := by
  classical
  let S : Set (HolderBesov η) := {z | ∃ f : C(Torus3, ℝ),
    IsSmoothOnTorus f ∧ toHolderBesov η f = z}
  have hS : Dense S := by
    apply Metric.dense_iff.mpr
    intro z ε hε
    obtain ⟨f, hf, _, hd⟩ := Flow.exists_smooth_approx_ball η z (R := ‖z‖) le_rfl hε
    exact ⟨toHolderBesov η f, hd, f, hf, rfl⟩
  obtain ⟨D, hDS, hDc, hDd⟩ := hS.exists_countable_dense_subset
  let := hDc.to_subtype
  let := hDd.nonempty.to_subtype
  obtain ⟨e, he⟩ := exists_surjective_nat D
  choose d hd hde using (fun n => hDS (e n).property)
  refine ⟨d, hd, hDd.mono ?_⟩
  intro z hz
  obtain ⟨n, hn⟩ := he ⟨z, hz⟩
  exact ⟨n, (hde n).trans (congrArg Subtype.val hn)⟩

/-- The observation sequence is rational, positive, at most one and dense even at t=1. -/
theorem exists_dense_rational_times :
    ∃ q : ℕ → Ioc (0 : ℝ) 1, DenseRange q ∧ ∀ n, ∃ r : ℚ, (q n : ℝ) = r := by
  classical
  let Q := {r : ℚ // 0 < r ∧ r ≤ 1}
  let toT : Q → Ioc (0 : ℝ) 1 := fun r => ⟨r.val, by exact_mod_cast r.property.1,
    by exact_mod_cast r.property.2⟩
  have hd : DenseRange toT := by
    apply Metric.dense_iff.mpr
    intro t ε hε
    have hgap : max 0 ((t : ℝ) - ε) < min 1 ((t : ℝ) + ε) := by
      apply lt_min
      · exact max_lt (by norm_num) (by linarith [t.property.2])
      · exact max_lt (by linarith [t.property.1]) (by linarith)
    obtain ⟨r, hr, hr'⟩ := exists_rat_btwn hgap
    have hr0 : 0 < (r : ℝ) := (le_max_left _ _).trans_lt hr
    have hr1 : (r : ℝ) ≤ 1 := hr'.le.trans (min_le_left _ _)
    let rq : Q := ⟨r, by exact_mod_cast hr0, by exact_mod_cast hr1⟩
    refine ⟨toT rq, ?_, ⟨rq, rfl⟩⟩
    change dist (r : ℝ) (t : ℝ) < ε
    rw [Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith [(le_max_right _ _).trans_lt hr],
      by linarith [hr'.trans_le (min_le_right _ _)]⟩
  have : Nonempty Q := ⟨⟨1, by norm_num⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat Q
  refine ⟨fun n => toT (e n), hd.mono ?_, fun n => ⟨(e n).val, rfl⟩⟩
  rintro _ ⟨r, rfl⟩
  obtain ⟨n, rfl⟩ := he r
  exact mem_range_self n

variable {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}

/-- A positive-time weighted probe of the supplied single flow. -/
def windowProbe (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (s : ℝ) (ω : Ω) (p : HolderBesov η × Ioc (0 : ℝ) 1) : ℝ≥0∞ :=
  ENNReal.ofReal (√(p.2 : ℝ) * ‖u (s + p.2) s p.1 ω‖)

theorem continuous_windowProbe {Ω₀ : Set Ω}
    {u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η}
    (hu : IsContinuousMeasurableFlow Ω₀ u) {s : ℝ} (hs : 0 ≤ s) (ω : Ω) :
    Continuous (windowProbe u s ω) := by
  have hm : Continuous (fun p : HolderBesov η × Ioc (0 : ℝ) 1 =>
      ((⟨s + p.2, by change s ≤ s + (p.2 : ℝ); linarith [p.2.property.1]⟩ : Ici s), p.1)) := by fun_prop
  exact ENNReal.continuous_ofReal.comp
    ((Real.continuous_sqrt.comp (continuous_subtype_val.comp continuous_snd)).mul
      (((hu.2.2.1 ω s hs).comp hm).norm))

/-- The window supremum equals the supremum over countably many dense data and times.
The equality also holds outside the full-probability event. -/
theorem windowSup_eq_countable {Ω₀ : Set Ω}
    {u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η}
    (hu : IsContinuousMeasurableFlow Ω₀ u) {s : ℝ} (hs : 0 ≤ s)
    (d : ℕ → HolderBesov η) (hd : DenseRange d)
    (q : ℕ → Ioc (0 : ℝ) 1) (hq : DenseRange q) (ω : Ω) :
    windowSup u s ω = ⨆ i : ℕ × ℕ, windowProbe u s ω (d i.1, q i.2) := by
  have he : windowSup u s ω = ⨆ p : HolderBesov η × Ioc (0 : ℝ) 1, windowProbe u s ω p := by
    simp only [windowSup, windowProbe, iSup_prod, iSup_subtype]
  rw [he]
  exact Invariant.iSup_eq_iSup_dense (Prod.map d q) (hd.prodMap hq) _
    (continuous_windowProbe hu hs ω).lowerSemicontinuous

/-- Joint measurability of the flow gives the measurable samples in the countable supremum. -/
theorem measurable_windowProbe {Ω₀ : Set Ω}
    {u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η}
    (hu : IsContinuousMeasurableFlow Ω₀ u) {s : ℝ} (hs : 0 ≤ s)
    (p : HolderBesov η × Ioc (0 : ℝ) 1) : Measurable (fun ω => windowProbe u s ω p) := by
  let ts : {r : ℝ × ℝ // 0 ≤ r.2 ∧ r.2 ≤ r.1} :=
    ⟨(s + p.2, s), hs, by change s ≤ s + (p.2 : ℝ); linarith [p.2.property.1]⟩
  have hm : Measurable (fun ω => u (s + p.2) s p.1 ω) :=
    hu.1.comp ((measurable_const (a := ts)).prodMk
      ((measurable_const (a := p.1)).prodMk measurable_id))
  exact ENNReal.measurable_ofReal.comp (measurable_const.mul hm.norm)

/-- Measurability of the all-data supremum, also outside the full-probability event. -/
theorem measurable_windowSup {Ω₀ : Set Ω}
    {u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η}
    (hu : IsContinuousMeasurableFlow Ω₀ u) {s : ℝ} (hs : 0 ≤ s) :
    Measurable (windowSup u s) := by
  obtain ⟨d, _, hd⟩ := exists_dense_smooth_seq η
  obtain ⟨q, hq, _⟩ := exists_dense_rational_times
  have he : windowSup u s = fun ω => ⨆ i : ℕ × ℕ,
      windowProbe u s ω (toHolderBesov η (d i.1), q i.2) :=
    funext fun ω => windowSup_eq_countable hu hs _ hd q hq ω
  rw [he]
  exact Measurable.iSup fun i => measurable_windowProbe hu hs _

end GlobalPhi43.Assembly
