module

public import GlobalPhi43.Assembly.WindowDense

/-! # The actual stronger heat-probe window, with countable dense reduction -/

@[expose] public noncomputable section

open MeasureTheory RegularityStructures Set Filter Topology
open scoped ENNReal

namespace GlobalPhi43.Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}

/-- An extended-valued stronger probe of the same eta-flow, without a new flow
or an exceptional-set replacement. -/
def strongerWindowProbe (α : ℝ)
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (s : ℝ) (ω : Ω) (p : HolderBesov η × Ioc (0 : ℝ) 1) : ℝ≥0∞ :=
  ENNReal.ofReal (√(p.2 : ℝ)) * extNorm η α (u (s + p.2) s p.1 ω)

/-- A stronger-norm analogue of windowSup. -/
def strongWindowSup (α : ℝ)
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) (s : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ p : HolderBesov η × Ioc (0 : ℝ) 1, strongerWindowProbe α u s ω p

/-- Supremum of continuous heat probes proves lsc even at infinite stronger norm. -/
theorem lowerSemicontinuous_strongerWindowProbe (α : ℝ) {Ω₀ : Set Ω}
    {u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η}
    (hu : IsContinuousMeasurableFlow Ω₀ u) {s : ℝ} (hs : 0 ≤ s) (ω : Ω) :
    LowerSemicontinuous (strongerWindowProbe α u s ω) := by
  have hm : Continuous (fun p : HolderBesov η × Ioc (0 : ℝ) 1 =>
      ((⟨s + p.2, by change s ≤ s + (p.2 : ℝ); linarith [p.2.property.1]⟩ : Ici s), p.1)) := by
    fun_prop
  have hc : Continuous (fun p : HolderBesov η × Ioc (0 : ℝ) 1 =>
      u (s + p.2) s p.1 ω) := (hu.2.2.1 ω s hs).comp hm
  change LowerSemicontinuous (fun p : HolderBesov η × Ioc (0 : ℝ) 1 =>
    ENNReal.ofReal (√(p.2 : ℝ)) * extNorm η α (u (s + p.2) s p.1 ω))
  simp only [extNorm, ENNReal.mul_iSup, ← mul_assoc]
  apply lowerSemicontinuous_iSup
  intro t
  apply lowerSemicontinuous_iSup
  intro x
  have hw : Continuous (fun p : HolderBesov η × Ioc (0 : ℝ) 1 =>
      ENNReal.ofReal (√(p.2 : ℝ)) * ENNReal.ofReal ((t : ℝ) ^ (-α / 2))) :=
    (ENNReal.continuous_mul_const ENNReal.ofReal_ne_top).comp
      (ENNReal.continuous_ofReal.comp (Real.continuous_sqrt.comp
        (continuous_subtype_val.comp continuous_snd)))
  exact (hw.ennreal_mul
    (continuous_enorm.comp ((continuous_heatAt η t x).comp hc))
    (fun _ => Or.inr enorm_ne_top)
    (fun _ => Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))).lowerSemicontinuous

/-- Dense reduction uses lsc, not continuity of the stronger norm. -/
theorem strongWindowSup_eq_countable (α : ℝ) {Ω₀ : Set Ω}
    {u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η}
    (hu : IsContinuousMeasurableFlow Ω₀ u) {s : ℝ} (hs : 0 ≤ s)
    (d : ℕ → HolderBesov η) (hd : DenseRange d)
    (q : ℕ → Ioc (0 : ℝ) 1) (hq : DenseRange q) (ω : Ω) :
    strongWindowSup α u s ω = ⨆ i : ℕ × ℕ, strongerWindowProbe α u s ω (d i.1, q i.2) :=
  Invariant.iSup_eq_iSup_dense (Prod.map d q) (hd.prodMap hq) _
    (lowerSemicontinuous_strongerWindowProbe α hu hs ω)

/-- Joint measurability of the flow gives each stronger-norm sample. -/
theorem measurable_strongerWindowProbe (α : ℝ) {Ω₀ : Set Ω}
    {u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η}
    (hu : IsContinuousMeasurableFlow Ω₀ u) {s : ℝ} (hs : 0 ≤ s)
    (p : HolderBesov η × Ioc (0 : ℝ) 1) :
    Measurable (fun ω => strongerWindowProbe α u s ω p) := by
  let ts : {r : ℝ × ℝ // 0 ≤ r.2 ∧ r.2 ≤ r.1} :=
    ⟨(s + p.2, s), hs, by change s ≤ s + (p.2 : ℝ); linarith [p.2.property.1]⟩
  have hm : Measurable (fun ω => u (s + p.2) s p.1 ω) :=
    hu.1.comp ((measurable_const (a := ts)).prodMk
      ((measurable_const (a := p.1)).prodMk measurable_id))
  exact measurable_const.mul ((measurable_extNorm η α).comp hm)

end GlobalPhi43.Assembly
