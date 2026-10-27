module

public import GlobalPhi43.Invariant.StrongTransfer
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Finite-family probability convergence and exact-constant Fatou transfer -/

public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace GlobalPhi43.Invariant

variable {Ω E ι : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace E]

/-- Each finite family admits one common a.e.-convergent subsequence. A global
countable a.e. convergence hypothesis is not required. -/
theorem exists_subseq_tendsto_ae_finite [Finite ι] (P : Measure Ω)
    (f : ℕ → ι → Ω → E) (g : ι → Ω → E)
    (h : ∀ i, TendstoInMeasure P (fun n => f n i) atTop (g i)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, ∀ᵐ ω ∂P, Tendsto (fun n => f (φ n) i ω) atTop (𝓝 (g i ω)) := by
  classical
  let := Fintype.ofFinite ι
  have aux (s : Finset ι) : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i ∈ s, ∀ᵐ ω ∂P, Tendsto (fun n => f (φ n) i ω) atTop (𝓝 (g i ω)) := by
    induction s using Finset.induction with
    | empty => exact ⟨id, strictMono_id, by simp⟩
    | @insert i s _ ih =>
      obtain ⟨φ, hφ, hprev⟩ := ih
      obtain ⟨ψ, hψ, hlim⟩ := ((h i).comp hφ.tendsto_atTop).exists_seq_tendsto_ae
      refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hlim
      · exact (hprev j hj).mono fun ω hω => hω.comp hψ.tendsto_atTop
  obtain ⟨φ, hφ, hlim⟩ := aux Finset.univ
  exact ⟨φ, hφ, fun i => hlim i (Finset.mem_univ i)⟩

/-- Finite lsc probes inherit a supplied majorant's moment constant from convergence
in probability. Every integral stays extended-valued; no limit bound is assumed. -/
theorem lintegral_finite_iSup_le_of_tendstoInMeasure [Finite ι] (P : Measure Ω)
    (f : ℕ → ι → Ω → E) (g : ι → Ω → E)
    (hconv : ∀ i, TendstoInMeasure P (fun n => f n i) atTop (g i))
    (N : ι → E → ℝ≥0∞) (hN : ∀ i, LowerSemicontinuous (N i))
    (B : ℕ → Ω → ℝ≥0∞) (hB : ∀ n, Measurable (B n))
    (hb : ∀ n i, ∀ᵐ ω ∂P, N i (f n i ω) ≤ B n ω)
    {C : ℝ≥0∞} (hC : ∀ n, ∫⁻ ω, B n ω ∂P ≤ C) :
    ∫⁻ ω, ⨆ i, N i (g i ω) ∂P ≤ C := by
  obtain ⟨φ, hφ, hlim⟩ := exists_subseq_tendsto_ae_finite P f g hconv
  have hi (i : ι) : ∀ᵐ ω ∂P, N i (g i ω) ≤ atTop.liminf (fun n => B (φ n) ω) := by
    filter_upwards [hlim i, ae_all_iff.mpr (fun n => hb (φ n) i)] with ω hc hm
    exact ((lowerSemicontinuousAt_iff_le_liminf.mp (hN i (g i ω))).trans
      hc.liminf_le_liminf_comp).trans (Filter.liminf_le_liminf (Eventually.of_forall hm))
  have hs : ∀ᵐ ω ∂P, (⨆ i, N i (g i ω)) ≤ atTop.liminf (fun n => B (φ n) ω) := by
    filter_upwards [ae_all_iff.mpr hi] with ω hω
    exact iSup_le hω
  exact (lintegral_mono_ae hs).trans ((lintegral_liminf_le (fun n => hB (φ n))).trans
    (by simpa using Filter.liminf_le_liminf (f := atTop) (Eventually.of_forall fun n => hC (φ n))))

/-- Positive real moments of the finite maximum retain exactly C. -/
theorem lintegral_finite_iSup_rpow_le_of_tendstoInMeasure [Finite ι] (P : Measure Ω)
    (f : ℕ → ι → Ω → E) (g : ι → Ω → E)
    (hconv : ∀ i, TendstoInMeasure P (fun n => f n i) atTop (g i))
    (N : ι → E → ℝ≥0∞) (hN : ∀ i, LowerSemicontinuous (N i))
    (B : ℕ → Ω → ℝ≥0∞) (hB : ∀ n, Measurable (B n))
    (hb : ∀ n i, ∀ᵐ ω ∂P, N i (f n i ω) ≤ B n ω)
    {p : ℝ} (hp : 0 < p) {C : ℝ≥0∞} (hC : ∀ n, ∫⁻ ω, B n ω ^ p ∂P ≤ C) :
    ∫⁻ ω, (⨆ i, N i (g i ω)) ^ p ∂P ≤ C := by
  simp_rw [iSup_rpow_eq _ hp]
  exact lintegral_finite_iSup_le_of_tendstoInMeasure P f g hconv (fun i z => N i z ^ p)
    (fun i => ENNReal.continuous_rpow_const.comp_lowerSemicontinuous (hN i)
      (fun _ _ h => ENNReal.rpow_le_rpow h hp.le)) (fun n ω => B n ω ^ p)
    (fun n => ENNReal.continuous_rpow_const.measurable.comp (hB n))
    (fun n i => (hb n i).mono fun _ h => ENNReal.rpow_le_rpow h hp.le) hC

/-- Directed finite exhaustion transfers unchanged bounds to a countable supremum. -/
theorem lintegral_iSup_le_of_finite [Countable ι] (P : Measure Ω)
    (G : ι → Ω → ℝ≥0∞) (hG : ∀ i, Measurable (G i)) {C : ℝ≥0∞}
    (hC : ∀ F : Finset ι, ∫⁻ ω, ⨆ i : F, G i ω ∂P ≤ C) :
    ∫⁻ ω, ⨆ i, G i ω ∂P ≤ C := by
  classical
  let A (F : Finset ι) (ω : Ω) := ⨆ i : F, G i ω
  have hs (ω : Ω) : (⨆ F : Finset ι, A F ω) = ⨆ i, G i ω := by
    apply le_antisymm
    · exact iSup_le fun F => iSup_le fun i => le_iSup (fun j => G j ω) i
    · refine iSup_le fun i => ?_
      exact le_iSup_of_le {i} (le_iSup_of_le
        (⟨i, Finset.mem_singleton_self i⟩ : ({i} : Finset ι)) le_rfl)
  have hm (F : Finset ι) : Measurable (A F) := Measurable.iSup fun i => hG i
  have hd : Directed (· ≤ ·) A := by
    intro F H
    refine ⟨F ∪ H, fun ω => ?_, fun ω => ?_⟩
    · exact iSup_le fun i => le_iSup_of_le
        (⟨i, Finset.mem_union_left H i.property⟩ : ↥(F ∪ H)) le_rfl
    · exact iSup_le fun i => le_iSup_of_le
        (⟨i, Finset.mem_union_right F i.property⟩ : ↥(F ∪ H)) le_rfl
  simp_rw [← hs]
  rw [lintegral_iSup_directed_of_measurable hm hd]
  exact iSup_le hC

end GlobalPhi43.Invariant
