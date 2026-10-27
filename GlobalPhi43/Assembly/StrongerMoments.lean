module

public import GlobalPhi43.Assembly.StrongerTransfer
public import GlobalPhi43Statements.Defs.IsTimeHomogeneous

/-! # Direct conditional stronger-window moments for the same eta-flow -/

public noncomputable section

open MeasureTheory RegularityStructures RegularityStructures.Phi43 Set Filter Topology
open scoped ENNReal NNReal

namespace GlobalPhi43.Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}

/-- Time homogeneity transfers finite weighted maxima; directed exhaustion then
transfers the all-data supremum. No supremum law is assumed. -/
theorem strongWindowSup_moment_of_homogeneity
    (P : Measure Ω) (α : ℝ) {Ω₀ : Set Ω}
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (hu : IsContinuousMeasurableFlow Ω₀ u) (hh : IsTimeHomogeneous P u)
    {s : ℝ} (hs : 0 ≤ s) {p : ℝ} (hp : 0 < p) {C : ℝ≥0∞}
    (hzero : ∫⁻ ω, strongWindowSup α u 0 ω ^ p ∂P ≤ C) :
    ∫⁻ ω, strongWindowSup α u s ω ^ p ∂P ≤ C := by
  classical
  obtain ⟨d, _, hd⟩ := exists_dense_smooth_seq η
  obtain ⟨q, hq, _⟩ := exists_dense_rational_times
  simp_rw [strongWindowSup_eq_countable α hu hs _ hd q hq, Invariant.iSup_rpow_eq _ hp]
  apply Invariant.lintegral_iSup_le_of_finite P
    (fun i : ℕ × ℕ => fun ω => strongerWindowProbe α u s ω (toHolderBesov η (d i.1), q i.2) ^ p)
    (fun i => ENNReal.continuous_rpow_const.measurable.comp
      (measurable_strongerWindowProbe α hu hs _))
  intro F
  by_cases hF : F.Nonempty
  · let k := F.card
    let e : Fin k ≃ F := (Fintype.equivFinOfCardEq (Fintype.card_coe F)).symm
    let t (i : Fin k) : ℝ := q (e i).val.2
    let x (i : Fin k) := toHolderBesov η (d (e i).val.1)
    let U (r : ℝ) (ω : Ω) (i : Fin k) := u (r + t i) r (x i) ω
    let probe (v : Fin k → HolderBesov η) : ℝ≥0∞ :=
      ⨆ i, (ENNReal.ofReal (√(t i)) * extNorm η α (v i)) ^ p
    have hm (r : ℝ) (hr : 0 ≤ r) : Measurable (U r) := by
      apply Measurable.of_eval
      intro i
      let ts : {a : ℝ × ℝ // 0 ≤ a.2 ∧ a.2 ≤ a.1} :=
        ⟨(r + t i, r), hr, by change r ≤ r + t i; dsimp [t]; linarith [(q (e i).val.2).property.1]⟩
      exact hu.1.comp ((measurable_const (a := ts)).prodMk
        ((measurable_const (a := x i)).prodMk measurable_id))
    have hprobe : Measurable probe := Measurable.iSup fun i =>
      ENNReal.continuous_rpow_const.measurable.comp (measurable_const.mul
        ((measurable_extNorm η α).comp (measurable_pi_apply i)))
    have hlaw : P.map (U s) = P.map (U 0) := by
      simpa only [U, zero_add] using hh s hs k (Finset.card_pos.mpr hF) t
        (fun i => (q (e i).val.2).property.1.le) x
    have he (r : ℝ) (ω : Ω) :
        (⨆ i : F, strongerWindowProbe α u r ω (toHolderBesov η (d i.val.1), q i.val.2) ^ p) =
          probe (U r ω) := by
      exact (e.iSup_comp).symm
    simp_rw [he s]
    calc
      _ = ∫⁻ v, probe v ∂P.map (U s) := (lintegral_map hprobe (hm s hs)).symm
      _ = ∫⁻ v, probe v ∂P.map (U 0) := by rw [hlaw]
      _ = ∫⁻ ω, probe (U 0 ω) ∂P := lintegral_map hprobe (hm 0 le_rfl)
      _ ≤ ∫⁻ ω, strongWindowSup α u 0 ω ^ p ∂P := by
        apply lintegral_mono
        intro ω
        change probe (U 0 ω) ≤ strongWindowSup α u 0 ω ^ p
        rw [← he 0 ω]
        apply iSup_le
        intro i
        apply ENNReal.rpow_le_rpow _ hp.le
        rw [strongWindowSup_eq_countable α hu (s := 0) le_rfl _ hd q hq ω]
        exact le_iSup (fun j : ℕ × ℕ =>
          strongerWindowProbe α u 0 ω (toHolderBesov η (d j.1), q j.2)) i.val
      _ ≤ C := hzero
  · have : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    subst F
    simp

end GlobalPhi43.Assembly
