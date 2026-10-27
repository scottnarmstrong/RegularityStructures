module

public import GlobalPhi43.Assembly.ComingDownZero
public import GlobalPhi43Statements.Defs.ComesDownFromInfinity
public import GlobalPhi43Statements.Defs.IsTimeHomogeneous

/-! # Conditional coming-down-from-infinity moments for a fixed flow and profile -/

public noncomputable section

open MeasureTheory RegularityStructures RegularityStructures.Phi43 Set Filter Topology
open scoped ENNReal NNReal

namespace GlobalPhi43.Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}

/-- Time homogeneity transfers finite weighted maxima; directed exhaustion then
transfers the all-data supremum. No supremum law is assumed. -/
theorem windowSup_moment_of_homogeneity
    (P : Measure Ω) {Ω₀ : Set Ω}
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (hu : IsContinuousMeasurableFlow Ω₀ u) (hh : IsTimeHomogeneous P u)
    {s : ℝ} (hs : 0 ≤ s) {p : ℝ} (hp : 0 < p) {C : ℝ≥0∞}
    (hzero : ∫⁻ ω, windowSup u 0 ω ^ p ∂P ≤ C) :
    ∫⁻ ω, windowSup u s ω ^ p ∂P ≤ C := by
  classical
  obtain ⟨d, _, hd⟩ := exists_dense_smooth_seq η
  obtain ⟨q, hq, _⟩ := exists_dense_rational_times
  simp_rw [windowSup_eq_countable hu hs _ hd q hq, Invariant.iSup_rpow_eq _ hp]
  apply Invariant.lintegral_iSup_le_of_finite P
    (fun i : ℕ × ℕ => fun ω => windowProbe u s ω (toHolderBesov η (d i.1), q i.2) ^ p)
    (fun i => ENNReal.continuous_rpow_const.measurable.comp
      (measurable_windowProbe hu hs _))
  intro F
  by_cases hF : F.Nonempty
  · let k := F.card
    let e : Fin k ≃ F := (Fintype.equivFinOfCardEq (Fintype.card_coe F)).symm
    let t (i : Fin k) : ℝ := q (e i).val.2
    let x (i : Fin k) := toHolderBesov η (d (e i).val.1)
    let U (r : ℝ) (ω : Ω) (i : Fin k) := u (r + t i) r (x i) ω
    let probe (v : Fin k → HolderBesov η) : ℝ≥0∞ :=
      ⨆ i, ENNReal.ofReal (√(t i) * ‖v i‖) ^ p
    have hm (r : ℝ) (hr : 0 ≤ r) : Measurable (U r) := by
      apply Measurable.of_eval
      intro i
      let ts : {a : ℝ × ℝ // 0 ≤ a.2 ∧ a.2 ≤ a.1} :=
        ⟨(r + t i, r), hr, by change r ≤ r + t i; dsimp [t]; linarith [(q (e i).val.2).property.1]⟩
      exact hu.1.comp ((measurable_const (a := ts)).prodMk
        ((measurable_const (a := x i)).prodMk measurable_id))
    have hprobe : Measurable probe := Measurable.iSup fun i =>
      ENNReal.continuous_rpow_const.measurable.comp (ENNReal.measurable_ofReal.comp
        (measurable_const.mul (measurable_pi_apply i).norm))
    have hlaw : P.map (U s) = P.map (U 0) := by
      simpa only [U, zero_add] using hh s hs k (Finset.card_pos.mpr hF) t
        (fun i => (q (e i).val.2).property.1.le) x
    have he (r : ℝ) (ω : Ω) :
        (⨆ i : F, windowProbe u r ω (toHolderBesov η (d i.val.1), q i.val.2) ^ p) =
          probe (U r ω) := by
      exact (e.iSup_comp).symm
    simp_rw [he s]
    calc
      _ = ∫⁻ v, probe v ∂P.map (U s) := (lintegral_map hprobe (hm s hs)).symm
      _ = ∫⁻ v, probe v ∂P.map (U 0) := by rw [hlaw]
      _ = ∫⁻ ω, probe (U 0 ω) ∂P := lintegral_map hprobe (hm 0 le_rfl)
      _ ≤ ∫⁻ ω, windowSup u 0 ω ^ p ∂P := by
        apply lintegral_mono
        intro ω
        change probe (U 0 ω) ≤ windowSup u 0 ω ^ p
        rw [← he 0 ω]
        apply iSup_le
        intro i
        apply ENNReal.rpow_le_rpow _ hp.le
        rw [windowSup_eq_countable hu (s := 0) le_rfl _ hd q hq ω]
        exact le_iSup (fun j : ℕ × ℕ =>
          windowProbe u 0 ω (toHolderBesov η (d j.1), q j.2)) i.val
      _ ≤ C := hzero
  · have : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    subst F
    simp

/-- Conditional coming-down-from-infinity moments. K is fixed before the noise space;
the regularised solution estimates and majorant moment bounds are explicit hypotheses.
The conclusion concerns the same u, including its value outside the full-probability event,
for every real deterministic start and every real p≥1. -/
theorem comesDownFromInfinity_of_reference (K : ℝ → ℝ≥0)
    {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}
    (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ) (a : ℝ)
    {Ω₀ : Set Ω} (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (hu : IsContinuousMeasurableFlow Ω₀ u)
    (hcons : IsConsistentWithTheoremA P W a η u) (hh : IsTimeHomogeneous P u)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (ξ : ℝ → Ω → SpaceTime → ℝ)
    (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
    (uε : ℝ → C(Torus3, ℝ) → Ω → ℝ → C(Torus3, ℝ))
    (hsol : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ x : C(Torus3, ℝ), IsSmoothOnTorus x → ∀ ω,
      IsClassicalSolution (a + 3 * wickConstant ρ ε - 9 * sunsetConstant ρ ε)
        (ξ ε ω) x (uε ε x ω))
    (M : ℝ → Ω → ℝ)
    (hM : ∀ ε ∈ Ioc (0 : ℝ) 1, Measurable (M ε) ∧ ∀ ω, 0 ≤ M ε ω)
    (hbound : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω (x : C(Torus3, ℝ)), IsSmoothOnTorus x →
      ∀ t ∈ Ioc (0 : ℝ) 1,
        ENNReal.ofReal (√t) * holderBesovENorm η (uε ε x ω t) ≤ ENNReal.ofReal (M ε ω))
    (hmoment : ∀ p : ℝ, 1 ≤ p →
      (⨆ ε ∈ Ioc (0 : ℝ) 1, ∫⁻ ω, ENNReal.ofReal (M ε ω) ^ p ∂P) ≤ K p) :
    ComesDownFromInfinity P K u := by
  intro s hs
  refine ⟨measurable_windowSup hu hs, fun p hp => ?_⟩
  exact windowSup_moment_of_homogeneity P u hu hh hs (lt_of_lt_of_le zero_lt_one hp)
    (windowSup_zero_moment K P W a u hu hcons ρ hρ ξ hξ uε hsol M hM hbound hmoment hp)

end GlobalPhi43.Assembly
