module

public import GlobalPhi43.Assembly.WindowConsistency
public import GlobalPhi43.Assembly.StrongerWindow

/-! # Direct stronger-norm window transfer at start zero -/

public noncomputable section

open MeasureTheory RegularityStructures RegularityStructures.Phi43 Set Filter Topology
open scoped ENNReal NNReal

namespace GlobalPhi43.Assembly

/-- The reference profile is fixed before the noise space. The physical majorant
and source families remain explicit. Regularised-solution consistency, finite-family
Fatou and finite exhaustion give the completed-flow estimate with the same profile. -/
theorem strongWindowSup_zero_moment (K : ℝ → ℝ≥0) (α : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}
    (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ) (a : ℝ)
    {Ω₀ : Set Ω} (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (hu : IsContinuousMeasurableFlow Ω₀ u)
    (hcons : IsConsistentWithTheoremA P W a η u)
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
        ENNReal.ofReal (√t) * holderBesovENorm α (uε ε x ω t) ≤ ENNReal.ofReal (M ε ω))
    (hmoment : ∀ p : ℝ, 1 ≤ p →
      (⨆ ε ∈ Ioc (0 : ℝ) 1, ∫⁻ ω, ENNReal.ofReal (M ε ω) ^ p ∂P) ≤ K p)
    {p : ℝ} (hp : 1 ≤ p) : ∫⁻ ω, strongWindowSup α u 0 ω ^ p ∂P ≤ K p := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  obtain ⟨d, hd, hdd⟩ := exists_dense_smooth_seq η
  obtain ⟨q, hq, _⟩ := exists_dense_rational_times
  have he (ω : Ω) := strongWindowSup_eq_countable α hu (s := 0) le_rfl _ hdd q hq ω
  simp_rw [he, Invariant.iSup_rpow_eq _ hp0]
  apply Invariant.lintegral_iSup_le_of_finite P
    (fun i : ℕ × ℕ => fun ω =>
      strongerWindowProbe α u 0 ω (toHolderBesov η (d i.1), q i.2) ^ p)
    (fun i => ENNReal.continuous_rpow_const.measurable.comp
      (measurable_strongerWindowProbe α hu le_rfl _))
  intro F
  let f (n : ℕ) (i : F) (ω : Ω) :=
    toHolderBesov η (uε (referenceScale n) (d i.val.1) ω (q i.val.2))
  let g (i : F) (ω : Ω) := u (q i.val.2) 0 (toHolderBesov η (d i.val.1)) ω
  let N (i : F) (z : HolderBesov η) :=
    ENNReal.ofReal (√(q i.val.2 : ℝ)) * extNorm η α z
  have hc (i : F) : TendstoInMeasure P (fun n => f n i) atTop (g i) :=
    sample_tendstoInMeasure_of_B3 P W a u hcons ρ hρ ξ hξ (d i.val.1) (hd _)
      (fun ε => uε ε (d i.val.1))
      (fun ε hε ω => hsol ε hε _ (hd _) ω) (q i.val.2)
  have hn (i : F) : LowerSemicontinuous (N i) := by
    exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_lowerSemicontinuous
      (lowerSemicontinuous_extNorm η α) (fun _ _ h => mul_le_mul_right h _)
  have hb (n : ℕ) (i : F) : ∀ᵐ ω ∂P,
      N i (f n i ω) ≤ ENNReal.ofReal (M (referenceScale n) ω) := by
    apply Eventually.of_forall
    intro ω
    simpa only [N, f, extNorm_toHolderBesov] using
      hbound _ (referenceScale_mem n) ω _ (hd _) _ (q i.val.2).property
  have hm (n : ℕ) : ∫⁻ ω, ENNReal.ofReal (M (referenceScale n) ω) ^ p ∂P ≤ K p :=
    le_trans (le_iSup₂_of_le (referenceScale n) (referenceScale_mem n) le_rfl)
      (hmoment p hp)
  have hh := Invariant.lintegral_finite_iSup_rpow_le_of_tendstoInMeasure P f g hc N hn
    (fun n ω => ENNReal.ofReal (M (referenceScale n) ω))
    (fun n => ENNReal.measurable_ofReal.comp (hM _ (referenceScale_mem n)).1) hb hp0 hm
  simpa only [Invariant.iSup_rpow_eq _ hp0, N, g, strongerWindowProbe, zero_add] using hh

end GlobalPhi43.Assembly
