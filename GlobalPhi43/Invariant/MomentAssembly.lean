module

public import GlobalPhi43.Invariant.MomentTightness
public import GlobalPhi43.Invariant.LimitMoments
public import GlobalPhi43.Invariant.WeakLimit
public import GlobalPhi43.Invariant.AverageComparison

/-! # Conditional invariant-measure assembly with one shared moment witness -/

public noncomputable section

open MeasureTheory ProbabilityTheory RegularityStructures Filter Set Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace GlobalPhi43.Invariant

/-- A single late-average subsequence supplies full-average convergence, invariance,
and every stronger-exponent real moment. The profile is an input, not selected after μ.
The physical late-moment, orbit, semigroup and Feller premises remain explicit. -/
theorem exists_invariant_with_moments (η : NegExponent) (hη : (η : ℝ) < -(1 / 2 : ℝ))
    (K : ℝ≥0 → Kernel (HolderBesov η) (HolderBesov η))
    [∀ s, IsMarkovKernel (K s)]
    (hFeller : ∀ s (f : HolderBesov η →ᵇ ℝ),
      Continuous (fun x => ∫ y, f y ∂K s x))
    (ρ : Kernel ℝ (HolderBesov η)) [IsMarkovKernel ρ] (x : HolderBesov η)
    (horbit : ∀ t (ht : 0 ≤ t), ρ t = K ⟨t, ht⟩ x)
    (hsemi : ∀ s t, K (s + t) = K t ∘ₖ K s)
    (C : ℝ → ℝ → ℝ≥0∞)
    (hfinite : ∀ α, (η : ℝ) ≤ α → α < -(1 / 2 : ℝ) →
      ∀ p, 1 ≤ p → C α p ≠ ⊤)
    (hlate : ∀ α, (η : ℝ) ≤ α → α < -(1 / 2 : ℝ) →
      ∀ p, 1 ≤ p → ∀ T, 1 < T →
        ∫⁻ z, extNorm η α z ^ p ∂lateAverage ρ T ≤ C α p) :
    ∃ μ : ProbabilityMeasure (HolderBesov η), ∃ T : ℕ → ℝ,
      (∀ n, 1 < T n) ∧ Tendsto T atTop atTop ∧
      (∃ ν : ℕ → ProbabilityMeasure (HolderBesov η),
        (∀ n, (ν n : Measure _) = fullAverage ρ (T n)) ∧ Tendsto ν atTop (𝓝 μ)) ∧
      (∀ s : ℝ≥0, (K s) ∘ₘ (μ : Measure _) = (μ : Measure _)) ∧
      ∀ α, (η : ℝ) ≤ α → α < -(1 / 2 : ℝ) → ∀ p, 1 ≤ p →
        (∫⁻ z, extNorm η α z ^ p ∂(μ : Measure _)) ≤ C α p ∧
        (∫⁻ z, extNorm η α z ^ p ∂(μ : Measure _)) < ⊤ := by
  let γ : NegExponent := ⟨((η : ℝ) + -(1 / 2 : ℝ)) / 2, by nlinarith [η.property]⟩
  have hηγ : (η : ℝ) < γ := by dsimp [γ]; linarith
  have hγ : (γ : ℝ) < -(1 / 2 : ℝ) := by dsimp [γ]; linarith
  let times : ℕ → ℝ := fun n => (n : ℝ) + 2
  have ht (n : ℕ) : 1 < times n := by dsimp [times]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have ht0 (n : ℕ) : 0 < times n := lt_trans zero_lt_one (ht n)
  have htlim : Tendsto times atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  let late : ℕ → ProbabilityMeasure (HolderBesov η) := fun n =>
    ⟨lateAverage ρ (times n), intervalAverage_isProbabilityMeasure ρ (ht n)⟩
  let full : ℕ → ProbabilityMeasure (HolderBesov η) := fun n =>
    ⟨fullAverage ρ (times n), intervalAverage_isProbabilityMeasure ρ (ht0 n)⟩
  have htight : IsTightMeasureSet (range fun n => (late n : Measure (HolderBesov η))) := by
    apply holderBesov_isTightMeasureSet_of_moment η γ hηγ _
      (hfinite γ hηγ.le hγ 1 le_rfl)
    rintro _ ⟨n, rfl⟩
    change (∫⁻ z, extNorm η γ z ∂lateAverage ρ (times n)) ≤ C γ 1
    simpa only [ENNReal.rpow_one] using hlate γ hηγ.le hγ 1 le_rfl (times n) (ht n)
  obtain ⟨μ, φ, hφ, hlim⟩ := exists_tendsto_subseq_of_tight late htight
  have htimes := htlim.comp hφ.tendsto_atTop
  have hfull : Tendsto (full ∘ φ) atTop (𝓝 μ) :=
    tendsto_fullAverage_of_lateAverage ρ htimes (fun _ => rfl) (fun _ => rfl) hlim
  refine ⟨μ, times ∘ φ, fun n => ht (φ n), htimes,
    ⟨full ∘ φ, fun _ => rfl, hfull⟩, ?_, ?_⟩
  · exact fun s => weakLimit_invariant K hFeller ρ x horbit hsemi htimes
      (fun _ => rfl) hfull s
  · intro α hα hα' p hp
    have hm := holderBesov_weakLimit_moment_le η hlim α (le_trans zero_le_one hp)
      (fun n => hlate α hα hα' p hp (times (φ n)) (ht (φ n)))
    exact ⟨hm, hm.trans_lt (lt_top_iff_ne_top.mpr (hfinite α hα hα' p hp))⟩

end GlobalPhi43.Invariant
