module

public import GlobalPhi43.Invariant.InvariantMeasureExistence
public import GlobalPhi43.Invariant.StationarySolution
public import GlobalPhi43Statements.Defs.IsGlobalPhi43Flow

public noncomputable section

open MeasureTheory ProbabilityTheory RegularityStructures Set Filter Topology
open scoped ENNReal NNReal

namespace GlobalPhi43.Assembly

/-- Invariant-measure existence and stationarity for the same flow.
The two moment bounds are explicit hypotheses. One selected measure is a
weak limit of averagedLaw and gives stationarity on P.prod mu. -/
theorem exists_global_of_moments (K : ℝ → ℝ≥0) (C : ℝ → ℝ → ℝ≥0)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {η : NegExponent} (hη : (η : ℝ) < -(1 / 2 : ℝ))
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W) (a : ℝ)
    (E : Set Ω) (hE : MeasurableSet E) (hfull : P E = 1)
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (h1 : IsContinuousMeasurableFlow E u) (h2 : IsWindowAdapted P W u)
    (h3 : IsConsistentWithTheoremA P W a η u) (h4 : ComesDownFromInfinity P K u)
    (h5 : IsTimeHomogeneous P u) (h6 : IsFellerMarkovFlow P W u)
    (hstrong : ∀ α, (η : ℝ) ≤ α → α < -(1 / 2 : ℝ) → ∀ p : ℝ, 1 ≤ p →
      (⨆ r ≥ (0 : ℝ), ∫⁻ ω, strongWindowSup α u r ω ^ p ∂P) ≤ C α p) :
    ∃ μ : ProbabilityMeasure (HolderBesov η),
      IsGlobalPhi43Flow K P W a η E u (μ : Measure _) ∧
      ∀ α, (η : ℝ) ≤ α → α < -(1 / 2 : ℝ) → ∀ p : ℝ, 1 ≤ p →
        ∫⁻ z, extNorm η α z ^ p ∂(μ : Measure _) ≤ C α p := by
  obtain ⟨μ, h7, hmom⟩ := Invariant.exists_invariantMeasure C P hη W u h1 h6 hstrong
  have h8 := Invariant.isStationarySolution_of_isKrylovBogoliubovInvariant P W hW u h1 h6 (μ : Measure _) h7
  exact ⟨μ, ⟨hE, hfull, h1, h2, h3, h4, h5, h6, inferInstance, h7, h8⟩, hmom⟩

end GlobalPhi43.Assembly
