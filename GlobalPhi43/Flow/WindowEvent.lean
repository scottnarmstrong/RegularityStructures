module

public import GlobalPhi43.Flow.WindowDyadic
public import GlobalPhi43.Attachment.GrowthEvent

@[expose] public noncomputable section

open MeasureTheory Set RegularityStructures RegularityStructures.Phi43
open scoped ENNReal

namespace GlobalPhi43.Flow

/-- The literal loss exponent of Part 2. -/
def lossExponent (κ : Kappa) : NegExponent :=
  ⟨-(1 / 2 : ℝ) - κ.1, by linarith [κ.2.1]⟩

theorem lossExponent_lt (κ : Kappa) : (lossExponent κ : ℝ) < -(1 / 2 : ℝ) := by
  change -(1 / 2 : ℝ) - κ.1 < _
  linarith [κ.2.1]

/-- The displayed potential window is [-1,k], rather than the reference estimate's [-1,k+1]. -/
def potentialWindowSize (η k : ℝ) (ψ : ℝ → C(Torus3, ℝ)) : ℝ≥0∞ :=
  ⨆ r ∈ Icc (-1 : ℝ) k, holderBesovENorm η (ψ r)

theorem potentialWindowSize_le (η k : ℝ) (ψ : ℝ → C(Torus3, ℝ)) :
    potentialWindowSize η k ψ ≤ Statements.phi43NoiseSize η k ψ := by
  refine iSup₂_le fun r hr => ?_
  exact le_iSup₂_of_le r ⟨hr.1, by linarith [hr.2]⟩ le_rfl

/-- Every translated unit potential window is controlled pathwise by the displayed size. -/
theorem restart_potential_le (η k : ℝ) (ψ : ℝ → C(Torus3, ℝ))
    {r t : ℝ} (hr : 0 ≤ r) (hrk : r ≤ k - 18) (ht : t ∈ Icc r (r + 1)) :
    holderBesovENorm η (ψ t) ≤ potentialWindowSize η k ψ :=
  le_iSup₂_of_le t (potentialWindow_subset hr hrk ht) le_rfl

variable {Ω : Type*} {κ : Kappa}

/-- Literal E_win: the two countable intersections of finite dyadic suprema. -/
def windowEvent (η : ℝ)
    (Z : ℝ → Ω → Model (phi43RegularityStructure κ) parabolicSemigroup)
    (ψ : ℝ → Ω → ℝ → C(Torus3, ℝ)) : Set Ω :=
  {ω | ∀ k : ℕ, 18 ≤ k →
    (⨆ n : ℕ, (Z ((2⁻¹ : ℝ) ^ n) ω).normOn (gamma κ) (windowSet k)) < ⊤ ∧
    (⨆ n : ℕ, potentialWindowSize η k (ψ ((2⁻¹ : ℝ) ^ n) ω)) < ⊤}

/-- The countable Cauchy event retains the same sequence for every k. -/
def windowCauchyEvent (η : ℝ)
    (Z : ℝ → Ω → Model (phi43RegularityStructure κ) parabolicSemigroup)
    (ψ : ℝ → Ω → ℝ → C(Torus3, ℝ)) : Set Ω :=
  {ω | ∀ k : ℕ, 18 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀,
    (Z ((2⁻¹ : ℝ) ^ n) ω).diffNormOn (Z ((2⁻¹ : ℝ) ^ m) ω) (gamma κ) (windowSet k) +
      Statements.phi43NoiseDist η k (ψ ((2⁻¹ : ℝ) ^ n) ω) (ψ ((2⁻¹ : ℝ) ^ m) ω) ≤
        ENNReal.ofReal δ}

/-- Completeness makes the literal full event measurable, with no replacement by a subset. -/
theorem measurableSet_measure_one_of_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete] {s : Set Ω}
    (hs : ∀ᵐ ω ∂P, ω ∈ s) : MeasurableSet s ∧ P s = 1 := by
  have hc : P sᶜ = 0 := ae_iff.mp hs
  have hm : MeasurableSet s := by simpa only [compl_compl] using (measurableSet_of_null hc).compl
  exact ⟨hm, (prob_compl_eq_zero_iff hm).mp hc⟩

universe u

variable {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
  (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa) (N : ℕ) (hN : 5 ≤ N)
  (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (a : ℝ)
  (ξ : ℝ → Ω → SpaceTime → ℝ)
  (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
  (Z : ℝ → Ω → Model (phi43RegularityStructure κ) parabolicSemigroup)
  (ψ : ℝ → Ω → ℝ → C(Torus3, ℝ))
  (hlift : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
    Statements.IsModeratePhi43Lift N κ (ξ ε ω)
      (wickConstant ρ ε + a / 3, sunsetConstant ρ ε + 0) (Z ε ω) (ψ ε ω))

include W hW hκE N hN ρ hρ a ξ hξ hlift

/-- The actual window event and simultaneous Cauchy event both have probability one. -/
theorem ae_window_events : ∀ᵐ ω ∂P,
    ω ∈ windowEvent (lossExponent κ) Z ψ ∧ ω ∈ windowCauchyEvent (lossExponent κ) Z ψ := by
  have h (k : ℕ) : ∀ᵐ ω ∂P, 18 ≤ k →
      (∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀,
        (Z ((2⁻¹ : ℝ) ^ n) ω).diffNormOn (Z ((2⁻¹ : ℝ) ^ m) ω) (gamma κ) (windowSet k) +
          Statements.phi43NoiseDist (lossExponent κ) k
            (ψ ((2⁻¹ : ℝ) ^ n) ω) (ψ ((2⁻¹ : ℝ) ^ m) ω) ≤ ENNReal.ofReal δ) ∧
      ∃ B : ℝ, ∀ n : ℕ, (Z ((2⁻¹ : ℝ) ^ n) ω).normOn (gamma κ) (windowSet k) +
        Statements.phi43NoiseSize (lossExponent κ) k (ψ ((2⁻¹ : ℝ) ^ n) ω) ≤ ENNReal.ofReal B := by
    by_cases hk : 18 ≤ k
    · exact (ae_window_dyadic P W hW κ hκE N hN ρ hρ a ξ hξ Z ψ hlift
        (lossExponent κ) (lossExponent_lt κ) k (by exact_mod_cast hk)).mono fun _ hω _ => hω
    · exact ae_of_all _ fun _ hk' => (hk hk').elim
  filter_upwards [ae_all_iff.2 h] with ω hω
  constructor
  · intro k hk
    obtain ⟨B, hB⟩ := (hω k hk).2
    constructor
    · exact (iSup_le fun n => (le_add_right le_rfl).trans (hB n)).trans_lt ENNReal.ofReal_lt_top
    · exact (iSup_le fun n => (potentialWindowSize_le _ _ _).trans
        ((le_add_left le_rfl).trans (hB n))).trans_lt ENNReal.ofReal_lt_top
  · intro k hk
    exact (hω k hk).1

/-- The literal E_win and its companion Cauchy event are measurable probability-one sets. -/
theorem window_events_measurable_measure_one [P.IsComplete] :
    (MeasurableSet (windowEvent (lossExponent κ) Z ψ) ∧
      P (windowEvent (lossExponent κ) Z ψ) = 1) ∧
    (MeasurableSet (windowCauchyEvent (lossExponent κ) Z ψ) ∧
      P (windowCauchyEvent (lossExponent κ) Z ψ) = 1) := by
  have h := ae_window_events P W hW κ hκE N hN ρ hρ a ξ hξ Z ψ hlift
  exact ⟨measurableSet_measure_one_of_ae P (h.mono fun _ hω => hω.1),
    measurableSet_measure_one_of_ae P (h.mono fun _ hω => hω.2)⟩

end GlobalPhi43.Flow
