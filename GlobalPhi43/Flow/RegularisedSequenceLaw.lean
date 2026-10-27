module

public import GlobalPhi43.Attachment.RegularisedNoiseLaw
public import GlobalPhi43.Flow.NoiseWindowShift

/-! Mixed-scale finite laws and the law of the entire regularised family.
The coordinates may use different scales. No independence across scales is
asserted: every coordinate is driven by the same white noise. -/

public section

open MeasureTheory ProbabilityTheory RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

/-- White-noise finite-test laws identify arbitrary mixed-scale probes. -/
theorem regularisedFamily_finite_law {ι Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {W' : (SpaceTime → ℝ) → Ω' → ℝ}
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W')
    {ρ : ParabolicSpace → ℝ} (hρ : IsMollifier ρ) {ε : ι → ℝ} (hε : ∀ n, 0 < ε n)
    {ξ : ι → Ω → SpaceTime → ℝ} {ξ' : ι → Ω' → SpaceTime → ℝ}
    (hξ : ∀ n, IsRegularisedNoise P W ρ (ε n) (ξ n))
    (hξ' : ∀ n, IsRegularisedNoise P' W' ρ (ε n) (ξ' n))
    {m : ℕ} (p : Fin m → ι × SpaceTime) :
    P.map (fun ω i => ξ (p i).1 ω (p i).2) =
      P'.map (fun ω i => ξ' (p i).1 ω (p i).2) := by
  have hx : (fun ω i => ξ (p i).1 ω (p i).2) =ᵐ[P]
      (fun ω i => W (mollifierAt ρ (ε (p i).1) (p i).2) ω) :=
    (ae_all_iff.mpr fun i => ((hξ (p i).1).2 (p i).2).2).mono fun _ hi => funext hi
  have hy : (fun ω i => ξ' (p i).1 ω (p i).2) =ᵐ[P']
      (fun ω i => W' (mollifierAt ρ (ε (p i).1) (p i).2) ω) :=
    (ae_all_iff.mpr fun i => ((hξ' (p i).1).2 (p i).2).2).mono fun _ hi => funext hi
  rw [Measure.map_congr hx, Measure.map_congr hy]
  exact Attachment.whiteNoise_finite_law hW hW' _
    (fun i => memLp_mollifierAt ρ hρ (hε (p i).1) (p i).2)

/-- The whole indexed noise family has a common law on its coordinate carrier,
not merely a separate stationary law at each scale. -/
theorem regularisedFamily_identDistrib {ι Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {W : (SpaceTime → ℝ) → Ω → ℝ} {W' : (SpaceTime → ℝ) → Ω' → ℝ}
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W')
    {ρ : ParabolicSpace → ℝ} (hρ : IsMollifier ρ) {ε : ι → ℝ} (hε : ∀ n, 0 < ε n)
    {ξ : ι → Ω → SpaceTime → ℝ} {ξ' : ι → Ω' → SpaceTime → ℝ}
    (hξ : ∀ n, IsRegularisedNoise P W ρ (ε n) (ξ n))
    (hξ' : ∀ n, IsRegularisedNoise P' W' ρ (ε n) (ξ' n)) :
    IdentDistrib (fun ω (p : ι × SpaceTime) => ξ p.1 ω p.2)
      (fun ω (p : ι × SpaceTime) => ξ' p.1 ω p.2) P P' := by
  have hx : Measurable (fun ω (p : ι × SpaceTime) => ξ p.1 ω p.2) :=
    measurable_pi_iff.mpr fun p => ((hξ p.1).2 p.2).1
  have hy : Measurable (fun ω (p : ι × SpaceTime) => ξ' p.1 ω p.2) :=
    measurable_pi_iff.mpr fun p => ((hξ' p.1).2 p.2).1
  exact ⟨hx.aemeasurable, hy.aemeasurable, Attachment.process_map_eq_of_finite_law hx hy
    (fun _ p => regularisedFamily_finite_law hW hW' hρ hε hξ hξ' p)⟩

/-- Curried form on the literal entire sequence carrier. -/
theorem regularisedSequence_time_translate_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W) {ρ : ParabolicSpace → ℝ} (hρ : IsMollifier ρ)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) {ξ : ℕ → Ω → SpaceTime → ℝ}
    (hξ : ∀ n, IsRegularisedNoise P W ρ (ε n) (ξ n)) (s : ℝ) :
    IdentDistrib (fun ω n z => ξ n ω (z.1 + s, z.2)) (fun ω n z => ξ n ω z) P P := by
  have h := regularisedFamily_identDistrib (Attachment.whiteNoise_time_translate hW s) hW
    hρ hε (fun n => Attachment.regularisedNoise_time_translate (hξ n) s) hξ
  exact h.comp (u := fun F n z => F (n, z)) (by fun_prop)

end GlobalPhi43.Flow
