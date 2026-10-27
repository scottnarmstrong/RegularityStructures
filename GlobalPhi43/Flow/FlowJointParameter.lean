module

public import GlobalPhi43.Flow.RoughWindowMeasurable
public import GlobalPhi43.Flow.ClassicalJointMeasurable

public noncomputable section

open MeasureTheory Set Filter Topology RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.Flow

section Reference

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
  {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
  (N : ℕ) (hN : 5 ≤ N) (κ : Kappa) (hκE : κ.1 ∉ Statements.excludedKappa)
  (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (mass : ℝ)
  (η : NegExponent) (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
  (hκη : κ.1 < -(1 / 2 : ℝ) - η)
  (ξ : ℝ → Ω → SpaceTime → ℝ)
  (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))

include hW hN hκE hρ hη hκη

local notation "hsmooth" => (fun ε hε => And.left (hξ ε hε))
local notation "E" => referenceEvent N κ ρ mass η ξ hsmooth
local notation "A" => (fun ω : E => dyadicLiftData N κ ρ mass η ξ hsmooth (Subtype.val ω) (Subtype.property ω))

/-- Ambient joint start/observation/noise measurability for smooth data.
Continuity in the rough start is neither used nor asserted. -/
theorem referenceFlow_smooth_parameter_measurable (u : EventFlow E η A)
    (x : C(Torus3, ℝ)) (hx : IsSmoothOnTorus x) :
    Measurable (fun p : (ℝ × Ici (0 : ℝ)) × Ω =>
      u.value p.2 (max p.1.1 p.1.2.val) p.1.2.val (toHolderBesov η x)) := by
  classical
  obtain ⟨he, _⟩ := referenceEvent_measurable_measure_one P W hW N hN κ hκE
    ρ hρ mass η hη hκη ξ hξ
  let b := fun n => 3 * (wickConstant ρ (dyadicTailScale n) + mass / 3) -
    9 * (sunsetConstant ρ (dyadicTailScale n) + 0)
  let f := fun n (p : (ℝ × Ici (0 : ℝ)) × Ω) =>
    if p.2 ∈ E then toHolderBesov η
      (smoothSolution (b n) (shiftForcing p.1.2.val (ξ (dyadicTailScale n) p.2))
        (isSmoothOnSpaceTime_shiftForcing ((hξ _ (dyadicTailScale_mem n)).1 p.2) p.1.2.val)
        x hx (max (p.1.1 - p.1.2.val) 0)) else toHolderBesov η x
  apply measurable_of_tendsto_metrizable (f := f)
  · intro n
    have hm := measurable_renormalisedEndpoint_extended η P hW hρ
      (dyadicTailScale_mem n).1 (hξ _ (dyadicTailScale_mem n)) 0
      (wickConstant ρ (dyadicTailScale n) + mass / 3)
      (sunsetConstant ρ (dyadicTailScale n) + 0) ⟨x, hx⟩
    have hmap : Measurable (fun p : (ℝ × Ici (0 : ℝ)) × Ω =>
        ((p.1.1, p.1.2.val), p.2)) :=
      ((measurable_fst.fst.prodMk measurable_fst.snd.subtype_val).prodMk measurable_snd)
    have hh := hm.comp hmap
    dsimp only [f]
    apply Measurable.ite (he.preimage measurable_snd) ?_ measurable_const
    simpa only [zero_add, b, Function.comp_def] using hh
  · apply tendsto_pi_nhds.mpr
    intro p
    by_cases hp : p.2 ∈ E
    · have ht := (u.system ⟨p.2, hp⟩).tendsto_smooth_value p.1.2.val
        (max (p.1.1 - p.1.2.val) 0) p.1.2.property (le_max_right _ _) x hx
      have htime : max p.1.1 p.1.2.val - p.1.2.val = max (p.1.1 - p.1.2.val) 0 := by
        rw [← max_sub_sub_right, sub_self]
      rw [u.value_on ⟨p.2, hp⟩]
      simpa only [f, b, dyadicLiftData, ite_eq_left hp, FiniteLimitSystem.evolution, htime] using ht
    · simp only [f, ite_eq_right hp, u.value_off hp]
      exact tendsto_const_nhds

/-- Joint parameter measurability for every rough datum on the same flow.
The ambient product sigma-algebra is distinct from a fixed noise window. -/
theorem referenceFlow_parameter_measurable (u : EventFlow E η A) (x : HolderBesov η) :
    Measurable (fun p : (ℝ × Ici (0 : ℝ)) × Ω =>
      u.value p.2 (max p.1.1 p.1.2.val) p.1.2.val x) := by
  obtain ⟨q, hq, hlim⟩ := exists_smooth_sequence η x
  apply measurable_of_tendsto_metrizable
    (fun n => referenceFlow_smooth_parameter_measurable P hW N hN κ hκE ρ hρ mass
      η hη hκη ξ hξ u (q n) (hq n))
  apply tendsto_pi_nhds.mpr
  intro p
  exact ((u.continuous_datum p.2 p.1.2.property (le_max_right _ _)).tendsto x).comp hlim

/-- Full ambient product structure, with data, both time parameters, and noise.
This does not assert one time-dependent information field for all starts. -/
theorem referenceFlow_joint_parameter_measurable (u : EventFlow E η A) :
    Measurable (fun p : HolderBesov η × ((ℝ × Ici (0 : ℝ)) × Ω) =>
      u.value p.2.2 (max p.2.1.1 p.2.1.2.val) p.2.1.2.val p.1) := by
  apply Markov.measurable_joint_of_sections (F := fun (x : HolderBesov η)
    (p : (ℝ × Ici (0 : ℝ)) × Ω) =>
      u.value p.2 (max p.1.1 p.1.2.val) p.1.2.val x)
  · intro p
    exact u.continuous_datum p.2 p.1.2.property (le_max_right _ _)
  · intro x
    exact referenceFlow_parameter_measurable P hW N hN κ hκE ρ hρ mass η hη hκη ξ hξ u x

end Reference
end GlobalPhi43.Flow
