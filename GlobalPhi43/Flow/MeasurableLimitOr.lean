module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Total measurable sequential limits with the explicitly supplied fallback. -/

public noncomputable section

open MeasureTheory Filter Topology TopologicalSpace Set

namespace GlobalPhi43.Flow

/-- The actual sequence limit when it exists; exactly x otherwise. -/
@[expose] def limitOr {E : Type*} [TopologicalSpace E] (x : E) (f : ℕ → E) : E := by
  classical
  exact if h : ∃ y, Tendsto f atTop (𝓝 y) then h.choose else x

theorem limitOr_of_not_tendsto {E : Type*} [TopologicalSpace E] (x : E) (f : ℕ → E)
    (h : ¬ ∃ y, Tendsto f atTop (𝓝 y)) : limitOr x f = x := by
  rw [limitOr, dite_eq_right h]

theorem tendsto_limitOr {E : Type*} [TopologicalSpace E] (x : E) (f : ℕ → E)
    (h : ∃ y, Tendsto f atTop (𝓝 y)) : Tendsto f atTop (𝓝 (limitOr x f)) := by
  rw [limitOr, dite_eq_left h]
  exact h.choose_spec

theorem limitOr_eq_of_tendsto {E : Type*} [TopologicalSpace E] [T2Space E]
    (x : E) {f : ℕ → E} {y : E} (h : Tendsto f atTop (𝓝 y)) : limitOr x f = y :=
  tendsto_nhds_unique (tendsto_limitOr x f ⟨y, h⟩) h

/-- A total limit is measurable, including its specified measurable fallback. -/
theorem limitOr_measurable {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [IsCompletelyPseudoMetrizableSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] (x : Ω → E) (hx : Measurable x)
    (f : ℕ → Ω → E) (hf : ∀ n, Measurable (f n)) :
    Measurable (fun ω => limitOr (x ω) (fun n => f n ω)) := by
  let D := {ω | ∃ y, Tendsto (fun n => f n ω) atTop (𝓝 y)}
  have hD : MeasurableSet D := measurableSet_exists_tendsto hf
  apply measurable_of_restrict_of_restrict_compl hD
  · apply measurable_of_tendsto_metrizable' atTop
      (fun n => (hf n).comp measurable_subtype_coe)
    apply tendsto_pi_nhds.mpr
    intro ω
    exact tendsto_limitOr (x ω.val) (fun n => f n ω.val) ω.property
  · change Measurable (fun ω : {ω : Ω // ω ∉ D} => limitOr (x ω.val) (fun n => f n ω.val))
    have he : (fun ω : {ω : Ω // ω ∉ D} => limitOr (x ω.val) (fun n => f n ω.val)) =
        (fun ω : {ω : Ω // ω ∉ D} => x ω.val) := by
      funext ω
      exact limitOr_of_not_tendsto (x ω.val) (fun n => f n ω.val) ω.property
    rw [he]
    exact hx.comp measurable_subtype_coe

end GlobalPhi43.Flow
