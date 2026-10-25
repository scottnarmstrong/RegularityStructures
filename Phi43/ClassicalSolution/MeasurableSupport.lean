/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.Properties
public import RegularityStructures.Torus.HolderBesov
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Measurable factorisation through a Lipschitz range

This module contains the topological-measure-theoretic part of the measurability argument for
item (W5) of Lemma 4.1 of the statement.  A measurable map into a metric space,
together with a uniformly Lipschitz map on its range, has a measurable composition with any
selected representative of that map.  The proof extends the Lipschitz map
from the range to its closure, using completeness of the target.
-/

public section

open MeasureTheory Set Function
open scoped NNReal ENNReal
open scoped Topology

namespace RegularityStructures.Phi43

private theorem dense_range_subtype_closure {X : Type*} [TopologicalSpace X] (s : Set X) :
    Dense {x : closure s | (x : X) ∈ s} := by
  rw [Subtype.dense_iff]
  intro x hx
  have himage : ((↑) : closure s → X) '' {x : closure s | (x : X) ∈ s} = s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, subset_closure hy⟩, hy, rfl⟩
  rw [himage]
  exact hx

theorem measurable_of_lipschitz_range
    {Ω X Y : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompleteSpace Y]
    (F : Ω → X) (g : Ω → Y) (hF : Measurable F)
    {K : ℝ≥0} (hK : ∀ w w', edist (g w) (g w') ≤ K * edist (F w) (F w')) :
    Measurable g := by
  let s : Set X := range F
  let witness (x : s) : Ω :=
    Classical.choose (show ∃ w, F w = (x : X) by
      change (x : X) ∈ range F
      exact x.property)
  have witness_spec (x : s) : F (witness x) = (x : X) := by
    exact Classical.choose_spec (show ∃ w, F w = (x : X) by
      change (x : X) ∈ range F
      exact x.property)
  let f : s → Y := fun x => g (witness x)
  have hf_eq (x : s) : f x = g (witness x) := rfl
  have hf_well_defined (x : s) (w : Ω) (hw : F w = x) : f x = g w := by
    have hFx : F (witness x) = x := witness_spec x
    have hdist : edist (g (witness x)) (g w) ≤ K * edist (F (witness x)) (F w) :=
      hK (witness x) w
    have hzero : dist (g (witness x)) (g w) ≤ 0 := by
      simpa [hFx, hw, edist_dist] using hdist
    simpa [hf_eq] using (dist_le_zero.mp hzero)
  have hf : LipschitzWith K f := by
    intro x y
    change edist (g (witness x)) (g (witness y)) ≤ K * edist x y
    simp only [edist_dist]
    change ENNReal.ofReal (dist (g (witness x)) (g (witness y))) ≤
      (K : ℝ≥0∞) * ENNReal.ofReal (dist (x : X) (y : X))
    rw [← witness_spec x, ← witness_spec y]
    simpa only [edist_dist] using hK _ _
  let T : Set (closure s) := {x | (x : X) ∈ s}
  have hT : Dense T := by
    change Dense {x : closure s | (x : X) ∈ s}
    exact dense_range_subtype_closure s
  let fT : T → Y := fun x => f ⟨x.1, x.2⟩
  have hsub : LipschitzWith 1 (fun x : T => (⟨x.1, x.2⟩ : s)) := by
    intro x y
    simp only [edist_dist, ENNReal.coe_one, one_mul]
    change ENNReal.ofReal (dist x.1.1 y.1.1) ≤ ENNReal.ofReal (dist x.1.1 y.1.1)
    exact le_rfl
  have hfT : LipschitzWith K fT := by
    simpa only [Function.comp_def, mul_one] using hf.comp hsub
  have hucT : UniformContinuous fT := hfT.uniformContinuous
  let fbar : closure s → Y := hT.extend fT
  have hucbar : UniformContinuous fbar := hT.uniformContinuous_extend hucT
  have hfbar : Measurable fbar := hucbar.continuous.measurable
  let Fbar : Ω → closure s := fun w => ⟨F w, subset_closure (mem_range_self w)⟩
  have hFbar : Measurable Fbar := by
    change Measurable (fun w => (⟨F w, subset_closure (mem_range_self w)⟩ : closure s))
    exact hF.subtype_mk
  have hcomp : Measurable (fbar ∘ Fbar) := hfbar.comp hFbar
  have heq : g = fbar ∘ Fbar := by
    funext w
    let x : T := ⟨Fbar w, by
      change F w ∈ s
      exact mem_range_self w⟩
    have hx : fbar (Fbar w) = fT x := by
      have := hT.extend_of_ind hucT x
      simpa [x, fbar, fT] using this
    change g w = fbar (Fbar w)
    rw [hx]
    exact (hf_well_defined (⟨F w, mem_range_self w⟩) w rfl).symm
  rw [heq]
  exact hcomp

theorem regularisedNoise_restriction_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε t : ℝ) (ξ : Ω → SpaceTime → ℝ)
    (hξ : IsRegularisedNoise P W ρ ε ξ) :
    Measurable (fun w =>
      (ContinuousMap.mk (fun z : Set.Icc (0 : ℝ) t × Torus3 => ξ w (z.1.1, z.2)) <| by
        exact (Continuous.continuous_of_isSmoothOnSpaceTime (hξ.1 w)).comp
          ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))) := by
  apply ContinuousMap.measurable_iff_eval.2
  intro z
  simpa using (hξ.2 (z.1.1, z.2)).1

theorem second_deriv_nonpos_of_isLocalMax {f : ℝ → ℝ} {a : ℝ}
    (hmax : IsLocalMax f a) (hf : ContDiff ℝ 2 f) : deriv (deriv f) a ≤ 0 := by
  by_contra h
  have hpos : 0 < deriv (deriv f) a := lt_of_not_ge h
  have hderiv : deriv f a = 0 := hmax.deriv_eq_zero
  have hmin : IsLocalMin f a :=
    isLocalMin_of_deriv_deriv_pos hpos hderiv hf.continuous.continuousAt
  have hev : f =ᶠ[𝓝 a] (fun _ => f a) := by
    filter_upwards [hmax, hmin] with x hxmax hxmin
    exact le_antisymm hxmax hxmin
  have hev' : deriv f =ᶠ[𝓝 a] (fun _ => 0) := by
    have h := hev.deriv
    filter_upwards [h] with x hx
    simpa using hx
  have hzero := hev'.deriv_eq
  simp only [deriv_const] at hzero
  linarith

end RegularityStructures.Phi43

end
