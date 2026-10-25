/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyStatement
public import Mathlib.Order.CompletePartialOrder

/-!
# From the unit box to a general compact set (step C2)

If the `Π` half holds for every compact subset of the unit box `[0,1]⁴`, with fixed `qPi`, `KPi`,
then it holds for every compact `S`, with `qPi` unchanged and constant `m * KPi`, where `m` is the
number of unit boxes in a finite cover of `S`.  The pieces are translated into the unit box with
`Model.translate`.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace RegularityStructures

/-- The unit box `[0,1]⁴` in parabolic coordinates. -/
@[expose] def piHalfUnitBox : Set ParabolicSpace :=
  {x | x.1 ∈ Icc (0 : ℝ) 1 ∧ ∀ j, x.2 j ∈ Icc (0 : ℝ) 1}

theorem Model.piNormOn_mono {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
    {μ : Measure E} {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}
    (M : Model 𝒯 K) (γ : ℝ) {S S' : Set E} (h : S ⊆ S') :
    M.piNormOn γ S ≤ M.piNormOn γ S' :=
  le_iInf₂ fun C hC => iInf₂_le C fun i hi t ht x hx => hC i hi t ht x (h hx)

theorem Model.piDiffNormOn_mono {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
    {μ : Measure E} {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}
    (M M₂ : Model 𝒯 K) (γ : ℝ) {S S' : Set E} (h : S ⊆ S') :
    M.piDiffNormOn M₂ γ S ≤ M.piDiffNormOn M₂ γ S' :=
  le_iInf₂ fun C hC => iInf₂_le C fun i hi t ht x hx => hC i hi t ht x (h hx)

theorem ennreal_finset_sup_pow_le_sum {κ : Type*} (s : Finset κ) (f : κ → ℝ≥0∞) {p : ℕ}
    (hp : 1 ≤ p) : (s.sup f) ^ p ≤ ∑ i ∈ s, f i ^ p := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [zero_pow (by omega : p ≠ 0)]
  · obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup s hs f
    rw [hsup]
    exact Finset.single_le_sum (f := fun i => f i ^ p) (fun _ _ => zero_le) hi

/-- A compact set is covered by finitely many closed balls of radius `1/2` centred in it. -/
theorem exists_finset_cover_closedBall_half {S : Set ParabolicSpace} (hS : IsCompact S) :
    ∃ s : Finset ParabolicSpace, S ⊆ ⋃ z ∈ s, closedBall z (1 / 2) := by
  obtain ⟨t, -, htfin, hcov⟩ := hS.finite_cover_balls (e := 1 / 2) (by norm_num)
  refine ⟨htfin.toFinset, hcov.trans ?_⟩
  simp only [Set.Finite.mem_toFinset]
  exact iUnion₂_mono fun z _ => ball_subset_closedBall

/-- The translate of the ball piece around `z` lies in the unit box. -/
theorem piHalfPiece_subset_unitBox (z : ParabolicSpace) :
    (fun y : ParabolicSpace => y + (z - ((1 / 2 : ℝ), fun _ : Fin 3 => (1 / 2 : ℝ)))) ⁻¹'
        closedBall z (1 / 2) ⊆ piHalfUnitBox := by
  intro y hy
  have hd : dist (y + (z - ((1 / 2 : ℝ), fun _ : Fin 3 => (1 / 2 : ℝ)))) z ≤ 1 / 2 := hy
  rw [Prod.dist_eq, max_le_iff] at hd
  obtain ⟨h1, h2⟩ := hd
  rw [dist_pi_le_iff (by norm_num)] at h2
  rw [Real.dist_eq, abs_le] at h1
  refine ⟨?_, fun j => ?_⟩
  · simp only [Prod.fst_add, Prod.fst_sub] at h1
    constructor <;> linarith [h1.1, h1.2]
  · have := h2 j
    rw [Real.dist_eq, abs_le] at this
    simp only [Prod.snd_add, Prod.snd_sub, Pi.add_apply, Pi.sub_apply] at this
    constructor <;> linarith [this.1, this.2]

end RegularityStructures

end
