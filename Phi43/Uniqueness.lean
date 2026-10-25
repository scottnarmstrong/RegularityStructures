/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Limit
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Data.Rat.Cast.Order

/-!
# Conditions (A1)–(A3) determine the limit

Proposition 3.1 of the statement: if `(τ, v)` and `(τ', v')` both satisfy (A1)–(A3) for
the same solutions, then `τ = τ'` almost surely and the paths agree almost surely on `[0, τ)`.

The proof has three steps. Convergence (A3) of the same approximations to `v` and to `v'` shows
that the two limits agree on `[0, T]` almost surely on `{τ > T, τ' > T}`. A countable union over
rational `T` gives agreement on `[0, min(τ, τ'))`. Maximality (A2) then rules out `τ ≠ τ'`,
because a path that stays bounded up to `τ` cannot explode there. Only monotonicity and
subadditivity of `P` are used, so no measurability of the events is needed.
-/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace RegularityStructures.Phi43

variable {Ω : Type*} {η : NegExponent} {u₀ : C(Torus3, ℝ)} {u : ℝ → Ω → ℝ → C(Torus3, ℝ)}
  {τ τ' : Ω → ℝ≥0∞} {v v' : Ω → ℝ → HolderBesov η}

/-- The event that both limits exist beyond `T` and differ by more than `2δ` on `[0, T]`. -/
def disagreementSet (τ τ' : Ω → ℝ≥0∞) (v v' : Ω → ℝ → HolderBesov η) (T δ : ℝ) : Set Ω :=
  {ω | ENNReal.ofReal T < τ ω ∧ ENNReal.ofReal T < τ' ω ∧
    ∃ t ∈ Icc 0 T, 2 * δ < ‖v ω t - v' ω t‖}

theorem IsPhi43Limit.measure_disagreementSet [MeasurableSpace Ω] {P : Measure Ω} (h : IsPhi43Limit P η u₀ u τ v)
    (h' : IsPhi43Limit P η u₀ u τ' v') {T : ℝ} (hT : 0 < T) {δ : ℝ} (hδ : 0 < δ) :
    P (disagreementSet τ τ' v v' T δ) = 0 := by
  have hsub : ∀ ε, disagreementSet τ τ' v v' T δ ⊆
      {ω | ENNReal.ofReal T < τ ω ∧
        ∃ t ∈ Icc 0 T, δ < ‖toHolderBesov η (u ε ω t) - v ω t‖} ∪
      {ω | ENNReal.ofReal T < τ' ω ∧
        ∃ t ∈ Icc 0 T, δ < ‖toHolderBesov η (u ε ω t) - v' ω t‖} := by
    rintro ε ω ⟨h1, h2, t, ht, hlt⟩
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_and, not_exists, not_lt] at hcon
    have ha := hcon.1 h1 t ht
    have hb := hcon.2 h2 t ht
    have htri : ‖v ω t - v' ω t‖ ≤ ‖toHolderBesov η (u ε ω t) - v ω t‖ +
        ‖toHolderBesov η (u ε ω t) - v' ω t‖ := by
      calc ‖v ω t - v' ω t‖
          = ‖(toHolderBesov η (u ε ω t) - v' ω t) - (toHolderBesov η (u ε ω t) - v ω t)‖ := by
            congr 1
            abel
        _ ≤ ‖toHolderBesov η (u ε ω t) - v' ω t‖ + ‖toHolderBesov η (u ε ω t) - v ω t‖ :=
            norm_sub_le _ _
        _ = _ := add_comm _ _
    linarith
  have hlim := (h.converges T hT δ hδ).add (h'.converges T hT δ hδ)
  rw [add_zero] at hlim
  exact le_antisymm
    (ge_of_tendsto' hlim fun ε => (measure_mono (hsub ε)).trans (measure_union_le _ _))
    bot_le

/-- The exceptional null set: disagreement at some positive rational time and rational tolerance. -/
def exceptionalSet (τ τ' : Ω → ℝ≥0∞) (v v' : Ω → ℝ → HolderBesov η) : Set Ω :=
  ⋃ q : {q : ℚ // 0 < q}, ⋃ n : ℕ,
    disagreementSet τ τ' v v' (q : ℝ) (1 / ((n : ℝ) + 1))

theorem IsPhi43Limit.measure_exceptionalSet [MeasurableSpace Ω] {P : Measure Ω} (h : IsPhi43Limit P η u₀ u τ v)
    (h' : IsPhi43Limit P η u₀ u τ' v') : P (exceptionalSet τ τ' v v') = 0 := by
  refine measure_iUnion_null fun q => measure_iUnion_null fun n => ?_
  exact h.measure_disagreementSet h' (by exact_mod_cast q.2) Nat.one_div_pos_of_nat

/-- Off the exceptional set, the paths agree wherever both limits exist. -/
theorem eq_of_notMem_exceptionalSet {ω : Ω} (hω : ω ∉ exceptionalSet τ τ' v v') {t : ℝ}
    (ht : 0 ≤ t) (hτ : ENNReal.ofReal t < τ ω) (hτ' : ENNReal.ofReal t < τ' ω) :
    v ω t = v' ω t := by
  obtain ⟨q, hq0, htq, hqτ⟩ := ENNReal.lt_iff_exists_rat_btwn.1 (lt_min hτ hτ')
  change ENNReal.ofReal t < ENNReal.ofReal q at htq
  change ENNReal.ofReal q < min (τ ω) (τ' ω) at hqτ
  have htq' : t < q := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).1 htq
  have hqpos : (0 : ℚ) < q := by exact_mod_cast ht.trans_lt htq'
  by_contra hne
  have hd : 0 < ‖v ω t - v' ω t‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hd)
  apply hω
  refine mem_iUnion.2 ⟨⟨q, hqpos⟩, mem_iUnion.2 ⟨n, ?_⟩⟩
  refine ⟨hqτ.trans_le (min_le_left _ _), hqτ.trans_le (min_le_right _ _), t, ⟨ht, htq'.le⟩, ?_⟩
  linarith

/-- If `τ ω < τ' ω` off the exceptional set, then `v ω` stays bounded up to `τ ω`. -/
theorem bddAbove_of_lt {ω : Ω} (h' : ∀ ω, ContinuousOn (v' ω) {t | 0 ≤ t ∧ ENNReal.ofReal t < τ' ω})
    (hω : ω ∉ exceptionalSet τ τ' v v') (hlt : τ ω < τ' ω) :
    BddAbove ((fun t => ‖v ω t‖) '' {t | 0 ≤ t ∧ ENNReal.ofReal t < τ ω}) := by
  have hfin : τ ω ≠ ⊤ := (hlt.trans_le le_top).ne
  set R := (τ ω).toReal
  have hsub : Icc 0 R ⊆ {t | 0 ≤ t ∧ ENNReal.ofReal t < τ' ω} := by
    rintro t ⟨ht0, htR⟩
    refine ⟨ht0, lt_of_le_of_lt ?_ hlt⟩
    calc ENNReal.ofReal t ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal htR
      _ = τ ω := ENNReal.ofReal_toReal hfin
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn ((h' ω).mono hsub)
  refine ⟨C, ?_⟩
  rintro _ ⟨t, ⟨ht0, htτ⟩, rfl⟩
  have htR : t ≤ R := ((ENNReal.ofReal_lt_iff_lt_toReal ht0 hfin).1 htτ).le
  show ‖v ω t‖ ≤ C
  rw [eq_of_notMem_exceptionalSet hω ht0 htτ (htτ.trans hlt)]
  exact hC t ⟨ht0, htR⟩

/-- **Proposition 3.1.** Conditions (A1)–(A3) determine the limit: two limits of the same
solutions have almost surely equal explosion times and almost surely equal paths before them. -/
theorem IsPhi43Limit.unique [MeasurableSpace Ω] {P : Measure Ω} (h : IsPhi43Limit P η u₀ u τ v) (h' : IsPhi43Limit P η u₀ u τ' v') :
    τ =ᵐ[P] τ' ∧ ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ENNReal.ofReal t < τ ω → v ω t = v' ω t := by
  have hN := measure_eq_zero_iff_ae_notMem.1 (h.measure_exceptionalSet h')
  have hτ : ∀ ω, ω ∉ exceptionalSet τ τ' v v' → τ ω = τ' ω := by
    intro ω hω
    rcases lt_trichotomy (τ ω) (τ' ω) with hlt | heq | hgt
    · exact absurd (bddAbove_of_lt h'.continuousOn hω hlt)
        (h.explosion ω (hlt.trans_le le_top))
    · exact heq
    · have hω' : ω ∉ exceptionalSet τ' τ v' v := by
        intro hmem
        apply hω
        obtain ⟨q, n, hq⟩ := by simpa only [exceptionalSet, mem_iUnion] using hmem
        refine mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨n, ?_⟩⟩
        obtain ⟨h1, h2, t, ht, hlt⟩ := hq
        exact ⟨h2, h1, t, ht, by rwa [norm_sub_rev]⟩
      exact absurd (bddAbove_of_lt h.continuousOn hω' hgt)
        (h'.explosion ω (hgt.trans_le le_top))
  refine ⟨hN.mono fun ω hω => hτ ω hω, hN.mono fun ω hω t ht htτ => ?_⟩
  exact eq_of_notMem_exceptionalSet hω ht htτ (hτ ω hω ▸ htτ)

end RegularityStructures.Phi43

end
