/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovHSModelTransport
public import RegularityStructures.Statements.Defs.IsContinuousRandomModelOn

/-!
# Global section measurability of model regularisations

The random-model predicate gives measurable diagonal coordinates and measurable Gamma coordinates at
every base point. The strict lower-degree transport identity therefore gives measurability in the
random variable for every off-diagonal `regPi` coordinate, globally in both spatial points.

This is deliberately only a section-measurability result.  It does not turn
the two-variable field into a jointly measurable function; that stronger
property is available on compact continuity sets through the corresponding
Caratheodory lemma.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {𝒯 : RegularityStructure ι}
  {Z : Ω → Model 𝒯 parabolicSemigroup} {S : Set ParabolicSpace}

/-- Every global off-diagonal single-coordinate regularisation is measurable in `ω`. -/
theorem hsGlobal_offDiagonal_regPi_measurable
    (hZ : IsContinuousRandomModelOn Z S)
    (i : ι) (x y : ParabolicSpace) {u : ℝ} (hu : 0 < u) :
    Measurable (fun ω : Ω => (Z ω).regPi x (Pi.single i 1) u y) := by
  classical
  let lower : ι → Finset ι := fun k =>
    Finset.univ.filter (fun j => 𝒯.deg j < 𝒯.deg k)
  let Good : ι → Prop := fun k =>
    ∀ (v : ℝ), 0 < v → ∀ x y : ParabolicSpace, Measurable (fun ω : Ω =>
      (Z ω).regPi x (Pi.single k 1) v y)
  have hgood_of_card : ∀ n : ℕ, ∀ k : ι, (lower k).card = n → Good k := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro k hk
        dsimp only [Good]
        intro v hv x y
        have hlower : ∀ j ∈ lower k, Good j := by
          intro j hj
          have hjdeg : 𝒯.deg j < 𝒯.deg k := (Finset.mem_filter.1 hj).2
          have hsub : lower j ⊆ lower k := by
            intro l hl
            exact Finset.mem_filter.2 ⟨Finset.mem_univ l,
              lt_trans (Finset.mem_filter.1 hl).2 hjdeg⟩
          have hproper : lower j ⊂ lower k := by
            apply Finset.ssubset_iff_subset_ne.2
            refine ⟨hsub, ?_⟩
            intro heq
            have hjnot : j ∉ lower j := by
              intro hjj
              exact (lt_irrefl (𝒯.deg j)) (Finset.mem_filter.1 hjj).2
            exact hjnot (heq ▸ hj)
          have hcard : (lower j).card < n := by
            have hc : (lower j).card < (lower k).card := Finset.card_lt_card hproper
            exact hc.trans_eq hk
          exact ih _ hcard j rfl
        have hdiag : Measurable (fun ω : Ω =>
            (Z ω).regPi y (Pi.single k 1) v y) := hZ.1 k y v hv
        have hterm : ∀ j ∈ lower k, Measurable (fun ω : Ω =>
            (Z ω).gammaMap y x (Pi.single k 1) j *
              (Z ω).regPi y (Pi.single j 1) v y) := by
          intro j hj
          exact (hZ.2.1 k j x y).mul ((hlower j hj) v hv y y)
        have hsum : Measurable (fun ω : Ω =>
            ∑ j ∈ lower k, (Z ω).gammaMap y x (Pi.single k 1) j *
              (Z ω).regPi y (Pi.single j 1) v y) :=
          Finset.measurable_sum _ (fun j hj => hterm j hj)
        have heq : (fun ω : Ω =>
            (Z ω).regPi x (Pi.single k 1) v y) =
            (fun ω : Ω => (Z ω).regPi y (Pi.single k 1) v y) +
              (fun ω : Ω =>
                ∑ j ∈ lower k, (Z ω).gammaMap y x (Pi.single k 1) j *
                  (Z ω).regPi y (Pi.single j 1) v y) := by
          funext ω
          have h := (Z ω).regPi_single_sub_diag_eq_lower x y k v
          change (Z ω).regPi x (Pi.single k 1) v y =
            (Z ω).regPi y (Pi.single k 1) v y +
              ∑ j ∈ lower k, (Z ω).gammaMap y x (Pi.single k 1) j *
                (Z ω).regPi y (Pi.single j 1) v y
          simpa only [add_comm] using (sub_eq_iff_eq_add.1 h)
        rw [heq]
        exact hdiag.add hsum
  exact hgood_of_card (lower i).card i rfl u hu x y

end RegularityStructures

end
