/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.KolmogorovChentsovDense
public import RegularityStructures.Probability.KolmogorovChentsovSupremum

/-!
# Samplewise dyadic Hölder control

The normalised dyadic supremum controls every close pair on the dyadic grid.
The deterministic dense-skeleton estimate therefore gives a Hölder constant
whose only random input is that supremum.
-/

@[expose] public section

open Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

theorem holderOnWith_of_dyadicNormalisedSup_lt_top
    {Ω E : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace E]
    {X : UnitInterval → Ω → E} {r : ℝ≥0} (hr : 0 < r)
    {ω : Ω} (hS : dyadicNormalisedSup X r ω < ∞) :
    HolderOnWith
      (dyadicNormalisedSup X r ω *
        (1 + 2 * dyadicTailCoeff r) * (2 : ℝ≥0∞) ^ (r : ℝ)).toNNReal
      r (fun x => X x ω) dyadicUnitSet := by
  let S : ℝ≥0∞ := dyadicNormalisedSup X r ω
  have hS' : S < ∞ := hS
  have hbase_mul (n : ℕ) :
      (dyadicBase n) ^ (-(r : ℝ)) * (dyadicBase n) ^ (r : ℝ) = 1 := by
    rw [← ENNReal.rpow_add _ _ (dyadicBase_pos n).ne'
      (dyadicBase_ne_top n)]
    simp
  have hclose (n : ℕ) :
      dyadicCloseSup X n ω ≤ S * (dyadicBase n) ^ (r : ℝ) := by
    have hnorm : dyadicNormalised X r n ω ≤ S := by
      exact le_iSup (fun m => dyadicNormalised X r m ω) n
    calc
      dyadicCloseSup X n ω =
          (dyadicCloseSup X n ω * (dyadicBase n) ^ (-(r : ℝ))) *
            (dyadicBase n) ^ (r : ℝ) := by
        rw [mul_assoc, hbase_mul, mul_one]
      _ ≤ S * (dyadicBase n) ^ (r : ℝ) := by
        gcongr
        exact hnorm
  apply holderOnWith_dyadic hr hS'.ne
  intro n u v hu hv huv
  have hgrid := dyadicGrid_close_le_dyadicCloseSup
    (fun x => X x ω) n hu hv huv
  have hgrid' : dyadicCloseSup (fun x _ => X x ω) n () =
      dyadicCloseSup X n ω := by
    rfl
  rw [hgrid'] at hgrid
  exact hgrid.trans (hclose n)

end RegularityStructures

end
