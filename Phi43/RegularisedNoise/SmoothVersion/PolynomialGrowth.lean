/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.Growth

/-!
# From an eventual polynomial bound to a random polynomial constant

The first Borel--Cantelli argument naturally gives a cofinite bound in the frequency index.  For
positive weights this is equivalent to the more familiar formulation with a finite random
constant: absorb the finitely many exceptional coordinates into a finite maximum.  This is the
form used in the Fourier-series construction of a smooth regularised noise (Definition 2.4 of the
statement).
-/

@[expose] public section

open MeasureTheory
open Filter
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem ae_exists_mul_bound_of_ae_eventually_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {P : Measure Ω}
    {X : ι → Ω → ℝ} {b : ι → ℝ}
    (hb : ∀ i, 0 < b i)
    (hX : ∀ᵐ ω ∂P, ∀ᶠ i in (cofinite : Filter ι), |X i ω| ≤ b i) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ i, |X i ω| ≤ C * b i := by
  filter_upwards [hX] with ω hω
  rw [eventually_cofinite] at hω
  let s : Set ι := {i | ¬ |X i ω| ≤ b i}
  have hsfin : s.Finite := by simpa [s] using hω
  by_cases hs : s.Nonempty
  · let sf : Finset ι := hsfin.toFinset
    have hsf : sf.Nonempty := hsfin.toFinset_nonempty.mpr hs
    let M : ℝ := sf.sup' hsf (fun i => |X i ω| / b i)
    let C : ℝ := max 1 M
    refine ⟨C, (show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_left _ _), ?_⟩
    intro i
    by_cases hi : i ∈ s
    · have hsi : i ∈ sf := hsfin.mem_toFinset.mpr hi
      have hsup : |X i ω| / b i ≤ M := sf.le_sup' (fun j => |X j ω| / b j) hsi
      have hC : |X i ω| / b i ≤ C := le_max_of_le_right hsup
      calc
        |X i ω| = (|X i ω| / b i) * b i := by field_simp [ne_of_gt (hb i)]
        _ ≤ C * b i := mul_le_mul_of_nonneg_right hC (le_of_lt (hb i))
    · have hi' : |X i ω| ≤ b i := by
        exact not_not.mp hi
      exact hi'.trans (le_mul_of_one_le_left (le_of_lt (hb i)) (le_max_left _ _))
  · have hnone : ∀ i, |X i ω| ≤ b i := by
      intro i
      by_contra hi
      exact hs ⟨i, hi⟩
    refine ⟨1, by norm_num, ?_⟩
    intro i
    exact (hnone i).trans (le_mul_of_one_le_left (le_of_lt (hb i)) le_rfl)

end RegularityStructures.Phi43

end
