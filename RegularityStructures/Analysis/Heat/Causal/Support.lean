/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Causal.Moment
public import RegularityStructures.Analysis.Heat.Decomposition.LineIter
public import RegularityStructures.Analysis.Parabolic.SingularKernel
public import RegularityStructures.Analysis.Heat.Annihilating.Scaled

/-!
# Non-anticipativity of the causal decomposition

`annShellC N n z = 0` and `annRemainderC N z = 0` for `z.1 ≤ 0`
(`annShellC_eq_zero_of_nonpos`, `annRemainderC_eq_zero_of_nonpos`), and the same for every
iterated directional derivative (`lineIter_eq_zero_of_nonpos`, `lineIter_annShellC_eq_zero`,
`lineIter_annRemainderC_eq_zero`, in particular along `multiDirs k`).  This is the non-anticipativity
required in [Hai14, Theorem 7.1] and [Hai14, Lemma 7.7].

Source: Hairer, arXiv:1303.5113v4, Section 7.
-/

public section

open scoped ContDiff

namespace RegularityStructures

theorem heatShell_eq_zero_of_nonpos (n : ℕ) {z : ParabolicSpace} (hz : z.1 ≤ 0) :
    heatShell n z = 0 := by
  simp [heatShell, heatKernelR4, not_lt.2 hz]

theorem heatRemainder_eq_zero_of_nonpos {z : ParabolicSpace} (hz : z.1 ≤ 0) :
    heatRemainder z = 0 := by
  simp [heatRemainder, heatKernelR4, not_lt.2 hz]

theorem annKernel0C_eq_zero_of_nonpos (N : ℕ) {z : ParabolicSpace} (hz : z.1 ≤ 0) :
    annKernel0C N z = 0 := by
  have h2 : (parabolicDilate 2 z).1 ≤ 0 := by
    simp only [parabolicDilate]
    nlinarith
  simp [annKernel0C, heatShell_eq_zero_of_nonpos 0 hz, annBumpC_eq_zero_of_nonpos hz,
    annBumpC_eq_zero_of_nonpos h2]

/-- The causal shells are non-anticipative. -/
theorem annShellC_eq_zero_of_nonpos (N n : ℕ) {z : ParabolicSpace} (hz : z.1 ≤ 0) :
    annShellC N n z = 0 := by
  have h2 : (parabolicDilate (2 ^ n) z).1 ≤ 0 := by
    simp only [parabolicDilate]
    have : (0 : ℝ) ≤ ((2 : ℝ) ^ n) ^ 2 := by positivity
    nlinarith
  simp [annShellC, scaledShell, annKernel0C_eq_zero_of_nonpos N h2]

/-- The causal remainder is non-anticipative. -/
theorem annRemainderC_eq_zero_of_nonpos (N : ℕ) {z : ParabolicSpace} (hz : z.1 ≤ 0) :
    annRemainderC N z = 0 := by
  simp [annRemainderC, heatRemainder_eq_zero_of_nonpos hz, annBumpC_eq_zero_of_nonpos hz]

/-- A smooth function vanishing on `{t ≤ 0}` has all iterated directional derivatives vanishing
there. -/
theorem lineIter_eq_zero_of_nonpos {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (h0 : ∀ z : ParabolicSpace, z.1 ≤ 0 → f z = 0) (L : List ParabolicSpace)
    {z : ParabolicSpace} (hz : z.1 ≤ 0) : lineIter L f z = 0 := by
  have hopen : IsOpen {w : ParabolicSpace | w.1 < 0} := isOpen_lt continuous_fst continuous_const
  have hlt : ∀ L : List ParabolicSpace, ∀ w : ParabolicSpace, w.1 < 0 → lineIter L f w = 0 := by
    intro L
    induction L with
    | nil => intro w hw; exact h0 w hw.le
    | cons d L ih =>
      intro w hw
      have hev : lineIter L f =ᶠ[nhds w] fun _ => (0 : ℝ) :=
        Filter.eventuallyEq_of_mem (hopen.mem_nhds hw) fun v hv => ih v hv
      simp only [lineIter_cons, dirDeriv, hev.fderiv_eq]
      simp
  have hclosed : IsClosed {w : ParabolicSpace | lineIter L f w = 0} :=
    isClosed_eq (contDiff_lineIter hf L).continuous continuous_const
  have hcl : closure {w : ParabolicSpace | w.1 < 0} = {w : ParabolicSpace | w.1 ≤ 0} := by
    have := (isOpenMap_fst (X := ℝ) (Y := Fin 3 → ℝ)).preimage_closure_eq_closure_preimage
      continuous_fst (Set.Iio (0 : ℝ))
    rw [closure_Iio] at this
    exact this.symm
  have : z ∈ closure {w : ParabolicSpace | w.1 < 0} := by rw [hcl]; exact hz
  exact (hclosed.closure_subset_iff.2 (fun w hw => hlt L w hw)) this

end RegularityStructures

end
