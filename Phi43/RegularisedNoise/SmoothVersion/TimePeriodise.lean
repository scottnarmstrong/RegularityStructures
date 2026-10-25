/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.Deterministic
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Time periodisation for a compactly time-supported kernel

The local Fourier construction uses a finite time torus.  This file provides the elementary
time-periodised lift of a smooth kernel; the support hypothesis makes the defining integer sum
locally finite.  The construction is independent of the mollifier-specific periodisation.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Topology

namespace RegularityStructures.Phi43

def timePeriodise (Phi : SpaceTime → ℝ) (L : ℝ) (z : ℝ × (Fin 3 → ℝ)) : ℝ :=
  ∑' n : ℤ, Phi (z.1 + L * n, torusProj z.2)

theorem timePeriodise_add_period {Phi : SpaceTime → ℝ} {L : ℝ}
    (_hL : L ≠ 0) (z : ℝ × (Fin 3 → ℝ)) :
    timePeriodise Phi L (z.1 + L, z.2) = timePeriodise Phi L z := by
  unfold timePeriodise
  calc
    (∑' n : ℤ, Phi (z.1 + L + L * n, torusProj z.2)) =
        ∑' n : ℤ, Phi (z.1 + L * (n + 1), torusProj z.2) := by
          apply tsum_congr
          intro n
          congr 2
          ring
    _ = ∑' n : ℤ, Phi (z.1 + L * n, torusProj z.2) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (Equiv.addRight (1 : ℤ)).tsum_eq
          (fun n : ℤ => Phi (z.1 + L * n, torusProj z.2))

private theorem timePeriodise_term_eq_zero_of_abs_gt
    {Phi : SpaceTime → ℝ} {L t : ℝ} {x : Fin 3 → ℝ} {R : ℝ}
    (hR : ∀ z : SpaceTime, R < |z.1| → Phi z = 0)
    {n : ℤ} (hn : R < |t + L * n|) :
    Phi (t + L * n, torusProj x) = 0 := by
  exact hR _ hn

theorem contDiff_timePeriodise {Phi : SpaceTime → ℝ} {L R : ℝ}
    (hPhi : IsSmoothOnSpaceTime Phi)
    (hR : ∀ z : SpaceTime, R < |z.1| → Phi z = 0)
    (hL : 0 < L) :
    ContDiff ℝ ∞ (timePeriodise Phi L) := by
  by_cases hR0 : 0 ≤ R
  · apply contDiff_iff_contDiffAt.mpr
    intro z
    let S : ℝ := max R 0
    let B : ℤ := ⌈(S + |z.1| + 1) / L⌉ + 1
    let s : Finset ℤ := Finset.Icc (-B) B
    let U : Set (ℝ × (Fin 3 → ℝ)) :=
      Set.Ioo (z.1 - 1) (z.1 + 1) ×ˢ Set.univ
    have hzU : z ∈ U := by
      exact ⟨⟨by linarith, by linarith⟩, mem_univ _⟩
    have hU : U ∈ 𝓝 z := isOpen_Ioo.prod isOpen_univ |>.mem_nhds hzU
    have hterm : ∀ p ∈ U, ∀ n ∉ s,
        Phi (p.1 + L * n, torusProj p.2) = 0 := by
      intro p hp n hn
      have hp1 : p.1 < z.1 + 1 := hp.1.2
      have hp2 : z.1 - 1 < p.1 := hp.1.1
      have hnonnegS : 0 ≤ S := le_max_right _ _
      have hSR : R ≤ S := le_max_left _ _
      have hn_cases : n < -B ∨ B < n := by
        simpa only [s, Finset.mem_Icc, not_and_or, not_le] using hn
      have hlarge : S < |p.1 + L * n| := by
        rcases hn_cases with hnneg | hnpos
        · have hnneg' : (n : ℝ) < -((S + |z.1| + 1) / L) := by
            have hceil : ((S + |z.1| + 1) / L : ℝ) ≤ (⌈(S + |z.1| + 1) / L⌉ : ℝ) := by
              exact_mod_cast (Int.le_ceil ((S + |z.1| + 1) / L))
            have hn' : (n : ℝ) < (-B : ℤ) := by exact_mod_cast hnneg
            dsimp [B] at hn'
            norm_num at hn'
            linarith
          have hsmall : S + |z.1| + 1 < -L * n := by
            have hnneg'' : (n : ℝ) < -(S + |z.1| + 1) / L := by
              convert hnneg' using 1
              ring
            have hmul : (n : ℝ) * L < -(S + |z.1| + 1) :=
              (lt_div_iff₀ hL).mp hnneg''
            linarith
          have hneg : p.1 + L * n < -S := by
            linarith [le_abs_self z.1]
          have hneg0 : p.1 + L * n < 0 :=
            lt_of_lt_of_le hneg (neg_nonpos.mpr hnonnegS)
          rw [abs_of_neg hneg0]
          linarith
        · have hnpos' : (S + |z.1| + 1) / L < (n : ℝ) := by
            have hceil : ((S + |z.1| + 1) / L : ℝ) ≤ (⌈(S + |z.1| + 1) / L⌉ : ℝ) := by
              exact_mod_cast (Int.le_ceil ((S + |z.1| + 1) / L))
            have hn' : (B : ℤ) < n := by exact_mod_cast hnpos
            dsimp [B] at hn'
            have hceil_lt : (⌈(S + |z.1| + 1) / L⌉ : ℝ) < (n : ℝ) := by
              have hstep : (⌈(S + |z.1| + 1) / L⌉ : ℝ) <
                  (⌈(S + |z.1| + 1) / L⌉ : ℝ) + 1 := by linarith
              have hn'' : (⌈(S + |z.1| + 1) / L⌉ : ℝ) + 1 < (n : ℝ) := by
                exact_mod_cast hn'
              exact hstep.trans hn''
            exact lt_of_le_of_lt hceil hceil_lt
          have hsmall : S + |z.1| + 1 < L * n := by
            have hmul : S + |z.1| + 1 < (n : ℝ) * L :=
              (div_lt_iff₀ hL).mp hnpos'
            linarith
          have hpos : S < p.1 + L * n := by
            have hz : 0 ≤ z.1 + |z.1| := by linarith [neg_abs_le z.1]
            linarith
          have hpos0 : 0 < p.1 + L * n := lt_of_le_of_lt hnonnegS hpos
          rw [abs_of_pos hpos0]
          exact hpos
      exact timePeriodise_term_eq_zero_of_abs_gt hR (lt_of_le_of_lt hSR hlarge)
    have hsum : ∀ p ∈ U,
        timePeriodise Phi L p =
          ∑ n ∈ s, Phi (p.1 + L * n, torusProj p.2) := by
      intro p hp
      unfold timePeriodise
      apply tsum_eq_sum
      intro n hn
      exact hterm p hp n hn
    have hcont : ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) =>
        ∑ n ∈ s, Phi (p.1 + L * n, torusProj p.2)) := by
      apply ContDiff.sum
      intro n hn
      have harg : ContDiff ℝ ∞
          (fun p : ℝ × (Fin 3 → ℝ) =>
            (p.1 + L * n, p.2)) := by
        fun_prop
      change ContDiff ℝ ∞
        ((fun p : ℝ × (Fin 3 → ℝ) => Phi (p.1, torusProj p.2)) ∘
          (fun p : ℝ × (Fin 3 → ℝ) => (p.1 + L * n, p.2)))
      exact hPhi.comp harg
    apply hcont.contDiffAt.congr_of_eventuallyEq
    filter_upwards [hU] with p hp
    exact hsum p hp
  · have hzero : Phi = 0 := by
      funext z
      apply hR
      exact lt_of_not_ge hR0 |>.trans_le (abs_nonneg z.1)
    rw [hzero]
    have hz : timePeriodise (0 : SpaceTime → ℝ) L =
        (fun _ : ℝ × (Fin 3 → ℝ) => (0 : ℝ)) := by
      funext z
      simp [timePeriodise]
    rw [hz]
    exact contDiff_const

end RegularityStructures.Phi43

end
