/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesovMultiplierProfiles

/-!
# Fixed annular Green profiles

The cutoff difference `phi(u)-phi(8u)` vanishes near zero. Dividing it by `u^(2M)` therefore gives a
smooth compactly supported profile, including at zero. These fixed profiles supply scale-uniform
inverse-derivative multipliers for annular heat decay in the equivalence of the heat norm (2.3) of
the statement with the Littlewood--Paley norm.
-/

@[expose] public noncomputable section

open Real Set
open scoped Topology SchwartzMap

namespace RegularityStructures

private theorem bump_small (u : ℝ) (hu : |u| ≤ 1 / 8) :
    torusLPBump u = 1 ∧ torusLPBump (8 * u) = 1 := by
  constructor
  · apply torusLPBump.one_of_mem_closedBall
    change |u - 0| ≤ 1
    rw [sub_zero]
    linarith only [hu]
  · apply torusLPBump.one_of_mem_closedBall
    change |8 * u - 0| ≤ 1
    rw [sub_zero, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    linarith only [hu]

private theorem bump_large (u : ℝ) (hu : 2 ≤ |u|) :
    torusLPBump u = 0 ∧ torusLPBump (8 * u) = 0 := by
  constructor
  · apply torusLPBump.zero_of_le_dist
    simpa only [torusLPBump, Real.dist_eq, sub_zero] using hu
  · apply torusLPBump.zero_of_le_dist
    change 2 ≤ |8 * u - 0|
    rw [sub_zero, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
    linarith only [hu]

/-- The literal quotient of the annular cutoff by its coordinate power. -/
def torusLPAnnulusGreenFun (M : ℕ) (u : ℝ) : ℂ :=
  ((torusLPBump u : ℂ) - (torusLPBump (8 * u) : ℂ)) / (u : ℂ) ^ (2 * M)

theorem hasCompactSupport_torusLPAnnulusGreenFun (M : ℕ) : HasCompactSupport (torusLPAnnulusGreenFun M) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2))
  intro u hu
  by_contra hn
  have hh : 2 ≤ |u| := by
    by_contra! hh
    exact hn ⟨by linarith only [(abs_lt.mp hh).1], (abs_lt.mp hh).2.le⟩
  obtain ⟨h₁, h₂⟩ := bump_large u hh
  apply hu
  simp only [torusLPAnnulusGreenFun, h₁, h₂, Complex.ofReal_zero, sub_self, zero_div]

open scoped ContDiff in
theorem contDiff_torusLPAnnulusGreenFun (M : ℕ) : ContDiff ℝ ∞ (torusLPAnnulusGreenFun M) := by
  apply contDiff_iff_contDiffAt.mpr
  intro u
  change ContDiffAt ℝ ∞ (fun v : ℝ =>
    ((torusLPBump v : ℂ) - (torusLPBump (8 * v) : ℂ)) / (v : ℂ) ^ (2 * M)) u
  by_cases hu : u = 0
  · subst u
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 / 8 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1 / 8)] with v hv
    obtain ⟨h₁, h₂⟩ := bump_small v (abs_le.mpr ⟨by linarith only [hv.1], hv.2.le⟩)
    simp only [h₁, h₂, sub_self, zero_div]
  · have hn : ContDiff ℝ ∞ (fun v : ℝ =>
        (torusLPBump v : ℂ) - (torusLPBump (8 * v) : ℂ)) :=
      (Complex.ofRealCLM.contDiff.comp torusLPBump.contDiff).sub
        (Complex.ofRealCLM.contDiff.comp (torusLPBump.contDiff.comp
          (contDiff_const.mul contDiff_id)))
    have hd : ContDiff ℝ ∞ (fun v : ℝ => (v : ℂ) ^ (2 * M)) :=
      Complex.ofRealCLM.contDiff.pow _
    simpa only [div_eq_mul_inv, Pi.inv_apply] using (hn.contDiffAt (x := u)).mul
      ((hd.contDiffAt (x := u)).inv (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hu)))

/-- The annular inverse-coordinate multiplier of order `2M`, with its smooth zero extension. -/
def torusLPAnnulusGreenProfile (M : ℕ) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_torusLPAnnulusGreenFun M).toSchwartzMap (contDiff_torusLPAnnulusGreenFun M)

theorem torusLPAnnulusGreenProfile_apply (M : ℕ) (u : ℝ) :
    torusLPAnnulusGreenProfile M u =
      ((torusLPBump u : ℂ) - (torusLPBump (8 * u) : ℂ)) / (u : ℂ) ^ (2 * M) := rfl

theorem torusLPAnnulusGreenProfile_eq_zero (M : ℕ) {u : ℝ} (hu : 2 ≤ |u|) :
    torusLPAnnulusGreenProfile M u = 0 := by
  obtain ⟨h₁, h₂⟩ := bump_large u hu
  simp only [torusLPAnnulusGreenProfile_apply, h₁, h₂, Complex.ofReal_zero, sub_self, zero_div]

theorem torusLPAnnulusGreenProfile_mul_pow (M : ℕ) (u : ℝ) :
    torusLPAnnulusGreenProfile M u * (u : ℂ) ^ (2 * M) =
      (torusLPBump u : ℂ) - (torusLPBump (8 * u) : ℂ) := by
  rw [torusLPAnnulusGreenProfile_apply]
  by_cases hu : u = 0
  · subst u
    obtain ⟨h₁, h₂⟩ := bump_small 0 (by norm_num)
    simp only [h₁, h₂, sub_self, zero_div, zero_mul]
  · exact div_mul_cancel₀ _ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hu))

end RegularityStructures

end
