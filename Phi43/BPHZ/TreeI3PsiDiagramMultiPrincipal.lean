/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiDiagramMultiBasic
public import Phi43.BPHZ.TreeI3PsiPrincipalBound

/-!
# The principal majorant with general exponents

The principal diagram of `I(Ψ³)Ψ` is dominated by
`1_{|t| ≤ 2}(w) (s₃(z,w) + s₃(0,w)) · (s_{3+θ}(z',v) + s_{3+θ}(0,v)) s_{3+τ}(w,v)`,
where `θ` is the Hölder gain on `δK(z', ·)` and `τ ≥ 0` the loss in the exponent of the cube of the
covariance.  Its double integral is bounded by a constant if `θ + τ < 1`.

Source: [Hai14] = arXiv:1303.5113v4, p. 167--168.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

/-- The principal majorant with exponents `θ` (Hölder gain) and `τ` (loss in the cube). -/
def i3PsiPrincipalMajorant (θ τ : ℝ) (z z' w v : SpaceTime) : ℝ :=
  Set.indicator {w : SpaceTime | |w.1| ≤ 2} (fun w => singularPow 3 z w + singularPow 3 0 w) w *
    ((singularPow (3 + θ) z' v + singularPow (3 + θ) 0 v) * singularPow (3 + τ) w v)

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

/-- **Two-level bound for the principal majorant.** -/
theorem twoLevelLe_principalMajorant {θ τ : ℝ} (hθ : 0 < θ) (hτ : 0 ≤ τ) (hθτ : θ + τ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z z' : SpaceTime, torusParabolicSize z ≤ 1 → torusParabolicSize z' ≤ 1 →
      TwoLevelLe (i3PsiPrincipalMajorant θ τ z z') C := by
  obtain ⟨Cin, hCin, hin⟩ := singularIntLe_mul_two (a := 3 + θ) (b := 3 + τ) (η := 1 + θ + τ)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by ring)
  obtain ⟨Cs, hCs, hs⟩ := singularIntLe_slab_mul_two (a := 3) (b := 1 + θ + τ) (by norm_num)
    (by linarith) (by linarith)
  have hin2 : ∀ c₁ c₂ w : SpaceTime, 0 < torusParabolicSize (c₁ - w) →
      0 < torusParabolicSize (c₂ - w) →
      SingularIntLe (fun v => (singularPow (3 + θ) c₁ v + singularPow (3 + θ) c₂ v) *
          singularPow (3 + τ) w v)
        (Cin * (singularPow (1 + θ + τ) c₁ w + singularPow (1 + θ + τ) c₂ w)) := by
    intro c₁ c₂ w p₁ p₂
    have := (hin c₁ w p₁).add (hin c₂ w p₂)
    refine (this.congr_fun (fun v => by ring)).mono_right (le_of_eq ?_)
    simp only [singularPow]
    ring
  refine ⟨Cin * (Cs + Cs + Cs + Cs), by positivity, ?_⟩
  intro z z' hz hz'
  have hs0 : torusParabolicSize (0 : SpaceTime) ≤ 1 := by
    rw [torusParabolicSize_zero_spaceTime]; norm_num
  set S : Set SpaceTime := {w : SpaceTime | |w.1| ≤ 2} with hSdef
  let m : SpaceTime → ℝ := fun w => Set.indicator S
    (fun w => singularPow 3 z w + singularPow 3 0 w) w
  have hm0 : ∀ w, 0 ≤ m w := fun w => Set.indicator_nonneg (fun w _ =>
    add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)) w
  have t1 := hs z z' hz hz'
  have t2 := hs z 0 hz hs0
  have t3 := hs 0 z' hs0 hz'
  have t4 := hs 0 0 hs0 hs0
  have hsum := ((t1.add t2).add t3).add t4
  have hH := (hsum.const_mul (c := Cin) hCin).congr_fun
    (g := fun w => m w * (Cin * (singularPow (1 + θ + τ) z' w + singularPow (1 + θ + τ) 0 w)))
    (fun w => by
      by_cases hw : w ∈ S
      · simp only [m, Set.indicator_of_mem hw]
        ring
      · simp only [m, Set.indicator_of_notMem hw]
        ring)
  refine ⟨?_, fun w => m w * (Cin * (singularPow (1 + θ + τ) z' w +
    singularPow (1 + θ + τ) 0 w)), hH, ?_⟩
  · filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0] with w a b
    exact ((hin2 z' 0 w a b).1).const_mul _
  · filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0] with w a b
    calc ∫ v, i3PsiPrincipalMajorant θ τ z z' w v
        = m w * ∫ v, (singularPow (3 + θ) z' v + singularPow (3 + θ) 0 v) *
            singularPow (3 + τ) w v := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hin2 z' 0 w a b).2 (hm0 w)

end RegularityStructures

end
