module

public import GlobalPhi43.MW20.CubicPullbackRegularity
public import GlobalPhi43.MW20.MaximumPrinciple

/-!
# Lemma 2.7 on the literal interior cylinders used in MW20 (4.28)
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures

/-- The maximum-principle step on nested source cylinders, with the exact
boundary gap. The universal constant 15 is inherited from the proved Lemma 2.7;
no rescaled maximum-principle hypothesis is introduced. -/
theorem source_interior_cubic_maximum (w g : ParabolicSpace → ℝ)
    {S R G : ℝ} (hS : 0 ≤ S) (hSR : S < R) (hG : 0 ≤ G)
    (hw : ∀ z ∈ sourceCylinder S, ContDiffAt ℝ 2 w z)
    (hpde : ∀ z ∈ sourceCylinder S, sourceHeat w z = -w z ^ 3 + g z)
    (hg : ∀ z ∈ sourceCylinder S, |g z| ≤ G ^ 3)
    {x : ParabolicSpace} (hx : x ∈ sourceCylinder R) :
    |w x| ≤ 15 * max (1 / (R - S)) G := by
  let c := R - S
  let b : ParabolicSpace := (x.1 - c ^ 2, x.2)
  let gh : ParabolicSpace → ℝ := fun z => c ^ 3 * g (b + parabolicDilate c z)
  have hc : 0 < c := sub_pos.mpr hSR
  have hm : ∀ z ∈ sourceClosedCylinder, b + parabolicDilate c z ∈ sourceCylinder S :=
    fun z hz => cubicPullback_sourceCylinder hS hSR hx hz
  have hu := sourceCubicRegularity_pullback w b c (fun z hz => hw _ (hm z hz))
  have hpull : ∀ z ∈ sourceCylinder 0,
      sourceHeat (sourceCubicPullback w b c) z = -(sourceCubicPullback w b c z) ^ 3 + gh z := by
    intro z hz
    rw [sourceHeat_cubicPullback, hpde _ (hm z (sourceCylinder_subset_closed (by norm_num) hz))]
    dsimp [sourceCubicPullback, gh]
    ring
  have hforcing : ∀ z ∈ sourceCylinder 0, |gh z| ≤ (c * G) ^ 3 := by
    intro z hz
    dsimp [gh]
    rw [abs_mul, abs_of_nonneg (pow_nonneg hc.le 3), mul_pow]
    exact mul_le_mul_of_nonneg_left
      (hg _ (hm z (sourceCylinder_subset_closed (by norm_num) hz))) (pow_nonneg hc.le 3)
  have h := mw20_lemma_2_7_cubed hu (mul_nonneg hc.le hG) hpull hforcing
    ((1 : ℝ), 0) (ρ := 1) (by norm_num) (by norm_num) (by norm_num)
      (fun _ => by simp)
  have hpoint : b + parabolicDilate c ((1 : ℝ), 0) = x := by
    ext i <;> simp [b, parabolicDilate]
  have hvalue : |sourceCubicPullback w b c ((1 : ℝ), 0)| = c * |w x| := by
    rw [sourceCubicPullback, hpoint, abs_mul, abs_of_pos hc]
  rw [hvalue] at h
  have hmax : max (1 : ℝ) (c * G) = c * max (1 / c) G := by
    rw [mul_max_of_nonneg _ _ hc.le]
    congr 1
    field_simp
  norm_num only [div_one] at h
  rw [hmax] at h
  change |w x| ≤ 15 * max (1 / c) G
  nlinarith

end GlobalPhi43.MW20
