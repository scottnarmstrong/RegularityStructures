module

public import GlobalPhi43.MW20.ParentHolderNorm

/-!
# Extending interpolation cutoffs with the parent amplitude

Far pairs use actual amplitude and tree increments. No larger-radius affine
remainder estimate or contradiction hypothesis on a child is introduced.
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

/-- Compare a far-pair increment power to the local cutoff. -/
theorem parent_holder_far_power {ρ s a b : ℝ} (hρ : 0 < ρ) (hρs : ρ ≤ s) (hab : a ≤ b) :
    s ^ a ≤ ρ ^ (a - b) * s ^ b := by
  have hs : 0 < s := hρ.trans_le hρs
  calc
    _ = s ^ (a - b) * s ^ b := by rw [← Real.rpow_add hs]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hρ hρs (sub_nonpos.mpr hab)) (Real.rpow_nonneg hs.le b)

/-- The actual v seminorm at any larger cutoff is bounded using its near
seminorm and the parent amplitude, with no derivative bound for far pairs. -/
theorem localSourceHolder_extend_parent {v : ParabolicSpace → ℝ}
    {D : Set ParabolicSpace} {a ρ L B M : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hb : BddAbove (localSourceHolderValues v a D ρ))
    (hnear : localSourceHolder v a D ρ ≤ B) (hamp : ∀ x ∈ D, |v x| ≤ M) :
    localSourceHolder v a D L ≤ B + 2 * M * ρ ^ (-a) := by
  apply localSourceHolder_le_of_increment (by positivity)
  intro x hx y hy hs _
  by_cases hn : Local.pdist x y ≤ ρ
  · have hi := (localSourceHolder_increment hb hx hy hn hρ1).trans
      (mul_le_mul_of_nonneg_right hnear (Real.rpow_nonneg hs.le a))
    have hp : 0 ≤ 2 * M * ρ ^ (-a) * Local.pdist x y ^ a := by positivity
    nlinarith only [hi, hp]
  · have hi : |v y - v x| ≤ 2 * M := (abs_sub _ _).trans
      (by linarith [hamp x hx, hamp y hy])
    have hp := mul_le_mul_of_nonneg_left
      (parent_holder_far_power hρ (le_of_not_ge hn) ha) (show 0 ≤ 2 * M by positivity)
    simp only [Real.rpow_zero, zero_sub] at hp
    have hbase : 0 ≤ B * Local.pdist x y ^ a := by positivity
    nlinarith only [hi, hp, hbase]

end GlobalPhi43.MW20
