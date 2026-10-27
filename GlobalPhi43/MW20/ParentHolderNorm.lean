module

public import GlobalPhi43.MW20.ParentExpansionIncrement

/-! Local Holder bounds from increments and comparison of Holder powers on a bounded scale. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- Actual quotient supremum from pointwise increments, including empty domains. -/
theorem localSourceHolder_le_of_increment {v : ParabolicSpace → ℝ}
    {D : Set ParabolicSpace} {a L B : ℝ} (hB : 0 ≤ B)
    (h : ∀ x ∈ D, ∀ y ∈ D, 0 < Local.pdist x y → Local.pdist x y ≤ L →
      |v y - v x| ≤ B * Local.pdist x y ^ a) : localSourceHolder v a D L ≤ B := by
  apply csSup_le (show (localSourceHolderValues v a D L).Nonempty from ⟨0, Or.inl rfl⟩)
  rintro q (hq | ⟨x, hx, y, hy, hp, hxy, rfl⟩)
  · have he : q = 0 := hq
    rwa [he]
  · exact (div_le_iff₀ (Real.rpow_pos_of_pos hp a)).2 (h x hx y hy hp hxy)

/-- Change a local increment exponent at its actual cutoff, without an
extra smallness assumption on the child domain. -/
theorem parent_holder_power {s d a b : ℝ} (hs : 0 < s) (hsd : s ≤ d) (hab : a ≤ b) :
    s ^ b ≤ d ^ (b - a) * s ^ a := by
  calc
    _ = s ^ (b - a) * s ^ a := by rw [← Real.rpow_add hs]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hs.le hsd (sub_nonneg.mpr hab)) (Real.rpow_nonneg hs.le a)

end GlobalPhi43.MW20
