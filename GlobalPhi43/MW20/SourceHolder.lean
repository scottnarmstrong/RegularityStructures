module

public import GlobalPhi43.MW20.CylinderSup
public import GlobalPhi43.Local.RadiusGeometry
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The actual radius-local source Hölder seminorm
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

/-- The source parabolic metric dominates the ordinary norm at distances
at most one. -/
theorem norm_sub_le_pdist {x y : ParabolicSpace} (hxy : Local.pdist x y ≤ 1) :
    ‖x - y‖ ≤ Local.pdist x y := by
  have ht := le_max_left (Real.sqrt |x.1 - y.1|) ‖x.2 - y.2‖
  have hs := le_max_right (Real.sqrt |x.1 - y.1|) ‖x.2 - y.2‖
  change _ ≤ Local.pdist x y at ht hs
  have hp := Local.pdist_nonneg x y
  change max ‖x.1 - y.1‖ ‖x.2 - y.2‖ ≤ _
  apply max_le _ hs
  rw [Real.norm_eq_abs]
  nlinarith [Real.sq_sqrt (abs_nonneg (x.1 - y.1)), Real.sqrt_nonneg |x.1 - y.1|]

/-- The set of source local Hölder quotients, with zero included to cover
empty domains and the diagonal convention. -/
@[expose] def sourceHolderValues (v : ParabolicSpace → ℝ) (α R L : ℝ) : Set ℝ :=
  {0} ∪ {q | ∃ x ∈ sourceCylinder R, ∃ y ∈ sourceCylinder R,
    0 < Local.pdist x y ∧ Local.pdist x y ≤ L ∧
      q = |v y - v x| / Local.pdist x y ^ α}

/-- The actual radius-local MW20 Hölder seminorm. -/
@[expose] noncomputable def sourceHolder (v : ParabolicSpace → ℝ) (α R L : ℝ) : ℝ :=
  sSup (sourceHolderValues v α R L)

/-- Nonnegativity follows from the zero quotient. -/
theorem sourceHolder_nonneg {v : ParabolicSpace → ℝ} {α R L : ℝ}
    (hb : BddAbove (sourceHolderValues v α R L)) : 0 ≤ sourceHolder v α R L :=
  le_csSup hb (Or.inl rfl)

/-- The actual seminorm controls every tested increment, including the
zero-distance case, without any continuity premise. -/
theorem sourceHolder_increment {v : ParabolicSpace → ℝ} {α R L : ℝ}
    (hb : BddAbove (sourceHolderValues v α R L)) {x y : ParabolicSpace}
    (hx : x ∈ sourceCylinder R) (hy : y ∈ sourceCylinder R)
    (hxy : Local.pdist x y ≤ L) (hL : L ≤ 1) :
    |v y - v x| ≤ sourceHolder v α R L * Local.pdist x y ^ α := by
  by_cases hp : 0 < Local.pdist x y
  · have hq : |v y - v x| / Local.pdist x y ^ α ≤ sourceHolder v α R L :=
      le_csSup hb (Or.inr ⟨x, hx, y, hy, hp, hxy, rfl⟩)
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hp α)).mp hq
  · have hd : Local.pdist x y = 0 := le_antisymm (le_of_not_gt hp) (Local.pdist_nonneg _ _)
    have hn := norm_sub_le_pdist (hxy.trans hL)
    rw [hd] at hn
    have he : x = y := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))
    subst y
    simp only [sub_self, abs_zero]
    exact mul_nonneg (sourceHolder_nonneg hb) (Real.rpow_nonneg (Local.pdist_nonneg _ _) _)

end GlobalPhi43.MW20
