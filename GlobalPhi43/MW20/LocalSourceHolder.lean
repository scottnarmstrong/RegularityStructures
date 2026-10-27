module

public import GlobalPhi43.MW20.SourceHolderBound

/-!
# Positive source seminorms on arbitrary local domains

This supplies the mixed-time D_d domains of the middle section-4 rows,
without replacing them by the smaller P_(r+d) cylinders.
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

/-- The actual local Hölder quotient set on an arbitrary source domain. -/
@[expose] def localSourceHolderValues (v : ParabolicSpace → ℝ) (α : ℝ)
    (D : Set ParabolicSpace) (L : ℝ) : Set ℝ :=
  {0} ∪ {q | ∃ x ∈ D, ∃ y ∈ D, 0 < Local.pdist x y ∧ Local.pdist x y ≤ L ∧
    q = |v y - v x| / Local.pdist x y ^ α}

/-- The literal positive source seminorm on D with radius cutoff at most L. -/
@[expose] noncomputable def localSourceHolder (v : ParabolicSpace → ℝ) (α : ℝ)
    (D : Set ParabolicSpace) (L : ℝ) : ℝ := sSup (localSourceHolderValues v α D L)

/-- Enlarging a domain or cutoff includes all its Hölder quotients. -/
theorem localSourceHolderValues_mono (v : ParabolicSpace → ℝ) (α : ℝ)
    {D E : Set ParabolicSpace} {L K : ℝ} (hDE : D ⊆ E) (hLK : L ≤ K) :
    localSourceHolderValues v α D L ⊆ localSourceHolderValues v α E K := by
  rintro q (hq | ⟨x, hx, y, hy, hp, hxy, rfl⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨x, hDE hx, y, hDE hy, hp, hxy.trans hLK, rfl⟩

/-- Smooth local source data give finite seminorms on every domain contained
in a positive source inset, including the actual mixed-time D_d domains. -/
theorem localSourceHolder_bddAbove {v : ParabolicSpace → ℝ} (hv : SourceCubicRegularity v)
    {D : Set ParabolicSpace} {R α L : ℝ} (hR : 0 < R) (hα : α ≤ 1) (hL : L ≤ 1)
    (hD : D ⊆ sourceCylinder R) : BddAbove (localSourceHolderValues v α D L) :=
  (sourceHolder_bddAbove_of_regularity hv hR hα hL).mono
    (localSourceHolderValues_mono v α hD le_rfl)

/-- The zero quotient ensures nonnegativity. -/
theorem localSourceHolder_nonneg {v : ParabolicSpace → ℝ} {D : Set ParabolicSpace} {α L : ℝ}
    (hb : BddAbove (localSourceHolderValues v α D L)) : 0 ≤ localSourceHolder v α D L :=
  le_csSup hb (Or.inl rfl)

/-- The actual arbitrary-domain seminorm controls each source increment. -/
theorem localSourceHolder_increment {v : ParabolicSpace → ℝ} {D : Set ParabolicSpace} {α L : ℝ}
    (hb : BddAbove (localSourceHolderValues v α D L)) {x y : ParabolicSpace}
    (hx : x ∈ D) (hy : y ∈ D) (hxy : Local.pdist x y ≤ L) (hL : L ≤ 1) :
    |v y - v x| ≤ localSourceHolder v α D L * Local.pdist x y ^ α := by
  by_cases hp : 0 < Local.pdist x y
  · exact (div_le_iff₀ (Real.rpow_pos_of_pos hp α)).mp
      (le_csSup hb (Or.inr ⟨x, hx, y, hy, hp, hxy, rfl⟩))
  · have hd : Local.pdist x y = 0 := le_antisymm (le_of_not_gt hp) (Local.pdist_nonneg _ _)
    have hn := norm_sub_le_pdist (hxy.trans hL)
    rw [hd] at hn
    have he : x = y := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))
    subst y
    simp only [sub_self, abs_zero]
    exact mul_nonneg (localSourceHolder_nonneg hb) (Real.rpow_nonneg (Local.pdist_nonneg _ _) _)

end GlobalPhi43.MW20
