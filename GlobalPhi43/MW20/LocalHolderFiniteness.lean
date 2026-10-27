module

public import GlobalPhi43.MW20.LocalSourceHolder
public import GlobalPhi43.MW20.ScalarHolderFiniteness

/-!
# Finite actual real Holder suprema at arbitrary cutoffs on bounded domains
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- An actual extended scalar budget bounds every real local quotient,
without treating an unbounded real sSup as a source norm. -/
theorem localSourceHolder_bddAbove_of_scalar_budget
    (f : ParabolicSpace → ℝ) (D : Set ParabolicSpace) (a L : ℝ)
    {N : ℝ} (hN : 0 ≤ N) (hnorm : scalarHolderSeminorm f D a ≤ ENNReal.ofReal N) :
    BddAbove (localSourceHolderValues f a D L) := by
  refine ⟨N, ?_⟩
  rintro q (hq | ⟨x, hx, y, hy, hp, _, rfl⟩)
  · have he : q = 0 := hq
    rwa [he]
  · have hne : y ≠ x := by
      intro he; subst y
      simp only [Local.pdist, sub_self, abs_zero, Real.sqrt_zero, norm_zero, max_self] at hp
      exact (lt_irrefl 0) hp
    have hq : ENNReal.ofReal (|f y - f x| / Local.pdist x y ^ a) ≤ scalarHolderSeminorm f D a :=
      le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy
        (le_iSup_of_le hne le_rfl))))
    exact (ENNReal.ofReal_le_ofReal_iff hN).mp (hq.trans hnorm)

/-- Smooth bounded-domain source fields have finite actual real Holder
norms at every cutoff; no cutoff upper bound is needed. -/
theorem localSourceHolder_bddAbove_of_smooth
    (f : ParabolicSpace → ℝ) (hf : ContDiff ℝ ∞ f)
    (D : Set ParabolicSpace) (R : ℝ) (hD : D ⊆ Metric.closedBall 0 R)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (L : ℝ) :
    BddAbove (localSourceHolderValues f a D L) := by
  obtain ⟨N, hN, hnorm⟩ := scalarHolderSeminorm_finite_bound f hf D R hD ha ha1
  exact localSourceHolder_bddAbove_of_scalar_budget f D a L hN hnorm

/-- Restricting the actual domain and cutoff decreases its finite real norm. -/
theorem localSourceHolder_mono_of_bddAbove
    (f : ParabolicSpace → ℝ) (a : ℝ)
    {D E : Set ParabolicSpace} {L K : ℝ} (hDE : D ⊆ E) (hLK : L ≤ K)
    (hb : BddAbove (localSourceHolderValues f a E K)) :
    localSourceHolder f a D L ≤ localSourceHolder f a E K :=
  csSup_le_csSup hb ⟨0, Or.inl rfl⟩ (localSourceHolderValues_mono f a hDE hLK)

end GlobalPhi43.MW20
