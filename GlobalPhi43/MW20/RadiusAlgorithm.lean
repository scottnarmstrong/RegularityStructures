module

public import GlobalPhi43.MW20.RadiusStopping

/-!
# The radius algorithm with its stopping alternatives

This composes the actual recursive radii, finite termination, geometric bounds,
and interpolation. The local analytic halving estimate and the smallness test
are explicit inputs; no extra positivity premise is imposed on the mass profile.
-/

public section

namespace GlobalPhi43.MW20

/-- The clipped radius construction is nondecreasing, including after zero mass. -/
theorem radiusSequence_monotone (f : ℝ → ℝ) {C L : ℝ} (hC : 0 < C) (hL : 0 ≤ L)
    (hf : ∀ x ∈ Set.Icc 0 L, 0 ≤ f x) : Monotone (radiusSequence f C L) := by
  apply monotone_nat_of_le_succ
  intro i
  have hm := radiusSequence_mem f hC hL hf i
  rw [radiusSequence_succ]
  exact le_min hm.2 (le_add_of_nonneg_right (div_nonneg (by positivity) (hf _ hm)))

/-- The entire scalar radius algorithm: it stops at the endpoint, zero mass,
or failure of smallness, and bounds every intermediate radius. The halving
input is required only for full increments lying strictly before the endpoint. -/
theorem radiusSequence_estimate (f : ℝ → ℝ) (Good : ℝ → Prop) {C L A : ℝ}
    (hC : 0 < C) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hf : ∀ x ∈ Set.Icc 0 L, 0 ≤ f x) (hmono : AntitoneOn f (Set.Icc 0 L))
    (hhalf : ∀ r ∈ Set.Icc 0 L, Good r → 0 < f r → r + 4 * C / f r < L →
      f (r + 4 * C / f r) ≤ f r / 2)
    (hfail : ∀ r ∈ Set.Icc 0 L, ¬ Good r → f r ≤ A) :
    ∃ n, (radiusSequence f C L n = L ∨ f (radiusSequence f C L n) = 0 ∨
        ¬ Good (radiusSequence f C L n)) ∧
      (∀ i < n, radiusSequence f C L i < L ∧
        0 < f (radiusSequence f C L i) ∧ Good (radiusSequence f C L i)) ∧
      ∀ R ∈ Set.Ioc 0 L, f R ≤ max (8 * C / R) A := by
  classical
  let r := radiusSequence f C L
  have hmem (i : ℕ) : r i ∈ Set.Icc 0 L := radiusSequence_mem f hC hL hf i
  have hmon : Monotone r := radiusSequence_monotone f hC hL hf
  have hex : ∃ n, r n = L ∨ f (r n) = 0 ∨ ¬ Good (r n) := by
    obtain ⟨n, hn⟩ := radiusSequence_terminates_or_zero f hC hL hf hmono
    exact ⟨n, hn.imp_right Or.inl⟩
  let n := Nat.find hex
  have hstop : r n = L ∨ f (r n) = 0 ∨ ¬ Good (r n) := Nat.find_spec hex
  have hpre (i : ℕ) (hi : i < n) : r i < L ∧ 0 < f (r i) ∧ Good (r i) := by
    have hh := Nat.find_min hex hi
    have hneL : r i ≠ L := fun h => hh (Or.inl h)
    have hne0 : f (r i) ≠ 0 := fun h => hh (Or.inr (Or.inl h))
    have hgood : Good (r i) := by
      by_contra h
      exact hh (Or.inr (Or.inr h))
    exact ⟨lt_of_le_of_ne (hmem i).2 hneL,
      lt_of_le_of_ne (hf _ (hmem i)) hne0.symm, hgood⟩
  refine ⟨n, hstop, hpre, ?_⟩
  intro R hR
  apply radius_algorithm_stopping_bound f r C A L n hmono
    (fun i hi => (hpre i hi).2.1) hC.le rfl (hmem n).2
    (fun i hi => ⟨(hmem i).1, hmon hi⟩)
    (fun i _ => min_le_right _ _) ?_ ?_ hR.1 hR.2
  · intro i hi
    have hi0 : i < n := by omega
    have hfull : r i + 4 * C / f (r i) < L := by
      by_contra h
      have heq : r (i + 1) = L := min_eq_left (by linarith)
      exact (ne_of_lt (hpre (i + 1) hi).1) heq
    have heq : r (i + 1) = r i + 4 * C / f (r i) := min_eq_right hfull.le
    rw [heq]
    exact hhalf _ (hmem i) (hpre i hi0).2.2 (hpre i hi0).2.1 hfull
  · rcases hstop with he | hz | hg
    · exact Or.inl he
    · exact Or.inr (hz ▸ hA)
    · exact Or.inr (hfail _ (hmem n) hg)

end GlobalPhi43.MW20
