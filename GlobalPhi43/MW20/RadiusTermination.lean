module

public import GlobalPhi43.MW20.Radius

/-!
# Finite termination of MW20's clipped radius construction

A nonnegative decreasing mass profile reaches the target endpoint or zero
mass after finitely many steps. Before that first stop the increments have
a fixed positive lower bound. No bound on the number of steps is assumed.
-/

public section

namespace GlobalPhi43.MW20

/-- The source radius construction, with its last increment clipped at `L`. -/
@[expose] noncomputable def radiusSequence (f : ℝ → ℝ) (C L : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => min L (radiusSequence f C L n + 4 * C / f (radiusSequence f C L n))

@[simp] theorem radiusSequence_succ (f : ℝ → ℝ) (C L : ℝ) (n : ℕ) :
    radiusSequence f C L (n + 1) =
      min L (radiusSequence f C L n + 4 * C / f (radiusSequence f C L n)) := rfl

/-- Every constructed radius stays in the target interval. -/
theorem radiusSequence_mem (f : ℝ → ℝ) {C L : ℝ} (hC : 0 < C) (hL : 0 ≤ L)
    (hf : ∀ x ∈ Set.Icc 0 L, 0 ≤ f x) (n : ℕ) :
    radiusSequence f C L n ∈ Set.Icc 0 L := by
  induction n with
  | zero =>
    change (0 : ℝ) ∈ Set.Icc 0 L
    simpa using hL
  | succ n ih =>
    rw [radiusSequence_succ]
    exact ⟨le_min hL (by positivity [ih.1, hf _ ih]), min_le_left _ _⟩

/-- A nonnegative decreasing profile reaches the endpoint or a zero mass in
finitely many steps. Division by a vanishing mass is never used to claim progress. -/
theorem radiusSequence_terminates_or_zero (f : ℝ → ℝ) {C L : ℝ} (hC : 0 < C) (hL : 0 ≤ L)
    (hf : ∀ x ∈ Set.Icc 0 L, 0 ≤ f x) (hmono : AntitoneOn f (Set.Icc 0 L)) :
    ∃ n, radiusSequence f C L n = L ∨ f (radiusSequence f C L n) = 0 := by
  let r := radiusSequence f C L
  have hmem (n : ℕ) : r n ∈ Set.Icc 0 L := radiusSequence_mem f hC hL hf n
  by_contra hstop
  have hn (n : ℕ) : r n ≠ L ∧ f (r n) ≠ 0 := by
    simpa only [not_or] using (not_exists.mp hstop n)
  have hpositive (n : ℕ) : 0 < f (r n) :=
    lt_of_le_of_ne (hf _ (hmem n)) (hn n).2.symm
  have hf0 : 0 < f 0 := hpositive 0
  let δ := 4 * C / f 0
  have hδ : 0 < δ := div_pos (by positivity) hf0
  have hinc (n : ℕ) : r n + δ ≤ r (n + 1) := by
    have hmass : f (r n) ≤ f 0 := hmono ⟨le_rfl, hL⟩ (hmem n) (hmem n).1
    have hdiv : δ ≤ 4 * C / f (r n) :=
      div_le_div_of_nonneg_left (by positivity) (hpositive n) hmass
    have hnext : r n + 4 * C / f (r n) < L := by
      by_contra h
      have heq : r (n + 1) = L := by
        exact min_eq_left (by linarith)
      exact (hn (n + 1)).1 heq
    have heq : r (n + 1) = r n + 4 * C / f (r n) := min_eq_right hnext.le
    rw [heq]
    linarith
  have hlinear (n : ℕ) : (n : ℝ) * δ ≤ r n := by
    induction n with
    | zero =>
      rw [Nat.cast_zero, zero_mul]
      exact le_rfl
    | succ n ih =>
      have hs := hinc n
      push_cast
      nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt (L / δ)
  have hlarge : L < (n : ℝ) * δ := (div_lt_iff₀ hδ).1 hn
  have hsmall := (hlinear n).trans (hmem n).2
  linarith




end GlobalPhi43.MW20

namespace GlobalPhi43.MW20

/-- An early stop at a controlled mass and a geometric interior iteration give
the same bound. This is the abstract stopping alternative; supplying the
source tree-norm stopping test is an analytic attachment obligation. -/
theorem radius_algorithm_stopping_bound (f : ℝ → ℝ) (r : ℕ → ℝ)
    (C A L : ℝ) (n : ℕ) (hf : AntitoneOn f (Set.Icc 0 L))
    (hpos : ∀ i < n, 0 < f (r i)) (hC : 0 ≤ C)
    (hzero : r 0 = 0) (hend : r n ≤ L)
    (hr : ∀ i ≤ n, r i ∈ Set.Icc 0 (r n))
    (hstep : ∀ i < n, r (i + 1) ≤ r i + 4 * C / f (r i))
    (hhalf : ∀ i, i + 1 < n → f (r (i + 1)) ≤ f (r i) / 2)
    (hstop : r n = L ∨ f (r n) ≤ A)
    {R : ℝ} (hR : 0 < R) (hRL : R ≤ L) : f R ≤ max (8 * C / R) A := by
  by_cases hRn : R ≤ r n
  · have hsub : Set.Icc 0 (r n) ⊆ Set.Icc 0 L := fun _ hx => ⟨hx.1, hx.2.trans hend⟩
    have hb := radius_algorithm_bound f r C (r n) n
      (fun _ hx _ hy hxy => hf (hsub hx) (hsub hy) hxy)
      hpos hC hzero rfl hr hstep hhalf hR hRn
    exact hb.trans (le_max_left _ _)
  · have hlast : f (r n) ≤ A := hstop.resolve_left (by intro h; rw [h] at hRn; exact hRn hRL)
    have hrn := hr n le_rfl
    exact (hf ⟨hrn.1, hend⟩ ⟨hR.le, hRL⟩ (by linarith)).trans
      (hlast.trans (le_max_right _ _))

end GlobalPhi43.MW20
