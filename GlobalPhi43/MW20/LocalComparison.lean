module

public import GlobalPhi43.MW20.LocalMaximum

/-!
# Comparison on a compact source cylinder

A continuous field with nonpositive parabolic boundary values and a strictly
negative heat operator wherever it is positive is nonpositive throughout the
closed cylinder, including its top face.
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

/-- Local comparison, with boundary conditions only at initial and spatial
faces. No terminal boundary condition is present. -/
theorem nonpos_of_sourceHeat_neg {w : ParabolicSpace → ℝ} {s₀ T a b : ℝ}
    (hw : ContinuousOn w (Icc (s₀, fun _ : Fin 3 => a) (T, fun _ => b)))
    (hbd : ∀ z ∈ Icc (s₀, fun _ : Fin 3 => a) (T, fun _ => b),
      (z.1 = s₀ ∨ ∃ i, z.2 i = a ∨ z.2 i = b) → w z ≤ 0)
    (hdt : ∀ z ∈ Icc (s₀, fun _ : Fin 3 => a) (T, fun _ => b),
      s₀ < z.1 → (∀ i, a < z.2 i ∧ z.2 i < b) →
      DifferentiableAt ℝ (fun t => w (t, z.2)) z.1)
    (hsign : ∀ z ∈ Icc (s₀, fun _ : Fin 3 => a) (T, fun _ => b),
      s₀ < z.1 → (∀ i, a < z.2 i ∧ z.2 i < b) →
      0 < w z → sourceHeat w z < 0) :
    ∀ z ∈ Icc (s₀, fun _ : Fin 3 => a) (T, fun _ => b), w z ≤ 0 := by
  by_contra h
  push Not at h
  obtain ⟨z, hz, hp⟩ := h
  obtain ⟨q, hq, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨z, hz⟩ hw
  have hpos : 0 < w q := hp.trans_le (hmax hz)
  have ht : s₀ < q.1 := by
    apply lt_of_le_of_ne hq.1.1
    intro he
    exact (not_le_of_gt hpos) (hbd q hq (Or.inl he.symm))
  have hx (i : Fin 3) : a < q.2 i ∧ q.2 i < b := by
    constructor
    · apply lt_of_le_of_ne (hq.1.2 i)
      intro he
      exact (not_le_of_gt hpos) (hbd q hq (Or.inr ⟨i, Or.inl he.symm⟩))
    · apply lt_of_le_of_ne (hq.2.2 i)
      intro he
      exact (not_le_of_gt hpos) (hbd q hq (Or.inr ⟨i, Or.inr he⟩))
  have hnonneg := sourceHeat_nonneg_at_max hw ht hq.2.1 hx hmax (hdt q hq ht hx)
  exact (not_lt_of_ge hnonneg) (hsign q hq ht hx hpos)

end GlobalPhi43.MW20
