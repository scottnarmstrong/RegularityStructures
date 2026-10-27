module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic

public noncomputable section

open Set

namespace GlobalPhi43.Flow

/-- A common finite mesh; repeated terminal points are allowed. Every time,
including both endpoints, belongs to a closed mesh interval of length at most h. -/
structure RestartMesh (T h : ℝ) where
  count : ℕ
  point : ℕ → ℝ
  initial : point 0 = 0
  terminal : point count = T
  nonneg : ∀ j, 0 ≤ point j
  bounded : ∀ j, point j ≤ T
  mono : Monotone point
  step : ∀ j, point (j + 1) ≤ point j + h
  covers : ∀ t ∈ Icc (0 : ℝ) T, ∃ j < count, t ∈ Icc (point j) (point (j + 1))

/-- The choice depends only on the horizon and a positive common step, never
on a start, approximation index or initial datum. The final interval is clipped. -/
theorem exists_restartMesh (T h : ℝ) (hT : 0 ≤ T) (hh : 0 < h) :
    Nonempty (RestartMesh T h) := by
  let p : ℕ → ℝ := fun j => min ((j : ℝ) * h) T
  have hp0 : p 0 = 0 := by simp [p, hT]
  have hpmono : Monotone p := by
    intro i j hij
    exact min_le_min_right T (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hh.le)
  have hpstep (j : ℕ) : p (j + 1) ≤ p j + h := by
    dsimp [p]
    rw [← min_add_add_right]
    apply min_le_min
    · push_cast
      linarith
    · linarith
  let N := Nat.floor (T / h) + 1
  have hN : T ≤ (N : ℝ) * h := by
    have := Nat.lt_floor_add_one (T / h)
    dsimp [N]
    push_cast
    exact (div_lt_iff₀ hh).mp this |>.le
  refine ⟨⟨N, p, hp0, min_eq_right hN, ?_, ?_, hpmono, hpstep, ?_⟩⟩
  · intro j
    exact le_min (mul_nonneg (Nat.cast_nonneg j) hh.le) hT
  · intro j
    exact min_le_right _ _
  · intro t ht
    let j := Nat.floor (t / h)
    have hj : j < N := Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right ht.2 hh.le))
    have hlo : (j : ℝ) * h ≤ t :=
      (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg ht.1 hh.le))
    have hhi : t ≤ ((j + 1 : ℕ) : ℝ) * h := by
      have := (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one (t / h))
      simpa [j, Nat.cast_add, Nat.cast_one] using this.le
    exact ⟨j, hj, (min_le_left _ _).trans hlo, le_min hhi ht.2⟩

end GlobalPhi43.Flow
