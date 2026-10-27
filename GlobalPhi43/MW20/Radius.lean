module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Tactic

/-!
# Arithmetic of MW20's radius algorithm

The analytic halving estimate is an input here. These lemmas prove the finite
iteration arithmetic of (4.34)–(4.37), including a clipped last increment.
They do not assert the analytic smallness hypothesis or the halving estimate.
-/

public section

namespace GlobalPhi43.MW20


/-- One step of the geometric summation (4.37), allowing a clipped increment. -/
theorem radius_mass_step {r s M N C : ℝ} (hr : 0 ≤ r) (hM : 0 < M)
    (hN : 0 ≤ N) (hstep : s ≤ r + 4 * C / M) (hhalf : N ≤ M / 2)
    (hbound : r * M ≤ 4 * C) : s * N ≤ 4 * C := by
  have h1 := mul_le_mul_of_nonneg_right hstep hN
  have h2 := mul_le_mul_of_nonneg_left hhalf hr
  have h3 : 4 * C / M * N ≤ 2 * C := by
    have hC : 0 ≤ C := by nlinarith
    have h := mul_le_mul_of_nonneg_left hhalf (div_nonneg (by positivity : 0 ≤ 4 * C) hM.le)
    have heq : 4 * C / M * (M / 2) = 2 * C := by field_simp; ring
    linarith
  nlinarith

/-- The finite radius sequence has uniformly bounded radius times mass.
Only steps strictly before the final, possibly clipped, endpoint need halve. -/
theorem radius_mass_bound (r M : ℕ → ℝ) (C : ℝ) (n : ℕ)
    (hzero : r 0 = 0) (hr : ∀ i ≤ n, 0 ≤ r i)
    (hM : ∀ i ≤ n, 0 < M i)
    (hstep : ∀ i < n, r (i + 1) ≤ r i + 4 * C / M i)
    (hhalf : ∀ i < n, M (i + 1) ≤ M i / 2) (hC : 0 ≤ C) :
    r n * M n ≤ 4 * C := by
  induction n with
  | zero => simp [hzero, hC]
  | succ n ih =>
    have hb := ih (fun i hi => hr i (by omega)) (fun i hi => hM i (by omega))
      (fun i hi => hstep i (by omega)) (fun i hi => hhalf i (by omega))
    exact radius_mass_step (hr n (by omega)) (hM n (by omega))
      (hM (n + 1) (by omega)).le (hstep n (by omega)) (hhalf n (by omega)) hb

/-- Interpolation between successive algorithm radii. The terminal increment
may be clipped, and no halving is needed at its right endpoint. -/
theorem radius_interpolate {r s R M m C : ℝ} (hM : 0 < M)
    (hmM : m ≤ M) (hR : 0 ≤ R) (hRs : R ≤ s)
    (hstep : s ≤ r + 4 * C / M) (hbound : r * M ≤ 4 * C) :
    R * m ≤ 8 * C := by
  have h1 := mul_le_mul_of_nonneg_left hmM hR
  have h2 := mul_le_mul_of_nonneg_right (hRs.trans hstep) hM.le
  have heq : (r + 4 * C / M) * M = r * M + 4 * C := by
    field_simp
  nlinarith

/-- Finite-sequence version of the final interpolation in MW20 §4.6.
`f` is the nonincreasing cylinder supremum. This applies whenever the finite
algorithm reaches `L`; stopping through failure of smallness is separate. -/
theorem radius_algorithm_bound (f : ℝ → ℝ) (r : ℕ → ℝ) (C L : ℝ) (n : ℕ)
    (hf : AntitoneOn f (Set.Icc 0 L)) (hpos : ∀ i < n, 0 < f (r i))
    (hC : 0 ≤ C) (hzero : r 0 = 0) (hend : r n = L)
    (hr : ∀ i ≤ n, r i ∈ Set.Icc 0 L)
    (hstep : ∀ i < n, r (i + 1) ≤ r i + 4 * C / f (r i))
    (hhalf : ∀ i, i + 1 < n → f (r (i + 1)) ≤ f (r i) / 2)
    {R : ℝ} (hR : 0 < R) (hRL : R ≤ L) : f R ≤ 8 * C / R := by
  have hex : ∃ j, j ≤ n ∧ R ≤ r j := ⟨n, le_rfl, hend ▸ hRL⟩
  let j := Nat.find hex
  have hj : j ≤ n ∧ R ≤ r j := Nat.find_spec hex
  have hjpos : 0 < j := by
    by_contra hn
    have hj0 : j = 0 := by omega
    rw [hj0, hzero] at hj
    linarith [hj.2]
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hjpos)
  have hij : i + 1 = j := hi.symm
  have hin : i < n := by omega
  have hri : r i < R := by
    by_contra h
    have hsmall : i ≤ n ∧ R ≤ r i := ⟨by omega, by linarith⟩
    have hmin := Nat.find_min' hex hsmall
    change j ≤ i at hmin
    omega
  have hbound : r i * f (r i) ≤ 4 * C :=
    radius_mass_bound r (fun k => f (r k)) C i hzero
      (fun k hk => (hr k (by omega)).1)
      (fun k hk => hpos k (by omega))
      (fun k hk => hstep k (by omega)) (fun k hk => hhalf k (by omega)) hC
  have hinter := radius_interpolate (hpos i hin)
    (hf (hr i (by omega)) ⟨hR.le, hRL⟩ hri.le) hR.le
    (hij ▸ hj.2) (hstep i hin) hbound
  exact (le_div_iff₀ hR).2 (by nlinarith)

end GlobalPhi43.MW20
