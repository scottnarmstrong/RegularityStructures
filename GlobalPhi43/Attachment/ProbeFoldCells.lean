module

public import GlobalPhi43.Attachment.ProbePeriodicPartition
public import Mathlib.Data.Fintype.BigOperators

/-! A concrete finite lattice cube contains every contributing folded annulus
cell, with the source O(2^(3j)) count proved before any model data. -/

@[expose] public noncomputable section

open Set

namespace GlobalPhi43.Attachment

def probeFoldCells (j : ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-((3 * 2^j : ℕ) : ℤ)) ((3 * 2^j : ℕ) : ℤ))

theorem probeFoldCells_card (j : ℕ) : (probeFoldCells j).card = (6 * 2^j + 1)^3 := by
  rw [probeFoldCells, Fintype.card_piFinset_const, Int.card_Icc]
  have he : (((3 * 2^j : ℕ) : ℤ) + 1 - -((3 * 2^j : ℕ) : ℤ)).toNat = 6 * 2^j + 1 := by
    omega
  rw [he]

theorem probeFoldCells_card_bound (j : ℕ) : (probeFoldCells j).card ≤ 343 * 2^(3*j) := by
  rw [probeFoldCells_card]
  have hp : 1 ≤ (2 : ℕ)^j := Nat.one_le_pow j 2 (by decide)
  calc (6 * 2^j + 1)^3 ≤ (7 * 2^j)^3 := Nat.pow_le_pow_left (by omega : 6 * 2^j + 1 ≤ 7 * 2^j) 3
    _ = 343 * 2^(3*j) := by rw [mul_pow, ← pow_mul]; congr 1; ring

theorem probeFoldCells_mem {j : ℕ} {m : Fin 3 → ℤ}
    (hm : ∀ i, |(m i : ℝ)| ≤ 3 * (2 : ℝ)^j) : m ∈ probeFoldCells j := by
  apply Fintype.mem_piFinset.mpr
  intro i
  have hh := abs_le.mp (hm i)
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast hh.1
  · exact_mod_cast hh.2

/-- Unit folding support and the original Gaussian annulus force the lattice
index into the fixed cube; neither a finite-cell list nor its bound is assumed. -/
theorem probeFoldCells_of_support {j : ℕ} {r : ℝ} (hr : r ≤ 1)
    {y : ProbeSpace} (hy : ‖y‖ ≤ 1) {m : Fin 3 → ℤ}
    (hm : ‖y + fun i => (m i : ℝ)‖ ≤ (2 : ℝ)^(j+1) * r) :
    m ∈ probeFoldCells j := by
  apply probeFoldCells_mem
  intro i
  have hc : |(m i : ℝ)| ≤ (2 : ℝ)^(j+1) * r + 1 := by
    calc |(m i : ℝ)| = |(y + fun i => (m i : ℝ)) i - y i| := by simp
      _ ≤ |(y + fun i => (m i : ℝ)) i| + |y i| := abs_sub _ _
      _ ≤ ‖y + fun i => (m i : ℝ)‖ + ‖y‖ := by
        simpa only [Real.norm_eq_abs] using add_le_add
          (norm_le_pi_norm (y + fun i => (m i : ℝ)) i) (norm_le_pi_norm y i)
      _ ≤ _ := add_le_add hm hy
  have hp : 1 ≤ (2 : ℝ)^j := one_le_pow₀ (by norm_num)
  have hh := mul_le_mul_of_nonneg_left hr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (j+1))
  rw [mul_one, pow_succ] at hh
  rw [pow_succ] at hc
  linarith

end GlobalPhi43.Attachment
