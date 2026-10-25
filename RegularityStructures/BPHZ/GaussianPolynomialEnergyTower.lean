/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianPolynomialReversePoincare

/-!
# The tower of iterated-gradient energies of a polynomial

For a list `L` of polynomials write `sqSum L = ∑ p ∈ L, p ^ 2`, and `polyDerivs L` for the list of
all first partial derivatives of members of `L`.  The tower `derivTower f j` consists of all `j`-th
order partial derivatives of `f`, and `towerEnergy f j = sqSum (derivTower f j)` is the squared
norm of the `j`-th derivative tensor.

* `sum_sq_pderiv_sqSum_le`: the carré du champ of `sqSum L` is at most
  `4 (sqSum L) (sqSum (polyDerivs L))` (Cauchy--Schwarz);
* `gaussExp_sqSum_polyDerivs_le`: the reverse Poincaré inequality for a list of polynomials of
  degree at most `m`, `E[sqSum (polyDerivs L)] ≤ m E[sqSum L]`;
* `towerEnergy_eq_zero_of_lt`: derivatives of order greater than `m` of a polynomial of degree
  at most `m` vanish.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace RegularityStructures

variable {n : ℕ}

/-- The sum of squares of a list of polynomials. -/
def sqSum (L : List (MvPolynomial (Fin n) ℝ)) : MvPolynomial (Fin n) ℝ :=
  (L.map fun p => p ^ 2).sum

/-- All first partial derivatives of the members of a list of polynomials. -/
def polyDerivs (L : List (MvPolynomial (Fin n) ℝ)) : List (MvPolynomial (Fin n) ℝ) :=
  L.flatMap fun p => (List.finRange n).map fun i => pderiv i p

/-- The list of all `j`-th order partial derivatives of `f`. -/
def derivTower (f : MvPolynomial (Fin n) ℝ) : ℕ → List (MvPolynomial (Fin n) ℝ)
  | 0 => [f]
  | j + 1 => polyDerivs (derivTower f j)

/-- The squared norm of the `j`-th derivative tensor of `f`. -/
def towerEnergy (f : MvPolynomial (Fin n) ℝ) (j : ℕ) : MvPolynomial (Fin n) ℝ :=
  sqSum (derivTower f j)

end RegularityStructures

end

public section

open MvPolynomial MeasureTheory

namespace RegularityStructures

variable {n : ℕ}

@[simp] theorem sqSum_nil : sqSum ([] : List (MvPolynomial (Fin n) ℝ)) = 0 := by simp [sqSum]

@[simp] theorem sqSum_cons (a : MvPolynomial (Fin n) ℝ) (L : List (MvPolynomial (Fin n) ℝ)) :
    sqSum (a :: L) = a ^ 2 + sqSum L := by simp [sqSum]

theorem sqSum_append (A B : List (MvPolynomial (Fin n) ℝ)) :
    sqSum (A ++ B) = sqSum A + sqSum B := by simp [sqSum]

theorem eval_sqSum (x : Fin n → ℝ) (L : List (MvPolynomial (Fin n) ℝ)) :
    eval x (sqSum L) = (L.map fun p => eval x p ^ 2).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

theorem eval_sqSum_nonneg (x : Fin n → ℝ) (L : List (MvPolynomial (Fin n) ℝ)) :
    0 ≤ eval x (sqSum L) := by
  rw [eval_sqSum]
  exact List.sum_nonneg fun y hy => by
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hy
    exact sq_nonneg _

@[simp] theorem polyDerivs_nil : polyDerivs ([] : List (MvPolynomial (Fin n) ℝ)) = [] := by
  simp [polyDerivs]

theorem polyDerivs_cons (a : MvPolynomial (Fin n) ℝ) (L : List (MvPolynomial (Fin n) ℝ)) :
    polyDerivs (a :: L) = (List.finRange n).map (fun i => pderiv i a) ++ polyDerivs L := by
  simp [polyDerivs]

theorem sqSum_finRange_pderiv (a : MvPolynomial (Fin n) ℝ) :
    sqSum ((List.finRange n).map fun i => pderiv i a) = ∑ i, pderiv i a ^ 2 := by
  simp only [sqSum, List.map_map]
  rw [Fin.sum_univ_def]
  rfl

theorem sqSum_polyDerivs (L : List (MvPolynomial (Fin n) ℝ)) :
    sqSum (polyDerivs L) = (L.map fun p => ∑ i, pderiv i p ^ 2).sum := by
  induction L with
  | nil => simp
  | cons a L ih => rw [polyDerivs_cons, sqSum_append, sqSum_finRange_pderiv, ih]; simp

theorem coordinateEnergy_eval_eq_sqSum (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    coordinateEnergy (fun y : Fin n → ℝ => eval y p) x = eval x (sqSum (polyDerivs [p])) := by
  rw [coordinateEnergy_eval, sqSum_polyDerivs]
  simp

/-- Evaluation of the derivative of a sum of squares. -/
theorem eval_pderiv_sqSum (k : Fin n) (x : Fin n → ℝ) (L : List (MvPolynomial (Fin n) ℝ)) :
    eval x (pderiv k (sqSum L)) =
      (L.map fun p => 2 * eval x p * eval x (pderiv k p)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [sqSum_cons, map_add, pderiv_pow, map_add, ih]
    simp

private theorem list_sum_eq_fin_sum {α : Type*} (L : List α) (g : α → ℝ) :
    (L.map g).sum = ∑ i : Fin L.length, g L[i] := by
  induction L with
  | nil => simp
  | cons a L ih =>
    show _ = ∑ i : Fin (L.length + 1), g (a :: L)[i]
    rw [Fin.sum_univ_succ, List.map_cons, List.sum_cons, ih]
    rfl

theorem eval_sqSum_polyDerivs (x : Fin n → ℝ) (L : List (MvPolynomial (Fin n) ℝ)) :
    eval x (sqSum (polyDerivs L)) = (L.map fun p => ∑ i, eval x (pderiv i p) ^ 2).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [polyDerivs_cons, sqSum_append, sqSum_finRange_pderiv, map_add, ih]
    simp

/-- The carré du champ of `sqSum L` is controlled by `sqSum L` and `sqSum (polyDerivs L)`. -/
theorem sum_sq_pderiv_sqSum_le (x : Fin n → ℝ) (L : List (MvPolynomial (Fin n) ℝ)) :
    ∑ k, eval x (pderiv k (sqSum L)) ^ 2 ≤
      4 * eval x (sqSum L) * eval x (sqSum (polyDerivs L)) := by
  simp_rw [eval_pderiv_sqSum, eval_sqSum_polyDerivs, eval_sqSum, list_sum_eq_fin_sum]
  have hk : ∀ k : Fin n, (∑ i : Fin L.length, 2 * eval x L[i] * eval x (pderiv k L[i])) ^ 2 ≤
      4 * (∑ i : Fin L.length, eval x L[i] ^ 2) *
        ∑ i : Fin L.length, eval x (pderiv k L[i]) ^ 2 := fun k => by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : Fin L.length => eval x L[i])
      (fun i : Fin L.length => eval x (pderiv k L[i]))
    calc (∑ i : Fin L.length, 2 * eval x L[i] * eval x (pderiv k L[i])) ^ 2
        = 4 * (∑ i : Fin L.length, eval x L[i] * eval x (pderiv k L[i])) ^ 2 := by
          rw [show (∑ i : Fin L.length, 2 * eval x L[i] * eval x (pderiv k L[i])) =
            2 * ∑ i : Fin L.length, eval x L[i] * eval x (pderiv k L[i]) by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
          ring
      _ ≤ 4 * ((∑ i : Fin L.length, eval x L[i] ^ 2) *
          ∑ i : Fin L.length, eval x (pderiv k L[i]) ^ 2) := by linarith
      _ = _ := by ring
  calc _ ≤ ∑ k : Fin n, 4 * (∑ i : Fin L.length, eval x L[i] ^ 2) *
        ∑ i : Fin L.length, eval x (pderiv k L[i]) ^ 2 := Finset.sum_le_sum fun k _ => hk k
    _ = 4 * (∑ i : Fin L.length, eval x L[i] ^ 2) *
        ∑ i : Fin L.length, ∑ k : Fin n, eval x (pderiv k L[i]) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]

theorem mem_polyDerivs {L : List (MvPolynomial (Fin n) ℝ)} {p : MvPolynomial (Fin n) ℝ} :
    p ∈ polyDerivs L ↔ ∃ q ∈ L, ∃ i, pderiv i q = p := by
  simp [polyDerivs, List.mem_flatMap]

/-- Degree bookkeeping for iterated derivatives. -/
theorem derivTower_degree {f : MvPolynomial (Fin n) ℝ} {m : ℕ} (hf : f.totalDegree ≤ m) :
    ∀ j : ℕ, ∀ p ∈ derivTower f j, p.totalDegree ≤ m - j ∧ (m < j → p = 0)
  | 0, p, hp => by
    simp only [derivTower, List.mem_singleton] at hp
    subst hp
    exact ⟨by simpa using hf, fun h => absurd h (Nat.not_lt_zero _)⟩
  | j + 1, p, hp => by
    obtain ⟨q, hq, i, rfl⟩ := mem_polyDerivs.mp hp
    obtain ⟨h1, h2⟩ := derivTower_degree hf j q hq
    refine ⟨?_, fun hlt => ?_⟩
    · have := totalDegree_pderiv_le_of_le h1 i
      omega
    · by_cases hmj : m < j
      · rw [h2 hmj, map_zero]
      · exact pderiv_eq_zero_of_totalDegree_le_zero (by omega) i

theorem totalDegree_le_of_mem_derivTower {f : MvPolynomial (Fin n) ℝ} {m : ℕ}
    (hf : f.totalDegree ≤ m) {j : ℕ} {p : MvPolynomial (Fin n) ℝ} (hp : p ∈ derivTower f j) :
    p.totalDegree ≤ m :=
  ((derivTower_degree hf j p hp).1).trans (Nat.sub_le _ _)

theorem sqSum_eq_zero_of_forall_eq_zero {L : List (MvPolynomial (Fin n) ℝ)}
    (h : ∀ p ∈ L, p = 0) : sqSum L = 0 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [sqSum_cons, h a (by simp), ih fun p hp => h p (by simp [hp])]
    simp

/-- Derivatives of order larger than the degree vanish. -/
theorem towerEnergy_eq_zero_of_lt {f : MvPolynomial (Fin n) ℝ} {m : ℕ}
    (hf : f.totalDegree ≤ m) {j : ℕ} (hj : m < j) : towerEnergy f j = 0 :=
  sqSum_eq_zero_of_forall_eq_zero fun p hp => (derivTower_degree hf j p hp).2 hj

/-- The reverse Poincaré inequality for a list of polynomials of degree at most `m`. -/
theorem gaussExp_sqSum_polyDerivs_le {m : ℕ} :
    ∀ L : List (MvPolynomial (Fin n) ℝ), (∀ p ∈ L, p.totalDegree ≤ m) →
      gaussExp (sqSum (polyDerivs L)) ≤ m * gaussExp (sqSum L)
  | [], _ => by simp [gaussExp_zero]
  | a :: L, hL => by
    have ha : a.totalDegree ≤ m := hL a (by simp)
    have ih := gaussExp_sqSum_polyDerivs_le L fun p hp => hL p (by simp [hp])
    have h1 := sum_gaussExp_sq_pderiv_le m a ha
    rw [polyDerivs_cons, sqSum_append, sqSum_finRange_pderiv, sqSum_cons, gaussExp_add,
      gaussExp_add, gaussExp_finset_sum]
    simp_rw [sq]
    nlinarith [h1, ih]

theorem gaussExp_towerEnergy_le {f : MvPolynomial (Fin n) ℝ} {m : ℕ} (hf : f.totalDegree ≤ m) :
    ∀ j : ℕ, gaussExp (towerEnergy f j) ≤ (m : ℝ) ^ j * gaussExp (f * f)
  | 0 => by simp [towerEnergy, derivTower, sq]
  | j + 1 => by
    have ih := gaussExp_towerEnergy_le hf j
    have h := gaussExp_sqSum_polyDerivs_le (m := m) (derivTower f j)
      fun p hp => totalDegree_le_of_mem_derivTower hf hp
    calc gaussExp (towerEnergy f (j + 1)) ≤ m * gaussExp (towerEnergy f j) := h
      _ ≤ m * ((m : ℝ) ^ j * gaussExp (f * f)) :=
          mul_le_mul_of_nonneg_left ih (Nat.cast_nonneg m)
      _ = (m : ℝ) ^ (j + 1) * gaussExp (f * f) := by ring

end RegularityStructures

end
