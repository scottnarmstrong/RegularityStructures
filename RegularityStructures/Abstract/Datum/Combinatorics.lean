/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Polynomial
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi

/-!
# Multi-index bookkeeping for the Taylor lift

* `wt k = 2 k₀ + k₁ + k₂ + k₃` is the parabolic weight of `k : Fin 4 → ℕ` (`weight_eq_wt`);
* `multiFactorial k = ∏ᵢ kᵢ!`;
* `box n` is the set of `k` with all `kᵢ < n`, and `taylorIdx n μ` its subset `wt k < μ`;
* `sum_polyIndex`: a sum over `PolyIndex N` is a sum over `taylorIdx N N`;
* `sum_nested_four`: the nested range sums of `seq_taylor` are sums over `box n`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Datum

/-- The parabolic weight `2 k₀ + k₁ + k₂ + k₃` of a multi-index `k : Fin 4 → ℕ`. -/
def wt (k : Fin 4 → ℕ) : ℕ := 2 * k 0 + k 1 + k 2 + k 3

/-- `k! = ∏ᵢ kᵢ!`. -/
def multiFactorial (k : Fin 4 → ℕ) : ℝ := ∏ i, ((k i).factorial : ℝ)

/-- The multi-indices `k : Fin 4 → ℕ` with all `kᵢ < n`. -/
def box (n : ℕ) : Finset (Fin 4 → ℕ) := Fintype.piFinset fun _ => Finset.range n

/-- The multi-indices of `box n` with `wt k < μ`. -/
def taylorIdx (n : ℕ) (μ : ℝ) : Finset (Fin 4 → ℕ) :=
  (box n).filter fun k => (wt k : ℝ) < μ

end RegularityStructures.Datum

end

public section

namespace RegularityStructures.Datum

theorem mem_box {n : ℕ} {k : Fin 4 → ℕ} : k ∈ box n ↔ ∀ i, k i < n := by
  simp [box, Fintype.mem_piFinset]

theorem mem_taylorIdx {n : ℕ} {μ : ℝ} {k : Fin 4 → ℕ} :
    k ∈ taylorIdx n μ ↔ (∀ i, k i < n) ∧ (wt k : ℝ) < μ := by
  simp [taylorIdx, mem_box]

theorem weight_eq_wt (k : Fin 4 →₀ ℕ) : Finsupp.weight parabolicWeight k = wt ⇑k := by
  rw [weight_parabolicWeight]
  rfl

theorem polyDeg_eq_wt {N : ℕ} (k : PolyIndex N) : polyDeg N k = (wt ⇑k.1 : ℝ) := by
  simp [polyDeg, weight_eq_wt]

theorem wt_add (k l : Fin 4 → ℕ) : wt (k + l) = wt k + wt l := by
  simp only [wt, Pi.add_apply]
  ring

theorem coord_le_wt (k : Fin 4 → ℕ) (i : Fin 4) : k i ≤ wt k := by
  unfold wt
  fin_cases i <;> simp <;> omega

theorem multiFactorial_pos (k : Fin 4 → ℕ) : 0 < multiFactorial k :=
  Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos _

theorem one_le_multiFactorial (k : Fin 4 → ℕ) : 1 ≤ multiFactorial k :=
  Finset.one_le_prod₀ fun i _ => by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)

/-- A sum over the basis `PolyIndex N` is a sum over the multi-indices of weight `< N`. -/
theorem sum_polyIndex {N : ℕ} (g : (Fin 4 → ℕ) → ℝ) :
    ∑ k : PolyIndex N, g ⇑k.1 = ∑ a ∈ taylorIdx N N, g a := by
  have hinj : Function.Injective fun k : PolyIndex N => (⇑k.1 : Fin 4 → ℕ) := fun a b h =>
    Subtype.ext (Finsupp.ext fun i => congrFun h i)
  rw [← Finset.sum_image (f := g) (s := (Finset.univ : Finset (PolyIndex N)))
    (g := fun k : PolyIndex N => (⇑k.1 : Fin 4 → ℕ)) (fun a _ b _ h => hinj h)]
  congr 1
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and, mem_taylorIdx]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨fun i => coord_lt_of_weight_lt k.2 i, ?_⟩
    have := k.2
    rw [weight_eq_wt] at this
    exact_mod_cast this
  · rintro ⟨ha, hw⟩
    refine ⟨⟨Finsupp.equivFunOnFinite.symm a, ?_⟩, rfl⟩
    rw [weight_eq_wt]
    exact_mod_cast hw

/-- The nested range sums over `(a₀, a₁, a₂, a₃)` are a sum over `box n`. -/
theorem sum_nested_four (n : ℕ) (f : (Fin 4 → ℕ) → ℝ) :
    ∑ a3 ∈ Finset.range n, ∑ a2 ∈ Finset.range n, ∑ a1 ∈ Finset.range n,
      ∑ a0 ∈ Finset.range n, f ![a0, a1, a2, a3] = ∑ a ∈ box n, f a := by
  have h : ∑ a3 ∈ Finset.range n, ∑ a2 ∈ Finset.range n, ∑ a1 ∈ Finset.range n,
      ∑ a0 ∈ Finset.range n, f ![a0, a1, a2, a3] =
      ∑ p ∈ Finset.range n ×ˢ (Finset.range n ×ˢ (Finset.range n ×ˢ Finset.range n)),
        f ![p.2.2.2, p.2.2.1, p.2.1, p.1] := by
    simp only [Finset.sum_product]
  rw [h]
  refine Finset.sum_nbij' (fun p => ![p.2.2.2, p.2.2.1, p.2.1, p.1])
    (fun a => (a 3, a 2, a 1, a 0)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    rw [mem_box]
    intro i
    fin_cases i <;> simp [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]
  · intro a ha
    rw [mem_box] at ha
    simp [ha]
  · intro p _
    rfl
  · intro a _
    ext i
    fin_cases i <;> rfl
  · intro p _
    rfl

theorem choose_div_factorial (l m : ℕ) :
    (((l + m).choose l : ℕ) : ℝ) / ((l + m).factorial : ℝ) =
      1 / ((l.factorial : ℝ) * (m.factorial : ℝ)) := by
  have h := Nat.add_choose_mul_factorial_mul_factorial l m
  rw [Nat.choose_symm_add]
  have h' : (((l + m).choose m : ℕ) : ℝ) * (l.factorial : ℝ) * (m.factorial : ℝ) =
      ((l + m).factorial : ℝ) := by exact_mod_cast h
  have hl : (l.factorial : ℝ) ≠ 0 := by positivity
  have hm : (m.factorial : ℝ) ≠ 0 := by positivity
  have hlm : ((l + m).factorial : ℝ) ≠ 0 := by positivity
  rw [div_eq_div_iff hlm (mul_ne_zero hl hm)]
  rw [← h']
  ring

end RegularityStructures.Datum

end
