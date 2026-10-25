/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Datum.Taylor

/-!
# Coordinatewise Taylor expansion in space-time

Expanding one coordinate at a time (`x₃` first, `x₀` last) gives, for `G` smooth on `{t > 0}`,
`G(z + c) = ∑_{a ∈ [0,n)⁴} ∏ᵢ cᵢ^{aᵢ}/aᵢ! · ∂₀^{a₀} ∂₁^{a₁} ∂₂^{a₂} ∂₃^{a₃} G(z) + E`,
where `E` is a sum of four families of one-coordinate remainders (`seq_taylor`). If
`|D^k G| ≤ B k` at all points whose time coordinate lies between `z₀` and `z₀ + c₀`, then
`|E|` is bounded by the nested sum of `∏ᵢ |cᵢ|^{kᵢ} B k` over the multi-indices `k` of the
remainders (each `k` has `kᵢ = n` in the direction of the remainder, `0` before it).
-/

@[expose] public noncomputable section

namespace RegularityStructures.Datum

/-- The Taylor coefficient `c^a / a!`. -/
def taylorCoeff (c : ℝ) (a : ℕ) : ℝ := c ^ a / (a.factorial : ℝ)

end RegularityStructures.Datum

end

public section

open scoped ContDiff
open Set

namespace RegularityStructures.Datum

theorem taylorRem_add (i : Fin 4) (n : ℕ) (h : ℝ) (G : ParabolicSpace → ℝ) (z : ParabolicSpace) :
    G (z + h • stBasis i) = ∑ a ∈ Finset.range n, taylorCoeff h a * pdIter i a G z +
      taylorRem i n h G z := by
  simp [taylorRem, taylorCoeff]

theorem time_stBasis (i : Fin 4) : (stBasis i).1 = if i = 0 then 1 else 0 := by
  simp [stBasis, stOfCoords, Pi.single_apply, eq_comm]

theorem abs_taylorCoeff_le (c : ℝ) (a : ℕ) : |taylorCoeff c a| ≤ |c| ^ a := by
  unfold taylorCoeff
  rw [abs_div, abs_pow, Nat.abs_cast]
  have : (1 : ℝ) ≤ a.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero a)
  exact div_le_self (by positivity) this

theorem time_add_stBasis (z : ParabolicSpace) (i : Fin 4) (h : ℝ) :
    (z + h • stBasis i).1 = z.1 + if i = 0 then h else 0 := by
  simp only [Prod.fst_add, Prod.smul_fst, time_stBasis, smul_eq_mul]
  split_ifs <;> simp

/-- **Coordinatewise Taylor expansion.** -/
theorem seq_taylor {G : ParabolicSpace → ℝ} (hG : SmoothPos G) (z : ParabolicSpace)
    (c : Fin 4 → ℝ) (hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < z.1 + s * c 0) (n : ℕ)
    (B : (Fin 4 → ℕ) → ℝ)
    (hB : ∀ (k : Fin 4 → ℕ) (w : ParabolicSpace),
      (∃ s ∈ Icc (0 : ℝ) 1, w.1 = z.1 + s * c 0) → |D k G w| ≤ B k) :
    |G (z + stOfCoords c) - ∑ a3 ∈ Finset.range n, ∑ a2 ∈ Finset.range n,
        ∑ a1 ∈ Finset.range n, ∑ a0 ∈ Finset.range n,
          taylorCoeff (c 3) a3 * (taylorCoeff (c 2) a2 * (taylorCoeff (c 1) a1 *
            (taylorCoeff (c 0) a0 * D ![a0, a1, a2, a3] G z)))| ≤
      ∑ a3 ∈ Finset.range n, ∑ a2 ∈ Finset.range n, ∑ a1 ∈ Finset.range n,
        |c 3| ^ a3 * |c 2| ^ a2 * |c 1| ^ a1 * (B ![n, a1, a2, a3] * |c 0| ^ n) +
      ∑ a3 ∈ Finset.range n, ∑ a2 ∈ Finset.range n,
        |c 3| ^ a3 * |c 2| ^ a2 * (B ![0, n, a2, a3] * |c 1| ^ n) +
      ∑ a3 ∈ Finset.range n, |c 3| ^ a3 * (B ![0, 0, n, a3] * |c 2| ^ n) +
        B ![0, 0, 0, n] * |c 3| ^ n := by
  have hB0 : ∀ k, 0 ≤ B k := fun k =>
    (abs_nonneg _).trans (hB k z ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩)
  -- the successive points
  set p1 : ParabolicSpace := z + c 0 • stBasis 0 with hp1
  set p2 : ParabolicSpace := p1 + c 1 • stBasis 1 with hp2
  set p3 : ParabolicSpace := p2 + c 2 • stBasis 2 with hp3
  have hp4 : z + stOfCoords c = p3 + c 3 • stBasis 3 := by
    rw [stOfCoords_sum c, Fin.sum_univ_four, hp3, hp2, hp1]
    abel
  -- time coordinates of the points on the segments
  have hseg0 : ∀ s ∈ Icc (0 : ℝ) 1, 0 < (z + (s * c 0) • stBasis 0).1 := by
    intro s hs
    rw [time_add_stBasis]
    simpa using hpos s hs
  have hseg1 : ∀ s ∈ Icc (0 : ℝ) 1, 0 < (p1 + (s * c 1) • stBasis 1).1 := by
    intro s hs
    rw [time_add_stBasis, hp1, time_add_stBasis]
    simpa using hpos 1 ⟨zero_le_one, le_rfl⟩
  have hseg2 : ∀ s ∈ Icc (0 : ℝ) 1, 0 < (p2 + (s * c 2) • stBasis 2).1 := by
    intro s hs
    rw [time_add_stBasis, hp2, time_add_stBasis, hp1, time_add_stBasis]
    simpa using hpos 1 ⟨zero_le_one, le_rfl⟩
  have hseg3 : ∀ s ∈ Icc (0 : ℝ) 1, 0 < (p3 + (s * c 3) • stBasis 3).1 := by
    intro s hs
    rw [time_add_stBasis, hp3, time_add_stBasis, hp2, time_add_stBasis, hp1, time_add_stBasis]
    simpa using hpos 1 ⟨zero_le_one, le_rfl⟩
  -- the remainders
  have hT0 : ∀ a3 a2 a1 : ℕ, |taylorRem 0 n (c 0) (pdIter 1 a1 (pdIter 2 a2 (pdIter 3 a3 G))) z| ≤
      B ![n, a1, a2, a3] * |c 0| ^ n := fun a3 a2 a1 =>
    abs_taylorRem_le 0 n (((hG.pdIter 3 a3).pdIter 2 a2).pdIter 1 a1) z (c 0) _ hseg0
      (fun s hs => hB ![n, a1, a2, a3] _ ⟨s, hs, by rw [time_add_stBasis]; simp⟩)
  have hT1 : ∀ a3 a2 : ℕ, |taylorRem 1 n (c 1) (pdIter 2 a2 (pdIter 3 a3 G)) p1| ≤
      B ![0, n, a2, a3] * |c 1| ^ n := fun a3 a2 =>
    abs_taylorRem_le 1 n ((hG.pdIter 3 a3).pdIter 2 a2) p1 (c 1) _ hseg1
      (fun s hs => hB ![0, n, a2, a3] _ ⟨1, ⟨zero_le_one, le_rfl⟩, by
        rw [time_add_stBasis, hp1, time_add_stBasis]; simp⟩)
  have hT2 : ∀ a3 : ℕ, |taylorRem 2 n (c 2) (pdIter 3 a3 G) p2| ≤
      B ![0, 0, n, a3] * |c 2| ^ n := fun a3 =>
    abs_taylorRem_le 2 n (hG.pdIter 3 a3) p2 (c 2) _ hseg2
      (fun s hs => hB ![0, 0, n, a3] _ ⟨1, ⟨zero_le_one, le_rfl⟩, by
        rw [time_add_stBasis, hp2, time_add_stBasis, hp1, time_add_stBasis]; simp⟩)
  have hT3 : |taylorRem 3 n (c 3) G p3| ≤ B ![0, 0, 0, n] * |c 3| ^ n :=
    abs_taylorRem_le 3 n hG p3 (c 3) _ hseg3
      (fun s hs => hB ![0, 0, 0, n] _ ⟨1, ⟨zero_le_one, le_rfl⟩, by
        rw [time_add_stBasis, hp3, time_add_stBasis, hp2, time_add_stBasis, hp1,
          time_add_stBasis]; simp⟩)
  -- the algebraic identity
  have e3 : G (z + stOfCoords c) = ∑ a3 ∈ Finset.range n, taylorCoeff (c 3) a3 * pdIter 3 a3 G p3 +
      taylorRem 3 n (c 3) G p3 := by
    rw [hp4]
    exact taylorRem_add 3 n (c 3) G p3
  have e2 : ∀ a3, pdIter 3 a3 G p3 = ∑ a2 ∈ Finset.range n,
      taylorCoeff (c 2) a2 * pdIter 2 a2 (pdIter 3 a3 G) p2 +
        taylorRem 2 n (c 2) (pdIter 3 a3 G) p2 := fun a3 =>
    taylorRem_add 2 n (c 2) (pdIter 3 a3 G) p2
  have e1 : ∀ a3 a2, pdIter 2 a2 (pdIter 3 a3 G) p2 = ∑ a1 ∈ Finset.range n,
      taylorCoeff (c 1) a1 * pdIter 1 a1 (pdIter 2 a2 (pdIter 3 a3 G)) p1 +
        taylorRem 1 n (c 1) (pdIter 2 a2 (pdIter 3 a3 G)) p1 := fun a3 a2 =>
    taylorRem_add 1 n (c 1) (pdIter 2 a2 (pdIter 3 a3 G)) p1
  have e0 : ∀ a3 a2 a1, pdIter 1 a1 (pdIter 2 a2 (pdIter 3 a3 G)) p1 = ∑ a0 ∈ Finset.range n,
      taylorCoeff (c 0) a0 * D ![a0, a1, a2, a3] G z +
        taylorRem 0 n (c 0) (pdIter 1 a1 (pdIter 2 a2 (pdIter 3 a3 G))) z := fun a3 a2 a1 =>
    taylorRem_add 0 n (c 0) (pdIter 1 a1 (pdIter 2 a2 (pdIter 3 a3 G))) z
  have hmain : G (z + stOfCoords c) - ∑ a3 ∈ Finset.range n, ∑ a2 ∈ Finset.range n,
        ∑ a1 ∈ Finset.range n, ∑ a0 ∈ Finset.range n,
          taylorCoeff (c 3) a3 * (taylorCoeff (c 2) a2 * (taylorCoeff (c 1) a1 *
            (taylorCoeff (c 0) a0 * D ![a0, a1, a2, a3] G z))) =
      ∑ a3 ∈ Finset.range n, taylorCoeff (c 3) a3 * (∑ a2 ∈ Finset.range n, taylorCoeff (c 2) a2 *
        (∑ a1 ∈ Finset.range n, taylorCoeff (c 1) a1 *
          taylorRem 0 n (c 0) (pdIter 1 a1 (pdIter 2 a2 (pdIter 3 a3 G))) z +
          taylorRem 1 n (c 1) (pdIter 2 a2 (pdIter 3 a3 G)) p1) +
          taylorRem 2 n (c 2) (pdIter 3 a3 G) p2) + taylorRem 3 n (c 3) G p3 := by
    rw [e3]
    simp only [e2, e1, e0, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    ring
  rw [hmain]
  have b1 : ∀ a3 a2, |∑ a1 ∈ Finset.range n, taylorCoeff (c 1) a1 *
      taylorRem 0 n (c 0) (pdIter 1 a1 (pdIter 2 a2 (pdIter 3 a3 G))) z +
      taylorRem 1 n (c 1) (pdIter 2 a2 (pdIter 3 a3 G)) p1| ≤
      ∑ a1 ∈ Finset.range n, |c 1| ^ a1 * (B ![n, a1, a2, a3] * |c 0| ^ n) +
        B ![0, n, a2, a3] * |c 1| ^ n := by
    intro a3 a2
    refine (abs_add_le _ _).trans (add_le_add ?_ (hT1 a3 a2))
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a1 _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (abs_taylorCoeff_le _ _) (hT0 a3 a2 a1) (abs_nonneg _) (by positivity)
  have b2 : ∀ a3, |∑ a2 ∈ Finset.range n, taylorCoeff (c 2) a2 *
      (∑ a1 ∈ Finset.range n, taylorCoeff (c 1) a1 *
        taylorRem 0 n (c 0) (pdIter 1 a1 (pdIter 2 a2 (pdIter 3 a3 G))) z +
        taylorRem 1 n (c 1) (pdIter 2 a2 (pdIter 3 a3 G)) p1) +
        taylorRem 2 n (c 2) (pdIter 3 a3 G) p2| ≤
      ∑ a2 ∈ Finset.range n, |c 2| ^ a2 *
        (∑ a1 ∈ Finset.range n, |c 1| ^ a1 * (B ![n, a1, a2, a3] * |c 0| ^ n) +
          B ![0, n, a2, a3] * |c 1| ^ n) + B ![0, 0, n, a3] * |c 2| ^ n := by
    intro a3
    refine (abs_add_le _ _).trans (add_le_add ?_ (hT2 a3))
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a2 _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (abs_taylorCoeff_le _ _) (b1 a3 a2) (abs_nonneg _) (by positivity)
  refine le_of_le_of_eq ?_ (by simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib,
    mul_assoc] : (∑ a3 ∈ Finset.range n, |c 3| ^ a3 * (∑ a2 ∈ Finset.range n, |c 2| ^ a2 *
        (∑ a1 ∈ Finset.range n, |c 1| ^ a1 * (B ![n, a1, a2, a3] * |c 0| ^ n) +
          B ![0, n, a2, a3] * |c 1| ^ n) + B ![0, 0, n, a3] * |c 2| ^ n) +
        B ![0, 0, 0, n] * |c 3| ^ n) = _)
  refine (abs_add_le _ _).trans (add_le_add ?_ hT3)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a3 _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (abs_taylorCoeff_le _ _) (b2 a3) (abs_nonneg _) (by positivity)

end RegularityStructures.Datum

end
