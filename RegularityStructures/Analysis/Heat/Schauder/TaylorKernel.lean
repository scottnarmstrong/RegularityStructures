/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorWord
public import RegularityStructures.Analysis.Parabolic.Polynomial
public import RegularityStructures.Analysis.Heat.Schauder.TaylorTy

/-!
# The Taylor-remainder kernel `K^α_{n;xy}`

`taylorIdx σ = {k : |k|_𝔰 < σ}` (a finite set) and

  `taylorKernel h n σ x y (w) = g(y - w) - ∑_{k ∈ taylorIdx σ} (y - x)^k/k! · D^k g(x - w)`,
  `g = scaledShell h n`,

is Hairer's `K^α_{n;xy}` [Hai14, (5.14)] with `σ = α + β`.  We show it is the profile
`H(u) = g(u + (y - x)) - ∑ c_k D^k g(u)` evaluated at `x - w`, and that
`H = (remJ …)(−u) + ∑_{k ∈ box, |k|_𝔰 ≥ σ} c_k D^k g` (`taylorProfile_eq`), where `remJ` is the
box Taylor remainder of `TaylorBox.lean`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The multi-indices `k` with `|k|_𝔰 < σ`, as a finite set. -/
def taylorIdx (σ : ℝ) : Finset (Fin 4 →₀ ℕ) :=
  (boxSet (fun _ => ⌈σ⌉₊) (List.finRange 4)).filter fun k => (multiDeg k : ℝ) < σ

/-- The multi-indices of the box not in `taylorIdx σ`. -/
def taylorOut (σ : ℝ) : Finset (Fin 4 →₀ ℕ) :=
  (boxSet (fun _ => ⌈σ⌉₊) (List.finRange 4)).filter fun k => ¬ (multiDeg k : ℝ) < σ

/-- `k! = ∏ᵢ kᵢ!`. -/
def multiFact (k : Fin 4 →₀ ℕ) : ℝ := ∏ i, ((Nat.factorial (k i) : ℕ) : ℝ)

/-- `K^α_{n;xy}(w) = K_n(y - w) - ∑_{|k|_𝔰 < σ} (y - x)^k/k! D^k K_n(x - w)`, `K_n = scaledShell h n`. -/
def taylorKernel (h : ParabolicSpace → ℝ) (n : ℕ) (σ : ℝ) (x y : ParabolicSpace)
    (w : ParabolicSpace) : ℝ :=
  scaledShell h n (y - w) - ∑ k ∈ taylorIdx σ,
    (evalParabolic (MvPolynomial.monomial k 1) (y - x) / multiFact k) *
      lineIter (multiDirs k) (scaledShell h n) (x - w)

/-- The profile `u ↦ g(u + z) - ∑ c_k D^k g(u)` with `z = y - x`. -/
def taylorProfile (g : ParabolicSpace → ℝ) (σ : ℝ) (z : ParabolicSpace) (u : ParabolicSpace) : ℝ :=
  g (u + z) - ∑ k ∈ taylorIdx σ,
    (evalParabolic (MvPolynomial.monomial k 1) z / multiFact k) * lineIter (multiDirs k) g u

end RegularityStructures

end

public section

open scoped ContDiff

namespace RegularityStructures

theorem taylorKernel_eq_profile (h : ParabolicSpace → ℝ) (n : ℕ) (σ : ℝ) (x y w : ParabolicSpace) :
    taylorKernel h n σ x y w = taylorProfile (scaledShell h n) σ (y - x) (x - w) := by
  unfold taylorKernel taylorProfile
  rw [show x - w + (y - x) = y - w by abel]

theorem mem_taylorIdx_iff {σ : ℝ} (k : Fin 4 →₀ ℕ) :
    k ∈ taylorIdx σ ↔ (multiDeg k : ℝ) < σ := by
  unfold taylorIdx
  rw [Finset.mem_filter, mem_boxSet_iff _ _ (List.nodup_finRange 4)]
  refine ⟨fun h => h.2, fun h => ⟨⟨fun i hi => absurd (List.mem_finRange i) hi, fun i _ => ?_⟩, h⟩⟩
  have h1 : k i ≤ multiDeg k := by
    have : k i * parabolicWeight i ≤ multiDeg k := by
      unfold multiDeg
      rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
      exact Finset.single_le_sum (f := fun j => k j • parabolicWeight j)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hw : 1 ≤ parabolicWeight i := by fin_cases i <;> simp [parabolicWeight]
    nlinarith
  have h2 : (k i : ℝ) < σ := lt_of_le_of_lt (by exact_mod_cast h1) h
  have h3 : (k i : ℝ) ≤ ⌈σ⌉₊ := h2.le.trans (Nat.le_ceil σ)
  exact_mod_cast h3

theorem evalParabolic_monomial_div (k : Fin 4 →₀ ℕ) (z : ParabolicSpace) :
    evalParabolic (MvPolynomial.monomial k 1) z / multiFact k = coeffT (parabolicCoords z) k := by
  unfold evalParabolic coeffT multiFact
  rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod_fintype _ _ (by simp),
    Finset.prod_div_distrib]

theorem disp_finRange (z : ParabolicSpace) :
    disp (fun i => -parabolicCoords z i) (List.finRange 4) = -z := by
  unfold disp
  rw [← Fin.sum_univ_def, Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, coordDir_zero, coordDir_succ,
    Fin.succ_zero_eq_one]
  ext
  · simp [parabolicCoords, timeDir, spaceDir]
  · rename_i i
    fin_cases i <;> simp [parabolicCoords, timeDir, spaceDir]

theorem lineIter_reflect {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g) (L : List ParabolicSpace) :
    lineIter L (fun w => g (-w)) = fun w => (-1 : ℝ) ^ L.length * lineIter L g (-w) := by
  have h1 := lineIter_comp_clm hg (-ContinuousLinearMap.id ℝ ParabolicSpace) L
  have e : (g ∘ ⇑(-ContinuousLinearMap.id ℝ ParabolicSpace)) = fun w => g (-w) := by
    funext w; simp
  have e2 : L.map ⇑(-ContinuousLinearMap.id ℝ ParabolicSpace) = L.map Neg.neg := by
    refine List.map_congr_left fun d _ => ?_
    simp
  rw [e, e2, lineIter_map_neg hg] at h1
  rw [h1]
  funext w
  simp

theorem length_multiDirs (k : Fin 4 →₀ ℕ) : (multiDirs k).length = ∑ i, k i := by
  unfold multiDirs
  rw [List.length_map, Multiset.length_toList, Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (by simp)]
  rfl

theorem coeffT_neg (s : Fin 4 → ℝ) (k : Fin 4 →₀ ℕ) :
    coeffT (fun i => -s i) k = (-1 : ℝ) ^ (∑ i, k i) * coeffT s k := by
  unfold coeffT
  have : ∀ i, (-s i) ^ k i / ((Nat.factorial (k i) : ℕ) : ℝ) =
      (-1) ^ k i * (s i ^ k i / ((Nat.factorial (k i) : ℕ) : ℝ)) := fun i => by
    rw [neg_eq_neg_one_mul, mul_pow]; ring
  simp only [this, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

theorem taylorProfile_eq {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g) (σ : ℝ)
    (z u : ParabolicSpace) :
    taylorProfile g σ z u =
      remJ (fun i => -parabolicCoords z i) (fun _ => ⌈σ⌉₊) (List.finRange 4)
        (fun w => g (-w)) (-u) +
      ∑ k ∈ taylorOut σ, coeffT (parabolicCoords z) k * lineIter (multiDirs k) g u := by
  have hφ : ContDiff ℝ ∞ fun w => g (-w) := hg.comp contDiff_neg
  have hty := tyOp_eq_sum (fun i => -parabolicCoords z i) (fun _ => ⌈σ⌉₊) (List.finRange 4)
    (List.nodup_finRange 4) hφ (-u)
  have hterm : ∀ k : Fin 4 →₀ ℕ,
      coeffT (fun i => -parabolicCoords z i) k * lineIter (multiDirs k) (fun w => g (-w)) (-u) =
        coeffT (parabolicCoords z) k * lineIter (multiDirs k) g u := by
    intro k
    rw [lineIter_reflect hg, coeffT_neg, length_multiDirs]
    simp only [neg_neg]
    have : ((-1 : ℝ) ^ ∑ i, k i) * ((-1 : ℝ) ^ ∑ i, k i) = 1 := by
      rw [← mul_pow]; simp
    calc _ = (((-1 : ℝ) ^ ∑ i, k i) * ((-1 : ℝ) ^ ∑ i, k i)) * (coeffT (parabolicCoords z) k *
        lineIter (multiDirs k) g u) := by ring
      _ = _ := by rw [this, one_mul]
  have hbox : ∑ k ∈ boxSet (fun _ => ⌈σ⌉₊) (List.finRange 4),
      coeffT (parabolicCoords z) k * lineIter (multiDirs k) g u =
      (∑ k ∈ taylorIdx σ, coeffT (parabolicCoords z) k * lineIter (multiDirs k) g u) +
        ∑ k ∈ taylorOut σ, coeffT (parabolicCoords z) k * lineIter (multiDirs k) g u := by
    unfold taylorIdx taylorOut
    rw [Finset.sum_filter_add_sum_filter_not]
  unfold remJ taylorProfile
  rw [hty, disp_finRange]
  simp only [hterm]
  rw [hbox]
  simp only [evalParabolic_monomial_div, neg_neg, show -u + -z = -(u + z) from by abel]
  ring

end RegularityStructures

end
