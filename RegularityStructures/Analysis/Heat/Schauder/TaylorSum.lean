/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorTy

/-!
# The iterated Taylor polynomial as a sum over a box of multi-indices

`tyOp s m J φ (w) = ∑_{k ∈ boxSet m J} coeffT s k · D^k φ (w)` for `J` without repetitions, where
`boxSet m J = {k : supp k ⊆ J, k_i ≤ m_i}` and `coeffT s k = ∏_i s_i^{k_i}/k_i!`
(`tyOp_eq_sum`).  Here `D^k = lineIter (multiDirs k)`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The Taylor coefficient `∏ᵢ sᵢ^{kᵢ} / kᵢ!` of the multi-index `k`. -/
def coeffT (s : Fin 4 → ℝ) (k : Fin 4 →₀ ℕ) : ℝ :=
  ∏ i, s i ^ k i / ((Nat.factorial (k i) : ℕ) : ℝ)

/-- The box of multi-indices supported on `J` with `kᵢ ≤ mᵢ`, built recursively. -/
def boxSet (m : Fin 4 → ℕ) : List (Fin 4) → Finset (Fin 4 →₀ ℕ)
  | [] => {0}
  | j :: J => ((boxSet m J) ×ˢ (Finset.range (m j + 1))).image
      (fun q => q.1 + Finsupp.single j q.2)

end RegularityStructures

end

public section

open scoped ContDiff

namespace RegularityStructures

theorem mem_boxSet_iff (m : Fin 4 → ℕ) : ∀ (J : List (Fin 4)), J.Nodup → ∀ k : Fin 4 →₀ ℕ,
    k ∈ boxSet m J ↔ (∀ i, i ∉ J → k i = 0) ∧ ∀ i ∈ J, k i ≤ m i
  | [], _, k => by
    simp only [boxSet, Finset.mem_singleton, List.not_mem_nil, false_imp_iff, implies_true,
      and_true, not_false_eq_true, forall_const]
    constructor
    · rintro rfl; intro i; rfl
    · intro h; ext i; exact h i
  | j :: J, hJ, k => by
    have hj : j ∉ J := (List.nodup_cons.1 hJ).1
    have hJ' := (List.nodup_cons.1 hJ).2
    simp only [boxSet, Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists]
    constructor
    · rintro ⟨k', p, ⟨hk', hp⟩, rfl⟩
      have hk := (mem_boxSet_iff m J hJ' k').1 hk'
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · have hij : i ≠ j := fun h => hi (h ▸ List.mem_cons_self ..)
        have hiJ : i ∉ J := fun h => hi (List.mem_cons_of_mem _ h)
        simp [hk.1 i hiJ, Ne.symm hij]
      · rcases List.mem_cons.1 hi with rfl | hiJ
        · simp [hk.1 i hj]; omega
        · have hij : i ≠ j := fun h => hj (h ▸ hiJ)
          simpa [Finsupp.single_apply, Ne.symm hij] using hk.2 i hiJ
    · rintro ⟨h0, hle⟩
      refine ⟨Finsupp.erase j k, k j, ⟨?_, ?_⟩, ?_⟩
      · rw [mem_boxSet_iff m J hJ']
        refine ⟨fun i hi => ?_, fun i hi => ?_⟩
        · by_cases hij : i = j
          · subst hij; simp
          · rw [Finsupp.erase_ne hij]; exact h0 i (by simp [hij, hi])
        · have hij : i ≠ j := fun h => hj (h ▸ hi)
          rw [Finsupp.erase_ne hij]; exact hle i (List.mem_cons_of_mem _ hi)
      · have := hle j (List.mem_cons_self ..); omega
      · exact Finsupp.erase_add_single j k

theorem coe_multiDirs (k : Fin 4 →₀ ℕ) :
    (↑(multiDirs k) : Multiset ParabolicSpace) = (Finsupp.toMultiset k).map coordDir := by
  rw [multiDirs, ← Multiset.map_coe, Multiset.coe_toList]

theorem multiDirs_add_single_perm (k : Fin 4 →₀ ℕ) (j : Fin 4) (p : ℕ) :
    (multiDirs (k + Finsupp.single j p)).Perm (List.replicate p (coordDir j) ++ multiDirs k) := by
  rw [← Multiset.coe_eq_coe, coe_multiDirs, ← Multiset.coe_add, coe_multiDirs,
    Finsupp.toMultiset_add, Finsupp.toMultiset_single, Multiset.map_add, Multiset.map_nsmul,
    Multiset.map_singleton, Multiset.coe_replicate, ← Multiset.nsmul_singleton, add_comm]

theorem lineIter_multiDirs_add_single {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (k : Fin 4 →₀ ℕ) (j : Fin 4) (p : ℕ) :
    lineIter (multiDirs (k + Finsupp.single j p)) φ =
      (dirDeriv (coordDir j))^[p] (lineIter (multiDirs k) φ) := by
  rw [lineIter_perm hφ (multiDirs_add_single_perm k j p), lineIter_append, lineIter_replicate]

theorem coeffT_add_single (s : Fin 4 → ℝ) (k : Fin 4 →₀ ℕ) (j : Fin 4) (p : ℕ) (hk : k j = 0) :
    coeffT s (k + Finsupp.single j p) =
      coeffT s k * (s j ^ p / ((Nat.factorial p : ℕ) : ℝ)) := by
  unfold coeffT
  have : ∀ i : Fin 4, s i ^ (k + Finsupp.single j p) i /
      ((Nat.factorial ((k + Finsupp.single j p) i) : ℕ) : ℝ) =
      (s i ^ k i / ((Nat.factorial (k i) : ℕ) : ℝ)) *
        (if i = j then s j ^ p / ((Nat.factorial p : ℕ) : ℝ) else 1) := by
    intro i
    by_cases hij : i = j
    · subst hij; simp [hk]
    · simp [hij]
  simp only [this, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]

theorem tyOp_eq_sum (s : Fin 4 → ℝ) (m : Fin 4 → ℕ) : ∀ (J : List (Fin 4)), J.Nodup →
    ∀ {φ : ParabolicSpace → ℝ}, ContDiff ℝ ∞ φ → ∀ w,
      tyOp s m J φ w = ∑ k ∈ boxSet m J, coeffT s k * lineIter (multiDirs k) φ w
  | [], _, φ, _, w => by simp [tyOp, boxSet, coeffT, multiDirs]
  | j :: J, hJ, φ, hφ, w => by
    have hj : j ∉ J := (List.nodup_cons.1 hJ).1
    have hJ' := (List.nodup_cons.1 hJ).2
    simp only [tyOp]
    rw [tyOp_eq_sum s m J hJ' (contDiff_tayOp hφ _ _ _) w]
    have hinj : Set.InjOn (fun q : (Fin 4 →₀ ℕ) × ℕ => q.1 + Finsupp.single j q.2)
        ((boxSet m J ×ˢ Finset.range (m j + 1) : Finset _) : Set _) := by
      rintro ⟨k, p⟩ hq ⟨k', p'⟩ hq' h
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hq hq'
      have h0 := ((mem_boxSet_iff m J hJ' k).1 hq.1).1 j hj
      have h0' := ((mem_boxSet_iff m J hJ' k').1 hq'.1).1 j hj
      simp only at h
      have hp : p = p' := by
        have := congrArg (fun f => f j) h
        simpa [h0, h0'] using this
      subst hp
      simp only [Prod.mk.injEq, and_true]
      exact add_right_cancel h
    simp only [boxSet]
    rw [Finset.sum_image hinj, Finset.sum_product]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 := ((mem_boxSet_iff m J hJ' k).1 hk).1 j hj
    have e : lineIter (multiDirs k) (tayOp (coordDir j) (s j) (m j) φ) w =
        ∑ p ∈ Finset.range (m j + 1), (((Nat.factorial p : ℕ) : ℝ)⁻¹ * s j ^ p) *
          lineIter (multiDirs (k + Finsupp.single j p)) φ w := by
      rw [lineIter_tayOp hφ, tayOp_eq]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [lineIter_multiDirs_add_single hφ]
    rw [e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [coeffT_add_single s k j p hk0]
    ring

end RegularityStructures

end
