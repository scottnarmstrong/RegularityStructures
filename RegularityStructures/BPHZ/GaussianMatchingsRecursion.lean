/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianMatchings
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Basic

/-!
# The pairing recursion for matchings

If `a` is the minimum of `s`, every perfect matching of `s` pairs `a` with some `b ∈ s \ {a}` and
restricts to a perfect matching of `s \ {a, b}`.  Hence
`matchingSum W s = ∑_{b ∈ s \ {a}} W a b * matchingSum W (s \ {a, b})`
(`matchingSum_eq_sum_erase`).  The bijection is `link a b` (add the pair `{a, b}`) with inverse
`unlink a` (remove the pair containing `a`).
-/

public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Add the pair `{a, b}` to the matching `π`. -/
private def link (a b : ι) (π : ι → ι) (c : ι) : ι :=
  if c = a then b else if c = b then a else π c

/-- Remove the pair containing `a` from the matching `π`. -/
private def unlink (a : ι) (π : ι → ι) (c : ι) : ι :=
  if c = a ∨ c = π a then c else π c

private theorem apply_ne_of_mem {s : Finset ι} {π : ι → ι} (hπ : π ∈ partialMatchings s)
    {a b : ι} (ha : a ∉ s) (hb : b ∉ s) {c : ι} (hca : c ≠ a) (hcb : c ≠ b) :
    π c ≠ a ∧ π c ≠ b := by
  rw [mem_partialMatchings] at hπ
  have hπa : π a = a := by simpa [ha] using (hπ.2 a).not.mpr
  have hπb : π b = b := by simpa [hb] using (hπ.2 b).not.mpr
  constructor
  · intro h
    apply hca
    rw [← hπ.1 c, h, hπa]
  · intro h
    apply hcb
    rw [← hπ.1 c, h, hπb]

private theorem link_mem {s : Finset ι} {π : ι → ι} {a b : ι} (hab : a ≠ b) (ha : a ∈ s)
    (hb : b ∈ s) (hπ : π ∈ partialMatchings ((s.erase a).erase b)) :
    link a b π ∈ partialMatchings s := by
  have hna : a ∉ (s.erase a).erase b := by simp
  have hnb : b ∉ (s.erase a).erase b := by simp
  have hπ' := hπ
  rw [mem_partialMatchings] at hπ' ⊢
  refine ⟨fun c => ?_, fun c => ?_⟩
  · by_cases hca : c = a
    · subst hca
      simp [link, hab.symm]
    by_cases hcb : c = b
    · subst hcb
      simp [link, hab.symm]
    obtain ⟨h1, h2⟩ := apply_ne_of_mem hπ hna hnb hca hcb
    simp [link, hca, hcb, h1, h2, hπ'.1 c]
  · by_cases hca : c = a
    · subst hca
      simp [link, hab.symm, ha]
    by_cases hcb : c = b
    · subst hcb
      simp [link, hab, hab.symm, hb]
    simp [link, hca, hcb, hπ'.2 c]

private theorem unlink_mem {s : Finset ι} {π : ι → ι} {a : ι} (ha : a ∈ s)
    (hπ : π ∈ partialMatchings s) :
    unlink a π ∈ partialMatchings ((s.erase a).erase (π a)) := by
  have hπ' := hπ
  rw [mem_partialMatchings] at hπ' ⊢
  have hπa : π a ≠ a := (hπ'.2 a).2 ha
  have hb : π a ∈ s := (hπ'.2 (π a)).1 (by rw [hπ'.1 a]; exact hπa.symm)
  refine ⟨fun c => ?_, fun c => ?_⟩
  · by_cases hc : c = a ∨ c = π a
    · simp [unlink, hc]
    push Not at hc
    have h1 : π c ≠ a := fun h => hc.2 (by rw [← hπ'.1 c, h])
    have h2 : π c ≠ π a := fun h => hc.1 (by simpa using hπ'.1 |>.injective h)
    simp [unlink, hc.1, hc.2, h1, h2, hπ'.1 c]
  · by_cases hc : c = a ∨ c = π a
    · rcases hc with rfl | rfl <;> simp [unlink, hπa, hπa.symm]
    push Not at hc
    have h1 : π c ≠ a := fun h => hc.2 (by rw [← hπ'.1 c, h])
    have h2 : π c ≠ π a := fun h => hc.1 (hπ'.1.injective h)
    simp [unlink, hc.1, hc.2, hπ'.2 c]

private theorem unlink_link {s : Finset ι} {π : ι → ι} {a b : ι} (hab : a ≠ b)
    (hπ : π ∈ partialMatchings ((s.erase a).erase b)) : unlink a (link a b π) = π := by
  have hna : a ∉ (s.erase a).erase b := by simp
  have hnb : b ∉ (s.erase a).erase b := by simp
  have hπ' := hπ
  rw [mem_partialMatchings] at hπ'
  have hπa : π a = a := by simpa [hna] using (hπ'.2 a).not.mpr
  have hπb : π b = b := by simpa [hnb] using (hπ'.2 b).not.mpr
  funext c
  by_cases hca : c = a
  · subst hca; simp [unlink, link, hπa]
  by_cases hcb : c = b
  · subst hcb; simp [unlink, link, hπb, hab.symm]
  simp [unlink, link, hca, hcb]

private theorem link_unlink {s : Finset ι} {π : ι → ι} {a : ι} (ha : a ∈ s)
    (hπ : π ∈ partialMatchings s) : link a (π a) (unlink a π) = π := by
  have hπ' := hπ
  rw [mem_partialMatchings] at hπ'
  have hπa : π a ≠ a := (hπ'.2 a).2 ha
  funext c
  by_cases hca : c = a
  · subst hca; simp [link]
  by_cases hcb : c = π a
  · subst hcb; simp [link, hπa, hπ'.1 a]
  simp [link, unlink, hca, hcb]

variable [LinearOrder ι]

private theorem matchingWeight_link {s : Finset ι} {π : ι → ι} {a b : ι} (hab : a < b)
    (hπ : π ∈ partialMatchings ((s.erase a).erase b)) (W : ι → ι → ℝ) :
    matchingWeight W (link a b π) = W a b * matchingWeight W π := by
  have hna : a ∉ (s.erase a).erase b := by simp
  have hnb : b ∉ (s.erase a).erase b := by simp
  have hπ' := hπ
  rw [mem_partialMatchings] at hπ'
  have hπa : π a = a := by simpa [hna] using (hπ'.2 a).not.mpr
  have hπb : π b = b := by simpa [hnb] using (hπ'.2 b).not.mpr
  have hset : ∀ (i1 : DecidablePred fun c => c < link a b π c)
      (i2 : DecidablePred fun c => c < π c),
      (@Finset.filter _ (fun c => c < link a b π c) i1 Finset.univ) =
      insert a (@Finset.filter _ (fun c => c < π c) i2 Finset.univ) := by
    intro i1 i2
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hca : c = a
    · subst hca; simp [link, hab]
    by_cases hcb : c = b
    · subst hcb; simp [link, hab.ne', hab.not_gt, hπb]
    simp [link, hca, hcb]
  have hnotin : ∀ i2 : DecidablePred fun c => c < π c,
      a ∉ @Finset.filter _ (fun c => c < π c) i2 Finset.univ := by simp [hπa]
  unfold matchingWeight
  rw [hset, Finset.prod_insert (hnotin _)]
  have h1 : link a b π a = b := by simp [link]
  rw [h1]
  congr 1
  refine Finset.prod_congr rfl fun c hc => ?_
  have hc' : c ≠ a := fun h => hnotin _ (h ▸ hc)
  have hcb : c ≠ b := by
    rintro rfl
    simp [hπb] at hc
  simp [link, hc', hcb]

/-- **Pairing recursion.** If `a` is the least element of `s`, then
`matchingSum W s = ∑_{b ∈ s \ {a}} W a b * matchingSum W (s \ {a, b})`. -/
theorem matchingSum_eq_sum_erase (W : ι → ι → ℝ) {s : Finset ι} {a : ι} (ha : a ∈ s)
    (hmin : ∀ b ∈ s, a ≤ b) :
    matchingSum W s =
      ∑ b ∈ s.erase a, W a b * matchingSum W ((s.erase a).erase b) := by
  unfold matchingSum
  rw [← Finset.sum_fiberwise_of_maps_to (s := partialMatchings s) (t := s.erase a)
    (g := fun π => π a)]
  · refine Finset.sum_congr rfl fun b hb => ?_
    have hba : b ≠ a := Finset.ne_of_mem_erase hb
    have hbs : b ∈ s := Finset.mem_of_mem_erase hb
    have hab : a < b := lt_of_le_of_ne (hmin b hbs) hba.symm
    rw [Finset.mul_sum]
    refine Finset.sum_bij' (fun π _ => unlink a π) (fun π _ => link a b π) ?_ ?_ ?_ ?_ ?_
    · intro π hπ
      rw [Finset.mem_filter] at hπ
      have := unlink_mem ha hπ.1
      rwa [hπ.2] at this
    · intro π hπ
      have := link_mem hab.ne ha hbs hπ
      refine Finset.mem_filter.2 ⟨this, ?_⟩
      simp [link]
    · intro π hπ
      rw [Finset.mem_filter] at hπ
      have := link_unlink ha hπ.1
      rwa [hπ.2] at this
    · intro π hπ
      exact unlink_link hab.ne hπ
    · intro π hπ
      rw [Finset.mem_filter] at hπ
      have := unlink_mem ha hπ.1
      rw [hπ.2] at this
      have h2 := matchingWeight_link hab this W
      rw [← hπ.2] at h2 ⊢
      rw [link_unlink ha hπ.1] at h2
      rw [h2, hπ.2]
  · intro π hπ
    rw [mem_partialMatchings] at hπ
    have hπa : π a ≠ a := (hπ.2 a).2 ha
    refine Finset.mem_erase.2 ⟨hπa, (hπ.2 (π a)).1 ?_⟩
    rw [hπ.1 a]
    exact hπa.symm

end RegularityStructures

end
