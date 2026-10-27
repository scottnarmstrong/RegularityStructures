module

public import GlobalPhi43.Attachment.ProbeParabolicCalculus

/-! Product bounds localized to the actual cutoff support. Vanishing jets
outside that support are proved, not supplied as additional certificates. -/

public section

open RegularityStructures Set
open scoped ContDiff

namespace GlobalPhi43.Attachment

theorem probe_C4_product_local {f g : ParabolicSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ z ∈ tsupport g, ∀ k ≤ 4, ‖iteratedFDeriv ℝ k f z‖ ≤ A)
    (hb : ∀ k ≤ 4, ∀ z, ‖iteratedFDeriv ℝ k g z‖ ≤ B) :
    ∀ k ≤ 4, ∀ z, ‖iteratedFDeriv ℝ k (f * g) z‖ ≤ 16 * A * B := by
  intro k hk z
  by_cases hz : z ∈ tsupport g
  · change ‖iteratedFDeriv ℝ k (fun w => f w * g w) z‖ ≤ _
    refine (_root_.norm_iteratedFDeriv_mul_le (N := k)
      (hf.of_le (by exact_mod_cast le_top)) (hg.of_le (by exact_mod_cast le_top)) z
      (by exact_mod_cast le_refl k)).trans ?_
    have hs : ∀ i ∈ Finset.range (k+1),
        (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f z‖ * ‖iteratedFDeriv ℝ (k-i) g z‖ ≤
          k.choose i * (A * B) := by
      intro i hi
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (ha z hz i (hik.trans hk))
        (hb _ ((Nat.sub_le _ _).trans hk) z) (norm_nonneg _) hA) (Nat.cast_nonneg _)
    refine (Finset.sum_le_sum hs).trans ?_
    rw [← Finset.sum_mul]
    have he : ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) = 2 ^ k := by exact_mod_cast Nat.sum_range_choose k
    rw [he]
    have hp : (2 : ℝ)^k ≤ 16 :=
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk).trans_eq (by norm_num)
    exact (mul_le_mul_of_nonneg_right hp (mul_nonneg hA hB)).trans_eq (mul_assoc _ _ _).symm
  · have he : iteratedFDeriv ℝ k (f*g) z = 0 := by
      by_contra hn
      exact hz (tsupport_mul_subset_right
        (tsupport_iteratedFDeriv_subset k (subset_closure hn)))
    rw [he, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hA) hB

end GlobalPhi43.Attachment
