module

public import GlobalPhi43.MW20.ParentScaleAlgebra

/-! Parent-amplitude control of affine remainders beyond the testing radius. -/

public section

namespace GlobalPhi43.MW20

/-- Beyond radius d, a nonnegative weighted monomial loses no more than
its d-scale value whenever its exponent is at most gamma. -/
theorem far_weighted_monomial {d p γ a B : ℝ} (hd : 0 < d) (hdp : d ≤ p)
    (ha : a ≤ γ) (hB : 0 ≤ B) :
    (d ^ γ / p ^ γ) * (B * p ^ a) ≤ B * d ^ a := by
  have hp : 0 < p := hd.trans_le hdp
  have hm := Real.rpow_le_rpow hd.le hdp (sub_nonneg.mpr ha)
  have hq : d ^ (γ - a) / p ^ (γ - a) ≤ 1 :=
    (div_le_one (Real.rpow_pos_of_pos hp _)).2 hm
  have hed : d ^ γ = d ^ a * d ^ (γ - a) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  have hep : p ^ a / p ^ γ = (p ^ (γ - a))⁻¹ := by
    rw [← Real.rpow_sub hp, show a - γ = -(γ - a) by ring, Real.rpow_neg hp.le]
  calc
    _ = B * d ^ γ * (p ^ a / p ^ γ) := by ring
    _ = B * d ^ a * (d ^ (γ - a) / p ^ (γ - a)) := by rw [hed, hep]; ring
    _ ≤ B * d ^ a * 1 := mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := mul_one _

/-- The complete far source envelope has only parent-amplitude and weighted
coefficient costs. Neither a child amplitude nor a full affine norm is assumed. -/
theorem far_affine_parent_envelope {d p α β γ M N c E : ℝ}
    (hd : 0 < d) (hdp : d ≤ p) (hM : 0 < M) (hN : 0 ≤ N)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαγ : α ≤ γ) (hβγ : β ≤ γ) (hγ : 1 ≤ γ)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hscale : d * M ≤ 1)
    (he : E ≤ 2 * M + c * M ^ (1 + α) * p ^ α +
      3 * c * M ^ (1 + β) * p ^ β + 3 * N * p) :
    (d ^ γ / p ^ γ) * E ≤ 6 * M + 3 * d * N := by
  have h₀ := far_weighted_monomial hd hdp (show (0 : ℝ) ≤ γ by linarith)
    (by positivity : 0 ≤ 2 * M)
  have h₁ := far_weighted_monomial hd hdp hαγ
    (by positivity : 0 ≤ c * M ^ (1 + α))
  have h₂ := far_weighted_monomial hd hdp hβγ
    (by positivity : 0 ≤ 3 * c * M ^ (1 + β))
  have h₃ := far_weighted_monomial hd hdp hγ (by positivity : 0 ≤ 3 * N)
  simp only [Real.rpow_zero, mul_one] at h₀
  simp only [Real.rpow_one] at h₃
  have hαw := parent_tree_weight hd hM hc hc1 hα hscale
  have hβw := parent_tree_weight hd hM hc hc1 hβ hscale
  have hw := mul_le_mul_of_nonneg_left he
    (div_nonneg (Real.rpow_nonneg hd.le γ) (Real.rpow_nonneg (hd.trans_le hdp).le γ))
  nlinarith only [h₀, h₁, h₂, h₃, hαw, hβw, hw]

end GlobalPhi43.MW20
