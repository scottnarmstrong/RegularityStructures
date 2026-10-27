module

public import GlobalPhi43.MW20.ParentCoefficientWeight

/-! Reciprocal-scale control of weighted source monomials. -/

public section

namespace GlobalPhi43.MW20

/-- A monomial with the source scaling identity is controlled by its
weighted norm whenever dM≤1. The exponent p must be nonnegative. -/
theorem reciprocal_scale_norm_monomial {d M γ l a p H : ℝ}
    (hd : 0 < d) (hM : 0 < M) (hp : 0 ≤ p) (hH : 0 ≤ H)
    (hscale : d * M ≤ 1) (he : γ + l = a + p) :
    d ^ γ * (d ^ l * M ^ p * H) ≤ d ^ a * H := by
  have hpow : (d * M) ^ p ≤ 1 :=
    Real.rpow_le_one (by positivity) hscale hp
  have hid : d ^ γ * (d ^ l * M ^ p * H) =
      (d ^ a * H) * (d * M) ^ p := by
    rw [Real.mul_rpow hd.le hM.le]
    calc
      _ = (d ^ γ * d ^ l) * M ^ p * H := by ring
      _ = d ^ (a + p) * M ^ p * H := by rw [← Real.rpow_add hd, he]
      _ = _ := by rw [Real.rpow_add hd]; ring
  rw [hid]
  exact (mul_le_mul_of_nonneg_left hpow (by positivity)).trans_eq (mul_one _)

end GlobalPhi43.MW20
