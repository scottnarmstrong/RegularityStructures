module

public import GlobalPhi43.Flow.WindowEvent
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section
namespace GlobalPhi43.Attachment
open Set RegularityStructures RegularityStructures.Phi43

/-- The original loss range is sufficient for both endpoint integrability and
sqrt-time damping. No stronger loss exponent is introduced. -/
theorem slice_time_power_bounds (κ : Kappa) {t : ℝ} (ht : t ∈ Ioc (0:ℝ) 1) :
    -2 < (Flow.lossExponent κ : ℝ) ∧
    1 ≤ t^((Flow.lossExponent κ : ℝ)/2) ∧
    t^((Flow.lossExponent κ : ℝ)/2+1) ≤ t^((Flow.lossExponent κ : ℝ)/2) ∧
    t ≤ t^((Flow.lossExponent κ : ℝ)/2) ∧
    Real.sqrt t*t^((Flow.lossExponent κ : ℝ)/2) ≤ 1 := by
  have hα : (Flow.lossExponent κ : ℝ)/2 ≤ 0 := (div_neg_of_neg_of_pos (Flow.lossExponent κ).2 (by norm_num)).le
  have h1 : 1 ≤ t^((Flow.lossExponent κ : ℝ)/2) := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 hα
  refine ⟨?_,h1,Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 (by linarith),ht.2.trans h1,?_⟩
  · change -2 < -(1/2:ℝ)-κ.1
    linarith [κ.2.2]
  · rw [Real.sqrt_eq_rpow,← Real.rpow_add ht.1]
    apply Real.rpow_le_one ht.1.le ht.2
    change 0 ≤ 1/2+(-(1/2:ℝ)-κ.1)/2
    linarith [κ.2.2]

/-- Scalar bookkeeping for the signed split after each actual analytic term
has been estimated. This scalar estimate applies to the terms of the slice decomposition. -/
theorem slice_power_assembly (κ : Kappa) {t : ℝ} (ht : t ∈ Ioc (0:ℝ) 1)
    (j p e Y M W : ℝ) (hj : 0≤j) (hp : 0≤p) (he : 0≤e)
    (hY : 0≤Y) (hM : 0≤M)
    (hW : W ≤ j*M*t^((Flow.lossExponent κ : ℝ)/2) +
      p*t^((Flow.lossExponent κ : ℝ)/2)*Y +
      t^((Flow.lossExponent κ : ℝ)/2+1)/((Flow.lossExponent κ : ℝ)/2+1)*Y + t*e*M) :
    Real.sqrt t*(W+Y) ≤
      (1+j+p+((Flow.lossExponent κ : ℝ)/2+1)⁻¹+e)*(Y+M) := by
  let B := t^((Flow.lossExponent κ : ℝ)/2)
  let β := (Flow.lossExponent κ : ℝ)/2+1
  let K := 1+j+p+β⁻¹+e
  have hb := slice_time_power_bounds κ ht
  have hβ : 0<β := by dsimp [β]; linarith [hb.1]
  have hB : 0≤B := Real.rpow_nonneg ht.1.le _
  have hi : 0≤β⁻¹ := inv_nonneg.mpr hβ.le
  have hK : 0≤K := by dsimp [K]; positivity
  have hrpow : t^((Flow.lossExponent κ : ℝ)/2+1)/β*Y ≤ B/β*Y :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb.2.2.1 hβ.le) hY
  have hte : t*e*M ≤ B*e*M :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb.2.2.2.1 he) hM
  have hbase : W+Y ≤ B*((j+e)*M+(p+β⁻¹+1)*Y) := by
    have hy : Y ≤ B*Y := by simpa using mul_le_mul_of_nonneg_right hb.2.1 hY
    dsimp only [B,β] at hrpow hte hy ⊢
    simp only [div_eq_mul_inv] at hrpow hW hte hy ⊢
    nlinarith
  have htotal : W+Y ≤ K*B*(Y+M) := by
    calc _ ≤ B*((j+e)*M+(p+β⁻¹+1)*Y) := hbase
      _ ≤ B*(K*M+K*Y) := mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) hM)
        (mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) hY)) hB
      _ = K*B*(Y+M) := by ring
  calc _ ≤ Real.sqrt t*(K*B*(Y+M)) := mul_le_mul_of_nonneg_left htotal (Real.sqrt_nonneg t)
    _ = K*(Real.sqrt t*B)*(Y+M) := by ring
    _ ≤ K*1*(Y+M) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb.2.2.2.2 hK) (add_nonneg hY hM)
    _ = _ := by simp only [mul_one,K,β]

end GlobalPhi43.Attachment
