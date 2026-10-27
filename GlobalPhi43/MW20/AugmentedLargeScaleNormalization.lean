module

public import GlobalPhi43.Local.DefectBudget
public import Mathlib.Tactic

/-! Uniform maximum arithmetic for the actual (4.31) terms. -/

public section

namespace GlobalPhi43.MW20

/-- The added defect root fits the same c-small forcing scale for k>2. -/
theorem augmented_defect_root_normalization {c M E₁ E₂ E₃ k ε : ℝ}
    (hc : 0 ≤ c) (hM : 0 ≤ M) (hE₁ : 0 ≤ E₁) (hE₃ : 0 ≤ E₃)
    (he : Local.DefectSmall c M E₁ E₂ E₃) (hk : 2 < k) (hε : 0 < ε) :
    E₁ ^ (1 / 3 : ℝ) ≤ M * (c * k ^ (3 / 2 + 3 * ε)) ^ (1 / 3 : ℝ) := by
  have hk1 : 1 ≤ k := by linarith
  have hp : 1 ≤ k ^ (3 / 2 + 3 * ε) := Real.one_le_rpow hk1 (by linarith)
  have hh : c ≤ c * k ^ (3 / 2 + 3 * ε) := by nlinarith
  have hr := Real.rpow_le_rpow hc hh (by norm_num : (0 : ℝ) ≤ 1 / 3)
  calc
    _ ≤ c ^ (1 / 3 : ℝ) * M := Local.defect_cube_root_le hc hM hE₁ hE₃ he
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hr hM]

/-- Collect actual smoothing, commutator and all three forcing errors.
Every coefficient is fixed before the data; the maximum is unchanged. -/
theorem normalize_augmented_large_scale_maximum
    {N B E P F G W M a b p CE CP CF CG CW : ℝ}
    (hB : 0 ≤ B) (hCE : 0 ≤ CE) (hCP : 0 ≤ CP)
    (hCF : 0 ≤ CF) (hCG : 0 ≤ CG) (hCW : 0 ≤ CW)
    (hE : E ≤ CE * (M * a)) (hP : P ≤ CP * (M * b))
    (hF : F ≤ CF * (M * p)) (hG : G ≤ CG * (M * p)) (hW : W ≤ CW * (M * p))
    (hrow : N ≤ 92 * max (max B E) (max P (max F (max G W)))) :
    N ≤ (92 * (1 + CE + CP + CF + CG + CW)) *
      max B (max (M * a) (max (M * b) (M * p))) := by
  let K := 1 + CE + CP + CF + CG + CW
  let Q := max B (max (M * a) (max (M * b) (M * p)))
  have hQ : 0 ≤ Q := hB.trans (le_max_left _ _)
  have hK1 : 1 ≤ K := by dsimp [K]; linarith
  have hCEK : CE ≤ K := by dsimp [K]; linarith
  have hCPK : CP ≤ K := by dsimp [K]; linarith
  have hCFK : CF ≤ K := by dsimp [K]; linarith
  have hCGK : CG ≤ K := by dsimp [K]; linarith
  have hCWK : CW ≤ K := by dsimp [K]; linarith
  have hMa : M * a ≤ Q := (le_max_left _ _).trans (le_max_right _ _)
  have hMb : M * b ≤ Q := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hMp : M * p ≤ Q := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hbound {x C f : ℝ} (hC : 0 ≤ C) (hCK : C ≤ K) (hx : x ≤ C * f) (hf : f ≤ Q) :
      x ≤ K * Q :=
    (hx.trans (mul_le_mul_of_nonneg_left hf hC)).trans (mul_le_mul_of_nonneg_right hCK hQ)
  have hBQ : B ≤ K * Q := by
    have h := mul_le_mul_of_nonneg_right hK1 hQ
    exact (le_max_left _ _).trans (by simpa only [one_mul] using h)
  have hmax : max (max B E) (max P (max F (max G W))) ≤ K * Q :=
    max_le (max_le hBQ (hbound hCE hCEK hE hMa))
      (max_le (hbound hCP hCPK hP hMb)
        (max_le (hbound hCF hCFK hF hMp)
          (max_le (hbound hCG hCGK hG hMp) (hbound hCW hCWK hW hMp))))
  have hfinal := hrow.trans (mul_le_mul_of_nonneg_left hmax (by norm_num))
  change N ≤ (92 * K) * Q
  nlinarith only [hfinal]

end GlobalPhi43.MW20
