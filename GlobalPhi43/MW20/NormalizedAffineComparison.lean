module

public import GlobalPhi43.Local.AffineErrorComparison
public import GlobalPhi43.Local.ScaleNormalization

/-! Actual affine-infimum comparison in normalized source weights. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures
open scoped ENNReal

/-- Uniform weighted closeness acts directly on the actual affine infimum,
without selecting a minimizer or assuming either error is finite. -/
theorem weighted_pastAffineError_le_of_close
    (f g : ParabolicSpace → ℝ) (x : ParabolicSpace) {R W B : ℝ} (hW : 0 < W)
    (hclose : ∀ y ∈ Local.pastBall x R, W * |f y - g y| ≤ B) :
    ENNReal.ofReal W * Local.pastAffineError f x R ≤
      ENNReal.ofReal W * Local.pastAffineError g x R + ENNReal.ofReal B := by
  have hc : ∀ y ∈ Local.pastBall x R, |f y - g y| ≤ B / W := by
    intro y hy
    exact (le_div_iff₀ hW).2 (by simpa only [mul_comm] using hclose y hy)
  have hh := mul_le_mul_of_nonneg_left
    (Local.pastAffineError_le_of_close f g x hc) (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal W)
  have he : ENNReal.ofReal W * ENNReal.ofReal (B / W) = ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_mul hW.le]
    congr 1
    field_simp
  simpa only [mul_add, he] using hh

/-- The exact normalized far weight relative to the affine error at L. -/
theorem normalized_affine_far_weight {d γ η L : ℝ} (hη : 0 < η) (hL : 0 < L) :
    (d ^ γ * (η * L) ^ (-γ)) * ((η * L) / L) ^ 2 =
      η ^ (2 - γ) * (d ^ γ * L ^ (-γ)) := by
  have he : L ^ γ * L ^ (-γ) = 1 := by
    rw [← Real.rpow_add hL, add_neg_cancel, Real.rpow_zero]
  calc
    _ = (d ^ γ * (η * L) ^ (-γ) * ((η * L) / L) ^ 2) * (L ^ γ * L ^ (-γ)) := by
      rw [he, mul_one]
    _ = d ^ γ * ((η * L) ^ (-γ) * ((η * L) / L) ^ 2 * L ^ γ) * L ^ (-γ) := by ring
    _ = _ := by rw [Local.normalized_heat_factor hη hL]; ring

/-- Combine a heat-affine inequality with normalized closeness and forcing
bounds. The heat-affine inequality remains an explicit hypothesis. -/
theorem normalized_affine_comparison_step
    (f g : ParabolicSpace → ℝ) (x : ParabolicSpace)
    {d γ η L C F P Bnear Bfar Qheat : ℝ}
    (hd : 0 < d) (hη : 0 < η) (hL : 0 < L)
    (hC : 0 ≤ C) (hF : 0 ≤ F) (hP : 0 ≤ P) (hBn : 0 ≤ Bnear) (hBf : 0 ≤ Bfar)
    (hcaloric : Local.pastAffineError g x (η * L) ≤
      ENNReal.ofReal (C * ((η * L) / L) ^ 2) * Local.pastAffineError g x L +
        ENNReal.ofReal (C * L ^ 2 * Qheat))
    (hlarge : ENNReal.ofReal (d ^ γ * L ^ (-γ)) * Local.pastAffineError f x L ≤ ENNReal.ofReal F)
    (hnear : ∀ y ∈ Local.pastBall x (η * L),
      (d ^ γ * (η * L) ^ (-γ)) * |f y - g y| ≤ Bnear)
    (hfar : ∀ y ∈ Local.pastBall x L,
      ((d ^ γ * (η * L) ^ (-γ)) * ((η * L) / L) ^ 2) * |g y - f y| ≤ Bfar)
    (hforce : (d ^ γ * (η * L) ^ (-γ)) * L ^ 2 * Qheat ≤ P) :
    ENNReal.ofReal (d ^ γ * (η * L) ^ (-γ)) * Local.pastAffineError f x (η * L) ≤
      ENNReal.ofReal (C * η ^ (2 - γ) * F + C * P + C * Bfar + Bnear) := by
  let WR := d ^ γ * (η * L) ^ (-γ)
  let WL := d ^ γ * L ^ (-γ)
  let WF := WR * ((η * L) / L) ^ 2
  let p := η ^ (2 - γ)
  have hWR : 0 < WR := by dsimp [WR]; positivity
  have hWF : 0 < WF := by dsimp [WF]; positivity
  have hp : 0 ≤ p := Real.rpow_nonneg hη.le _
  have hn := weighted_pastAffineError_le_of_close f g x hWR hnear
  have hf := weighted_pastAffineError_le_of_close g f x hWF hfar
  have hweight : WF = p * WL := normalized_affine_far_weight hη hL
  have hprod : ENNReal.ofReal WR * ENNReal.ofReal (C * ((η * L) / L) ^ 2) =
      ENNReal.ofReal C * ENNReal.ofReal WF := by
    rw [← ENNReal.ofReal_mul hWR.le, ← ENNReal.ofReal_mul hC]
    congr 1
    dsimp [WF]
    ring
  have hheat : ENNReal.ofReal WR * ENNReal.ofReal (C * L ^ 2 * Qheat) ≤
      ENNReal.ofReal (C * P) := by
    rw [← ENNReal.ofReal_mul hWR.le]
    apply ENNReal.ofReal_le_ofReal
    nlinarith only [mul_le_mul_of_nonneg_left hforce hC]
  have hfar' : ENNReal.ofReal WF * Local.pastAffineError g x L ≤
      ENNReal.ofReal (p * F) + ENNReal.ofReal Bfar := by
    calc
      _ ≤ ENNReal.ofReal WF * Local.pastAffineError f x L + ENNReal.ofReal Bfar := hf
      _ = ENNReal.ofReal p * (ENNReal.ofReal WL * Local.pastAffineError f x L) + ENNReal.ofReal Bfar := by
        rw [hweight, ENNReal.ofReal_mul hp, mul_assoc]
      _ ≤ ENNReal.ofReal p * ENNReal.ofReal F + ENNReal.ofReal Bfar :=
        add_le_add (mul_le_mul' le_rfl hlarge) le_rfl
      _ = _ := by rw [← ENNReal.ofReal_mul hp]
  have hc := mul_le_mul_of_nonneg_left hcaloric (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal WR)
  rw [mul_add, ← mul_assoc, hprod, mul_assoc] at hc
  have hs := hn.trans (add_le_add (hc.trans
    (add_le_add (mul_le_mul' le_rfl hfar') hheat)) le_rfl)
  have he : ENNReal.ofReal C * (ENNReal.ofReal (p * F) + ENNReal.ofReal Bfar) +
      ENNReal.ofReal (C * P) + ENNReal.ofReal Bnear =
      ENNReal.ofReal (C * p * F + C * P + C * Bfar + Bnear) := by
    rw [← ENNReal.ofReal_add (mul_nonneg hp hF) hBf, ← ENNReal.ofReal_mul hC,
      ← ENNReal.ofReal_add (by positivity) (mul_nonneg hC hP),
      ← ENNReal.ofReal_add (by positivity) hBn]
    congr 1
    ring
  exact hs.trans_eq he

end GlobalPhi43.MW20
