/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.CausalHolder

/-! The actual affine approximation infimum on a strict past ball.
Near-minimizers are selected with a positive error allowance; attainment
is never assumed, including when the infimum is zero. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set
open scoped ENNReal

def pastAffineError (f : ParabolicSpace → ℝ) (x : ParabolicSpace) (R : ℝ) : ℝ≥0∞ :=
  ⨅ c : ℝ, ⨅ ν : Fin 3 → ℝ, ⨆ y ∈ pastBall x R,
    ENNReal.ofReal |f y - spatialAffine x c ν y|

theorem exists_past_affine_approximation (f : ParabolicSpace → ℝ) (x : ParabolicSpace)
    {R H γ δ : ℝ} (hR : 0 < R) (hH : 0 ≤ H) (hδ : 0 < δ)
    (herror : pastAffineError f x R ≤ ENNReal.ofReal (H * R ^ γ)) :
    ∃ c : ℝ, ∃ ν : Fin 3 → ℝ, ∀ y ∈ pastBall x R,
      |f y - spatialAffine x c ν y| ≤ (H + δ) * R ^ γ := by
  have hp : 0 < R ^ γ := Real.rpow_pos_of_pos hR _
  have htarget : 0 < (H + δ) * R ^ γ := mul_pos (by linarith) hp
  have hstrict : pastAffineError f x R < ENNReal.ofReal ((H + δ) * R ^ γ) :=
    herror.trans_lt ((ENNReal.ofReal_lt_ofReal_iff htarget).2 (by nlinarith))
  unfold pastAffineError at hstrict
  obtain ⟨c, hc⟩ := iInf_lt_iff.mp hstrict
  obtain ⟨ν, hν⟩ := iInf_lt_iff.mp hc
  refine ⟨c, ν, fun y hy => ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff htarget.le).mp
  have hb : ∀ y ∈ pastBall x R, ENNReal.ofReal |f y - spatialAffine x c ν y| ≤
      ENNReal.ofReal ((H + δ) * R ^ γ) := by
    simpa only [iSup_le_iff] using hν.le
  exact hb y hy

end GlobalPhi43.Local
