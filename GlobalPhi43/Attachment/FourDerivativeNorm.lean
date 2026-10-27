module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import RegularityStructures.Analysis.Parabolic.Basic

/-! Analytic properties of the order-four supremum used by the C4 norm. -/

public section

namespace GlobalPhi43.Attachment
open RegularityStructures

open scoped ContDiff in
/-- The C4 supremum of a smooth compact test is finite and bounds every
derivative of order at most four. -/
theorem four_derivative_supremum_bound {φ : ParabolicSpace → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    let A : ENNReal := ⨆ k ∈ Finset.range 5, ⨆ z, ‖iteratedFDeriv ℝ k φ z‖ₑ
    A ≠ ⊤ ∧ ∀ k ≤ 4, ∀ z, ‖iteratedFDeriv ℝ k φ z‖ ≤ A.toReal := by
  let A : ENNReal := ⨆ k ∈ Finset.range 5, ⨆ z, ‖iteratedFDeriv ℝ k φ z‖ₑ
  obtain ⟨B, _, hB⟩ := hc.exists_bound_iteratedFDeriv hφ 4
  have hAB : A ≤ ENNReal.ofReal B := by
    apply iSup₂_le
    intro k hk
    apply iSup_le
    intro z
    have h := ENNReal.ofReal_le_ofReal (hB k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) z)
    simpa only [ofReal_norm] using h
  have hfin : A ≠ ⊤ := ne_of_lt (hAB.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hfin, ?_⟩
  intro k hk z
  have hk' : k ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
  have hle : ‖iteratedFDeriv ℝ k φ z‖ₑ ≤ A :=
    le_iSup_of_le k (le_iSup_of_le hk' (le_iSup (fun z => ‖iteratedFDeriv ℝ k φ z‖ₑ) z))
  change ‖iteratedFDeriv ℝ k φ z‖ ≤ A.toReal
  simpa only [toReal_enorm] using ENNReal.toReal_mono hfin hle

end GlobalPhi43.Attachment
