module

public import GlobalPhi43.MW20.KernelNormClosure

/-! The ordinary scalar supremum in source (2.4), with faithful extended
values and derived finiteness on bounded continuous-source domains. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ENNReal

/-- The literal local supremum of the absolute value. -/
@[expose] noncomputable def localScalarSup (f : ParabolicSpace → ℝ) (D : Set ParabolicSpace) : ℝ≥0∞ :=
  ⨆ x ∈ D, ENNReal.ofReal |f x|

theorem localScalarSup_bound (f : ParabolicSpace → ℝ) (D : Set ParabolicSpace)
    {N : ℝ} (hN : 0 ≤ N) (hnorm : localScalarSup f D ≤ ENNReal.ofReal N)
    {x : ParabolicSpace} (hx : x ∈ D) : |f x| ≤ N := by
  have hh : ∀ x ∈ D, ENNReal.ofReal |f x| ≤ ENNReal.ofReal N := by
    simpa only [localScalarSup, iSup_le_iff] using hnorm
  exact (ENNReal.ofReal_le_ofReal_iff hN).mp (hh x hx)

theorem localScalarSup_ne_top (f : ParabolicSpace → ℝ) (hf : Continuous f)
    (D s : Set ParabolicSpace) (hDs : D ⊆ s) (hs : IsCompact s) : localScalarSup f D ≠ ⊤ := by
  obtain ⟨N, hN⟩ := hs.exists_bound_of_continuousOn hf.continuousOn
  have hh : localScalarSup f D ≤ ENNReal.ofReal (max N 0) := by
    unfold localScalarSup
    refine iSup_le fun x => iSup_le fun hx => ?_
    apply ENNReal.ofReal_le_ofReal
    simpa only [Real.norm_eq_abs] using (hN x (hDs hx)).trans (le_max_left _ _)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hh

end GlobalPhi43.MW20
