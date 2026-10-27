module

public import GlobalPhi43.Attachment.CoverFromPatch
public import RegularityStructures.Torus.KernelBoundsBasic
public import RegularityStructures.PDE.MildDeriv
public import Mathlib.Topology.ContinuousMap.Compact

/-! Passage from a normalized Moinat–Weber bound to the torus supremum norm,
with the normalized estimate as an explicit hypothesis. -/

public noncomputable section

open Set RegularityStructures
open scoped ENNReal

namespace GlobalPhi43.Attachment

/-- Conditional cover application in the precise norm form used by majorant_norm_of_rows.
The actual closed fundamental cell covers the torus through the representative. -/
theorem cover_torus_norm_of_normalized_row {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1)
    (s : ℝ) (v : ℝ → C(Torus3, ℝ)) (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hv : ContinuousOn (fun z : ParabolicSpace => v z.1 (torusProj z.2)) {z | s < z.1})
    (hMW : ∀ x₀ ∈ coverGrid (coverScale t), ∀ z ∈ mwInnerCylinder (1 / 2),
      coverScale t * |v (coverMap s t x₀ z).1 (torusProj (coverMap s t x₀ z).2)| ≤
        C * max 2 (coverScale t * M)) :
    ENNReal.ofReal (Real.sqrt t) * ‖v (s+t)‖ₑ ≤
      ENNReal.ofReal (2*C) * max 2 (ENNReal.ofReal M) := by
  have hpoint (x : Torus3) : Real.sqrt t * |v (s+t) x| ≤ 2*C*max 2 M := by
    have hcell (i : Fin 3) : torusRep x i ∈ Icc (0 : ℝ) 1 :=
      ⟨(torusRep_mem_Ico x i).1, (torusRep_mem_Ico x i).2.le⟩
    simpa only [PDE.torusProj_torusRep] using
      cover_bound_of_normalized_row ht s (fun z => v z.1 (torusProj z.2))
        C M hC hM hv hMW (torusRep x) hcell
  have hnorm : ‖Real.sqrt t • v (s+t)‖ ≤ 2*C*max 2 M := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro x
    simpa only [ContinuousMap.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg t)] using hpoint x
  have he := ENNReal.ofReal_le_ofReal hnorm
  rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg t),
    ENNReal.ofReal_mul (Real.sqrt_nonneg t), ofReal_norm] at he
  convert he using 1
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2*C), ENNReal.ofReal_max]
  norm_num

end GlobalPhi43.Attachment
