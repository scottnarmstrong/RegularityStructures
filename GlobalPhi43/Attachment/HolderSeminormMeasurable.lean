module

public import GlobalPhi43.MW20.ScalarHolderSeminorm
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Measurability of the actual two-sided scalar Holder seminorm on arbitrary base sets. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures Local MW20 Set

/-- The true distinct-point Holder seminorm is a measurable observable for continuous fields. -/
theorem scalarHolderSeminorm_measurable {Ω : Type*} [MeasurableSpace Ω]
    (S : Set ParabolicSpace) (α : ℝ) (g : Ω → ParabolicSpace → ℝ)
    (hc : ∀ ω, Continuous (g ω)) (hm : ∀ x, Measurable (fun ω => g ω x)) :
    Measurable (fun ω => scalarHolderSeminorm (g ω) S α) := by
  let P := {p : ParabolicSpace × ParabolicSpace // p.1 ∈ S ∧ p.2 ∈ S ∧ p.2 ≠ p.1}
  let F (p : P) (ω : Ω) : ENNReal :=
    ENNReal.ofReal (|g ω p.1.2 - g ω p.1.1| / pdist p.1.1 p.1.2 ^ α)
  have he (ω : Ω) : scalarHolderSeminorm (g ω) S α = ⨆ p : P, F p ω := by
    apply le_antisymm
    · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hne => ?_
      exact le_iSup_of_le (⟨(x, y), hx, hy, hne⟩ : P) le_rfl
    · refine iSup_le fun p => ?_
      exact le_iSup₂_of_le p.1.1 p.2.1 (le_iSup₂_of_le p.1.2 p.2.2.1
        (le_iSup_of_le p.2.2.2 le_rfl))
  have hefun : (fun ω => scalarHolderSeminorm (g ω) S α) = ⨆ p : P, F p := by
    funext ω
    simp only [iSup_apply]
    exact he ω
  rw [hefun]
  have hmeas (p : P) : Measurable (F p) :=
    ((continuous_abs.measurable.comp ((hm p.1.2).sub (hm p.1.1))).div_const _).ennreal_ofReal
  apply measurable_iSup_of_lowerSemicontinuous hmeas
  intro ω
  have h1 : Continuous (fun p : P => g ω p.1.1) :=
    (hc ω).comp (continuous_fst.comp continuous_subtype_val)
  have h2 : Continuous (fun p : P => g ω p.1.2) :=
    (hc ω).comp (continuous_snd.comp continuous_subtype_val)
  have hd : Continuous (fun p : P => pdist p.1.1 p.1.2) := by
    unfold pdist
    fun_prop
  have hp (p : P) : 0 < pdist p.1.1 p.1.2 := pdist_pos_of_ne p.2.2.2
  have hpow : Continuous (fun p : P => pdist p.1.1 p.1.2 ^ α) :=
    hd.rpow_const (fun p => Or.inl (hp p).ne')
  exact (ENNReal.continuous_ofReal.comp
    ((h2.sub h1).abs.div hpow (fun p => (Real.rpow_pos_of_pos (hp p) α).ne'))).lowerSemicontinuous

end GlobalPhi43.Attachment
