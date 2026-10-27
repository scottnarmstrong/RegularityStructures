module

public import GlobalPhi43.Attachment.UnitKernelTesting
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Countable-supremum measurability of actual scalar germ seminorms. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures MW20 Set Filter

/-- Fixed-parameter measurability of the actual unit-kernel integral. -/
theorem unitGermAverage_measurable {Ω : Type*} [MeasurableSpace Ω]
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (G : Ω → ParabolicSpace × ParabolicSpace → ℝ) (hc : ∀ ω, Continuous (G ω))
    (hm : ∀ p, Measurable (fun ω => G ω p)) (p : ParabolicSpace × ℝ) :
    Measurable (fun ω => unitGermAverage Φ hΦ (G ω) p) := by
  have hi := measurable_uncurry_of_continuous_of_measurable
    (u := fun (w : ParabolicSpace) (ω : Ω) => G ω (p.1, p.1 + parabolicDilate p.2 w))
    (fun ω => (hc ω).comp (by unfold parabolicDilate; fun_prop))
    (fun w => hm (p.1, p.1 + parabolicDilate p.2 w))
  have hj : Measurable (fun q : Ω × ParabolicSpace =>
      G q.1 (p.1, p.1 + parabolicDilate p.2 q.2)) :=
    hi.comp (measurable_snd.prodMk measurable_fst)
  have := infiniteKernelMeasure_probability Φ hΦ (by norm_num : (0 : ℝ) < 1) le_rfl
  exact hj.stronglyMeasurable.integral_prod_right'.measurable

/-- Scalar test norms are measurable for arbitrary base sets and exact scale ranges.
Continuity and fixed-point measurability of the actual germ are the only field inputs. -/
theorem localTestSeminorm_measurable {Ω : Type*} [MeasurableSpace Ω]
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (S : Set ParabolicSpace)
    (I : Set ℝ) (hI : I ⊆ Ioc 0 1) (α : ℝ)
    (G : Ω → ParabolicSpace × ParabolicSpace → ℝ) (hc : ∀ ω, Continuous (G ω))
    (hm : ∀ p, Measurable (fun ω => G ω p)) :
    Measurable (fun ω => localTestSeminorm (mw20TestingKernel Φ hΦ) S I α
      (fun x y => G ω (x, y))) := by
  let H (p : S × I) (ω : Ω) : ENNReal :=
    ENNReal.ofReal (p.2.1 ^ (-α) * |unitGermAverage Φ hΦ (G ω) (p.1.1, p.2.1)|)
  have he (ω : Ω) : localTestSeminorm (mw20TestingKernel Φ hΦ) S I α (fun x y => G ω (x, y)) =
      ⨆ p : S × I, H p ω := by
    apply le_antisymm
    · refine iSup₂_le fun x hx => iSup₂_le fun t ht => ?_
      change ENNReal.ofReal (t ^ (-α) * |pastSmooth (mw20TestingKernel Φ hΦ t)
        (fun y => G ω (x, y)) x|) ≤ _
      rw [pastSmooth_eq_unitGermAverage Φ hΦ (hI ht).1 (hI ht).2]
      exact le_iSup_of_le (⟨x, hx⟩, ⟨t, ht⟩) le_rfl
    · refine iSup_le fun p => ?_
      refine le_iSup₂_of_le p.1.1 p.1.2 (le_iSup₂_of_le p.2.1 p.2.2 ?_)
      change H p ω ≤ ENNReal.ofReal (p.2.1 ^ (-α) * |pastSmooth (mw20TestingKernel Φ hΦ p.2.1)
        (fun y => G ω (p.1.1, y)) p.1.1|)
      rw [pastSmooth_eq_unitGermAverage Φ hΦ (hI p.2.2).1 (hI p.2.2).2]
  have hefun : (fun ω => localTestSeminorm (mw20TestingKernel Φ hΦ) S I α (fun x y => G ω (x, y))) =
      (⨆ p : S × I, H p) := by
    funext ω
    simp only [iSup_apply]
    exact he ω
  rw [hefun]
  apply measurable_iSup_of_lowerSemicontinuous
    (fun p : S × I => (measurable_const.mul (continuous_abs.measurable.comp
      (unitGermAverage_measurable Φ hΦ G hc hm (p.1.1, p.2.1)))).ennreal_ofReal)
  intro ω
  have hparam : Continuous (fun p : S × I => (p.1.1, p.2.1)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  have hp : Continuous (fun p : S × I => p.2.1 ^ (-α)) :=
    (continuous_subtype_val.comp continuous_snd).rpow_const (fun p => Or.inl (hI p.2.2).1.ne')
  exact (ENNReal.continuous_ofReal.comp
    (hp.mul (((unitGermAverage_continuous Φ hΦ (G ω) (hc ω)).comp hparam).abs))).lowerSemicontinuous

end GlobalPhi43.Attachment
