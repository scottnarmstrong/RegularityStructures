module

public import GlobalPhi43.Attachment.AttachedTranslation
public import Phi43.Mollifier
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic.Ring

/-! The shifted white noise and the corresponding translated regularisation. -/

public section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43

/-- Translation of only the time factor preserves space-time volume. No spatial Haar instance
is needed for this map. -/
theorem timeTranslate_measurePreserving (k : ℝ) :
    MeasurePreserving (fun z : SpaceTime => (z.1 + k, z.2)) volume volume := by
  rw [Measure.volume_eq_prod]
  exact (measurePreserving_add_right (volume : Measure ℝ) k).prod (MeasurePreserving.id volume)

/-- The translated noise W_k(h) = W(h(· - k)) is white noise on the original probability space. -/
theorem whiteNoise_time_translate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W) (k : ℝ) :
    IsWhiteNoise P (fun h => W (fun z => h (z.1 - k, z.2))) := by
  have hmp := timeTranslate_measurePreserving (-k)
  have hm (h : SpaceTime → ℝ) (hh : MemLp h 2) :
      MemLp (fun z : SpaceTime => h (z.1 - k, z.2)) 2 := by
    simpa only [Function.comp_def, sub_eq_add_neg] using hh.comp_measurePreserving hmp
  constructor
  · intro h hh
    exact hW.1 _ (hm h hh)
  · intro n h hh
    have hvec := hW.2 n (fun i z => h i (z.1 - k, z.2)) (fun i => hm (h i) (hh i))
    have he (i j : Fin n) : (∫ z : SpaceTime, h i (z.1 - k, z.2) * h j (z.1 - k, z.2)) =
        ∫ z : SpaceTime, h i z * h j z := by
      let e : SpaceTime ≃ᵐ SpaceTime :=
        (MeasurableEquiv.addRight (-k)).prodCongr (MeasurableEquiv.refl Torus3)
      have hemp : MeasurePreserving e (volume : Measure SpaceTime) volume := hmp
      have heq (z : SpaceTime) : e z = (z.1 - k, z.2) := by
        apply Prod.ext
        · change z.1 + -k = z.1 - k
          ring
        · rfl
      simpa only [heq] using hemp.integral_comp' (fun z => h i z * h j z)
    simpa only [he] using hvec

/-- The actual translated regularisation is driven by that same shifted white noise. -/
theorem regularisedNoise_time_translate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ParabolicSpace → ℝ} {ε : ℝ}
    {ξ : Ω → SpaceTime → ℝ} (hξ : IsRegularisedNoise P W ρ ε ξ) (k : ℝ) :
    IsRegularisedNoise P (fun h => W (fun z => h (z.1 - k, z.2))) ρ ε
      (fun ω z => ξ ω (z.1 + k, z.2)) := by
  constructor
  · intro ω
    exact smooth_time_translate (hξ.1 ω) k
  · intro z
    obtain ⟨hmeas, hae⟩ := hξ.2 (z.1 + k, z.2)
    refine ⟨hmeas, ?_⟩
    have htest : mollifierAt ρ ε (z.1 + k, z.2) =
        fun w => mollifierAt ρ ε z (w.1 - k, w.2) := by
      funext w
      unfold mollifierAt
      congr 1
      apply Prod.ext
      · change z.1 + k - w.1 = z.1 - (w.1 - k)
        ring
      · rfl
    rwa [htest] at hae

end GlobalPhi43.Attachment
