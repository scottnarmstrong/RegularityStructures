/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramMultiSq
import Mathlib.Tactic

/-!
# Lower-integral bounds for kernels with a pointwise majorant

The estimates of `TreeI2Psi2DiagramMulti*` are stated for the increment of a kernel `K` of order
`3`.  We prove the same estimates for an arbitrary kernel `A` (a gradient increment, a Taylor
remainder, ...) that is only known through the pointwise majorant

`|A w| ≤ slab(w) * M * r^a * (s(y - w)^(-p) + s(x - w)^(-p))`,

where `slab(w) = 1` for `|w₀ - x₀| ≤ 2` and `0` otherwise (`gammaMajorant`).  The exponent `p` is
the decay of `A` at its singularities and `a` the gain in `r = s(y - x)`; they are independent.

* `gammaMajorant_lint_single`: `∫ |A| s(g - w)^(-e) ≲ M r^a (s(y-g)^(-(p+e-5)) + s(x-g)^(-(p+e-5)))`
  for `0 < p < 5`, `0 < e < 5`, `p + e > 5`;
* `gammaMajorant_lint_slab`: `∫ |A| s(g₁ - w)^(-l₁) s(g₂ - w)^(-l₂) ≲ M r^a` for `p + l₁ + l₂ < 5`;
* `gammaMajorant_lint_diag`: `∬ |A(w)| |A'(w')| s(w' - w)^(-e) ≲ M M' r^a r'^a'`.
-/

@[expose] public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The pointwise majorant `|A w| ≤ slab * M r^a (s(y-w)^(-p) + s(x-w)^(-p))`, `r = s(y-x)`. -/
def gammaMajorant (A : SpaceTime → ℝ) (x y : SpaceTime) (r M a p : ℝ) : Prop :=
  0 ≤ r ∧ 0 ≤ M ∧ Measurable A ∧ ∀ w : SpaceTime, 0 < torusParabolicSize (y - w) →
    0 < torusParabolicSize (x - w) →
      |A w| ≤ i2Psi2Slab x.1 w * (M * r ^ a *
        (torusParabolicSize (y - w) ^ (-p) + torusParabolicSize (x - w) ^ (-p)))

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem gmaj_measurable_weight (p g : SpaceTime) (a b : ℝ) :
    Measurable fun w : SpaceTime => torusParabolicSize (p - w) ^ a * torusParabolicSize (g - w) ^ b :=
  (measurable_torusParabolicSize_sub_rpow p a).mul (measurable_torusParabolicSize_sub_rpow g b)

private theorem gmaj_weight_nonneg (p g : SpaceTime) (a b : ℝ) (w : SpaceTime) :
    0 ≤ torusParabolicSize (p - w) ^ a * torusParabolicSize (g - w) ^ b :=
  mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
    (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)

/-- **Majorant kernel against `s(g - w)^(-e)`.** -/
theorem gammaMajorant_lint_single {a p e : ℝ} (hp : 0 < p) (hp5 : p < 5) (he : 0 < e)
    (he5 : e < 5) (hpe : 5 < p + e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {A : SpaceTime → ℝ} {x y : SpaceTime} {r M : ℝ},
      gammaMajorant A x y r M a p → ∀ g : SpaceTime, 0 < torusParabolicSize (y - g) →
        0 < torusParabolicSize (x - g) →
        i2Psi2LintBound volume (fun w => |A w| * torusParabolicSize (g - w) ^ (-e))
          (C * M * r ^ a *
            (torusParabolicSize (y - g) ^ (-(p + e - 5)) +
              torusParabolicSize (x - g) ^ (-(p + e - 5)))) := by
  obtain ⟨CG, hCG, hG⟩ := i2Psi2LintBound_rpow_mul_rpow_of_gt (a := p) (b := e) hp hp5 he he5 hpe
  refine ⟨CG, hCG, ?_⟩
  intro A x y r M hA g hyg hxg
  obtain ⟨hr0, hM, -, hAb⟩ := hA
  have e0 : (5 : ℝ) - p - e = -(p + e - 5) := by ring
  have gy := hG y g hyg
  have gx := hG x g hxg
  rw [e0] at gy gx
  have s := gy.add (g := fun w => torusParabolicSize (x - w) ^ (-p) *
      torusParabolicSize (g - w) ^ (-e)) (gmaj_measurable_weight y g _ _).aemeasurable
    (gmaj_weight_nonneg y g _ _) (gmaj_weight_nonneg x g _ _)
    (mul_nonneg hCG (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
    (mul_nonneg hCG (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)) gx
  have hr := Real.rpow_nonneg hr0 a
  have c := s.const_mul (c := M * r ^ a) (mul_nonneg hM hr)
  refine c.mono_ae ?_ (le_of_eq (by ring))
  filter_upwards [ae_torusParabolicSize_sub_pos y, ae_torusParabolicSize_sub_pos x]
    with w hy hx
  have h := hAb w hy hx
  have n2 : 0 ≤ torusParabolicSize (g - w) ^ (-e) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hsl := i2Psi2Slab_le_one x.1 w
  have hsum : 0 ≤ M * r ^ a * (torusParabolicSize (y - w) ^ (-p) +
      torusParabolicSize (x - w) ^ (-p)) :=
    mul_nonneg (mul_nonneg hM hr) (add_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  calc |A w| * torusParabolicSize (g - w) ^ (-e)
      ≤ (M * r ^ a * (torusParabolicSize (y - w) ^ (-p) +
        torusParabolicSize (x - w) ^ (-p))) * torusParabolicSize (g - w) ^ (-e) :=
        mul_le_mul_of_nonneg_right (h.trans (mul_le_of_le_one_left hsum hsl)) n2
    _ = _ := by ring

/-- **Majorant kernel against two weights, bounded case** (`p + l₁ + l₂ < 5`). -/
theorem gammaMajorant_lint_slab {a p l₁ l₂ : ℝ} (hp : 0 < p) (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂)
    (he : p + l₁ + l₂ < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {A : SpaceTime → ℝ} {x y : SpaceTime} {r M : ℝ},
      gammaMajorant A x y r M a p → |y.1 - x.1| ≤ 2 → ∀ g₁ g₂ : SpaceTime,
        |g₁.1 - x.1| ≤ 2 → |g₂.1 - x.1| ≤ 2 →
        i2Psi2LintBound volume (fun w => |A w| *
          (torusParabolicSize (g₁ - w) ^ (-l₁) * torusParabolicSize (g₂ - w) ^ (-l₂)))
          (C * M * r ^ a) := by
  obtain ⟨CT, hCT, hT⟩ := i2Psi2LintBound_slab_triple (l₁ := p) (l₂ := l₁) (l₃ := l₂)
    hp.le hl₁ hl₂ (by linarith) he
  refine ⟨2 * CT, by positivity, ?_⟩
  intro A x y r M hA hy2 g₁ g₂ hg₁ hg₂
  obtain ⟨hr0, hM, -, hAb⟩ := hA
  have hx2 : |x.1 - x.1| ≤ 2 := by simp
  have ty := hT x.1 y g₁ g₂ hy2 hg₁ hg₂
  have tx := hT x.1 x g₁ g₂ hx2 hg₁ hg₂
  have m : ∀ q : SpaceTime, Measurable fun w : SpaceTime => i2Psi2Slab x.1 w *
      (torusParabolicSize (q - w) ^ (-p) * torusParabolicSize (g₁ - w) ^ (-l₁) *
        torusParabolicSize (g₂ - w) ^ (-l₂)) := fun q =>
    (measurable_i2Psi2Slab _).mul (((measurable_torusParabolicSize_sub_rpow q _).mul
      (measurable_torusParabolicSize_sub_rpow g₁ _)).mul
      (measurable_torusParabolicSize_sub_rpow g₂ _))
  have n : ∀ (q : SpaceTime) w, 0 ≤ i2Psi2Slab x.1 w *
      (torusParabolicSize (q - w) ^ (-p) * torusParabolicSize (g₁ - w) ^ (-l₁) *
        torusParabolicSize (g₂ - w) ^ (-l₂)) := fun q w =>
    mul_nonneg (i2Psi2Slab_nonneg _ _) (mul_nonneg (mul_nonneg (Real.rpow_nonneg
      (torusParabolicSize_nonneg _) _) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  have s := ty.add (g := fun w => i2Psi2Slab x.1 w *
      (torusParabolicSize (x - w) ^ (-p) * torusParabolicSize (g₁ - w) ^ (-l₁) *
        torusParabolicSize (g₂ - w) ^ (-l₂))) (m y).aemeasurable (n y) (n x) hCT hCT tx
  have hr := Real.rpow_nonneg hr0 a
  have c := s.const_mul (c := M * r ^ a) (mul_nonneg hM hr)
  refine c.mono_ae ?_ (le_of_eq (by ring))
  filter_upwards [ae_torusParabolicSize_sub_pos y, ae_torusParabolicSize_sub_pos x]
    with w hyw hxw
  have h := hAb w hyw hxw
  have n2 : 0 ≤ torusParabolicSize (g₁ - w) ^ (-l₁) * torusParabolicSize (g₂ - w) ^ (-l₂) :=
    gmaj_weight_nonneg g₁ g₂ _ _ w
  calc |A w| * (torusParabolicSize (g₁ - w) ^ (-l₁) * torusParabolicSize (g₂ - w) ^ (-l₂))
      ≤ (i2Psi2Slab x.1 w * (M * r ^ a *
        (torusParabolicSize (y - w) ^ (-p) + torusParabolicSize (x - w) ^ (-p)))) *
          (torusParabolicSize (g₁ - w) ^ (-l₁) * torusParabolicSize (g₂ - w) ^ (-l₂)) :=
        mul_le_mul_of_nonneg_right h n2
    _ = _ := by ring

/-- **Principal pairing for majorant kernels**: for two kernels with majorants `(M, a, p)` and
`(M', a', p')` at the same base point `x`,
`∬ |A(w)| |A'(w')| s(w' - w)^(-e) ≲ M M' r^a r'^a'`, provided `p + e > 5`, `p < 5`, `e < 5`
and `p' + (p + e - 5) < 5`. -/
theorem gammaMajorant_lint_diag {a a' p p' e : ℝ} (hp : 0 < p) (hp5 : p < 5) (he : 0 < e)
    (he5 : e < 5) (hpe : 5 < p + e) (hp' : 0 < p') (hpp : p' + (p + e - 5) < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {A A' : SpaceTime → ℝ} {x y y' : SpaceTime} {r r' M M' : ℝ},
      gammaMajorant A x y r M a p → gammaMajorant A' x y' r' M' a' p' →
      |y.1 - x.1| ≤ 1 → |y'.1 - x.1| ≤ 1 →
        i2Psi2LintBound (volume.prod volume) (fun q : SpaceTime × SpaceTime =>
          |A q.1| * |A' q.2| * torusParabolicSize (q.2 - q.1) ^ (-e))
          (C * M * M' * r ^ a * r' ^ a') := by
  obtain ⟨C1, hC1, h1⟩ := gammaMajorant_lint_single (a := a) hp hp5 he he5 hpe
  obtain ⟨CO, hCO, hO⟩ := gammaMajorant_lint_slab (a := a') (p := p') (l₁ := p + e - 5) (l₂ := 0)
    hp' (by linarith) le_rfl (by linarith)
  refine ⟨2 * (C1 * CO), by positivity, ?_⟩
  intro A A' x y y' r r' M M' hA hA' hxy hxy'
  have hM := hA.2.1
  have hM' := hA'.2.1
  have mA := hA.2.2.1
  have mA' := hA'.2.2.1
  have hr0 : 0 ≤ r ^ a := Real.rpow_nonneg hA.1 _
  have hr0' : 0 ≤ r' ^ a' := Real.rpow_nonneg hA'.1 _
  refine i2Psi2LintBound.of_prod_symm
    (G := fun w' => |A' w'| * (C1 * M * r ^ a *
      (torusParabolicSize (y - w') ^ (-(p + e - 5)) + torusParabolicSize (x - w') ^ (-(p + e - 5)))))
    ?_ ?_ ?_
  · exact ((continuous_abs.measurable.comp mA).comp measurable_fst |>.mul
      ((continuous_abs.measurable.comp mA').comp measurable_snd)).mul
      ((Phi43.measurable_torusParabolicSize.comp (measurable_snd.sub measurable_fst)).pow_const _)
  · filter_upwards [ae_torusParabolicSize_sub_pos y, ae_torusParabolicSize_sub_pos x]
      with w' hy hx
    have h := (h1 hA w' hy hx).const_mul (c := |A' w'|) (abs_nonneg _)
    refine h.mono (fun w => ?_) le_rfl
    exact le_of_eq (by ring)
  · have e0 : ∀ u : SpaceTime, torusParabolicSize u ^ (-(0 : ℝ)) = 1 := fun u => by simp
    have hy2 : |y.1 - x.1| ≤ 2 := by linarith
    have hy2' : |y'.1 - x.1| ≤ 2 := by linarith
    have hx2 : |x.1 - x.1| ≤ 2 := by simp
    have hOy := hO hA' hy2' y x hy2 hx2
    have hOx := hO hA' hy2' x y hx2 hy2
    have nn : ∀ (g₁ g₂ : SpaceTime) (w' : SpaceTime), 0 ≤ |A' w'| *
        (torusParabolicSize (g₁ - w') ^ (-(p + e - 5)) * torusParabolicSize (g₂ - w') ^ (-(0 : ℝ))) :=
      fun g₁ g₂ w' => mul_nonneg (abs_nonneg _) (gmaj_weight_nonneg g₁ g₂ _ _ w')
    have hMM : 0 ≤ CO * M' * r' ^ a' := mul_nonneg (mul_nonneg hCO hM') hr0'
    have mm : Measurable fun w' : SpaceTime => |A' w'| *
        (torusParabolicSize (y - w') ^ (-(p + e - 5)) * torusParabolicSize (x - w') ^ (-(0 : ℝ))) :=
      (continuous_abs.measurable.comp mA').mul (gmaj_measurable_weight y x _ _)
    have s := hOy.add mm.aemeasurable (nn y x) (nn x y) hMM hMM hOx
    have c := s.const_mul (c := C1 * M * r ^ a) (mul_nonneg (mul_nonneg hC1 hM) hr0)
    refine c.mono (fun w' => ?_) (le_of_eq (by ring))
    simp only [e0, mul_one]
    exact le_of_eq (by ring)

end RegularityStructures.Phi43

end
