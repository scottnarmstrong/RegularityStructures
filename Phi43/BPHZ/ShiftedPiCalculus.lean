/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedPiMoment
import Mathlib.Tactic

/-!
# `L^q` calculus and the atoms of the shifted moment bounds

`ShiftMom P q f A` says `∫⁻ ‖f‖ₑ^q ≤ ofReal A ^ q`.  Its stability under sums, differences,
multiplication by constants and products through `L^(2q)` is the Minkowski and Cauchy-Schwarz
calculus; `ShiftedPiAtoms` bundles the unshifted bounds (exponents `q` and `2q`), the bound on
the gradients and the `iPsi` row from which the shifted rows are built.
-/

@[expose] public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The `q`-th moment bound `∫⁻ ‖f‖ₑ^q ≤ ofReal A ^ q`. -/
def ShiftMom {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (q : ℕ) (f : Ω → ℝ) (A : ℝ) :
    Prop :=
  ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal A ^ q

/-- The Hairer constants of the mollifier `ρ` at the scale `ε`. -/
noncomputable abbrev shiftedPiHairerConst (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) :
    RenormalisationConstants :=
  (hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε)

end RegularityStructures.Phi43

end

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

section Calculus

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f g : Ω → ℝ} {q : ℕ} {A B : ℝ}

theorem ShiftMom.mono (h : ShiftMom P q f A) (hAB : A ≤ B) : ShiftMom P q f B :=
  lintegral_enorm_pow_mono h hAB

theorem ShiftMom.congr (hfg : ∀ ω, f ω = g ω) (h : ShiftMom P q g A) : ShiftMom P q f A := by
  have : f = g := funext hfg
  rwa [this]

theorem ShiftMom.add (hq : 1 ≤ q) (hf : Measurable f) (hg : Measurable g) (h1 : ShiftMom P q f A)
    (h2 : ShiftMom P q g B) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ShiftMom P q (fun ω => f ω + g ω) (A + B) :=
  lintegral_enorm_pow_add_le hq hf.aestronglyMeasurable hg.aestronglyMeasurable h1 h2 hA hB

theorem ShiftMom.sub (hq : 1 ≤ q) (hf : Measurable f) (hg : Measurable g) (h1 : ShiftMom P q f A)
    (h2 : ShiftMom P q g B) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ShiftMom P q (fun ω => f ω - g ω) (A + B) :=
  lintegral_enorm_pow_sub_le hq hf.aestronglyMeasurable hg.aestronglyMeasurable h1 h2 hA hB

theorem ShiftMom.const_mul (c : ℝ) (h : ShiftMom P q f A) (hc : |c| ≤ B) (hA : 0 ≤ A) :
    ShiftMom P q (fun ω => c * f ω) (B * A) :=
  lintegral_enorm_pow_mono (lintegral_enorm_pow_const_mul_le c h)
    (mul_le_mul_of_nonneg_right hc hA)

theorem ShiftMom.mul_const (m : ℝ) (h : ShiftMom P q f A) (hm : |m| ≤ B) (hA : 0 ≤ A) :
    ShiftMom P q (fun ω => f ω * m) (A * B) := by
  have := ShiftMom.const_mul m h hm hA
  refine ShiftMom.congr (fun ω => mul_comm _ _) (this.mono (le_of_eq (mul_comm _ _)))

theorem ShiftMom.mul (hf : Measurable f) (hg : Measurable g) (h1 : ShiftMom P (2 * q) f A)
    (h2 : ShiftMom P (2 * q) g B) (hA : 0 ≤ A) : ShiftMom P q (fun ω => f ω * g ω) (A * B) :=
  lintegral_enorm_pow_mul_le hf.aemeasurable hg.aemeasurable h1 h2 hA

theorem ShiftMom.const [IsProbabilityMeasure P] (c : ℝ) (h : |c| ≤ A) :
    ShiftMom P q (fun _ => c) A :=
  lintegral_enorm_pow_const_le c h

/-- Lower the power of `t` (for `t ≤ 1`). -/
theorem ShiftMom.tpow {t e₁ e₂ : ℝ} (h : ShiftMom P q f (A * t ^ e₂)) (hA : 0 ≤ A)
    (ht : t ∈ Set.Ioc (0 : ℝ) 1) (he : e₁ ≤ e₂) : ShiftMom P q f (A * t ^ e₁) :=
  h.mono (shiftedPi_tpow_mono hA ht he)

/-- Difference of two scalar multiples: `c f - c' f' = (c - c') f + c' (f - f')`. -/
theorem ShiftMom.cdiff {f f' : Ω → ℝ} {S d B' : ℝ} (hq : 1 ≤ q) (hf : Measurable f)
    (hf' : Measurable f') (c c' : ℝ) (h : ShiftMom P q f A)
    (hd : ShiftMom P q (fun ω => f ω - f' ω) S) (hc' : |c'| ≤ B') (hcc : |c - c'| ≤ d)
    (hA : 0 ≤ A) (hS : 0 ≤ S) (hd0 : 0 ≤ d) (hB' : 0 ≤ B') :
    ShiftMom P q (fun ω => c * f ω - c' * f' ω) (d * A + B' * S) := by
  have h1 := ShiftMom.const_mul (c - c') h hcc hA
  have h2 := ShiftMom.const_mul c' hd hc' hS
  have := ShiftMom.add hq (hf.const_mul _) ((hf.sub hf').const_mul _) h1 h2
    (by positivity) (by positivity)
  refine ShiftMom.congr (fun ω => ?_) this
  simp only [Pi.sub_apply]
  ring

/-- Difference of products through `L^(2q)`: `g f - g' f' = (g - g') f + g' (f - f')`. -/
theorem ShiftMom.mulDiff {g g' f f' : Ω → ℝ} {Sg Sf Ag' A' : ℝ} (hq : 1 ≤ q)
    (hg : Measurable g) (hg' : Measurable g') (hf : Measurable f) (hf' : Measurable f')
    (h1 : ShiftMom P (2 * q) (fun ω => g ω - g' ω) Sg) (h2 : ShiftMom P (2 * q) f A')
    (h3 : ShiftMom P (2 * q) g' Ag') (h4 : ShiftMom P (2 * q) (fun ω => f ω - f' ω) Sf)
    (hSg : 0 ≤ Sg) (hAg' : 0 ≤ Ag') (hA' : 0 ≤ A') (hSf : 0 ≤ Sf) :
    ShiftMom P q (fun ω => g ω * f ω - g' ω * f' ω) (Sg * A' + Ag' * Sf) := by
  have e1 := ShiftMom.mul (hg.sub hg') hf h1 h2 hSg
  have e2 := ShiftMom.mul hg' (hf.sub hf') h3 h4 hAg'
  have := ShiftMom.add hq ((hg.sub hg').mul hf) (hg'.mul (hf.sub hf')) e1 e2
    (mul_nonneg hSg hA') (mul_nonneg hAg' hSf)
  refine ShiftMom.congr (fun ω => ?_) this
  simp only [Pi.sub_apply, Pi.mul_apply]
  ring

/-- A six-term combination `u - v₂ - v₃ - v₄ + v₅ - v₆`. -/
theorem ShiftMom.assemble6 {u v2 v3 v4 v5 v6 : Ω → ℝ} {a0 a2 a3 a4 a5 a6 : ℝ} (hq : 1 ≤ q)
    (hu : Measurable u) (hv2 : Measurable v2) (hv3 : Measurable v3) (hv4 : Measurable v4)
    (hv5 : Measurable v5) (hv6 : Measurable v6) (h0 : ShiftMom P q u a0)
    (h2 : ShiftMom P q v2 a2) (h3 : ShiftMom P q v3 a3) (h4 : ShiftMom P q v4 a4)
    (h5 : ShiftMom P q v5 a5) (h6 : ShiftMom P q v6 a6) (n0 : 0 ≤ a0) (n2 : 0 ≤ a2)
    (n3 : 0 ≤ a3) (n4 : 0 ≤ a4) (n5 : 0 ≤ a5) (n6 : 0 ≤ a6) :
    ShiftMom P q (fun ω => u ω - v2 ω - v3 ω - v4 ω + v5 ω - v6 ω)
      (a0 + a2 + a3 + a4 + a5 + a6) := by
  have s1 := ShiftMom.sub hq hu hv2 h0 h2 n0 n2
  have s2 := ShiftMom.sub hq (hu.sub hv2) hv3 s1 h3 (add_nonneg n0 n2) n3
  have s3 := ShiftMom.sub hq ((hu.sub hv2).sub hv3) hv4 s2 h4 (add_nonneg (add_nonneg n0 n2) n3) n4
  have s4 := ShiftMom.add hq (((hu.sub hv2).sub hv3).sub hv4) hv5 s3 h5
    (add_nonneg (add_nonneg (add_nonneg n0 n2) n3) n4) n5
  exact ShiftMom.sub hq ((((hu.sub hv2).sub hv3).sub hv4).add hv5) hv6 s4 h6
    (add_nonneg (add_nonneg (add_nonneg (add_nonneg n0 n2) n3) n4) n5) n6

end Calculus

end RegularityStructures.Phi43

end
