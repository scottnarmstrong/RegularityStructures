/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorRegime
public import RegularityStructures.Analysis.Heat.Schauder.DiffBound
public import RegularityStructures.Analysis.Heat.Schauder.TaylorLap
public import RegularityStructures.Analysis.Heat.Schauder.TaylorPairingCentre

/-!
# `L¹` norms of the Taylor profile and of its generator

For `h` smooth and supported in the unit ball, `d = ‖z‖_𝔰 ≤ 2^{-n}`, `g = scaledShell h n` and
`H = taylorProfile g σ z`, we bound `∫ |H|` and `∫ |L H|` by sums over a finite list of derivative
words `ℓ` of terms `d^{|ℓ|_𝔰} (2^n)^{|ℓ|_𝔰 ∓ 2} ∫ |D^ℓ h|`, `∫ |D^ℓ L h|` (`taylorProfile_L1`).
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

theorem integral_abs_add_sum_le {ι : Type*} (s : Finset ι) {A : ParabolicSpace → ℝ}
    {F : ι → ParabolicSpace → ℝ} (c : ι → ℝ) (hA : Integrable A)
    (hF : ∀ i ∈ s, Integrable (F i)) :
    ∫ u, |A u + ∑ i ∈ s, c i * F i u| ≤ (∫ u, |A u|) + ∑ i ∈ s, |c i| * ∫ u, |F i u| := by
  have hF' : ∀ i ∈ s, Integrable fun u => |c i| * |F i u| := fun i hi => (hF i hi).abs.const_mul _
  have hS : Integrable fun u => ∑ i ∈ s, |c i| * |F i u| := integrable_finsetSum _ hF'
  have hpt : ∀ u, |A u + ∑ i ∈ s, c i * F i u| ≤ |A u| + ∑ i ∈ s, |c i| * |F i u| := by
    intro u
    refine (abs_add_le _ _).trans (add_le_add_right ((Finset.abs_sum_le_sum_abs _ _).trans ?_) _)
    exact le_of_eq (Finset.sum_congr rfl fun i _ => abs_mul _ _)
  have hint : Integrable fun u => |A u| + ∑ i ∈ s, |c i| * |F i u| := hA.abs.add hS
  have hle := integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => abs_nonneg _) hint
    (Filter.Eventually.of_forall hpt)
  refine hle.trans (le_of_eq ?_)
  rw [integral_add hA.abs hS, integral_finsetSum _ hF']
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]

theorem integral_neg_abs (f : ParabolicSpace → ℝ) : ∫ u, |f (-u)| = ∫ u, |f u| := by
  have : (volume : Measure ParabolicSpace).IsNegInvariant := by
    rw [Measure.volume_eq_prod]
    have : (volume.prod volume : Measure ParabolicSpace).IsAddHaarMeasure := inferInstance
    have : (volume.prod volume : Measure ParabolicSpace).Regular := inferInstance
    infer_instance
  exact integral_neg_eq_self (fun u => |f u|) volume

/-- The hypothesis of `exists_integral_abs_remJ_le`, packaged. -/
def RemBound (m : Fin 4 → ℕ) (J : List (Fin 4)) (E : List (List (Fin 4))) : Prop :=
  ∀ (s : Fin 4 → ℝ) (d : ℝ), 0 ≤ d → (∀ j, |s j| ≤ d ^ parabolicWeight j) →
    ∀ {φ : ParabolicSpace → ℝ}, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ w, |remJ s m J φ w| ≤
        (E.map fun ℓ => d ^ indexWeight ℓ * ∫ w, |lineIter (ℓ.map coordDir) φ w|).sum

theorem remBound_intro {m : Fin 4 → ℕ} {J : List (Fin 4)} {E : List (List (Fin 4))}
    (h : ∀ (s : Fin 4 → ℝ) (d : ℝ), 0 ≤ d → (∀ j, |s j| ≤ d ^ parabolicWeight j) →
      ∀ {φ : ParabolicSpace → ℝ}, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        ∫ w, |remJ s m J φ w| ≤
          (E.map fun ℓ => d ^ indexWeight ℓ * ∫ w, |lineIter (ℓ.map coordDir) φ w|).sum) :
    RemBound m J E := h

theorem integral_abs_lineIter_reflect {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g)
    (L : List ParabolicSpace) :
    ∫ w, |lineIter L (fun u => g (-u)) w| = ∫ w, |lineIter L g w| := by
  rw [lineIter_reflect hg]
  have : ∀ w, |(-1 : ℝ) ^ L.length * lineIter L g (-w)| = |lineIter L g (-w)| := fun w => by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  simp_rw [this]
  exact integral_neg_abs (lineIter L g)

theorem integral_abs_remNeg_le {m : Fin 4 → ℕ} {J : List (Fin 4)} {E : List (List (Fin 4))}
    (hE : RemBound m J E) {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) {s : Fin 4 → ℝ} {d : ℝ} (hd : 0 ≤ d)
    (hs : ∀ j, |s j| ≤ d ^ parabolicWeight j) :
    ∫ u, |remJ s m J (fun w => g (-w)) (-u)| ≤
      (E.map fun ℓ => d ^ indexWeight ℓ * ∫ w, |lineIter (ℓ.map coordDir) g w|).sum := by
  have hφ : ContDiff ℝ ∞ fun w => g (-w) := hg.comp contDiff_neg
  have hφc : HasCompactSupport fun w => g (-w) := hgc.comp_homeomorph (Homeomorph.neg _)
  rw [integral_neg_abs (remJ s m J fun w => g (-w))]
  refine (hE s d hd hs hφ hφc).trans (le_of_eq ?_)
  congr 1
  refine List.map_congr_left fun ℓ _ => ?_
  rw [integral_abs_lineIter_reflect hg]

theorem integral_abs_gen_remNeg_le {m : Fin 4 → ℕ} {J : List (Fin 4)} {E : List (List (Fin 4))}
    (hE : RemBound m J E) {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) {s : Fin 4 → ℝ} {d : ℝ} (hd : 0 ≤ d)
    (hs : ∀ j, |s j| ≤ d ^ parabolicWeight j) :
    ∫ u, |parabolicGenerator (fun u => remJ s m J (fun w => g (-w)) (-u)) u| ≤
      (E.map fun ℓ => d ^ indexWeight ℓ *
        ∫ w, |parabolicGenerator (lineIter (ℓ.map coordDir) g) w|).sum := by
  have hφ : ContDiff ℝ ∞ fun w => g (-w) := hg.comp contDiff_neg
  have hRm := contDiff_remJ s m J hφ
  have hLg := contDiff_parabolicGenerator hg
  have hLgc := hasCompactSupport_parabolicGenerator hg hgc
  have e1 : parabolicGenerator (fun u => remJ s m J (fun w => g (-w)) (-u)) =
      fun u => parabolicGenerator (remJ s m J fun w => g (-w)) (-u) := by
    funext u
    have := parabolicGenerator_sub_left hRm 0 u
    simpa only [zero_sub] using this
  have e2 : parabolicGenerator (fun w => g (-w)) = fun w => parabolicGenerator g (-w) := by
    funext w
    have := parabolicGenerator_sub_left hg 0 w
    simpa only [zero_sub] using this
  rw [e1, integral_neg_abs (parabolicGenerator (remJ s m J fun w => g (-w))),
    parabolicGenerator_remJ s m J hφ, e2]
  have hψ : ContDiff ℝ ∞ fun w => parabolicGenerator g (-w) := hLg.comp contDiff_neg
  have hψc : HasCompactSupport fun w => parabolicGenerator g (-w) :=
    hLgc.comp_homeomorph (Homeomorph.neg _)
  refine (hE s d hd hs hψ hψc).trans (le_of_eq ?_)
  congr 1
  refine List.map_congr_left fun ℓ _ => ?_
  rw [integral_abs_lineIter_reflect hLg, parabolicGenerator_lineIter hg]

theorem taylorProfile_L1 {σ : ℝ} {E : List (List (Fin 4))}
    (hE : RemBound (fun _ => ⌈σ⌉₊) (List.finRange 4) E) {g : ParabolicSpace → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) {z : ParabolicSpace} {d : ℝ} (hd : 0 ≤ d)
    (hz : ∀ i, |parabolicCoords z i| ≤ d ^ parabolicWeight i) :
    (∫ u, |taylorProfile g σ z u| ≤
      (E.map fun ℓ => d ^ indexWeight ℓ * ∫ w, |lineIter (ℓ.map coordDir) g w|).sum +
        ∑ k ∈ taylorOut σ, d ^ multiDeg k * ∫ w, |lineIter (multiDirs k) g w|) ∧
    (∫ u, |parabolicGenerator (taylorProfile g σ z) u| ≤
      (E.map fun ℓ => d ^ indexWeight ℓ *
        ∫ w, |parabolicGenerator (lineIter (ℓ.map coordDir) g) w|).sum +
        ∑ k ∈ taylorOut σ, d ^ multiDeg k *
          ∫ w, |parabolicGenerator (lineIter (multiDirs k) g) w|) := by
  set s : Fin 4 → ℝ := fun i => -parabolicCoords z i with hsdef
  have hs : ∀ j, |s j| ≤ d ^ parabolicWeight j := fun j => by
    rw [hsdef]; simp only [abs_neg]; exact hz j
  have hφ : ContDiff ℝ ∞ fun w => g (-w) := hg.comp contDiff_neg
  have hφc : HasCompactSupport fun w => g (-w) := hgc.comp_homeomorph (Homeomorph.neg _)
  set m : Fin 4 → ℕ := fun _ => ⌈σ⌉₊ with hm
  set J := List.finRange 4 with hJ
  set A : ParabolicSpace → ℝ := fun u => remJ s m J (fun w => g (-w)) (-u) with hAdef
  have hAs : ContDiff ℝ ∞ A := (contDiff_remJ s m J hφ).comp contDiff_neg
  have hAc : HasCompactSupport A :=
    (hasCompactSupport_remJ s m J hφc).comp_homeomorph (Homeomorph.neg _)
  set F : (Fin 4 →₀ ℕ) → ParabolicSpace → ℝ := fun k => lineIter (multiDirs k) g with hF
  have hFs : ∀ k, ContDiff ℝ ∞ (F k) := fun k => contDiff_lineIter hg _
  have hFc : ∀ k, HasCompactSupport (F k) := fun k => hasCompactSupport_lineIter hgc _
  set c : (Fin 4 →₀ ℕ) → ℝ := fun k => coeffT (parabolicCoords z) k with hc
  have hH : taylorProfile g σ z = fun u => A u + ∑ k ∈ taylorOut σ, c k * F k u := by
    funext u; exact taylorProfile_eq hg σ z u
  have hAi : Integrable A := hAs.continuous.integrable_of_hasCompactSupport hAc
  have hFi : ∀ k, Integrable (F k) := fun k => (hFs k).continuous.integrable_of_hasCompactSupport (hFc k)
  have hLA := contDiff_parabolicGenerator hAs
  have hLAc := hasCompactSupport_parabolicGenerator hAs hAc
  have hLAi : Integrable (parabolicGenerator A) := hLA.continuous.integrable_of_hasCompactSupport hLAc
  have hLFs : ∀ k, ContDiff ℝ ∞ (parabolicGenerator (F k)) := fun k => contDiff_parabolicGenerator (hFs k)
  have hLFi : ∀ k, Integrable (parabolicGenerator (F k)) := fun k =>
    (hLFs k).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_parabolicGenerator (hFs k) (hFc k))
  refine ⟨?_, ?_⟩
  · rw [hH]
    refine (integral_abs_add_sum_le (taylorOut σ) c hAi fun k _ => hFi k).trans ?_
    refine add_le_add (integral_abs_remNeg_le hE hg hgc hd hs) ?_
    refine Finset.sum_le_sum fun k _ => ?_
    exact mul_le_mul_of_nonneg_right (abs_coeffT_le hz k)
      (integral_nonneg fun _ => abs_nonneg _)
  · have hsum : ContDiff ℝ ∞ fun u => ∑ k ∈ taylorOut σ, c k * F k u :=
      ContDiff.sum fun k _ => contDiff_const.mul (hFs k)
    have hL : parabolicGenerator (taylorProfile g σ z) =
        fun u => parabolicGenerator A u + ∑ k ∈ taylorOut σ, c k * parabolicGenerator (F k) u := by
      rw [hH, parabolicGenerator_add' hAs hsum,
        parabolicGenerator_finset_sum _ fun k _ => contDiff_const.mul (hFs k)]
      funext u
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [parabolicGenerator_const_mul (hFs k)]
    rw [hL]
    refine (integral_abs_add_sum_le (taylorOut σ) c hLAi fun k _ => hLFi k).trans ?_
    refine add_le_add (integral_abs_gen_remNeg_le hE hg hgc hd hs) ?_
    refine Finset.sum_le_sum fun k _ => ?_
    exact mul_le_mul_of_nonneg_right (abs_coeffT_le hz k)
      (integral_nonneg fun _ => abs_nonneg _)

end RegularityStructures

end
