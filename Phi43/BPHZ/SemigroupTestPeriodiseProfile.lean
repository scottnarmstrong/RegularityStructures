/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestMoment
public import Phi43.BPHZ.SemigroupTestProfile
public import Phi43.BPHZ.SemigroupTestUnfold
public import RegularityStructures.BPHZ.SemigroupTestLattice

/-!
# The periodisation of a decaying function on `ℝ⁴` is a semigroup test profile

For a measurable `h : ℝ⁴ → ℝ` the periodisation `g(u) = ∑_{k ∈ ℤ³} h (u₀, torusRep u' + k)` is a
`SemigroupTestProfile` at scale `lam` as soon as

* `∑_k |h (lift_k u)| ≤ B lam⁻⁵` (summable) for every `u` (the sup bound; it follows from a
  pointwise decay `|h z| ≤ C ∏ᵢ (1 + |aᵢ - zᵢ|)⁻²`, `tsum_abs_periodise_le`);
* the absolute moments `∫ |h| ‖y - x‖_𝔰^r ≤ Mom r lam^r` on `ℝ⁴`.

This extends the profile of the periodised semigroup kernel to kernels with polynomial weights,
for instance `Q_t(x, y) (y - x)ᵢ / lam`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

/-- The lattice sum of a quadratically decaying function is bounded uniformly. -/
theorem tsum_abs_periodise_le :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {h : ParabolicSpace → ℝ} {C : ℝ} {a0 : Fin 3 → ℝ}, 0 ≤ C →
      (∀ z : ParabolicSpace, |h z| ≤ C * ∏ i, ((1 + |a0 i - z.2 i|) ^ 2)⁻¹) →
      ∀ u : SpaceTime,
        Summable (fun k : Fin 3 → ℤ => |h (u.1, torusRep u.2 + fun i => (k i : ℝ))|) ∧
          ∑' k : Fin 3 → ℤ, |h (u.1, torusRep u.2 + fun i => (k i : ℝ))| ≤ C * L := by
  obtain ⟨L, hL0, hL⟩ := exists_lattice_sum_le
  refine ⟨L, hL0, fun {h C a0} hC hdec u => ?_⟩
  set a : Fin 3 → ℝ := fun i => a0 i - torusRep u.2 i with ha
  set P : (Fin 3 → ℤ) → ℝ := fun k => ∏ i, ((1 + |a i + (k i : ℝ)|) ^ 2)⁻¹ with hP
  have hterm : ∀ k : Fin 3 → ℤ,
      |h (u.1, torusRep u.2 + fun i => (k i : ℝ))| ≤ C * P (-k) := by
    intro k
    refine (hdec _).trans (le_of_eq ?_)
    simp only [hP, ha, Pi.add_apply, Pi.neg_apply, Int.cast_neg]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show a0 i - (torusRep u.2 i + (k i : ℝ)) = a0 i - torusRep u.2 i + -(k i : ℝ) by ring]
  obtain ⟨hPs, hPL⟩ := hL a
  have hPs' : Summable (fun k => P (-k)) := ((Equiv.neg (Fin 3 → ℤ)).summable_iff (f := P)).2 hPs
  have hPt : ∑' k, P (-k) = ∑' k, P k := (Equiv.neg (Fin 3 → ℤ)).tsum_eq P
  have hsum : Summable (fun k : Fin 3 → ℤ =>
      |h (u.1, torusRep u.2 + fun i => (k i : ℝ))|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hterm (hPs'.mul_left _)
  refine ⟨hsum, ?_⟩
  calc ∑' k : Fin 3 → ℤ, |h (u.1, torusRep u.2 + fun i => (k i : ℝ))|
      ≤ ∑' k : Fin 3 → ℤ, C * P (-k) := hsum.tsum_le_tsum hterm (hPs'.mul_left _)
    _ = C * ∑' k : Fin 3 → ℤ, P k := by rw [tsum_mul_left, hPt]
    _ ≤ C * L := mul_le_mul_of_nonneg_left hPL hC

/-- The periodisation of a measurable `h : ℝ⁴ → ℝ` with a lattice sup bound and `ℝ⁴`-moments is a
semigroup test profile. -/
theorem semigroupTestProfile_periodise {x : ParabolicSpace} {lam B : ℝ} {Mom : ℝ → ℝ}
    {h : ParabolicSpace → ℝ} (hm : Measurable h)
    (hsup : ∀ u : SpaceTime,
      Summable (fun k : Fin 3 → ℤ => |h (u.1, torusRep u.2 + fun i => (k i : ℝ))|) ∧
        ∑' k : Fin 3 → ℤ, |h (u.1, torusRep u.2 + fun i => (k i : ℝ))| ≤ B * (lam ^ 5)⁻¹)
    (hint : ∀ r : ℝ, 0 ≤ r → Integrable (fun y => |h y| * parabolicNorm (y - x) ^ r))
    (hmom : ∀ r : ℝ, 0 ≤ r → ∫ y, |h y| * parabolicNorm (y - x) ^ r ≤ Mom r * lam ^ r) :
    SemigroupTestProfile (Phi43.spaceTimeProj x) lam B Mom
      (fun u : SpaceTime => ∑' k : Fin 3 → ℤ, h (u.1, torusRep u.2 + fun i => (k i : ℝ))) := by
  have hlift : Measurable (fun (u : SpaceTime) (k : Fin 3 → ℤ) =>
      h (u.1, torusRep u.2 + fun i => (k i : ℝ))) := by
    refine measurable_pi_iff.2 fun k => hm.comp ?_
    exact measurable_fst.prodMk ((measurable_torusRep.comp measurable_snd).add measurable_const)
  have hgm : Measurable (fun u : SpaceTime => ∑' k : Fin 3 → ℤ,
      h (u.1, torusRep u.2 + fun i => (k i : ℝ))) := Measurable.tsum fun k => (measurable_pi_apply k).comp hlift
  refine ⟨hgm, fun u => ?_, fun r hr => ?_, fun r hr => ?_⟩
  · obtain ⟨hs, hb⟩ := hsup u
    have h1 : ‖∑' k : Fin 3 → ℤ, h (u.1, torusRep u.2 + fun i => (k i : ℝ))‖ ≤
        ∑' k : Fin 3 → ℤ, ‖h (u.1, torusRep u.2 + fun i => (k i : ℝ))‖ :=
      norm_tsum_le_tsum_norm (by simpa [Real.norm_eq_abs] using hs)
    simp only [Real.norm_eq_abs] at h1
    exact h1.trans hb
  all_goals
    set Θ : ParabolicSpace → ℝ := fun y => |h y| * parabolicNorm (y - x) ^ r with hΘ
    have hΘi : Integrable Θ := hint r hr
    have hΘ0 : ∀ y, 0 ≤ Θ y := fun y => mul_nonneg (abs_nonneg _)
      (Real.rpow_nonneg (parabolicNorm_nonneg _) _)
    have hΘm : Measurable Θ :=
      (continuous_abs.measurable.comp hm).mul
        ((continuous_parabolicNorm.measurable.comp (measurable_id.sub measurable_const)).pow_const _)
    set f : SpaceTime → ℝ := fun u => |∑' k : Fin 3 → ℤ, h (u.1, torusRep u.2 + fun i => (k i : ℝ))| *
      torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r with hf
    have hf0 : ∀ u, 0 ≤ f u := fun u => mul_nonneg (abs_nonneg _)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
    have hfm : Measurable f :=
      (continuous_abs.measurable.comp hgm).mul
        ((Phi43.measurable_torusParabolicSize.comp (measurable_id.sub measurable_const)).pow_const _)
    have hpt : ∀ u : SpaceTime, ENNReal.ofReal (f u) ≤ ∑' k : Fin 3 → ℤ,
        ENNReal.ofReal (Θ (u.1, torusRep u.2 + fun i => (k i : ℝ))) := by
      intro u
      have hsize : ∀ k : Fin 3 → ℤ, torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r ≤
          parabolicNorm ((u.1, torusRep u.2 + fun i => (k i : ℝ)) - x) ^ r := by
        intro k
        refine Real.rpow_le_rpow (torusParabolicSize_nonneg _) ?_ hr
        have h := torusParabolicSize_spaceTimeProj_le ((u.1, torusRep u.2 + fun i => (k i : ℝ)) - x)
        rwa [Phi43.spaceTimeProj_sub, spaceTimeProj_semigroup_lift] at h
      calc ENNReal.ofReal (f u)
          = ‖∑' k : Fin 3 → ℤ, h (u.1, torusRep u.2 + fun i => (k i : ℝ))‖ₑ *
              ENNReal.ofReal (torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r) := by
            rw [hf, ENNReal.ofReal_mul (abs_nonneg _), Real.enorm_eq_ofReal_abs]
        _ ≤ (∑' k : Fin 3 → ℤ, ‖h (u.1, torusRep u.2 + fun i => (k i : ℝ))‖ₑ) *
              ENNReal.ofReal (torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r) := by
            gcongr; exact enorm_tsum_le_tsum_enorm
        _ = ∑' k : Fin 3 → ℤ, ‖h (u.1, torusRep u.2 + fun i => (k i : ℝ))‖ₑ *
              ENNReal.ofReal (torusParabolicSize (u - Phi43.spaceTimeProj x) ^ r) :=
            ENNReal.tsum_mul_right.symm
        _ ≤ _ := by
            refine ENNReal.tsum_le_tsum fun k => ?_
            rw [Real.enorm_eq_ofReal_abs]
            show _ ≤ ENNReal.ofReal (|h (u.1, torusRep u.2 + fun i => (k i : ℝ))| *
                parabolicNorm ((u.1, torusRep u.2 + fun i => (k i : ℝ)) - x) ^ r)
            rw [ENNReal.ofReal_mul (abs_nonneg _)]
            exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hsize k))
    have hlint : ∫⁻ u : SpaceTime, ENNReal.ofReal (f u) ≤ ENNReal.ofReal (∫ y, Θ y) := by
      calc ∫⁻ u : SpaceTime, ENNReal.ofReal (f u)
          ≤ ∫⁻ u : SpaceTime, ∑' k : Fin 3 → ℤ,
              ENNReal.ofReal (Θ (u.1, torusRep u.2 + fun i => (k i : ℝ))) :=
            lintegral_mono hpt
        _ = ∫⁻ y : ParabolicSpace, ENNReal.ofReal (Θ y) :=
            (Phi43.lintegral_eq_lintegral_spaceTime_tsum
              (H := fun y => ENNReal.ofReal (Θ y)) hΘm.ennreal_ofReal).symm
        _ = ENNReal.ofReal (∫ y, Θ y) :=
            (ofReal_integral_eq_lintegral_ofReal hΘi (Filter.Eventually.of_forall hΘ0)).symm
    have hmo : ∫ y, Θ y ≤ Mom r * lam ^ r := hmom r hr
    have hbd : 0 ≤ Mom r * lam ^ r := (integral_nonneg hΘ0).trans hmo
    have hlt : ∫⁻ u : SpaceTime, ENNReal.ofReal (f u) < ⊤ :=
      lt_of_le_of_lt (hlint.trans (ENNReal.ofReal_le_ofReal hmo)) ENNReal.ofReal_lt_top
    have hfi : Integrable f :=
      ⟨hfm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall hf0)).2 hlt⟩
  · exact hfi
  · have h1 : ENNReal.ofReal (∫ u, f u) ≤ ENNReal.ofReal (Mom r * lam ^ r) := by
      rw [ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0)]
      exact hlint.trans (ENNReal.ofReal_le_ofReal hmo)
    exact (ENNReal.ofReal_le_ofReal_iff hbd).1 h1

/-- **Periodisation for a general weight.**  For measurable `G` on `ℝ × T³` and measurable
`h` on `ℝ⁴` such that `h (G ∘ proj)` is integrable,
`∫_{ℝ⁴} h(y) G(proj y) dy = ∫_{ℝ × T³} (∑_k h (lift_k u)) G(u) du`, with integrable right-hand
integrand. -/
theorem integral_mul_comp_proj_periodise {h : ParabolicSpace → ℝ} {G : SpaceTime → ℝ}
    (hh : Measurable h) (hG : Measurable G)
    (hint : Integrable (fun y : ParabolicSpace => h y * G (Phi43.spaceTimeProj y))) :
    Integrable (fun u : SpaceTime =>
        (∑' k : Fin 3 → ℤ, h (u.1, torusRep u.2 + fun i => (k i : ℝ))) * G u) ∧
      ∫ y : ParabolicSpace, h y * G (Phi43.spaceTimeProj y) =
        ∫ u : SpaceTime,
          (∑' k : Fin 3 → ℤ, h (u.1, torusRep u.2 + fun i => (k i : ℝ))) * G u := by
  set H : ParabolicSpace → ℝ := fun y => h y * G (Phi43.spaceTimeProj y) with hH
  have hHm : Measurable H := hh.mul (hG.comp Phi43.continuous_spaceTimeProj.measurable)
  have hlift : ∀ q : SpaceTime, ∑' k : Fin 3 → ℤ, H (q.1, torusRep q.2 + fun i => (k i : ℝ)) =
      (∑' k : Fin 3 → ℤ, h (q.1, torusRep q.2 + fun i => (k i : ℝ))) * G q := by
    intro q
    rw [← tsum_mul_right]
    refine tsum_congr fun k => ?_
    simp only [hH, spaceTimeProj_semigroup_lift]
  have hHt : Measurable (fun q : SpaceTime =>
      ∑' k : Fin 3 → ℤ, H (q.1, torusRep q.2 + fun i => (k i : ℝ))) :=
    Measurable.tsum fun k => hHm.comp
      (measurable_fst.prodMk ((measurable_torusRep.comp measurable_snd).add measurable_const))
  have hfin : ∫⁻ q : SpaceTime, ‖∑' k : Fin 3 → ℤ, H (q.1, torusRep q.2 + fun i => (k i : ℝ))‖ₑ <
      ⊤ := by
    calc ∫⁻ q : SpaceTime, ‖∑' k : Fin 3 → ℤ, H (q.1, torusRep q.2 + fun i => (k i : ℝ))‖ₑ
        ≤ ∫⁻ q : SpaceTime, ∑' k : Fin 3 → ℤ,
            ‖H (q.1, torusRep q.2 + fun i => (k i : ℝ))‖ₑ :=
          lintegral_mono fun q => enorm_tsum_le_tsum_enorm
      _ = ∫⁻ y : ParabolicSpace, ‖H y‖ₑ :=
          (Phi43.lintegral_eq_lintegral_spaceTime_tsum hHm.enorm).symm
      _ < ⊤ := hint.2
  have hIntT : Integrable (fun u : SpaceTime =>
      (∑' k : Fin 3 → ℤ, h (u.1, torusRep u.2 + fun i => (k i : ℝ))) * G u) := by
    have h1 : Integrable (fun q : SpaceTime =>
        ∑' k : Fin 3 → ℤ, H (q.1, torusRep q.2 + fun i => (k i : ℝ))) :=
      ⟨hHt.aestronglyMeasurable, hfin⟩
    exact h1.congr (Filter.Eventually.of_forall hlift)
  refine ⟨hIntT, ?_⟩
  have hint' : Integrable H (volume.prod volume : Measure (ℝ × (Fin 3 → ℝ))) := by
    rwa [← Measure.volume_eq_prod]
  have hIntT' : Integrable (fun u : SpaceTime =>
      (∑' k : Fin 3 → ℤ, h (u.1, torusRep u.2 + fun i => (k i : ℝ))) * G u)
      (volume.prod volume : Measure (ℝ × Torus3)) := by
    rwa [← Measure.volume_eq_prod]
  rw [show (∫ y : ParabolicSpace, H y) = ∫ t' : ℝ, ∫ z : Fin 3 → ℝ, H (t', z) by
      rw [Measure.volume_eq_prod]; exact integral_prod _ hint',
    show (∫ u : SpaceTime, (∑' k : Fin 3 → ℤ, h (u.1, torusRep u.2 + fun i => (k i : ℝ))) * G u) =
      ∫ t' : ℝ, ∫ u : Torus3,
        (∑' k : Fin 3 → ℤ, h (t', torusRep u + fun i => (k i : ℝ))) * G (t', u) by
      rw [Measure.volume_eq_prod]; exact integral_prod _ hIntT']
  refine integral_congr_ae ?_
  filter_upwards [hint'.prod_right_ae] with t' ht'
  rw [Phi43.integral_eq_integral_torus_tsum (H := fun z => H (t', z)) ht']
  exact integral_congr_ae (Filter.Eventually.of_forall fun u => hlift (t', u))

end RegularityStructures

end
