/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaDiffUnitPair
public import RegularityStructures.Statements.Defs.IsContinuousRandomModelWithFieldsOn
import Mathlib.Tactic.Linarith

/-!
# The unit-box Gamma-difference bound from the source bounds

`randomModel_gammaDiffUnitBoxBound` (the unit-box case of the Kolmogorov criterion for models,
before compact rescaling): for two continuous random models on a subset `S` of the unit box whose
Gamma maps satisfy the source bounds (pathwise bounds on the deterministic sector `DΓ`, `q`-th
moment bounds with reserve `κ̄` off it, and the corresponding bounds for the difference with the
factor `C ε^θ`), the Gamma difference is bounded on `S` by a random constant `B` with
`∫ B^p ≤ K (C ε^θ)^p`, where `q` is chosen before `C̄` and `K` depends only on `C̄`.

Each moment-controlled coordinate is bounded by the envelope of
`gammaDiffUnitPair_envelope`; the deterministic coordinates are bounded pathwise by `C ε^θ`.
The envelope `B` is the sum of these, and its `p`-th moment follows from its `m`-th moment
(`m ≥ p`) by Jensen's inequality.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RegularityStructures

private theorem gammaDiffUnitBox_exists_rho {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒯 : RegularityStructure ι) (κ : ℝ) (hκ : 0 < κ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < κ ∧ ∀ a b : ι, 𝒯.deg b < 𝒯.deg a → ρ < 𝒯.deg a - 𝒯.deg b := by
  classical
  let s : Finset ℝ := insert (κ / 2) ((Finset.univ : Finset (ι × ι)).image
    (fun ab => if 𝒯.deg ab.2 < 𝒯.deg ab.1 then (𝒯.deg ab.1 - 𝒯.deg ab.2) / 2 else 1))
  have hs : s.Nonempty := Finset.insert_nonempty _ _
  have hpos : ∀ x ∈ s, 0 < x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · linarith
    · obtain ⟨ab, -, rfl⟩ := Finset.mem_image.mp hx
      split_ifs with h
      · linarith
      · norm_num
  refine ⟨s.min' hs, hpos _ (Finset.min'_mem s hs), ?_, ?_⟩
  · have := s.min'_le _ (Finset.mem_insert_self _ _)
    linarith
  · intro a b hab
    have hm : (𝒯.deg a - 𝒯.deg b) / 2 ∈ s :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, by simp [hab]⟩)
    have := s.min'_le _ hm
    linarith

private theorem gammaDiffUnitBox_exists_order (p : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ m : ℕ, p ≤ m ∧ 1 ≤ m ∧ 20 < (m : ℝ) * ρ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max ((p : ℝ) + 1) (20 / ρ))
  have h1 : (p : ℝ) + 1 < n := lt_of_le_of_lt (le_max_left _ _) hn
  have h2 : 20 / ρ < n := lt_of_le_of_lt (le_max_right _ _) hn
  refine ⟨n, ?_, ?_, (div_lt_iff₀ hρ).mp h2⟩
  · exact_mod_cast (show (p : ℝ) ≤ n by linarith)
  · exact_mod_cast (show (1 : ℝ) ≤ n by linarith [Nat.cast_nonneg (α := ℝ) p])

private theorem gammaDiffUnitBox_moment_le_of_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (f : Ω → ℝ≥0∞) (hf : AEMeasurable f P)
    {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) {A : ℝ≥0∞} (hA : ∫⁻ ω, f ω ^ q ∂P ≤ A ^ q) :
    ∫⁻ ω, f ω ^ p ∂P ≤ A ^ p := by
  by_cases hAtop : A = ∞
  · rw [hAtop, ENNReal.top_pow (by omega)]
    exact le_top
  have hAq : A ^ q ≠ ∞ := ENNReal.pow_ne_top hAtop
  have htop : ∀ᵐ ω ∂P, f ω ≠ ∞ := by
    filter_upwards [ae_lt_top' (hf.pow_const q) (ne_top_of_le_ne_top hAq hA)] with ω hω
    intro hfω
    rw [hfω, ENNReal.top_pow (by omega)] at hω
    exact lt_irrefl _ hω
  let g : Ω → ℝ := fun ω => (f ω).toReal
  have hg : AEMeasurable g P := hf.ennreal_toReal
  have hgeq : ∀ᵐ ω ∂P, ‖g ω‖ₑ = f ω := by
    filter_upwards [htop] with ω hω
    simp [g, Real.enorm_of_nonneg, ENNReal.toReal_nonneg, hω]
  have hpow (n : ℕ) : (fun ω => ‖g ω‖ₑ ^ n) =ᵐ[P] fun ω => f ω ^ n :=
    hgeq.mono fun ω hω => by simp only [hω]
  have hreal : ∫⁻ ω, ‖g ω‖ₑ ^ q ∂P ≤ A ^ q := (lintegral_congr_ae (hpow q)).trans_le hA
  exact (lintegral_congr_ae (hpow p)).symm.trans_le
    (lintegral_enorm_pow_le_of_nat_le hg hp hpq hreal)

private theorem gammaDiffUnitBox_eq_of_parabolicNorm_sub_eq_zero {x y : ParabolicSpace}
    (h : parabolicNorm (x - y) = 0) : x = y := by
  have h0 := Real.sqrt_nonneg |(x - y).1|
  have h1 : 0 ≤ ∑ i, |(x - y).2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h2 : Real.sqrt |(x - y).1| = 0 := by unfold parabolicNorm at h; linarith
  have h3 : ∑ i, |(x - y).2 i| = 0 := by unfold parabolicNorm at h; linarith
  have hz1 : (x - y).1 = 0 := abs_eq_zero.1 ((Real.sqrt_eq_zero (abs_nonneg _)).1 h2)
  have hz2 : ∀ i, (x - y).2 i = 0 := fun i => abs_eq_zero.1
    ((Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => abs_nonneg _)).1 h3 i (Finset.mem_univ i))
  exact sub_eq_zero.1 (Prod.ext hz1 (funext hz2))

/-- **The unit-box Gamma-difference bound from the source bounds.**  The moment order `q`
is chosen before the upper bound `C̄`, and the constant `K` depends only on `C̄`. -/
theorem randomModel_gammaDiffUnitBoxBound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒯 : RegularityStructures.RegularityStructure ι) (γ κbar θ : ℝ)
    (hκbar : 0 < κbar) (_hθ : 0 ≤ θ)
    (DΓ : Set (ι × ι)) (S : Set RegularityStructures.ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Set.Icc (0 : ℝ) 1)
    (p : ℕ) (hp : 1 ≤ p) :
    ∃ q : ℕ, p ≤ q ∧ ∀ Cbar : ℝ, ∃ K : ℝ, 0 ≤ K ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure P]
      (Z₁ Z₂ : Ω → RegularityStructures.Model 𝒯
        RegularityStructures.parabolicSemigroup)
      (C ε : ℝ), 0 ≤ C → C ≤ Cbar → 0 ≤ ε →
      RegularityStructures.IsContinuousRandomModelWithFieldsOn Z₁ S →
      RegularityStructures.IsContinuousRandomModelWithFieldsOn Z₂ S →
      (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → RegularityStructures.Model 𝒯
          RegularityStructures.parabolicSemigroup)),
        ∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ ω,
          ∀ x y : RegularityStructures.ParabolicSpace,
          |(Z ω).gammaMap y x (Pi.single i 1) j| ≤
            C * RegularityStructures.parabolicSemigroup.scaleDist y x ^
              (𝒯.deg i - 𝒯.deg j)) →
      (∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ ω,
          ∀ x y : RegularityStructures.ParabolicSpace,
          |(Z₁ ω).gammaMap y x (Pi.single i 1) j -
              (Z₂ ω).gammaMap y x (Pi.single i 1) j| ≤
            C * ε ^ θ * RegularityStructures.parabolicSemigroup.scaleDist y x ^
              (𝒯.deg i - 𝒯.deg j)) →
      (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → RegularityStructures.Model 𝒯
          RegularityStructures.parabolicSemigroup)),
        ∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
          ∀ x y : RegularityStructures.ParabolicSpace,
          ∫⁻ ω, ‖(Z ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P ≤
            ENNReal.ofReal (C * RegularityStructures.parabolicSemigroup.scaleDist y x ^
              (𝒯.deg i - 𝒯.deg j + κbar)) ^ q) →
      (∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
          ∀ x y : RegularityStructures.ParabolicSpace,
          ∫⁻ ω, ‖(Z₁ ω).gammaMap y x (Pi.single i 1) j -
              (Z₂ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P ≤
            ENNReal.ofReal (C * ε ^ θ *
              RegularityStructures.parabolicSemigroup.scaleDist y x ^
                (𝒯.deg i - 𝒯.deg j + κbar)) ^ q) →
      ∃ B : Ω → ℝ≥0∞, AEMeasurable B P ∧
        (∀ᵐ ω ∂P, B ω ≠ ∞) ∧
        (∫⁻ ω, B ω ^ p ∂P ≤
          ENNReal.ofReal (K * (C * ε ^ θ) ^ p)) ∧
        (∀ᵐ ω ∂P,
          (Z₁ ω).GammaDiffBoundOn (Z₂ ω) γ (B ω).toNNReal S) := by
  classical
  obtain ⟨ρ, hρ, hρκ, hρgap⟩ := gammaDiffUnitBox_exists_rho 𝒯 κbar hκbar
  obtain ⟨m, hpm, hm1, hmρ⟩ := gammaDiffUnitBox_exists_order p hρ
  refine ⟨2 * m, by omega, fun Cbar => ?_⟩
  choose K₀ hK₀top hK₀ using fun ij : ι × ι => gammaDiffUnitPair_envelope S hbox DΓ γ
    κbar ρ Cbar ij.1 ij.2 (q := 2 * m) hm1 le_rfl hκbar hρ hρκ hρgap hmρ
  set Kt : ℝ≥0∞ := (Fintype.card (Option (ι × ι)) : ℝ≥0∞) ^ ((m : ℝ) - 1) *
    (1 + ∑ ij : ι × ι, K₀ ij) with hKtdef
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hKt : Kt ≠ ∞ := by
    rw [hKtdef]
    refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by
      linarith [show (1 : ℝ) ≤ m by exact_mod_cast hm1]) (ENNReal.natCast_ne_top _)) ?_
    exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
      ENNReal.sum_ne_top.2 fun ij _ => hK₀top ij⟩
  have hKtp : (Kt ^ (1 / (m : ℝ))) ^ p ≠ ∞ :=
    ENNReal.pow_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hKt)
  refine ⟨((Kt ^ (1 / (m : ℝ))) ^ p).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro Ω _ P _ Z₁ Z₂ C ε hC hCbar hε hZ₁ hZ₂ hdet hdiff hann hdiffN
  have hZ₁mem : Z₁ ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)) := Set.mem_insert _ _
  have hZ₂mem : Z₂ ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)) :=
    Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hδ : 0 ≤ ε ^ θ := Real.rpow_nonneg hε θ
  set c : ℝ := C * ε ^ θ with hcdef
  have hc : 0 ≤ c := mul_nonneg hC hδ
  have hm₁ : ∀ x y a b, AEMeasurable
      (fun ω => ((Z₁ ω).gammaMap y x (Pi.single a 1) b)) P :=
    fun x y a b => (hZ₁.1.2.1 a b x y).aemeasurable
  have hm₂ : ∀ x y a b, AEMeasurable
      (fun ω => ((Z₂ ω).gammaMap y x (Pi.single a 1) b)) P :=
    fun x y a b => (hZ₂.1.2.1 a b x y).aemeasurable
  have hcont : ∀ (a b : ι) (ω : Ω), Continuous (fun z : S × S =>
      (Z₁ ω).gammaMap (z.1 : ParabolicSpace) z.2 (Pi.single a 1) b -
        (Z₂ ω).gammaMap (z.1 : ParabolicSpace) z.2 (Pi.single a 1) b) := by
    intro a b ω
    have hsw : Continuous (fun z : S × S => ((z.2 : ParabolicSpace), (z.1 : ParabolicSpace))) :=
      (continuous_subtype_val.comp continuous_snd).prodMk
        (continuous_subtype_val.comp continuous_fst)
    have hmaps : ∀ z : S × S, ((z.2 : ParabolicSpace), (z.1 : ParabolicSpace)) ∈ S ×ˢ S :=
      fun z => ⟨z.2.2, z.1.2⟩
    exact ((hZ₁.1.2.2.2 ω a b).comp_continuous hsw hmaps).sub
      ((hZ₂.1.2.2.2 ω a b).comp_continuous hsw hmaps)
  -- the coordinate envelopes
  have hE : ∀ ij : ι × ι, ∃ E : Ω → ℝ≥0∞, AEMeasurable E P ∧
      (∫⁻ ω, E ω ^ m ∂P ≤ K₀ ij * ENNReal.ofReal c ^ m) ∧
      ∀ᵐ ω ∂P, ((ij.1, ij.2) ∉ DΓ → 𝒯.deg ij.1 < γ → 𝒯.deg ij.2 < 𝒯.deg ij.1 →
        ∀ x y : S, 0 < parabolicNorm ((x : ParabolicSpace) - y) →
          ‖(Z₁ ω).gammaMap (x : ParabolicSpace) y (Pi.single ij.1 1) ij.2 -
              (Z₂ ω).gammaMap (x : ParabolicSpace) y (Pi.single ij.1 1) ij.2‖ₑ ≤
            E ω * ENNReal.ofReal (parabolicNorm ((x : ParabolicSpace) - y)) ^
              (𝒯.deg ij.1 - 𝒯.deg ij.2)) := by
    intro ij
    by_cases hcond : (ij.1, ij.2) ∉ DΓ ∧ 𝒯.deg ij.1 < γ ∧ 𝒯.deg ij.2 < 𝒯.deg ij.1
    · obtain ⟨E, hEm, hEmom, hEpt⟩ := hK₀ ij hcond.1 hcond.2.1 hcond.2.2 P Z₁ Z₂ C (ε ^ θ)
        hC hCbar hδ hm₁ hm₂ (hcont ij.1 ij.2)
        (fun a b hab ha hb ω x y => hdet Z₁ hZ₁mem a b hab ha hb ω x y)
        (fun a b hab ha hb ω x y => hdet Z₂ hZ₂mem a b hab ha hb ω x y)
        (fun a b hab ha hb x y => hann Z₁ hZ₁mem a b hab ha hb x y)
        (fun a b hab ha hb x y => hann Z₂ hZ₂mem a b hab ha hb x y)
        hdiff hdiffN
      exact ⟨E, hEm, hEmom, hEpt.mono fun ω hω _ _ _ => hω⟩
    · refine ⟨fun _ => 0, aemeasurable_const, ?_,
        Filter.Eventually.of_forall fun ω h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hcond⟩
      simp [zero_pow (by omega : m ≠ 0)]
  choose E hEmeas hEmom hEpt using hE
  -- the total envelope
  let V : Ω → Option (ι × ι) → ℝ≥0∞ := fun ω o => o.elim (ENNReal.ofReal c) (fun ij => E ij ω)
  have hVmeas : ∀ o, AEMeasurable (fun ω => V ω o) P := by
    intro o
    cases o with
    | none => exact aemeasurable_const
    | some ij => exact hEmeas ij
  let b : Option (ι × ι) → ℝ≥0∞ := fun o =>
    o.elim (ENNReal.ofReal c ^ m) (fun ij => K₀ ij * ENNReal.ofReal c ^ m)
  have hb : ∀ o, ∫⁻ ω, V ω o ^ m ∂P ≤ b o := by
    intro o
    cases o with
    | none => simp [V, b]
    | some ij => exact hEmom ij
  set B : Ω → ℝ≥0∞ := finiteFamilyEnvelope V with hBdef
  have hBmeas : AEMeasurable B P := finiteFamilyEnvelope_aemeasurable hVmeas
  have hBmom : ∫⁻ ω, B ω ^ m ∂P ≤ Kt * ENNReal.ofReal c ^ m := by
    refine (finiteFamilyEnvelope_moment_le_of_pointwise hm1 hVmeas hb).trans_eq ?_
    rw [Fintype.sum_option, hKtdef]
    simp only [b, Option.elim, ← Finset.sum_mul]
    ring
  have hBtop : ∀ᵐ ω ∂P, B ω ≠ ∞ := by
    have hfin : Kt * ENNReal.ofReal c ^ m ≠ ∞ :=
      ENNReal.mul_ne_top hKt (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    filter_upwards [ae_lt_top' (hBmeas.pow_const m) (ne_top_of_le_ne_top hfin hBmom)] with ω hω
    intro hBω
    rw [hBω, ENNReal.top_pow (by omega)] at hω
    exact lt_irrefl _ hω
  have hcomp : ∀ ω ij, E ij ω ≤ B ω := fun ω ij =>
    Finset.single_le_sum (f := fun o => V ω o) (fun _ _ => bot_le)
      (Finset.mem_univ (some ij))
  have hcB : ∀ ω, ENNReal.ofReal c ≤ B ω := fun ω =>
    Finset.single_le_sum (f := fun o => V ω o) (fun _ _ => bot_le) (Finset.mem_univ none)
  refine ⟨B, hBmeas, hBtop, ?_, ?_⟩
  · -- the `p`-th moment, by Jensen from the `m`-th moment
    have hA : ∫⁻ ω, B ω ^ m ∂P ≤ (Kt ^ (1 / (m : ℝ)) * ENNReal.ofReal c) ^ m := by
      have hroot : (Kt ^ (1 / (m : ℝ))) ^ m = Kt := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, one_div,
          inv_mul_cancel₀ hm0.ne', ENNReal.rpow_one]
      rw [mul_pow, hroot]
      exact hBmom
    refine (gammaDiffUnitBox_moment_le_of_le B hBmeas hp hpm hA).trans_eq ?_
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hKtp,
      ENNReal.ofReal_pow hc, mul_pow]
  · -- the pathwise bound
    filter_upwards [ae_all_iff.2 hEpt, hBtop] with ω hω hBω
    unfold Model.GammaDiffBoundOn
    intro i j hi hj x hx y hy
    have hβ : 0 ≤ 𝒯.deg i - 𝒯.deg j := by linarith
    have hsd : 0 ≤ parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j) :=
      Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg _ _) _
    change _ ≤ (B ω).toReal * _
    by_cases hD : (i, j) ∈ DΓ
    · have hcB' : c ≤ (B ω).toReal := (ENNReal.ofReal_le_iff_le_toReal hBω).1 (hcB ω)
      exact (hdiff i j hD hi hj ω x y).trans (mul_le_mul_of_nonneg_right hcB' hsd)
    by_cases hxy : y = x
    · subst hxy
      rw [(Z₁ ω).gammaMap_self, (Z₂ ω).gammaMap_self, sub_self, abs_zero]
      exact mul_nonneg ENNReal.toReal_nonneg hsd
    have hpos : 0 < parabolicNorm (y - x) := lt_of_le_of_ne (parabolicNorm_nonneg _)
      (fun h => hxy (gammaDiffUnitBox_eq_of_parabolicNorm_sub_eq_zero h.symm))
    have h := hω (i, j) hD hi hj ⟨y, hy⟩ ⟨x, hx⟩ hpos
    have hfin : B ω * ENNReal.ofReal (parabolicNorm (y - x)) ^ (𝒯.deg i - 𝒯.deg j) ≠ ∞ :=
      ENNReal.mul_ne_top hBω (ENNReal.rpow_ne_top_of_nonneg hβ ENNReal.ofReal_ne_top)
    have h2 : ENNReal.ofReal |(Z₁ ω).gammaMap y x (Pi.single i 1) j -
        (Z₂ ω).gammaMap y x (Pi.single i 1) j| ≤
        B ω * ENNReal.ofReal (parabolicNorm (y - x)) ^ (𝒯.deg i - 𝒯.deg j) := by
      rw [← Real.enorm_eq_ofReal_abs]
      exact h.trans (mul_le_mul_of_nonneg_right (hcomp ω (i, j)) (by positivity))
    have h3 := (ENNReal.ofReal_le_iff_le_toReal hfin).1 h2
    rw [ENNReal.toReal_mul, ENNReal.ofReal_rpow_of_nonneg (parabolicNorm_nonneg _) hβ,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (parabolicNorm_nonneg _) _)] at h3
    exact h3

end RegularityStructures

end
