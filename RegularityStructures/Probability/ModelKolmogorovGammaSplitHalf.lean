/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaSplitInduction
public import RegularityStructures.Probability.ModelKolmogorovGammaSplitCompletion
public import RegularityStructures.Probability.ModelKolmogorovGammaSplitConstants
public import RegularityStructures.Probability.ModelKolmogorovGammaProductNet
public import RegularityStructures.Probability.ModelKolmogorovGammaMeasurability
public import RegularityStructures.Probability.ModelKolmogorovMomentOrder
public import RegularityStructures.Probability.ModelKolmogorovHSCompactRescale
public import RegularityStructures.Statements.Defs.IsContinuousRandomModelWithFieldsOn
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.Linarith
public import Mathlib.Order.CompletePartialOrder
public import RegularityStructures.Probability.ModelKolmogorovAnnealed

/-!
# The finite-sector Gamma induction with the deterministic split

This module supplies the single-model Gamma half of the Kolmogorov criterion for models. The annular
telescope keeps the two deterministic Chen factors pathwise, while the complementary channels use
the source moment reserve.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒯 : RegularityStructure ι}

theorem gammaSplit_uniform_delta
    (𝒯 : RegularityStructure ι) (κ : ℝ) (hκ : 0 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ κ / 2 ∧
      ∀ i j, 𝒯.deg j < 𝒯.deg i →
        ∀ k, 𝒯.deg j < 𝒯.deg k → 𝒯.deg k < 𝒯.deg i →
          δ ≤ (𝒯.deg k - 𝒯.deg j) / 2 ∧
          δ ≤ (𝒯.deg i - 𝒯.deg k) / 2 := by
  classical
  let s : Finset ℝ := insert (κ / 2)
    ((Finset.univ : Finset (ι × ι)).image
      (fun ij => if 𝒯.deg ij.2 < 𝒯.deg ij.1 then
        (𝒯.deg ij.1 - 𝒯.deg ij.2) / 2 else 1))
  have hs : s.Nonempty := Finset.insert_nonempty _ _
  let δ : ℝ := s.min' hs
  have hmem_pos : ∀ x ∈ s, 0 < x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · linarith
    · obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hx
      by_cases h : 𝒯.deg ij.2 < 𝒯.deg ij.1
      · simp [h]
      · simp [h]
  have hδpos : 0 < δ := hmem_pos δ (Finset.min'_mem s hs)
  refine ⟨δ, hδpos, s.min'_le _ (Finset.mem_insert_self _ _), ?_⟩
  intro i j hji k hjk hki
  constructor
  · have hm : (𝒯.deg k - 𝒯.deg j) / 2 ∈ s := by
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨(k, j), Finset.mem_univ _, ?_⟩
      simp [hjk]
    exact s.min'_le _ hm
  · have hm : (𝒯.deg i - 𝒯.deg k) / 2 ∈ s := by
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨(i, k), Finset.mem_univ _, ?_⟩
      simp [hki]
    exact s.min'_le _ hm

theorem gammaSplit_exists_reserve
    (p : ℕ) (κ δ : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ r : ℕ, p ≤ r ∧ 1 ≤ r ∧
      10 < (r : ℝ) * κ ∧ 10 < (r : ℝ) * δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt
    (max (max (p : ℝ) 1) (max (10 / κ) (10 / δ)))
  refine ⟨n, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast (le_of_lt (lt_of_le_of_lt
      (le_trans (le_max_left _ _) (le_max_left _ _)) hn))
  · exact_mod_cast (le_of_lt (lt_of_le_of_lt
      (le_trans (le_max_right _ _) (le_max_left _ _)) hn))
  · have hnk : 10 / κ < (n : ℝ) := lt_of_le_of_lt
      (le_trans (le_max_left _ _) (le_max_right _ _)) hn
    exact (div_lt_iff₀ hκ).mp hnk
  · have hnd : 10 / δ < (n : ℝ) := lt_of_le_of_lt
      (le_trans (le_max_right _ _) (le_max_right _ _)) hn
    exact (div_lt_iff₀ hδ).mp hnd

private theorem gammaSplit_leftGoodAnnulus_moment_scale_le
    (S : Set ParabolicSpace) (M : Ω → Model 𝒯 parabolicSemigroup)
    (D : Set (ι × ι)) (γ κ C Cbar : ℝ) {r q : ℕ}
    (hr : 1 ≤ r) (hrq : 2 * r ≤ q) (hC : 0 ≤ C) (hCbar : C ≤ Cbar)
    (hm : ∀ x y i j, AEMeasurable
      (fun ω => (M ω).gammaMap y x (Pi.single i 1) j) P)
    (hdet : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
      ∀ ω x y, |(M ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j))
    (hann : ∀ i j, (i, j) ∉ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x y,
      (∫⁻ ω, ‖(M ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P) ≤
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ q)
    (i j : ι) (hi : 𝒯.deg i < γ) (hj : 𝒯.deg j < 𝒯.deg i)
    (hij : (i, j) ∉ D) (β δ : ℝ)
    (L : ℝ≥0∞)
    (hL : ∀ N l : ℕ, ∀ a b : gammaCell S (N + l + 1),
      parabolicNorm (hsParabolicCellRepresentative S (N + l)
          (hsParabolicCellParent S (N + l) a) -
        hsParabolicCellRepresentative S (N + l + 1) b) ≤
        20 / (2 : ℝ) ^ N →
      gammaSplitNearLeftGoodBound 𝒯 D κ C Cbar r i j
          (hsParabolicCellRepresentative S (N + l + 1) b)
          (hsParabolicCellRepresentative S (N + l + 1) a)
          (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) a)) ≤
        L * (dyadicBase N ^ ((r : ℝ) * (β + κ)) *
          dyadicBase l ^ ((r : ℝ) * (2 * δ))))
    (N l : ℕ) :
    ∫⁻ ω, gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω ^ r ∂P ≤
      (Fintype.card (gammaCell S (N + l + 1)) : ℝ≥0∞) ^ 2 * L *
        (dyadicBase N ^ ((r : ℝ) * (β + κ)) *
          dyadicBase l ^ ((r : ℝ) * (2 * δ))) := by
  classical
  have hmeas : ∀ z : gammaCell S (N + l + 1) × gammaCell S (N + l + 1),
      AEMeasurable (fun ω => if parabolicNorm
        (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) z.1) -
          hsParabolicCellRepresentative S (N + l + 1) z.2) ≤ 20 / (2 : ℝ) ^ N then
        ‖gammaSplitLeftGoodTerm (M ω) D i j
          (hsParabolicCellRepresentative S (N + l + 1) z.2)
          (hsParabolicCellRepresentative S (N + l + 1) z.1)
          (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) z.1))‖ₑ else 0) P := by
    intro z
    split_ifs
    · unfold gammaSplitLeftGoodTerm
      apply AEMeasurable.enorm
      apply AEMeasurable.add
      · exact hm _ _ i j
      · apply Finset.aemeasurable_fun_sum
        intro k hk
        exact (hm _ _ i k).mul (hm _ _ k j)
    · exact aemeasurable_const
  have hterm : ∀ z : gammaCell S (N + l + 1) × gammaCell S (N + l + 1),
      (∫⁻ ω, (if parabolicNorm
        (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) z.1) -
          hsParabolicCellRepresentative S (N + l + 1) z.2) ≤ 20 / (2 : ℝ) ^ N then
        ‖gammaSplitLeftGoodTerm (M ω) D i j
          (hsParabolicCellRepresentative S (N + l + 1) z.2)
          (hsParabolicCellRepresentative S (N + l + 1) z.1)
          (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) z.1))‖ₑ else 0) ^ r ∂P) ≤
        L * (dyadicBase N ^ ((r : ℝ) * (β + κ)) *
          dyadicBase l ^ ((r : ℝ) * (2 * δ))) := by
    intro z
    by_cases hz : parabolicNorm
        (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) z.1) -
          hsParabolicCellRepresentative S (N + l + 1) z.2) ≤ 20 / (2 : ℝ) ^ N
    · simp only [ite_eq_left hz]
      have hs := gammaSplitLeftGoodTerm_moment_le M D γ κ C Cbar
        hr hrq hC hCbar hm hdet hann i j hi hj hij
        (hsParabolicCellRepresentative S (N + l + 1) z.2)
        (hsParabolicCellRepresentative S (N + l + 1) z.1)
        (hsParabolicCellRepresentative S (N + l)
          (hsParabolicCellParent S (N + l) z.1))
      exact hs.trans (hL N l z.1 z.2 hz)
    · simp only [ite_eq_right hz, zero_pow (by omega : r ≠ 0), lintegral_zero]
      exact bot_le
  have hsup := finiteSup_lintegral_pow_le_card_mul (by omega : r ≠ 0)
    hmeas hterm
  simpa only [gammaSplitLeftGoodStepSupAnnulus, iSup_prod,
    Fintype.card_prod, Nat.cast_mul, ENNReal.coe_mul, ENNReal.coe_pow,
    pow_two, mul_assoc] using hsup

private theorem gammaSplit_rightGoodAnnulus_moment_scale_le
    (S : Set ParabolicSpace) (M : Ω → Model 𝒯 parabolicSemigroup)
    (D : Set (ι × ι)) (γ κ C Cbar : ℝ) {r q : ℕ}
    (hr : 1 ≤ r) (hrq : 2 * r ≤ q) (hC : 0 ≤ C) (hCbar : C ≤ Cbar)
    (hm : ∀ x y i j, AEMeasurable
      (fun ω => (M ω).gammaMap y x (Pi.single i 1) j) P)
    (hdet : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
      ∀ ω x y, |(M ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j))
    (hann : ∀ i j, (i, j) ∉ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x y,
      (∫⁻ ω, ‖(M ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P) ≤
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ q)
    (i j : ι) (hi : 𝒯.deg i < γ) (hj : 𝒯.deg j < 𝒯.deg i)
    (hij : (i, j) ∉ D) (β δ : ℝ)
    (L : ℝ≥0∞)
    (hL : ∀ N l : ℕ, ∀ a b : gammaCell S (N + l + 1),
      parabolicNorm (hsParabolicCellRepresentative S (N + l)
          (hsParabolicCellParent S (N + l) a) -
        hsParabolicCellRepresentative S (N + l + 1) b) ≤
        20 / (2 : ℝ) ^ N →
      gammaSplitNearRightGoodBound 𝒯 D κ C Cbar r i j
          (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) a))
          (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) b))
          (hsParabolicCellRepresentative S (N + l + 1) b) ≤
        L * (dyadicBase N ^ ((r : ℝ) * (β + κ)) *
          dyadicBase l ^ ((r : ℝ) * (2 * δ))))
    (N l : ℕ) :
    ∫⁻ ω, gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l) ω ^ r ∂P ≤
      (Fintype.card (gammaCell S (N + l + 1)) : ℝ≥0∞) ^ 2 * L *
        (dyadicBase N ^ ((r : ℝ) * (β + κ)) *
          dyadicBase l ^ ((r : ℝ) * (2 * δ))) := by
  classical
  have hmeas : ∀ z : gammaCell S (N + l + 1) × gammaCell S (N + l + 1),
      AEMeasurable (fun ω => if parabolicNorm
        (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) z.1) -
          hsParabolicCellRepresentative S (N + l + 1) z.2) ≤
          20 / (2 : ℝ) ^ N then
        ‖gammaSplitRightGoodTerm (M ω) D i j
          (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) z.1))
          (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) z.2))
          (hsParabolicCellRepresentative S (N + l + 1) z.2)‖ₑ else 0) P := by
    intro z
    split_ifs
    · unfold gammaSplitRightGoodTerm
      apply AEMeasurable.enorm
      apply AEMeasurable.add
      · exact hm _ _ i j
      · apply Finset.aemeasurable_fun_sum
        intro k hk
        exact (hm _ _ i k).mul (hm _ _ k j)
    · exact aemeasurable_const
  have hterm : ∀ z : gammaCell S (N + l + 1) × gammaCell S (N + l + 1),
      (∫⁻ ω, (if parabolicNorm
        (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) z.1) -
          hsParabolicCellRepresentative S (N + l + 1) z.2) ≤
          20 / (2 : ℝ) ^ N then
        ‖gammaSplitRightGoodTerm (M ω) D i j
          (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) z.1))
          (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) z.2))
          (hsParabolicCellRepresentative S (N + l + 1) z.2)‖ₑ else 0) ^ r ∂P) ≤
        L * (dyadicBase N ^ ((r : ℝ) * (β + κ)) *
          dyadicBase l ^ ((r : ℝ) * (2 * δ))) := by
    intro z
    by_cases hz : parabolicNorm
        (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) z.1) -
          hsParabolicCellRepresentative S (N + l + 1) z.2) ≤
        20 / (2 : ℝ) ^ N
    · simp only [ite_eq_left hz]
      have hs := gammaSplitRightGoodTerm_moment_le M D γ κ C Cbar
        hr hrq hC hCbar hm hdet hann i j hi hj hij
        (hsParabolicCellRepresentative S (N + l)
          (hsParabolicCellParent S (N + l) z.1))
        (hsParabolicCellRepresentative S (N + l)
          (hsParabolicCellParent S (N + l) z.2))
        (hsParabolicCellRepresentative S (N + l + 1) z.2)
      exact hs.trans (hL N l z.1 z.2 hz)
    · simp only [ite_eq_right hz, zero_pow (by omega : r ≠ 0), lintegral_zero]
      exact bot_le
  have hsup := finiteSup_lintegral_pow_le_card_mul (by omega : r ≠ 0)
    hmeas hterm
  simpa only [gammaSplitRightGoodStepSupAnnulus, iSup_prod,
    Fintype.card_prod, Nat.cast_mul, ENNReal.coe_mul, ENNReal.coe_pow,
    pow_two, mul_assoc] using hsup

private theorem gammaSplit_unit_envelope_moment_of_split
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (F : S → S → Ω → ℝ) (β δ : ℝ) (p : ℕ) (hp : 1 ≤ p)
    (A0 G : Ω → ℝ≥0∞) (Bbad : ℝ≥0∞)
    (hA0meas : AEMeasurable A0 P) (hGmeas : AEMeasurable G P)
    {KA KG : ℝ≥0∞} (hA0moment : ∫⁻ ω, A0 ω ^ p ∂P ≤ KA)
    (hA0eq : A0 = gammaProductCellNormalisedSup S F β 0)
    (hGmoment : ∫⁻ ω, G ω ^ p ∂P ≤ KG)
    (_hKA : KA ≠ ∞) (hKG : KG ≠ ∞) (hBbad : Bbad ≠ ∞)
    (hA : ∀ (ω : Ω) (N : ℕ), ∀ x y : S,
      parabolicNorm ((x : ParabolicSpace) - y) ≤ 1 / (2 : ℝ) ^ N →
      ‖F (hsParabolicCellApprox S N x)
          (hsParabolicCellApprox S N y) ω‖ₑ ≤
        A0 ω * dyadicBase N ^ β)
    (hG : ∀ (ω : Ω) (N l : ℕ),
      gammaProductLeftStepSupAnnulus S F N (N + l) ω +
          gammaProductRightStepSupAnnulus S F N (N + l) ω ≤
        (G ω + Bbad) * dyadicBase N ^ β * dyadicBase l ^ δ)
    (hcont : ∀ ω, Continuous (fun z : S × S => F z.1 z.2 ω))
    (hβ : 0 ≤ β) (hδ : 0 < δ) :
    ∃ B : Ω → ℝ≥0∞, AEMeasurable B P ∧
      (∫⁻ ω, B ω ^ p ∂P ≤
        ((2 : ℝ≥0∞) ^ β) ^ p *
          (Fintype.card (Fin 3) : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          (KA + (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ p * KG +
            (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ p * Bbad ^ p)) ∧
      (∀ᵐ ω ∂P, ∀ x y : S, 0 < parabolicNorm
        ((x : ParabolicSpace) - y) →
        parabolicNorm ((x : ParabolicSpace) - y) ≤ 20 →
        ‖F x y ω‖ₑ ≤ B ω * ENNReal.ofReal
          (parabolicNorm ((x : ParabolicSpace) - y)) ^ β) := by
  let d : ℝ≥0∞ := 1 - ((2 : ℝ≥0∞)⁻¹) ^ δ
  let c : ℝ≥0∞ := (2 : ℝ≥0∞) ^ β
  let V : Ω → Fin 3 → ℝ≥0∞ := fun ω n =>
    if n = 0 then A0 ω else if n = 1 then d⁻¹ * G ω else d⁻¹ * Bbad
  let H : Ω → ℝ≥0∞ := finiteFamilyEnvelope V
  let B : Ω → ℝ≥0∞ := fun ω => c * H ω
  have hd : d ≠ 0 := by
    dsimp [d]
    exact ne_of_gt (tsub_pos_iff_lt.2
      (ENNReal.rpow_lt_one (by norm_num) hδ))
  have hVmeas : ∀ n : Fin 3, AEMeasurable (V · n) P := by
    intro n
    fin_cases n
    · simpa [V] using hA0meas
    · simpa [V] using hGmeas.const_mul d⁻¹
    · exact aemeasurable_const
  have hHmeas : AEMeasurable H P := by
    exact finiteFamilyEnvelope_aemeasurable hVmeas
  let b : Fin 3 → ℝ≥0∞ := fun n =>
    if n = 0 then KA else if n = 1 then d⁻¹ ^ p * KG else d⁻¹ ^ p * Bbad ^ p
  have hb : ∀ n : Fin 3, ∫⁻ ω, V ω n ^ p ∂P ≤ b n := by
    intro n
    fin_cases n
    · change ∫⁻ ω, V ω (0 : Fin 3) ^ p ∂P ≤ KA
      simpa [V] using hA0moment
    · have hV1 : ∀ ω, V ω (1 : Fin 3) = d⁻¹ * G ω := by
        intro ω
        simp [V]
      have heq : (fun ω => V ω (1 : Fin 3) ^ p) =
          (fun ω => (d⁻¹ * G ω) ^ p) := by
        funext ω
        rw [hV1]
      have hcalc : ∫⁻ ω, V ω (1 : Fin 3) ^ p ∂P =
          d⁻¹ ^ p * ∫⁻ ω, G ω ^ p ∂P := by
        rw [heq, show (fun ω => (d⁻¹ * G ω) ^ p) =
            (fun ω => d⁻¹ ^ p * G ω ^ p) by funext ω; rw [mul_pow]]
        rw [lintegral_const_mul'' _ (hGmeas.pow_const p)]
      change ∫⁻ ω, V ω (1 : Fin 3) ^ p ∂P ≤ d⁻¹ ^ p * KG
      rw [hcalc]
      gcongr
    · change ∫⁻ ω, V ω (2 : Fin 3) ^ p ∂P ≤ d⁻¹ ^ p * Bbad ^ p
      have hV2 : ∀ ω, V ω (2 : Fin 3) = d⁻¹ * Bbad := by
        intro ω
        simp [V]
      have heq : (fun ω => V ω (2 : Fin 3) ^ p) =
          (fun _ : Ω => (d⁻¹ * Bbad) ^ p) := by
        funext ω
        rw [hV2]
      rw [heq, show (d⁻¹ * Bbad) ^ p = d⁻¹ ^ p * Bbad ^ p by rw [mul_pow]]
      simp [MeasureTheory.lintegral_const]
  let KH : ℝ≥0∞ :=
    (Fintype.card (Fin 3) : ℝ≥0∞) ^ ((p : ℝ) - 1) * ∑ n, b n
  have hKH : KH ≠ ∞ := by
    dsimp [KH]
    apply ENNReal.mul_ne_top
    · finiteness
    apply ENNReal.sum_ne_top.mpr
    intro n hn
    fin_cases n <;> simp only [b]
    · exact _hKA
    · exact ENNReal.mul_ne_top (by finiteness) hKG
    · exact ENNReal.mul_ne_top (by finiteness) (ENNReal.pow_ne_top hBbad)
  have hHmoment : ∫⁻ ω, H ω ^ p ∂P ≤ KH := by
    exact finiteFamilyEnvelope_moment_le_of_pointwise hp hVmeas hb
  have hBmeas : AEMeasurable B P := by
    exact hHmeas.const_mul c
  have hBmoment : ∫⁻ ω, B ω ^ p ∂P ≤ c ^ p * KH := by
    dsimp [B]
    simp only [mul_pow]
    rw [lintegral_const_mul'' _ (hHmeas.pow_const p)]
    gcongr
  have hKH' : KH = (Fintype.card (Fin 3) : ℝ≥0∞) ^ ((p : ℝ) - 1) *
      (KA + d⁻¹ ^ p * KG + d⁻¹ ^ p * Bbad ^ p) := by
    have hsum : ∑ n : Fin 3, b n = KA + d⁻¹ ^ p * KG + d⁻¹ ^ p * Bbad ^ p := by
      norm_num [b, Fin.sum_univ_succ]
      rw [← add_assoc]
    dsimp [KH]
    rw [hsum]
  have hGtop : ∀ᵐ ω ∂P, G ω ≠ ∞ := by
    filter_upwards [ae_lt_top' (hGmeas.pow_const p)
      (ne_top_of_le_ne_top hKG hGmoment)] with ω hω
    intro htop
    have hpowtop : G ω ^ p = ∞ := by
      rw [htop]
      simp [Nat.ne_of_gt hp]
    exact hω.ne hpowtop
  have hGB : ∀ᵐ ω ∂P, G ω + Bbad ≠ ∞ := by
    filter_upwards [hGtop] with ω hω
    exact (ENNReal.add_ne_top).2 ⟨hω, hBbad⟩
  have hpoint : ∀ᵐ ω ∂P, ∀ x y : S,
      0 < parabolicNorm ((x : ParabolicSpace) - y) →
      parabolicNorm ((x : ParabolicSpace) - y) ≤ 20 →
      ‖F x y ω‖ₑ ≤ B ω * ENNReal.ofReal
        (parabolicNorm ((x : ParabolicSpace) - y)) ^ β := by
    filter_upwards [hGB] with ω hGBω
    intro x y hxy0 hxy20
    have hvalueN (N : ℕ) (x' y' : S)
        (hxy : parabolicNorm ((x' : ParabolicSpace) - y') ≤
          1 / (2 : ℝ) ^ N) :
        ‖F (hsParabolicCellApprox S N x')
            (hsParabolicCellApprox S N y') ω‖ₑ ≤
          A0 ω * dyadicBase N ^ β := by
      exact hA ω N x' y' hxy
    have hvalue (x' y' : S) :
        ‖F (hsParabolicCellApprox S 0 x')
            (hsParabolicCellApprox S 0 y') ω‖ₑ ≤ A0 ω := by
      have hv := gammaProductCellApprox_value_le_of_box S hbox F x' y' ω
        (gammaSplit_box_distance_le_four S hbox x' y')
      have hn := gammaProductCellSup_le_normalisedSup S F β 0 0 ω
      rw [hA0eq]
      simpa [dyadicBase] using hv.trans hn
    have hstep (x' y' : S) (l : ℕ) :
        ‖F (hsParabolicCellApprox S l x')
            (hsParabolicCellApprox S l y') ω -
          F (hsParabolicCellApprox S (l + 1) x')
            (hsParabolicCellApprox S (l + 1) y') ω‖ₑ ≤
        (G ω + Bbad) * dyadicBase 0 ^ β * dyadicBase l ^ δ := by
      have hs := gammaProductCellApprox_step_le_of_box S hbox F l x' y' ω
      have hg := hG ω 0 l
      have hg' : gammaProductLeftStepSupAnnulus S F 0 l ω +
          gammaProductRightStepSupAnnulus S F 0 l ω ≤
          (G ω + Bbad) * dyadicBase 0 ^ β * dyadicBase l ^ δ := by
        simpa only [Nat.zero_add] using hg
      exact hs.trans hg'
    have hstepN (N l : ℕ) (x' y' : S)
        (hxy : parabolicNorm ((x' : ParabolicSpace) - y') ≤
          1 / (2 : ℝ) ^ N) :
        ‖F (hsParabolicCellApprox S (N + l) x')
            (hsParabolicCellApprox S (N + l) y') ω -
          F (hsParabolicCellApprox S (N + l + 1) x')
            (hsParabolicCellApprox S (N + l + 1) y') ω‖ₑ ≤
          (G ω + Bbad) * dyadicBase N ^ β * dyadicBase l ^ δ := by
      have hs := gammaProductCellApprox_step_le_of_annulus S hbox F
        (Nat.le_add_right N l) x' y' ω hxy
      exact hs.trans (hG ω N l)
    have h := gammaSplit_pointwise_bound_of_envelopes_global S hbox F β δ ω
      (A0 ω) (G ω) Bbad hGBω hβ hδ (hcont ω) hvalueN hstepN hvalue hstep
      x y hxy0
    have hH : H ω = A0 ω + d⁻¹ * G ω + d⁻¹ * Bbad := by
      simp [H, V, finiteFamilyEnvelope, Fin.sum_univ_succ]
      rw [add_assoc]
    calc
      ‖F x y ω‖ₑ ≤
          (A0 ω + (G ω + Bbad) / d) * c * ENNReal.ofReal
            (parabolicNorm ((x : ParabolicSpace) - y)) ^ β := by
        simpa [c] using h
      _ = B ω * ENNReal.ofReal
          (parabolicNorm ((x : ParabolicSpace) - y)) ^ β := by
        change _ = c * H ω * ENNReal.ofReal
          (parabolicNorm ((x : ParabolicSpace) - y)) ^ β
        rw [hH]
        rw [div_eq_mul_inv]
        ring
  refine ⟨B, hBmeas, ?_, hpoint⟩
  calc
    _ ≤ c ^ p * KH := hBmoment
    _ = ((2 : ℝ≥0∞) ^ β) ^ p *
          (Fintype.card (Fin 3) : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          (KA + (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ p * KG +
            (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ p * Bbad ^ p) := by
      rw [hKH']
      dsimp [c, d]
      ring

private theorem gammaSplit_cell_envelope_moment
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ κ C : ℝ) {q r : ℕ} (hr : 1 ≤ r) (hrq : r ≤ q)
    (hκ : 0 < κ) (hC : 0 ≤ C) (hreserve : 10 < (r : ℝ) * κ)
    (hm : ∀ x y i j, AEMeasurable
      (fun ω => (M ω).gammaMap y x (Pi.single i 1) j) P)
    (hdet : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
      ∀ ω x y, |(M ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j))
    (hann : ∀ i j, (i, j) ∉ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x y,
      (∫⁻ ω, ‖(M ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P) ≤
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ q)
    (i j : ι) (hi : 𝒯.deg i < γ) (hj : 𝒯.deg j < 𝒯.deg i)
    (hij : (i, j) ∉ D) :
    ∃ A0 : Ω → ℝ≥0∞, AEMeasurable A0 P ∧
      ∃ KA : ℝ≥0∞, KA ≠ ∞ ∧
        (∫⁻ ω, A0 ω ^ r ∂P ≤ KA) ∧
        KA = gammaSplitCellConstant 𝒯 i j κ C r ∧
        A0 = gammaProductCellNormalisedSup S
          (fun x y ω => (M ω).gammaMap (x : ParabolicSpace)
            (y : ParabolicSpace) (Pi.single i 1) j)
          (𝒯.deg i - 𝒯.deg j) 0 ∧
        (∀ (ω : Ω) (N : ℕ), ∀ x y : S,
          parabolicNorm ((x : ParabolicSpace) - y) ≤ 1 / (2 : ℝ) ^ N →
          ‖(M ω).gammaMap
              (hsParabolicCellApprox S N x)
              (hsParabolicCellApprox S N y) (Pi.single i 1) j‖ₑ ≤
            A0 ω * dyadicBase N ^ (𝒯.deg i - 𝒯.deg j)) := by
  let F : S → S → Ω → ℝ := fun x y ω =>
    (M ω).gammaMap (x : ParabolicSpace) (y : ParabolicSpace)
      (Pi.single i 1) j
  let β : ℝ := 𝒯.deg i - 𝒯.deg j
  let e : ℝ := β + κ
  let A0 : Ω → ℝ≥0∞ := gammaProductCellNormalisedSup S F β 0
  have hβ : 0 ≤ β := by
    dsimp [β]
    linarith
  have he : 0 ≤ e := by
    dsimp [e]
    linarith
  have hmeasF : ∀ x y, AEMeasurable (F x y) P := by
    intro x y
    exact hm (y : ParabolicSpace) (x : ParabolicSpace) i j
  have hpair (x y : S) :
      ∫⁻ ω, ‖F x y ω‖ₑ ^ r ∂P ≤
        (ENNReal.ofReal C) ^ r *
          ENNReal.ofReal (parabolicNorm ((x : ParabolicSpace) - y)) ^
            ((r : ℝ) * e) := by
    have hs := randomModel_gamma_coordinate_moment_le_global_source M D γ κ C
      (p := r) (q := q) hr hrq hm hdet hann
      (y : ParabolicSpace) (x : ParabolicSpace) hi hj
    have hrewrite (u v : ParabolicSpace) :
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist u v ^ e) ^ r =
          (ENNReal.ofReal C) ^ r * ENNReal.ofReal (parabolicNorm
            (u - v)) ^ ((r : ℝ) * e) := by
      calc
        _ = (ENNReal.ofReal C) ^ r *
            ENNReal.ofReal (parabolicSemigroup.scaleDist u v ^ e) ^ r := by
          rw [ENNReal.ofReal_mul hC,
            mul_pow]
        _ = (ENNReal.ofReal C) ^ r *
            (ENNReal.ofReal (parabolicSemigroup.scaleDist u v) ^ e) ^ r := by
          rw [ENNReal.ofReal_rpow_of_nonneg
            (parabolicSemigroup.scaleDist_nonneg _ _) he]
        _ = (ENNReal.ofReal C) ^ r *
            ENNReal.ofReal (parabolicSemigroup.scaleDist u v) ^
              ((r : ℝ) * e) := by
          have hpow : (ENNReal.ofReal (parabolicSemigroup.scaleDist u v) ^ e) ^ r =
              ENNReal.ofReal (parabolicSemigroup.scaleDist u v) ^
                ((r : ℝ) * e) := by
            rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
            congr 1
            ring
          rw [hpow]
        _ = (ENNReal.ofReal C) ^ r * ENNReal.ofReal
              (parabolicNorm (u - v)) ^ ((r : ℝ) * e) := by
          simp [parabolicSemigroup]
    have heq := hrewrite (x : ParabolicSpace) (y : ParabolicSpace)
    have hs' := hs
    simp [hij] at hs'
    simpa [F, e, β] using hs'.trans_eq heq
  have hpair' (x y : S) :
      ∫⁻ ω, ‖F x y ω‖ₑ ^ r ∂P ≤
        (ENNReal.ofReal C) ^ r * ENNReal.ofReal
          (parabolicNorm ((x : ParabolicSpace) - y)) ^ ((r : ℝ) * e) :=
    hpair x y
  have hgap : (r : ℝ) * β < (r : ℝ) * e - 10 := by
    dsimp [e]
    linarith
  have hpair'' : ∀ x y : S, parabolicNorm ((x : ParabolicSpace) - y) ≤ 20 →
      ∫⁻ ω, ‖F x y ω‖ₑ ^ r ∂P ≤
        (ENNReal.ofReal C) ^ r * ENNReal.ofReal
          (parabolicNorm ((x : ParabolicSpace) - y)) ^ ((r : ℝ) * e) := by
    intro x y _
    exact hpair' x y
  have hA0moment := gammaProductCellNormalisedSup_moment_le S F hmeasF hr
    (q := (r : ℝ) * e) (ε := 20) (by positivity) (M := (ENNReal.ofReal C) ^ r)
    hpair'' β hgap 0
    (by norm_num)
  let KA : ℝ≥0∞ := gammaSplitCellConstant 𝒯 i j κ C r
  have hKA : KA ≠ ∞ := by
    dsimp [KA, gammaSplitCellConstant]
    simp only [dyadicBase, pow_zero, ENNReal.one_rpow, mul_one]
    have hden : 1 - ((2 : ℝ≥0∞)⁻¹) ^ ((r : ℝ) * κ - 10) ≠ 0 := by
      exact ne_of_gt (tsub_pos_iff_lt.2
        (ENNReal.rpow_lt_one (by norm_num) (by linarith)))
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · finiteness
        · exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
      · exact (ENNReal.rpow_lt_top_of_nonneg (by positivity)
          ENNReal.ofNat_ne_top).ne
    · exact ENNReal.inv_ne_top.mpr hden
  have hKAeq : KA = gammaSplitCellConstant 𝒯 i j κ C r := by
    dsimp [KA, gammaSplitCellConstant, e, β]
  refine ⟨A0, gammaProductCellNormalisedSup_aemeasurable S F β 0 hmeasF,
    KA, hKA, ?_, hKAeq, ?_, ?_⟩
  · rw [hKAeq]
    convert hA0moment using 1
    dsimp [KA, gammaSplitCellConstant, e, β]
    ring_nf
  · rfl
  intro ω N x y hxy
  have hcell := gammaProductCellApprox_value_le S hbox F N x y ω hxy
  have hnorm := gammaProductCellSup_le_normalisedSup S F β 0 N ω
  have hnorm' : gammaProductCellSup S F N ω ≤ A0 ω * dyadicBase N ^ β := by
    simpa [A0, Nat.zero_add] using hnorm
  exact hcell.trans hnorm'

omit [IsProbabilityMeasure P] in
private theorem gammaSplit_good_global_envelope_moment
    (S : Set ParabolicSpace)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (β κ δ : ℝ) {p : ℕ} (hp : 1 ≤ p) (hδ : 0 < δ)
    (hκp : 10 < (p : ℝ) * κ) (hδp : 10 < (p : ℝ) * δ)
    (hm : ∀ x y a b, AEMeasurable
      (fun ω => (M ω).gammaMap x y (Pi.single a 1) b) P)
    {Lleft Lright : ℝ≥0∞}
    (hLleft : Lleft ≠ ∞) (hLright : Lright ≠ ∞)
    (hleft : ∀ N l : ℕ,
      ∫⁻ ω, gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω ^ p ∂P ≤
        (Fintype.card (gammaCell S (N + l + 1)) : ℝ≥0∞) ^ 2 * Lleft *
          (dyadicBase N ^ ((p : ℝ) * (β + κ)) *
            dyadicBase l ^ ((p : ℝ) * (2 * δ))))
    (hright : ∀ N l : ℕ,
      ∫⁻ ω, gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l) ω ^ p ∂P ≤
        (Fintype.card (gammaCell S (N + l + 1)) : ℝ≥0∞) ^ 2 * Lright *
          (dyadicBase N ^ ((p : ℝ) * (β + κ)) *
            dyadicBase l ^ ((p : ℝ) * (2 * δ)))) :
    ∃ G : Ω → ℝ≥0∞, AEMeasurable G P ∧
      ∃ KG : ℝ≥0∞, KG ≠ ∞ ∧
        (∫⁻ ω, G ω ^ p ∂P ≤ KG) ∧
        KG = (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) * (512 : ℝ≥0∞) ^ 2 *
          (Lleft + Lright) *
            (1 - ((2 : ℝ≥0∞)⁻¹) ^
              (min ((p : ℝ) * κ - 10) ((p : ℝ) * δ - 10)))⁻¹ *
            (1 - ((2 : ℝ≥0∞)⁻¹) ^
              (min ((p : ℝ) * κ - 10) ((p : ℝ) * δ - 10)))⁻¹ ∧
        (∀ (ω : Ω) (N l : ℕ),
          gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω +
              gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l) ω ≤
            G ω * dyadicBase N ^ β * dyadicBase l ^ δ) := by
  let G := gammaSplitGoodGlobalEnvelope S M D i j β δ
  have hGmeas : AEMeasurable G P := by
    exact gammaSplitGoodGlobalEnvelope_aemeasurable S M D i j β δ hm
  let η : ℝ := min ((p : ℝ) * κ - 10) ((p : ℝ) * δ - 10)
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min (by linarith) (by linarith)
  let L : ℝ≥0∞ := Lleft + Lright
  let A : ℝ≥0∞ := (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
    (512 : ℝ≥0∞) ^ 2 * L
  have hterm : ∀ N l : ℕ,
      ∫⁻ ω, gammaSplitGoodGlobalTerm S M D i j β δ N l ω ^ p ∂P ≤
        A * dyadicBase N ^ η * dyadicBase l ^ η := by
    intro N l
    have hmleft := hleft N l
    have hmright := hright N l
    have hml : AEMeasurable
        (gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l)) P := by
      exact gammaSplitLeftGoodStepSupAnnulus_aemeasurable S M D i j N (N + l)
        hm
    have hmr : AEMeasurable
        (gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l)) P := by
      exact gammaSplitRightGoodStepSupAnnulus_aemeasurable S M D i j N (N + l)
        hm
    have hsum : ∫⁻ ω,
        (gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω +
          gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l) ω) ^ p ∂P ≤
        (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          (Fintype.card (gammaCell S (N + l + 1)) : ℝ≥0∞) ^ 2 * L *
            (dyadicBase N ^ ((p : ℝ) * (β + κ)) *
              dyadicBase l ^ ((p : ℝ) * (2 * δ))) := by
      have hpoint (ω : Ω) :
          (gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω +
            gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l) ω) ^ p ≤
          (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
            (gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω ^ p +
              gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l) ω ^ p) := by
        simpa only [ENNReal.rpow_natCast] using
          ENNReal.rpow_add_le_mul_rpow_add_rpow
            (gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω)
            (gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l) ω)
            (show (1 : ℝ) ≤ p by exact_mod_cast hp)
      calc
        _ ≤ ∫⁻ ω, (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
            (gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω ^ p +
              gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l) ω ^ p) ∂P :=
          lintegral_mono hpoint
        _ = (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
            (∫⁻ ω, gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω ^ p ∂P +
              ∫⁻ ω, gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l) ω ^ p ∂P) := by
          rw [lintegral_const_mul''
            (f := fun ω => gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω ^ p +
              gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l) ω ^ p) _
            ((hml.pow_const p).add (hmr.pow_const p)),
            lintegral_add_left' (f := fun ω =>
              gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω ^ p)
              (hml.pow_const p)]
        _ ≤ _ := by
          calc
            _ ≤ (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
                ((Fintype.card (gammaCell S (N + l + 1)) : ℝ≥0∞) ^ 2 * Lleft *
                  (dyadicBase N ^ ((p : ℝ) * (β + κ)) *
                    dyadicBase l ^ ((p : ℝ) * (2 * δ))) +
                  (Fintype.card (gammaCell S (N + l + 1)) : ℝ≥0∞) ^ 2 * Lright *
                  (dyadicBase N ^ ((p : ℝ) * (β + κ)) *
                    dyadicBase l ^ ((p : ℝ) * (2 * δ)))) := by
              gcongr
            _ = _ := by dsimp [L]; ring
    have hnorm : AEMeasurable
        (gammaSplitGoodGlobalTerm S M D i j β δ N l) P :=
      gammaSplitGoodGlobalTerm_aemeasurable S M D i j β δ N l hm
    have hpow : ∀ ω,
        gammaSplitGoodGlobalTerm S M D i j β δ N l ω ^ p =
          (gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω +
            gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l) ω) ^ p *
            dyadicBase N ^ (-(p : ℝ) * β) *
            dyadicBase l ^ (-(p : ℝ) * δ) := by
      intro ω
      unfold gammaSplitGoodGlobalTerm
      rw [mul_pow, mul_pow]
      have hNpow : (dyadicBase N ^ (-β)) ^ p =
          dyadicBase N ^ (-(p : ℝ) * β) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        congr 1
        ring
      have hLpow : (dyadicBase l ^ (-δ)) ^ p =
          dyadicBase l ^ (-(p : ℝ) * δ) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        congr 1
        ring
      rw [hNpow, hLpow]
    have hnormeq :
        ∫⁻ ω, gammaSplitGoodGlobalTerm S M D i j β δ N l ω ^ p ∂P =
          (∫⁻ ω, (gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω +
            gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l) ω) ^ p ∂P) *
            dyadicBase N ^ (-(p : ℝ) * β) *
            dyadicBase l ^ (-(p : ℝ) * δ) := by
      simp_rw [hpow]
      calc
        _ = (∫⁻ ω, (gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω +
              gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l) ω) ^ p *
              dyadicBase N ^ (-(p : ℝ) * β) ∂P) *
              dyadicBase l ^ (-(p : ℝ) * δ) := by
          exact lintegral_mul_const'' (μ := P)
            (dyadicBase l ^ (-(p : ℝ) * δ))
            (((hml.add hmr).pow_const p).mul_const _)
        _ = _ := by
          congr 1
          exact lintegral_mul_const'' (μ := P)
            (dyadicBase N ^ (-(p : ℝ) * β))
            ((hml.add hmr).pow_const p)
    rw [hnormeq]
    calc
      _ ≤ ((2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          (Fintype.card (gammaCell S (N + l + 1)) : ℝ≥0∞) ^ 2 * L *
                  (dyadicBase N ^ ((p : ℝ) * (β + κ)) *
              dyadicBase l ^ ((p : ℝ) * (2 * δ)))) *
          dyadicBase N ^ (-(p : ℝ) * β) *
          dyadicBase l ^ (-(p : ℝ) * δ) := by gcongr
      _ ≤ A * dyadicBase N ^ η * dyadicBase l ^ η := by
        have hcard := gammaProduct_card_le S (N + l)
        have hcard' :
            (Fintype.card (gammaCell S (N + l + 1)) : ℝ≥0∞) ^ 2 ≤
              (512 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞) ^ (10 * (N + l)) := hcard
        have hscaleN :
            (2 : ℝ≥0∞) ^ (10 * (N + l)) =
              dyadicBase N ^ (-10 : ℝ) * dyadicBase l ^ (-10 : ℝ) := by
          have hbase (n : ℕ) : (2 : ℝ≥0∞) ^ (10 * n) =
              dyadicBase n ^ (-10 : ℝ) := by
            rw [ENNReal.rpow_neg]
            rw [dyadicBase_rpow_eq_geometric]
            simp [← pow_mul, mul_comm, ← ENNReal.inv_pow]
          rw [hbase, show dyadicBase (N + l) ^ (-10 : ℝ) =
              dyadicBase N ^ (-10 : ℝ) * dyadicBase l ^ (-10 : ℝ) by
            rw [dyadicBase_rpow_eq_geometric, pow_add,
              ← dyadicBase_rpow_eq_geometric,
              ← dyadicBase_rpow_eq_geometric]]
        have hscale :
            (2 : ℝ≥0∞) ^ (10 * (N + l)) *
                (dyadicBase N ^ ((p : ℝ) * (β + κ)) *
                  dyadicBase l ^ ((p : ℝ) * (2 * δ))) *
                dyadicBase N ^ (-(p : ℝ) * β) *
                dyadicBase l ^ (-(p : ℝ) * δ) =
              dyadicBase N ^ ((p : ℝ) * κ - 10) *
                dyadicBase l ^ ((p : ℝ) * δ - 10) := by
          rw [hscaleN]
          calc
            dyadicBase N ^ (-10 : ℝ) * dyadicBase l ^ (-10 : ℝ) *
                (dyadicBase N ^ ((p : ℝ) * (β + κ)) *
                  dyadicBase l ^ ((p : ℝ) * (2 * δ))) *
                dyadicBase N ^ (-(p : ℝ) * β) *
                dyadicBase l ^ (-(p : ℝ) * δ) =
              (dyadicBase N ^ (-10 : ℝ) *
                  dyadicBase N ^ ((p : ℝ) * (β + κ)) *
                  dyadicBase N ^ (-(p : ℝ) * β)) *
                (dyadicBase l ^ (-10 : ℝ) *
                  dyadicBase l ^ ((p : ℝ) * (2 * δ)) *
                  dyadicBase l ^ (-(p : ℝ) * δ)) := by ring
            _ = dyadicBase N ^ (-10 + (p : ℝ) * (β + κ) - (p : ℝ) * β) *
                dyadicBase l ^ (-10 + (p : ℝ) * (2 * δ) - (p : ℝ) * δ) := by
              rw [← ENNReal.rpow_add _ _ (dyadicBase_pos N).ne'
                (dyadicBase_ne_top N),
                ← ENNReal.rpow_add _ _ (dyadicBase_pos N).ne'
                  (dyadicBase_ne_top N),
                ← ENNReal.rpow_add _ _ (dyadicBase_pos l).ne'
                  (dyadicBase_ne_top l),
                ← ENNReal.rpow_add _ _ (dyadicBase_pos l).ne'
                  (dyadicBase_ne_top l)]
              congr 1 <;> ring_nf
            _ = dyadicBase N ^ ((p : ℝ) * κ - 10) *
                dyadicBase l ^ ((p : ℝ) * δ - 10) := by
              congr 1 <;> ring_nf
        have hN : dyadicBase N ^ ((p : ℝ) * κ - 10) ≤ dyadicBase N ^ η := by
          apply ENNReal.rpow_le_rpow_of_exponent_ge
          · unfold dyadicBase
            exact pow_le_one₀ (by positivity) (by norm_num)
          · exact min_le_left _ _
        have hL : dyadicBase l ^ ((p : ℝ) * δ - 10) ≤ dyadicBase l ^ η := by
          apply ENNReal.rpow_le_rpow_of_exponent_ge
          · unfold dyadicBase
            exact pow_le_one₀ (by positivity) (by norm_num)
          · exact min_le_right _ _
        calc
          _ ≤ (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
              ((512 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞) ^ (10 * (N + l))) * L *
              (dyadicBase N ^ ((p : ℝ) * (β + κ)) *
                dyadicBase l ^ ((p : ℝ) * (2 * δ))) *
              dyadicBase N ^ (-(p : ℝ) * β) *
              dyadicBase l ^ (-(p : ℝ) * δ) := by
            gcongr
          _ = A * dyadicBase N ^ ((p : ℝ) * κ - 10) *
              dyadicBase l ^ ((p : ℝ) * δ - 10) := by
            dsimp [A]
            calc
              _ = (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
                  (512 : ℝ≥0∞) ^ 2 * L *
                  ((2 : ℝ≥0∞) ^ (10 * (N + l)) *
                    (dyadicBase N ^ ((p : ℝ) * (β + κ)) *
                      dyadicBase l ^ ((p : ℝ) * (2 * δ))) *
                    dyadicBase N ^ (-(p : ℝ) * β) *
                    dyadicBase l ^ (-(p : ℝ) * δ)) := by ring
              _ = _ := by
                rw [hscale]
                ring
          _ ≤ A * dyadicBase N ^ η * dyadicBase l ^ η := by
            gcongr
  have hGmoment := gammaSplitGoodGlobalEnvelope_moment_le S M D i j β δ η p hp
    hδ hη hm hterm
  let KG : ℝ≥0∞ := A * (1 - ((2 : ℝ≥0∞)⁻¹) ^ η)⁻¹ *
      (1 - ((2 : ℝ≥0∞)⁻¹) ^ η)⁻¹
  have hKG : KG ≠ ∞ := by
    have hden : 1 - ((2 : ℝ≥0∞)⁻¹) ^ η ≠ 0 := by
      exact ne_of_gt (tsub_pos_iff_lt.2 (ENNReal.rpow_lt_one (by norm_num) hη))
    have hA : A ≠ ∞ := by
      have hC0 : (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) ≠ ∞ := by finiteness
      have h512 : (512 : ℝ≥0∞) ^ 2 ≠ ∞ := by finiteness
      have hLsum : Lleft + Lright ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hLleft, hLright⟩
      dsimp [A, L]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hC0 h512) hLsum
    dsimp [KG]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hA
      (ENNReal.inv_ne_top.mpr hden)) (ENNReal.inv_ne_top.mpr hden)
  have hGmoment' : ∫⁻ ω, G ω ^ p ∂P ≤ KG := by
    simpa [KG] using hGmoment
  have hKGformula : KG = (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) * (512 : ℝ≥0∞) ^ 2 *
      (Lleft + Lright) *
        (1 - ((2 : ℝ≥0∞)⁻¹) ^
          (min ((p : ℝ) * κ - 10) ((p : ℝ) * δ - 10)))⁻¹ *
        (1 - ((2 : ℝ≥0∞)⁻¹) ^
          (min ((p : ℝ) * κ - 10) ((p : ℝ) * δ - 10)))⁻¹ := by
    dsimp [KG, A, L, η]
  refine ⟨G, hGmeas, KG, hKG, hGmoment', hKGformula, ?_⟩
  intro ω N l
  have hterm' := gammaSplitGoodGlobalTerm_le_envelope_mul_scale
    S M D i j β δ N l ω
  simpa [G] using hterm'

/-! The following finite-sector coordinate theorem is the interface used by the
compact assembly.  Its deterministic branch is pathwise, while its
non-deterministic branch is supplied by the reserve-bearing source estimates.
-/
theorem gammaSplit_unit_coordinate_envelope
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ κ C Cbar δ : ℝ) (i j : ι) {q r : ℕ} (hr : 1 ≤ r) (hrq : 2 * r ≤ q)
    (hκ : 0 < κ) (hC : 0 ≤ C) (hCbar : C ≤ Cbar)
    (hreserveκ : 10 < (r : ℝ) * κ)
    (hδ : 0 < δ) (hreserveδ : 10 < (r : ℝ) * δ) (hδκ : 2 * δ ≤ κ)
    (hδleft : ∀ k, 𝒯.deg j < 𝒯.deg k → 𝒯.deg k < 𝒯.deg i →
      δ ≤ (𝒯.deg k - 𝒯.deg j) / 2)
    (hδright : ∀ k, 𝒯.deg j < 𝒯.deg k → 𝒯.deg k < 𝒯.deg i →
      δ ≤ (𝒯.deg i - 𝒯.deg k) / 2)
    (hm : ∀ x y a b, AEMeasurable
      (fun ω => (M ω).gammaMap x y (Pi.single a 1) b) P)
    (hdet : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
      ∀ ω x y, |(M ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j))
    (hann : ∀ i j, (i, j) ∉ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x y,
      (∫⁻ ω, ‖(M ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P) ≤
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ q)
    (hcont : ∀ ω, Continuous (fun z : S × S =>
      (M ω).gammaMap z.1 z.2 (Pi.single i 1) j))
    (hi : 𝒯.deg i < γ) (hj : 𝒯.deg j < 𝒯.deg i)
    (hij : (i, j) ∉ D) :
    ∃ B : Ω → ℝ≥0∞, AEMeasurable B P ∧
      ∃ KB : ℝ≥0∞, KB ≠ ∞ ∧
        (∫⁻ ω, B ω ^ r ∂P ≤ KB) ∧
        KB = gammaSplitUnitConstant 𝒯 D i j κ C Cbar δ r ∧
        (∀ᵐ ω ∂P, ∀ x y : S, 0 < parabolicNorm
          ((x : ParabolicSpace) - y) →
          parabolicNorm ((x : ParabolicSpace) - y) ≤ 20 →
          ‖(M ω).gammaMap y x (Pi.single i 1) j‖ₑ ≤
            B ω * ENNReal.ofReal (parabolicNorm
              ((x : ParabolicSpace) - y)) ^ (𝒯.deg i - 𝒯.deg j)) := by
  classical
  have hm' : ∀ x y a b, AEMeasurable
      (fun ω => (M ω).gammaMap y x (Pi.single a 1) b) P := by
    intro x y a b
    exact hm y x a b
  let β : ℝ := 𝒯.deg i - 𝒯.deg j
  let Lleft : ℝ≥0∞ := gammaSplitLeftConstant 𝒯 D i j κ C Cbar r
  let Lright : ℝ≥0∞ := gammaSplitRightConstant 𝒯 D i j κ C Cbar r
  let Bbad : ℝ≥0∞ := gammaSplitBadConstant 𝒯 D i j C r
  have hLleft : Lleft ≠ ∞ := by
    dsimp [Lleft]
    have hcard :
        ((gammaGoodIntermediate 𝒯 D i j).card : ℝ≥0∞) ^ ((r : ℝ) - 1) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by
        have hr' : 1 ≤ (r : ℝ) := by exact_mod_cast hr
        linarith) ENNReal.coe_ne_top
    apply ENNReal.mul_ne_top
    · finiteness
    apply ENNReal.add_ne_top.mpr
    refine ⟨by finiteness, ENNReal.mul_ne_top hcard ?_⟩
    apply ENNReal.sum_ne_top.mpr
    intro k hk
    finiteness
  have hLright : Lright ≠ ∞ := by
    dsimp [Lright]
    have hcard :
        ((gammaGoodIntermediate 𝒯 D i j).card : ℝ≥0∞) ^ ((r : ℝ) - 1) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by
        have hr' : 1 ≤ (r : ℝ) := by exact_mod_cast hr
        linarith) ENNReal.coe_ne_top
    apply ENNReal.mul_ne_top
    · finiteness
    apply ENNReal.add_ne_top.mpr
    refine ⟨by finiteness, ENNReal.mul_ne_top hcard ?_⟩
    apply ENNReal.sum_ne_top.mpr
    intro k hk
    finiteness
  have hBbad : Bbad ≠ ∞ := by
    dsimp [Bbad]
    apply ENNReal.add_ne_top.mpr
    constructor <;> apply ENNReal.sum_ne_top.mpr <;> intro k hk <;> finiteness
  have hLleft' : ∀ N l : ℕ, ∀ a b : gammaCell S (N + l + 1),
      parabolicNorm (hsParabolicCellRepresentative S (N + l)
          (hsParabolicCellParent S (N + l) a) -
        hsParabolicCellRepresentative S (N + l + 1) b) ≤
        20 / (2 : ℝ) ^ N →
      gammaSplitNearLeftGoodBound 𝒯 D κ C Cbar r i j
          (hsParabolicCellRepresentative S (N + l + 1) b)
          (hsParabolicCellRepresentative S (N + l + 1) a)
          (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) a)) ≤
        Lleft * (dyadicBase N ^ ((r : ℝ) * (β + κ)) *
          dyadicBase l ^ ((r : ℝ) * (2 * δ))) := by
    intro N l a b hnear
    have h := gammaSplit_leftGoodBound_scale_le S hbox 𝒯 D κ C Cbar r i j
      β δ hκ hC hCbar (by rfl) hj hδ
      hδκ hδleft N l a b hnear
    simpa [Lleft, gammaSplitLeftConstant] using h
  have hLright' : ∀ N l : ℕ, ∀ a b : gammaCell S (N + l + 1),
      parabolicNorm (hsParabolicCellRepresentative S (N + l)
          (hsParabolicCellParent S (N + l) a) -
        hsParabolicCellRepresentative S (N + l + 1) b) ≤
        20 / (2 : ℝ) ^ N →
      gammaSplitNearRightGoodBound 𝒯 D κ C Cbar r i j
          (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) a))
          (hsParabolicCellRepresentative S (N + l)
            (hsParabolicCellParent S (N + l) b))
          (hsParabolicCellRepresentative S (N + l + 1) b) ≤
        Lright * (dyadicBase N ^ ((r : ℝ) * (β + κ)) *
          dyadicBase l ^ ((r : ℝ) * (2 * δ))) := by
    intro N l a b hnear
    have h := gammaSplit_rightGoodBound_scale_le S hbox 𝒯 D κ C Cbar r i j
      β δ hκ hC hCbar (by rfl) hj hδ
      hδκ hδright N l a b hnear
    simpa [Lright, gammaSplitRightConstant] using h
  have hleft : ∀ N l : ℕ,
      ∫⁻ ω, gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω ^ r ∂P ≤
        (Fintype.card (gammaCell S (N + l + 1)) : ℝ≥0∞) ^ 2 * Lleft *
          (dyadicBase N ^ ((r : ℝ) * (β + κ)) *
            dyadicBase l ^ ((r : ℝ) * (2 * δ))) := by
    intro N l
    exact gammaSplit_leftGoodAnnulus_moment_scale_le S M D γ κ C Cbar
      hr hrq hC hCbar hm' hdet hann i j hi hj hij β δ Lleft hLleft' N l
  have hright : ∀ N l : ℕ,
      ∫⁻ ω, gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l) ω ^ r ∂P ≤
        (Fintype.card (gammaCell S (N + l + 1)) : ℝ≥0∞) ^ 2 * Lright *
          (dyadicBase N ^ ((r : ℝ) * (β + κ)) *
            dyadicBase l ^ ((r : ℝ) * (2 * δ))) := by
    intro N l
    exact gammaSplit_rightGoodAnnulus_moment_scale_le S M D γ κ C Cbar
      hr hrq hC hCbar hm' hdet hann i j hi hj hij β δ Lright hLright' N l
  obtain ⟨G, hGmeas, KG, hKG, hGmoment, hKGformula, hGpoint⟩ :=
    gammaSplit_good_global_envelope_moment S M D i j β κ δ hr
      hδ hreserveκ hreserveδ hm hLleft hLright hleft hright
  have hbad : ∀ (ω : Ω) (N l : ℕ),
      gammaSplitLeftBadStepSupAnnulus S M D i j N (N + l) ω +
        gammaSplitRightBadStepSupAnnulus S M D i j N (N + l) ω ≤
      Bbad * dyadicBase N ^ β * dyadicBase l ^ δ := by
    intro ω N l
    have hl := gammaSplit_leftBadStepSupAnnulus_le S hbox M D γ C hC
      hdet i j hi hj β δ (by rfl) hδ hδleft ω N l
    have hr' := gammaSplit_rightBadStepSupAnnulus_le S hbox M D γ C hC
      hdet i j hi hj β δ (by rfl) hδ hδright ω N l
    calc
      _ ≤ (∑ k ∈ gammaBadIntermediate 𝒯 D i j,
          ENNReal.ofReal (C ^ 2 * 24 ^ (𝒯.deg i - 𝒯.deg k) *
            4 ^ (𝒯.deg k - 𝒯.deg j)) * dyadicBase N ^ β *
              dyadicBase l ^ δ) +
          (∑ k ∈ gammaBadIntermediate 𝒯 D i j,
          ENNReal.ofReal (C ^ 2 * 24 ^ (𝒯.deg k - 𝒯.deg j) *
            4 ^ (𝒯.deg i - 𝒯.deg k)) * dyadicBase N ^ β *
              dyadicBase l ^ δ) := add_le_add hl hr'
      _ = Bbad * dyadicBase N ^ β * dyadicBase l ^ δ := by
        dsimp [Bbad, gammaSplitBadConstant]
        have hleft :
            (∑ k ∈ gammaBadIntermediate 𝒯 D i j,
              ENNReal.ofReal (C ^ 2 * 24 ^ (𝒯.deg i - 𝒯.deg k) *
                4 ^ (𝒯.deg k - 𝒯.deg j)) * dyadicBase N ^ β *
                dyadicBase l ^ δ) =
              (∑ k ∈ gammaBadIntermediate 𝒯 D i j,
                ENNReal.ofReal (C ^ 2 * 24 ^ (𝒯.deg i - 𝒯.deg k) *
                  4 ^ (𝒯.deg k - 𝒯.deg j))) * dyadicBase N ^ β *
                dyadicBase l ^ δ := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
        have hright :
            (∑ k ∈ gammaBadIntermediate 𝒯 D i j,
              ENNReal.ofReal (C ^ 2 * 24 ^ (𝒯.deg k - 𝒯.deg j) *
                4 ^ (𝒯.deg i - 𝒯.deg k)) * dyadicBase N ^ β *
                dyadicBase l ^ δ) =
              dyadicBase N ^ β * dyadicBase l ^ δ *
                (∑ k ∈ gammaBadIntermediate 𝒯 D i j,
                  ENNReal.ofReal (C ^ 2 * 24 ^ (𝒯.deg k - 𝒯.deg j) *
                    4 ^ (𝒯.deg i - 𝒯.deg k))) := by
          calc
            _ = ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
                dyadicBase N ^ β * dyadicBase l ^ δ *
                  ENNReal.ofReal (C ^ 2 * 24 ^ (𝒯.deg k - 𝒯.deg j) *
                    4 ^ (𝒯.deg i - 𝒯.deg k)) := by
              apply Finset.sum_congr rfl
              intro k hk
              ring
            _ = _ := by rw [Finset.mul_sum]
        rw [hleft, hright]
        ring
  have hGfull : ∀ (ω : Ω) (N l : ℕ),
      gammaProductLeftStepSupAnnulus S
          (fun x y ω => (M ω).gammaMap x y (Pi.single i 1) j) N (N + l) ω +
        gammaProductRightStepSupAnnulus S
          (fun x y ω => (M ω).gammaMap x y (Pi.single i 1) j) N (N + l) ω ≤
      (G ω + Bbad) * dyadicBase N ^ β * dyadicBase l ^ δ := by
    intro ω N l
    have hl := gammaSplit_leftStepSupAnnulus_le S M D i j N (N + l) ω hj
    have hr' := gammaSplit_rightStepSupAnnulus_le S M D i j N (N + l) ω hj
    calc
      _ ≤ (gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω +
          gammaSplitLeftBadStepSupAnnulus S M D i j N (N + l) ω) +
          (gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l) ω +
          gammaSplitRightBadStepSupAnnulus S M D i j N (N + l) ω) :=
        add_le_add hl hr'
      _ = (gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω +
          gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l) ω) +
          (gammaSplitLeftBadStepSupAnnulus S M D i j N (N + l) ω +
          gammaSplitRightBadStepSupAnnulus S M D i j N (N + l) ω) := by ring
      _ ≤ G ω * dyadicBase N ^ β * dyadicBase l ^ δ +
          Bbad * dyadicBase N ^ β * dyadicBase l ^ δ :=
        add_le_add (hGpoint ω N l) (hbad ω N l)
      _ = _ := by ring
  obtain ⟨A0, hA0meas, KA, hKAtop, hA0moment, hKAeq, hA0eq, hA0point⟩ :=
    gammaSplit_cell_envelope_moment S hbox M D γ κ C hr
      (by omega : r ≤ q) hκ hC
      hreserveκ hm' hdet hann i j hi hj hij
  have hA0point' : ∀ (ω : Ω) (N : ℕ), ∀ x y : S,
      parabolicNorm ((x : ParabolicSpace) - y) ≤ 1 / (2 : ℝ) ^ N →
      ‖(M ω).gammaMap (hsParabolicCellApprox S N x)
          (hsParabolicCellApprox S N y) (Pi.single i 1) j‖ₑ ≤
        A0 ω * dyadicBase N ^ β := by
    intro ω N x y hxy
    have h := hA0point ω N x y hxy
    simpa only [β] using h
  obtain ⟨B, hBmeas, hBmoment, hBpoint⟩ :=
      gammaSplit_unit_envelope_moment_of_split S hbox
      (fun x y ω => (M ω).gammaMap x y (Pi.single i 1) j) β δ r hr
      A0 G Bbad hA0meas hGmeas hA0moment hA0eq hGmoment hKAtop hKG hBbad
      hA0point' hGfull hcont (by dsimp [β]; linarith) hδ
  let KB : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ β) ^ r *
      (Fintype.card (Fin 3) : ℝ≥0∞) ^ ((r : ℝ) - 1) *
        (KA + (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ r * KG +
          (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)⁻¹ ^ r * Bbad ^ r)
  have hKB : KB ≠ ∞ := by
    have hden : 1 - ((2 : ℝ≥0∞)⁻¹) ^ δ ≠ 0 := by
      exact ne_of_gt (tsub_pos_iff_lt.2
        (ENNReal.rpow_lt_one (by norm_num) hδ))
    dsimp [KB]
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · finiteness
      · finiteness
    · apply ENNReal.add_ne_top.mpr
      refine ⟨ENNReal.add_ne_top.mpr ?_, ?_⟩
      · exact ⟨hKAtop, ENNReal.mul_ne_top
          (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hden)) hKG⟩
      · exact ENNReal.mul_ne_top
          (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hden))
            (ENNReal.pow_ne_top hBbad)
  have hBmoment' : ∫⁻ ω, B ω ^ r ∂P ≤ KB := by
    simpa [KB] using hBmoment
  have hKGsource :
      (2 : ℝ≥0∞) ^ ((r : ℝ) - 1) * (512 : ℝ≥0∞) ^ 2 *
          (Lleft + Lright) *
            (1 - ((2 : ℝ≥0∞)⁻¹) ^
              (min ((r : ℝ) * κ - 10) ((r : ℝ) * δ - 10)))⁻¹ *
            (1 - ((2 : ℝ≥0∞)⁻¹) ^
              (min ((r : ℝ) * κ - 10) ((r : ℝ) * δ - 10)))⁻¹ =
        gammaSplitGlobalConstant 𝒯 D i j κ C Cbar δ r := by
    dsimp [Lleft, Lright, gammaSplitGlobalConstant,
      gammaSplitLeftConstant, gammaSplitRightConstant]
    
  have hKBformula : KB = gammaSplitUnitConstant 𝒯 D i j κ C Cbar δ r := by
    dsimp [KB]
    rw [hKAeq, hKGformula, hKGsource]
    dsimp [KB, gammaSplitUnitConstant, Bbad,
      gammaSplitCellConstant, gammaSplitBadConstant, β]
  refine ⟨B, hBmeas, KB, hKB, hBmoment', hKBformula, ?_⟩
  filter_upwards [hBpoint] with ω hω
  intro x y hxy0 hxy1
  have h := hω y x (by simpa only [parabolicNorm_sub_comm] using hxy0)
    (by simpa only [parabolicNorm_sub_comm] using hxy1)
  simpa only [parabolicNorm_sub_comm] using h

private theorem gammaSplit_unit_coordinate_envelope_deterministic
    (S : Set ParabolicSpace)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ C : ℝ) (i j : ι) {r : ℕ} (_hr : 1 ≤ r)
    (hC : 0 ≤ C)
    (hdet : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
      ∀ ω x y, |(M ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j))
    (hi : 𝒯.deg i < γ) (hj : 𝒯.deg j < 𝒯.deg i)
    (hij : (i, j) ∈ D) :
    ∃ B : Ω → ℝ≥0∞, AEMeasurable B P ∧
      ∃ KB : ℝ≥0∞, KB ≠ ∞ ∧
        (∫⁻ ω, B ω ^ r ∂P ≤ KB) ∧
        KB = (ENNReal.ofReal C) ^ r ∧
        (∀ᵐ ω ∂P, ∀ x y : S, 0 < parabolicNorm
          ((x : ParabolicSpace) - y) →
          parabolicNorm ((x : ParabolicSpace) - y) ≤ 20 →
          ‖(M ω).gammaMap y x (Pi.single i 1) j‖ₑ ≤
            B ω * ENNReal.ofReal (parabolicNorm
              ((x : ParabolicSpace) - y)) ^ (𝒯.deg i - 𝒯.deg j)) := by
  let B : Ω → ℝ≥0∞ := fun _ => ENNReal.ofReal C
  let KB : ℝ≥0∞ := (ENNReal.ofReal C) ^ r
  have hKB : KB ≠ ∞ := by
    dsimp [KB]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  refine ⟨B, aemeasurable_const, KB, hKB, ?_, rfl, ?_⟩
  · dsimp [B, KB]
    simp [MeasureTheory.lintegral_const]
  · filter_upwards with ω
    intro x y hxy0 hxy1
    have h := hdet i j hij hi hj ω x y
    have hdist : parabolicSemigroup.scaleDist y x =
        parabolicNorm ((x : ParabolicSpace) - y) := by
      change parabolicNorm ((y : ParabolicSpace) - x) =
        parabolicNorm ((x : ParabolicSpace) - y)
      exact parabolicNorm_sub_comm _ _
    calc
      ‖(M ω).gammaMap y x (Pi.single i 1) j‖ₑ =
          ENNReal.ofReal |(M ω).gammaMap y x (Pi.single i 1) j| := by
            rw [Real.enorm_eq_ofReal_abs]
      _ ≤ ENNReal.ofReal (C * parabolicNorm
          ((x : ParabolicSpace) - y) ^ (𝒯.deg i - 𝒯.deg j)) := by
            rw [hdist] at h
            exact ENNReal.ofReal_le_ofReal h
      _ = ENNReal.ofReal C * ENNReal.ofReal
          (parabolicNorm ((x : ParabolicSpace) - y) ^
            (𝒯.deg i - 𝒯.deg j)) := by
            rw [ENNReal.ofReal_mul hC]
      _ = B ω * ENNReal.ofReal (parabolicNorm
          ((x : ParabolicSpace) - y)) ^ (𝒯.deg i - 𝒯.deg j) := by
            dsimp [B]
            rw [ENNReal.ofReal_rpow_of_nonneg
              (parabolicNorm_nonneg _) (by linarith)]

theorem gammaSplit_unit_coordinate_envelope_full
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ κ C Cbar δ : ℝ) (i j : ι) {q r : ℕ} (hr : 1 ≤ r) (hrq : 2 * r ≤ q)
    (hκ : 0 < κ) (hC : 0 ≤ C) (hCbar : C ≤ Cbar)
    (hreserveκ : 10 < (r : ℝ) * κ)
    (hδ : 0 < δ) (hreserveδ : 10 < (r : ℝ) * δ) (hδκ : 2 * δ ≤ κ)
    (hδleft : ∀ k, 𝒯.deg j < 𝒯.deg k → 𝒯.deg k < 𝒯.deg i →
      δ ≤ (𝒯.deg k - 𝒯.deg j) / 2)
    (hδright : ∀ k, 𝒯.deg j < 𝒯.deg k → 𝒯.deg k < 𝒯.deg i →
      δ ≤ (𝒯.deg i - 𝒯.deg k) / 2)
    (hm : ∀ x y a b, AEMeasurable
      (fun ω => (M ω).gammaMap x y (Pi.single a 1) b) P)
    (hdet : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
      ∀ ω x y, |(M ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j))
    (hann : ∀ i j, (i, j) ∉ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x y,
      (∫⁻ ω, ‖(M ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P) ≤
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ q)
    (hcont : ∀ ω, Continuous (fun z : S × S =>
      (M ω).gammaMap z.1 z.2 (Pi.single i 1) j))
    (hi : 𝒯.deg i < γ) (hj : 𝒯.deg j < 𝒯.deg i) :
    ∃ B : Ω → ℝ≥0∞, AEMeasurable B P ∧
      ∃ KB : ℝ≥0∞, KB ≠ ∞ ∧
        (∫⁻ ω, B ω ^ r ∂P ≤ KB) ∧
        KB ≤ (1 + gammaSplitUnitProfile 𝒯 D i j κ
          (max 1 Cbar) δ r) * (ENNReal.ofReal C) ^ r ∧
        (∀ᵐ ω ∂P, ∀ x y : S, 0 < parabolicNorm
          ((x : ParabolicSpace) - y) →
          parabolicNorm ((x : ParabolicSpace) - y) ≤ 20 →
          ‖(M ω).gammaMap y x (Pi.single i 1) j‖ₑ ≤
            B ω * ENNReal.ofReal (parabolicNorm
              ((x : ParabolicSpace) - y)) ^ (𝒯.deg i - 𝒯.deg j)) := by
  classical
  by_cases hij : (i, j) ∈ D
  · obtain ⟨B, hBmeas, KB, hKB, hBmoment, hKBeq, hBpoint⟩ :=
      gammaSplit_unit_coordinate_envelope_deterministic (P := P) S M D γ C i j
        hr hC hdet hi hj hij
    refine ⟨B, hBmeas, KB, hKB, hBmoment, ?_, hBpoint⟩
    calc
      KB = (ENNReal.ofReal C) ^ r := hKBeq
      _ = 1 * (ENNReal.ofReal C) ^ r := by rw [one_mul]
      _ ≤ (1 + gammaSplitUnitProfile 𝒯 D i j κ
          (max 1 Cbar) δ r) * (ENNReal.ofReal C) ^ r := by
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (by positivity)) (by positivity)
  · obtain ⟨B, hBmeas, KB, hKB, hBmoment, hKBeq, hBpoint⟩ :=
      gammaSplit_unit_coordinate_envelope S hbox M D γ κ C Cbar δ i j
        hr hrq hκ hC hCbar hreserveκ hδ hreserveδ hδκ hδleft hδright hm hdet hann
        hcont hi hj hij
    refine ⟨B, hBmeas, KB, hKB, hBmoment, ?_, hBpoint⟩
    calc
      KB = gammaSplitUnitConstant 𝒯 D i j κ C Cbar δ r := hKBeq
      _ ≤ gammaSplitUnitProfile 𝒯 D i j κ (max 1 Cbar) δ r *
          (ENNReal.ofReal C) ^ r :=
        gammaSplitUnitConstant_le_profile_mul_source 𝒯 D i j κ C Cbar δ r
          hC hCbar
      _ ≤ (1 + gammaSplitUnitProfile 𝒯 D i j κ (max 1 Cbar) δ r) *
          (ENNReal.ofReal C) ^ r := by
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left (by positivity)) (by positivity)

end RegularityStructures

end
