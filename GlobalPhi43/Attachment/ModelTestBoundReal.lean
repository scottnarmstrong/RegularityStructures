module

public import GlobalPhi43.Attachment.CutoffEstimate
public import GlobalPhi43.Attachment.PartitionIntegral
public import GlobalPhi43.Attachment.PartitionScaling
import Mathlib.Tactic.Ring

/-! Uniform model-to-compact-test conversion by one fixed finite partition. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43 GlobalPhi43.Local

open scoped ContDiff in
/-- The complete real-valued conversion estimate, with the noise-growth hypothesis, the literal C4 supremum,
exact max-metric enlargement radius three, and exponent m0 = 3. -/
theorem modelTestBound_real (N : ℕ) (κ : Kappa) :
    ∃ c : ℝ, 0 < c ∧
    ∀ (f₀ : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      Statements.IsModeratePhi43ModelOf N κ f₀ C Z → Statements.HasPhi43NoiseGrowth f₀ →
    ∀ (S : Set ParabolicSpace), IsCompact S → ∀ x ∈ S, ∀ T ∈ Set.Ioc (0 : ℝ) 1,
    ∀ φ : ParabolicSpace → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ {z | pdist 0 z ≤ 1} →
    ∀ τ : Symbol, homogeneity κ τ < 0 →
    ∀ f : ParabolicSpace → ℝ, Continuous f →
      (∃ (Cg : ℝ) (q : ℕ), ∀ z, |f z| ≤ Cg * (1 + parabolicNorm z) ^ q) →
      (∀ u, 0 < u → ∀ y, Z.regPi x (Pi.single τ 1) u y = parabolicSemigroup.apply u f y) →
      |∫ y, f y * rescaledTestFunction φ T x y| ≤
        c * (⨆ k ∈ Finset.range 5, ⨆ z, ‖iteratedFDeriv ℝ k φ z‖ₑ : ENNReal).toReal *
          (1 + (Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3}).toReal) ^ 3 * T ^ homogeneity κ τ := by
  classical
  let K : Set ParabolicSpace := {z | pdist 0 z ≤ 1}
  let r : ℝ := 1 / 64
  have hr : 0 < r := by norm_num [r]
  have hr1 : r ≤ 1 := by norm_num [r]
  have hK : IsCompact K := isCompact_pdist_ball (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨s, χ, B, hB0, hχ, hχs, hsum, hder⟩ := exists_parabolic_test_partition hK hr hr1
  let c : ℝ := 1 + ∑ _i : s, ∑ τ : Symbol, ∑ σ ∈ fMinus, |cutoffPairingCoefficient κ τ σ r B|
  have hc : 0 < c := by
    have hn : 0 ≤ ∑ _i : s, ∑ τ : Symbol, ∑ σ ∈ fMinus, |cutoffPairingCoefficient κ τ σ r B| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    exact add_pos_of_pos_of_nonneg zero_lt_one hn
  refine ⟨c, hc, ?_⟩
  intro f₀ C Z hZ hg S hS x hx T hT φ hφ hφc hφs τ hτ f hf hfg hreal
  let A := (⨆ k ∈ Finset.range 5, ⨆ z, ‖iteratedFDeriv ℝ k φ z‖ₑ : ENNReal).toReal
  let D : Set ParabolicSpace := {y | ∃ z ∈ S, pdist z y ≤ 3}
  let M := (Z.normOn (gamma κ) D).toReal
  let w : s → ParabolicSpace := fun i => x + parabolicDilate T (i.1 : ParabolicSpace)
  have hD := isCompact_parabolic_enlargement hS (by norm_num : (0 : ℝ) ≤ 3)
  have hfin : Z.normOn (gamma κ) D ≠ ⊤ := by
    obtain ⟨noise, hn, hm⟩ := hZ
    exact hm.2.2.1 D hD
  have hxD : x ∈ D := ⟨x, hx, by simp [pdist]⟩
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hA := (four_derivative_supremum_bound hφ hφc).2
  have hτF : τ ∈ fMinus := (mem_fMinus_iff_isFMinus τ).mpr ((homogeneity_neg_iff_isFMinus κ τ).mp hτ)
  have hτcut : homogeneity κ τ < gamma κ := by
    have hk := kappa_pos κ
    dsimp [gamma]; linarith
  obtain ⟨g, hgc, hQ⟩ := exists_negative_model_realisations hg hZ
  obtain ⟨Cg, q, hfg⟩ := hfg
  have hpoly : PolyBounded f := ⟨hf.measurable, Cg, q, hfg⟩
  have hfid : f = g x τ := function_realisation_unique hf (hgc x τ).1 hpoly (hgc x τ).2
    (fun u hu y => (hreal u hu y).symm.trans (hQ x τ hτF u hu y))
  have hsK : ∀ z, z ∉ K → φ z = 0 := by
    intro z hz
    by_contra hn
    exact hz (hφs (subset_closure hn))
  have hs4 : ∀ z, 4 < parabolicNorm z → φ z = 0 := by
    intro z hz
    by_contra hn
    have hd : pdist 0 z ≤ 1 := hφs (subset_closure hn)
    have hp := parabolicNorm_le_four_pdist 0 z
    simp only [zero_sub, parabolicNorm_neg] at hp
    linarith
  have hw (i : s) : pdist x (w i) ≤ T := by
    rw [show w i = x + parabolicDilate T (i.1 : ParabolicSpace) from rfl, pdist_scaled_center hT.1.le]
    have hi : pdist 0 (i.1 : ParabolicSpace) ≤ 1 := i.1.2
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hi hT.1.le
  have hwD (i : s) : w i ∈ D := ⟨x, hx, (hw i).trans (by linarith [hT.2])⟩
  have hsmall : 4 * (T * r) ≤ 1 := by dsimp [r]; linarith [hT.2]
  have hball (i : s) : ∀ y, parabolicNorm (y - w i) ≤ 4 * (T * r) → y ∈ D := by
    intro y hy
    refine ⟨x, hx, ?_⟩
    have hd := pdist_le_parabolicNorm (w i) y
    rw [parabolicNorm_sub_comm (w i) y] at hd
    have htri := pdist_triangle x (w i) y
    linarith [hw i, hT.2]
  have hR (i : s) : parabolicNorm (w i - x) ≤ 4 * T := by
    have hp := parabolicNorm_le_four_pdist (w i) x
    rw [pdist_symm (w i) x] at hp
    linarith [hw i]
  have hterm (i : s) (σ : Symbol) (hσ : σ ∈ fMinus) :
      |Z.gammaMap (w i) x (Pi.single τ 1) σ *
        ∫ y, g (w i) σ y * rescaledTestFunction (φ * χ i) T x y| ≤
      |cutoffPairingCoefficient κ τ σ r B| * A * (1 + M) ^ 3 * T ^ homogeneity κ τ := by
    let p := fun z => φ ((i.1 : ParabolicSpace) + parabolicDilate r z) *
      χ i ((i.1 : ParabolicSpace) + parabolicDilate r z)
    have hi (y : ParabolicSpace) : rescaledTestFunction (φ * χ i) T x y =
        r ^ 5 * rescaledTestFunction p (T * r) (w i) y :=
      rescaled_piece_recenter (φ * χ i) hT.1.ne' hr.ne' x (i.1 : ParabolicSpace) y
    have hint : (∫ y, g (w i) σ y * rescaledTestFunction (φ * χ i) T x y) =
        r ^ 5 * ∫ y, g (w i) σ y * rescaledTestFunction p (T * r) (w i) y := by
      simp_rw [hi]
      calc _ = ∫ y, r ^ 5 * (g (w i) σ y * rescaledTestFunction p (T * r) (w i) y) := by
            congr 1; funext y; ring
        _ = _ := integral_const_mul _ _
    rw [hint]
    have hσneg : homogeneity κ σ < 0 := (homogeneity_neg_iff_isFMinus κ σ).mpr
      ((mem_fMinus_iff_isFMinus σ).mp hσ)
    exact cutoff_recenter_estimate hZ hg hfin hxD (hwD i) hτcut hσneg hT.1 hr hr1 hsmall
      (hR i) (hball i) hφ (hχ i) hA (hder i) (hχs i) (hgc (w i) σ).1 (hgc (w i) σ).2
      (fun u hu y => hQ (w i) σ hσ u hu y)
  have hcτ : (∑ _i : s, ∑ σ ∈ fMinus, |cutoffPairingCoefficient κ τ σ r B|) ≤ c := by
    have heach : (∑ σ ∈ fMinus, |cutoffPairingCoefficient κ τ σ r B|) ≤
        ∑ υ : Symbol, ∑ σ ∈ fMinus, |cutoffPairingCoefficient κ υ σ r B| :=
      Finset.single_le_sum (f := fun υ : Symbol => ∑ σ ∈ fMinus, |cutoffPairingCoefficient κ υ σ r B|)
        (fun υ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ τ)
    have hsumle := Finset.sum_le_sum (s := Finset.univ) (fun (_i : s) _ => heach)
    exact hsumle.trans (by dsimp [c]; linarith)
  change |∫ y, f y * rescaledTestFunction φ T x y| ≤ c * A * (1 + M) ^ 3 * T ^ homogeneity κ τ
  rw [hfid, integral_partition_recenter Z hgc hQ hτF x w hφ hs4 hsK χ hχ hsum hT.1]
  calc _ ≤ ∑ i : s, ∑ σ ∈ fMinus, |Z.gammaMap (w i) x (Pi.single τ 1) σ *
        ∫ y, g (w i) σ y * rescaledTestFunction (φ * χ i) T x y| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : s, ∑ σ ∈ fMinus, |cutoffPairingCoefficient κ τ σ r B| * A * (1 + M) ^ 3 * T ^ homogeneity κ τ :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun σ hσ => hterm i σ hσ
    _ = (∑ _i : s, ∑ σ ∈ fMinus, |cutoffPairingCoefficient κ τ σ r B|) * A * (1 + M) ^ 3 * T ^ homogeneity κ τ := by
      simp only [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcτ hA0) (pow_nonneg (by linarith) 3))
      (Real.rpow_nonneg hT.1.le _)

end GlobalPhi43.Attachment
