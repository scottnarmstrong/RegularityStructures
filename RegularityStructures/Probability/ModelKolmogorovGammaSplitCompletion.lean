/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaSplitAnnulus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.CompletePartialOrder

/-!
# Fixed-coarse-scale completion for the split Gamma telescope

The deterministic channels in the Chen source have no reserve gain.  They are
therefore summed with the fine endpoint scale while the coarse pair scale is
held fixed.  This module contains the source-independent completion lemmas;
the stochastic estimate for the good channels is supplied by the induction
module.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace RegularityStructures

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒯 : RegularityStructure ι}

private theorem gammaSplit_dyadic_selection {d : ℝ}
    (hd0 : 0 < d) (hd1 : d ≤ 1) :
    ∃ n : ℕ, d ≤ 1 / (2 : ℝ) ^ n ∧ 1 / (2 : ℝ) ^ n ≤ 2 * d := by
  let x : UnitInterval := ⟨d, ⟨by linarith, hd1⟩⟩
  let y : UnitInterval := ⟨0, by norm_num⟩
  have hxy : edist x y ≠ 0 := by
    simp only [edist_dist, Subtype.dist_eq, Real.dist_eq]
    change ENNReal.ofReal |d - 0| ≠ 0
    rw [sub_zero, abs_of_pos hd0]
    exact ne_of_gt (ENNReal.ofReal_pos.2 hd0)
  obtain ⟨n, hn, hn'⟩ := dyadicBase_selection x y hxy
  have he : edist x y = ENNReal.ofReal d := by
    simp only [edist_dist, Subtype.dist_eq, Real.dist_eq]
    change ENNReal.ofReal |d - 0| = ENNReal.ofReal d
    rw [sub_zero, abs_of_pos hd0]
  have hn'' : ENNReal.ofReal d ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ n) := by
    simpa only [he, ← ofReal_inv_two_pow] using hn
  have hn''' : ENNReal.ofReal (1 / (2 : ℝ) ^ n) ≤ ENNReal.ofReal (2 * d) := by
    rw [ofReal_inv_two_pow]
    rw [ENNReal.ofReal_mul (by norm_num)]
    norm_num
    simpa only [he] using hn'
  refine ⟨n, ?_, ?_⟩
  · exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hn''
  · exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hn'''

private theorem gammaSplit_rpow_ofReal_mul (d : ℝ) (_hd : 0 ≤ d) (β : ℝ)
    (hβ : 0 ≤ β) :
    ENNReal.ofReal (2 * d) ^ β =
      (2 : ℝ≥0∞) ^ β * ENNReal.ofReal d ^ β := by
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ hβ,
    ENNReal.ofReal_ofNat]

/-- The good Chen channels, normalized at the coarse annulus scale and at a
positive fine degree exponent. -/
def gammaSplitGoodGlobalTerm
    (S : Set ParabolicSpace)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (β δ : ℝ) (N l : ℕ) (ω : Ω) : ℝ≥0∞ :=
  (gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω +
      gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l) ω) *
    dyadicBase N ^ (-β) * dyadicBase l ^ (-δ)

/-- The global good-channel envelope is the supremum over all coarse annuli
and all endpoint refinements. -/
def gammaSplitGoodGlobalEnvelope
    (S : Set ParabolicSpace)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (β δ : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ N : ℕ, ⨆ l : ℕ, gammaSplitGoodGlobalTerm S M D i j β δ N l ω

omit [IsProbabilityMeasure P] in
theorem gammaSplitGoodGlobalTerm_aemeasurable
    (S : Set ParabolicSpace)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (β δ : ℝ) (N l : ℕ)
    (hm : ∀ x y a b, AEMeasurable
      (fun ω => (M ω).gammaMap x y (Pi.single a 1) b) P) :
    AEMeasurable (gammaSplitGoodGlobalTerm S M D i j β δ N l) P := by
  change AEMeasurable
    (fun ω => (gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω +
      gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l) ω) *
        dyadicBase N ^ (-β) * dyadicBase l ^ (-δ)) P
  exact (((gammaSplitLeftGoodStepSupAnnulus_aemeasurable S M D i j N (N + l)
    hm).add
      (gammaSplitRightGoodStepSupAnnulus_aemeasurable S M D i j N (N + l)
        hm)).mul_const _).mul_const _

omit [IsProbabilityMeasure P] in
theorem gammaSplitGoodGlobalEnvelope_aemeasurable
    (S : Set ParabolicSpace)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (β δ : ℝ)
    (hm : ∀ x y a b, AEMeasurable
      (fun ω => (M ω).gammaMap x y (Pi.single a 1) b) P) :
    AEMeasurable (gammaSplitGoodGlobalEnvelope S M D i j β δ) P := by
  unfold gammaSplitGoodGlobalEnvelope
  apply AEMeasurable.iSup
  intro N
  apply AEMeasurable.iSup
  intro l
  exact gammaSplitGoodGlobalTerm_aemeasurable S M D i j β δ N l hm

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem gammaSplitGoodGlobalTerm_le_envelope_mul_scale
    (S : Set ParabolicSpace)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (β δ : ℝ) (N l : ℕ) (ω : Ω) :
    gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω +
        gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l) ω ≤
      gammaSplitGoodGlobalEnvelope S M D i j β δ ω *
        dyadicBase N ^ β * dyadicBase l ^ δ := by
  have hterm : gammaSplitGoodGlobalTerm S M D i j β δ N l ω ≤
      gammaSplitGoodGlobalEnvelope S M D i j β δ ω := by
    unfold gammaSplitGoodGlobalEnvelope
    exact le_iSup_of_le N (le_iSup_of_le l le_rfl)
  have hcancelN : dyadicBase N ^ (-β) * dyadicBase N ^ β = 1 := by
    rw [← ENNReal.rpow_add _ _ (dyadicBase_pos _).ne' (dyadicBase_ne_top _)]
    simp
  have hcancelL : dyadicBase l ^ (-δ) * dyadicBase l ^ δ = 1 := by
    rw [← ENNReal.rpow_add _ _ (dyadicBase_pos _).ne' (dyadicBase_ne_top _)]
    simp
  calc
    _ = ((gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω +
        gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l) ω) *
        dyadicBase N ^ (-β) * dyadicBase l ^ (-δ)) *
        (dyadicBase N ^ β * dyadicBase l ^ δ) := by
      calc
        _ = (gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω +
            gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l) ω) * 1 := by
          rw [mul_one]
        _ = (gammaSplitLeftGoodStepSupAnnulus S M D i j N (N + l) ω +
            gammaSplitRightGoodStepSupAnnulus S M D i j N (N + l) ω) *
            (dyadicBase N ^ (-β) * dyadicBase N ^ β) *
            (dyadicBase l ^ (-δ) * dyadicBase l ^ δ) := by
          rw [hcancelN, hcancelL]
          simp
        _ = _ := by ring
    _ ≤ _ := by
      simpa only [gammaSplitGoodGlobalTerm, mul_assoc] using
        (mul_le_mul_of_nonneg_right hterm
          (show 0 ≤ dyadicBase N ^ β * dyadicBase l ^ δ by positivity))

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem gammaSplitCellApprox_tail_le_of_fixed_coarse_scale
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (F : S → S → Ω → ℝ) (β δ : ℝ) (N : ℕ) (ω : Ω)
    (hF : Continuous (fun z : S × S => F z.1 z.2 ω))
    (x y : S)
    (H : ℝ≥0∞) (hH : H ≠ ∞) (hδ : 0 < δ)
    (hstep : ∀ l : ℕ,
      ‖F (hsParabolicCellApprox S (N + l) x)
          (hsParabolicCellApprox S (N + l) y) ω -
        F (hsParabolicCellApprox S (N + l + 1) x)
          (hsParabolicCellApprox S (N + l + 1) y) ω‖ₑ ≤
        H * dyadicBase N ^ β * dyadicBase l ^ δ) :
    ‖F (hsParabolicCellApprox S N x)
        (hsParabolicCellApprox S N y) ω - F x y ω‖ₑ ≤
      H * dyadicBase N ^ β /
        (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ) := by
  let a : ℝ≥0∞ := ((2 : ℝ≥0∞)⁻¹) ^ δ
  let C : ℝ≥0∞ := H * dyadicBase N ^ β
  have ha : a < 1 := by
    dsimp [a]
    exact ENNReal.rpow_lt_one (by norm_num) hδ
  have hC : C ≠ ∞ := by
    dsimp [C]
    exact ENNReal.mul_ne_top
      hH (ENNReal.rpow_ne_top_of_ne_zero (dyadicBase_pos _).ne'
        (dyadicBase_ne_top _))
  have hscale (l : ℕ) :
      C * a ^ l = H * dyadicBase N ^ β * dyadicBase l ^ δ := by
    dsimp [C, a]
    simp only [dyadicBase_rpow_eq_geometric]
  have hstep' (l : ℕ) :
      edist (F (hsParabolicCellApprox S (N + l) x)
          (hsParabolicCellApprox S (N + l) y) ω)
        (F (hsParabolicCellApprox S (N + l + 1) x)
          (hsParabolicCellApprox S (N + l + 1) y) ω) ≤ C * a ^ l := by
    have hfull : ‖F (hsParabolicCellApprox S (N + l) x)
          (hsParabolicCellApprox S (N + l) y) ω -
        F (hsParabolicCellApprox S (N + l + 1) x)
          (hsParabolicCellApprox S (N + l + 1) y) ω‖ₑ ≤ C * a ^ l := by
      calc
        _ ≤ H * dyadicBase N ^ β * dyadicBase l ^ δ := hstep l
        _ = C * a ^ l := (hscale l).symm
    simpa only [edist_eq_enorm_sub] using hfull
  have hlim : Tendsto (fun l =>
      F (hsParabolicCellApprox S (N + l) x)
        (hsParabolicCellApprox S (N + l) y) ω) atTop
      (𝓝 (F x y ω)) := by
    have hx := (hsParabolicCellApprox_tendsto S hbox x).comp
      (tendsto_add_atTop_nat N)
    have hy := (hsParabolicCellApprox_tendsto S hbox y).comp
      (tendsto_add_atTop_nat N)
    have hx' : Tendsto (fun l => hsParabolicCellApprox S (N + l) x)
        atTop (𝓝 x) := by
      simpa only [Function.comp_def, Nat.add_comm] using hx
    have hy' : Tendsto (fun l => hsParabolicCellApprox S (N + l) y)
        atTop (𝓝 y) := by
      simpa only [Function.comp_def, Nat.add_comm] using hy
    exact (hF.tendsto (x, y)).comp (hx'.prodMk_nhds hy')
  have htail := edist_le_of_edist_le_geometric_of_tendsto₀ a C hstep' hlim
  dsimp [C, a] at htail ⊢
  calc
    _ ≤ H * dyadicBase N ^ β /
        (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ) := by
      simpa only [edist_eq_enorm_sub] using htail
    _ ≤ H * dyadicBase N ^ β /
        (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ) := by
      exact le_rfl

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem gammaSplit_pointwise_bound_of_envelopes
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (F : S → S → Ω → ℝ) (β δ : ℝ) (ω : Ω)
    (A G B : ℝ≥0∞) (hGB : G + B ≠ ∞) (hβ : 0 ≤ β) (hδ : 0 < δ)
    (hcont : Continuous (fun z : S × S => F z.1 z.2 ω))
    (hvalue : ∀ N : ℕ, ∀ x y : S,
      parabolicNorm ((x : ParabolicSpace) - y) ≤ 1 / (2 : ℝ) ^ N →
      ‖F (hsParabolicCellApprox S N x)
          (hsParabolicCellApprox S N y) ω‖ₑ ≤ A * dyadicBase N ^ β)
    (hstep : ∀ N l : ℕ, ∀ x y : S,
      parabolicNorm ((x : ParabolicSpace) - y) ≤ 1 / (2 : ℝ) ^ N →
      ‖F (hsParabolicCellApprox S (N + l) x)
          (hsParabolicCellApprox S (N + l) y) ω -
        F (hsParabolicCellApprox S (N + l + 1) x)
          (hsParabolicCellApprox S (N + l + 1) y) ω‖ₑ ≤
        (G + B) * dyadicBase N ^ β * dyadicBase l ^ δ)
    (x y : S) (hd0 : 0 < parabolicNorm ((x : ParabolicSpace) - y))
    (hd1 : parabolicNorm ((x : ParabolicSpace) - y) ≤ 1) :
    ‖F x y ω‖ₑ ≤
      (A + (G + B) / (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)) *
        (2 : ℝ≥0∞) ^ β * ENNReal.ofReal
          (parabolicNorm ((x : ParabolicSpace) - y)) ^ β := by
  let d : ℝ := parabolicNorm ((x : ParabolicSpace) - y)
  obtain ⟨N, hN, hN'⟩ := gammaSplit_dyadic_selection (d := d)
    (by simpa [d] using hd0) (by simpa [d] using hd1)
  have hNreal : d ≤ 1 / (2 : ℝ) ^ N := hN
  have hcell := hvalue N x y hNreal
  have htail := gammaSplitCellApprox_tail_le_of_fixed_coarse_scale S hbox F β δ N ω
    hcont x y (G + B) hGB hδ
    (fun l => hstep N l x y hNreal)
  have hsum : ‖F x y ω‖ₑ ≤
      (A + (G + B) / (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)) * dyadicBase N ^ β := by
    calc
      ‖F x y ω‖ₑ ≤ ‖F x y ω -
          F (hsParabolicCellApprox S N x)
            (hsParabolicCellApprox S N y) ω‖ₑ +
          ‖F (hsParabolicCellApprox S N x)
            (hsParabolicCellApprox S N y) ω‖ₑ := by
        calc
          ‖F x y ω‖ₑ = ‖(F x y ω -
              F (hsParabolicCellApprox S N x)
                (hsParabolicCellApprox S N y) ω) +
              F (hsParabolicCellApprox S N x)
                (hsParabolicCellApprox S N y) ω‖ₑ := by
            congr 1
            ring
          _ ≤ _ := enorm_add_le _ _
      _ ≤ (G + B) * dyadicBase N ^ β /
          (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ) + A * dyadicBase N ^ β := by
        have htail' : ‖F x y ω -
              F (hsParabolicCellApprox S N x)
                (hsParabolicCellApprox S N y) ω‖ₑ ≤
            (G + B) * dyadicBase N ^ β /
              (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ) := by
          rw [show F x y ω -
              F (hsParabolicCellApprox S N x)
                (hsParabolicCellApprox S N y) ω =
              -(F (hsParabolicCellApprox S N x)
                (hsParabolicCellApprox S N y) ω - F x y ω) by ring]
          simpa only [enorm_neg] using htail
        exact add_le_add htail' hcell
      _ = _ := by
        simp only [div_eq_mul_inv, add_mul, mul_add, mul_assoc, mul_comm,
          mul_left_comm]
        simp only [add_comm]
  have hscale : dyadicBase N ^ β ≤
      ENNReal.ofReal (2 * d) ^ β := by
    apply ENNReal.rpow_le_rpow
    · simpa only [← ofReal_inv_two_pow] using
        (ENNReal.ofReal_le_ofReal (by linarith : 1 / (2 : ℝ) ^ N ≤ 2 * d))
    · exact hβ
  calc
    _ ≤ (A + (G + B) / (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)) * dyadicBase N ^ β := hsum
    _ ≤ (A + (G + B) / (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)) *
        ENNReal.ofReal (2 * d) ^ β :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by
      rw [gammaSplit_rpow_ofReal_mul d (le_of_lt hd0) β hβ]
      simp only [d]
      simp only [mul_assoc]

omit [IsProbabilityMeasure P] in
theorem gammaSplitGoodGlobalEnvelope_moment_le
    (S : Set ParabolicSpace)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (β δ η : ℝ) (r : ℕ) (hr : 1 ≤ r)
    (_hδ : 0 < δ) (hη : 0 < η)
    (hm : ∀ x y a b, AEMeasurable
      (fun ω => (M ω).gammaMap x y (Pi.single a 1) b) P)
    {A : ℝ≥0∞} (hterm : ∀ N l : ℕ,
      ∫⁻ ω, gammaSplitGoodGlobalTerm S M D i j β δ N l ω ^ r ∂P ≤
        A * dyadicBase N ^ η * dyadicBase l ^ η) :
    ∫⁻ ω, gammaSplitGoodGlobalEnvelope S M D i j β δ ω ^ r ∂P ≤
      A * (1 - ((2 : ℝ≥0∞)⁻¹) ^ η)⁻¹ *
        (1 - ((2 : ℝ≥0∞)⁻¹) ^ η)⁻¹ := by
  have hmeas : ∀ N l, AEMeasurable
      (gammaSplitGoodGlobalTerm S M D i j β δ N l) P := by
    intro N l
    exact gammaSplitGoodGlobalTerm_aemeasurable S M D i j β δ N l hm
  have hinner : ∀ N : ℕ,
      ∫⁻ ω, (⨆ l : ℕ,
        gammaSplitGoodGlobalTerm S M D i j β δ N l ω) ^ r ∂P ≤
        ∑' l : ℕ,
          ∫⁻ ω, gammaSplitGoodGlobalTerm S M D i j β δ N l ω ^ r ∂P := by
    intro N
    apply lintegral_iSup_pow_le_tsum_lintegral_pow hr
    intro l
    exact hmeas N l
  have hsup0 :
      ∫⁻ ω, (⨆ N : ℕ, ⨆ l : ℕ,
        gammaSplitGoodGlobalTerm S M D i j β δ N l ω) ^ r ∂P ≤
        ∑' N : ℕ, ∫⁻ ω, (⨆ l : ℕ,
          gammaSplitGoodGlobalTerm S M D i j β δ N l ω) ^ r ∂P := by
    apply lintegral_iSup_pow_le_tsum_lintegral_pow hr
    intro N
    exact AEMeasurable.iSup (fun l => hmeas N l)
  have hsup :
      ∫⁻ ω, (⨆ N : ℕ, ⨆ l : ℕ,
        gammaSplitGoodGlobalTerm S M D i j β δ N l ω) ^ r ∂P ≤
        ∑' N : ℕ, ∑' l : ℕ,
          ∫⁻ ω, gammaSplitGoodGlobalTerm S M D i j β δ N l ω ^ r ∂P := by
    exact hsup0.trans (ENNReal.tsum_le_tsum hinner)
  calc
    _ ≤ ∑' N : ℕ, ∑' l : ℕ,
        ∫⁻ ω, gammaSplitGoodGlobalTerm S M D i j β δ N l ω ^ r ∂P := hsup
    _ ≤ ∑' N : ℕ, ∑' l : ℕ,
        A * dyadicBase N ^ η * dyadicBase l ^ η := by
      gcongr with N l
      exact hterm N l
    _ = A * (1 - ((2 : ℝ≥0∞)⁻¹) ^ η)⁻¹ *
        (1 - ((2 : ℝ≥0∞)⁻¹) ^ η)⁻¹ := by
      let b : ℝ≥0∞ := ((2 : ℝ≥0∞)⁻¹) ^ η
      have hb : b < 1 := by
        dsimp [b]
        exact ENNReal.rpow_lt_one (by norm_num) hη
      have hterm' (N l : ℕ) :
          A * dyadicBase N ^ η * dyadicBase l ^ η =
            (A * b ^ N) * b ^ l := by
        simp only [dyadicBase_rpow_eq_geometric]
        ring
      simp_rw [hterm']
      calc
        (∑' N : ℕ, ∑' l : ℕ, (A * b ^ N) * b ^ l) =
            ∑' N : ℕ, (A * b ^ N) * (∑' l : ℕ, b ^ l) := by
          apply tsum_congr
          intro N
          rw [ENNReal.tsum_mul_left]
        _ = ∑' N : ℕ, (A * b ^ N) * (1 - b)⁻¹ := by
          have hgeom : ∑' l : ℕ, b ^ l = (1 - b)⁻¹ := by
            rw [ENNReal.tsum_geometric]
          rw [hgeom]
        _ = A * (1 - b)⁻¹ * (1 - b)⁻¹ := by
          rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left,
            ENNReal.tsum_geometric]

theorem gammaSplit_box_distance_le_four
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (x y : S) :
    parabolicNorm ((x : ParabolicSpace) - y) ≤ 4 := by
  have hx := hbox x x.property
  have hy := hbox y y.property
  have ht : |(x : ParabolicSpace).1 - (y : ParabolicSpace).1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hx.1.1, hx.1.2, hy.1.1, hy.1.2]
  have hs (j : Fin 3) :
      |(x : ParabolicSpace).2 j - (y : ParabolicSpace).2 j| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hx.2 j |>.1, hx.2 j |>.2,
      hy.2 j |>.1, hy.2 j |>.2]
  have ht' : Real.sqrt |(x : ParabolicSpace).1 - (y : ParabolicSpace).1| ≤ 1 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by simpa using ht⟩
  unfold parabolicNorm
  calc
    Real.sqrt |(x : ParabolicSpace).1 - (y : ParabolicSpace).1| +
        ∑ j, |(x : ParabolicSpace).2 j - (y : ParabolicSpace).2 j| ≤
        1 + ∑ _ : Fin 3, (1 : ℝ) := by
      exact add_le_add ht' (Finset.sum_le_sum fun j _ => hs j)
    _ = 4 := by norm_num

omit [MeasurableSpace Ω] in
theorem gammaProductCellApprox_value_le_of_box
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (F : S → S → Ω → ℝ) (x y : S) (ω : Ω)
    (hxy : parabolicNorm ((x : ParabolicSpace) - y) ≤ 4) :
    ‖F (hsParabolicCellApprox S 0 x)
        (hsParabolicCellApprox S 0 y) ω‖ₑ ≤
      gammaProductCellSup S F 0 ω := by
  let i : gammaCell S 0 := ⟨hsParabolicCellIndex 0 x, x, rfl⟩
  let j : gammaCell S 0 := ⟨hsParabolicCellIndex 0 y, y, rfl⟩
  have hi : hsParabolicCellRepresentative S 0 i =
      hsParabolicCellApprox S 0 x := rfl
  have hj : hsParabolicCellRepresentative S 0 j =
      hsParabolicCellApprox S 0 y := rfl
  have hd := gammaProductCellApprox_distance_le S hbox 0 x y
  have hd0 : parabolicNorm
      ((hsParabolicCellRepresentative S 0 i : ParabolicSpace) -
        hsParabolicCellRepresentative S 0 j) ≤ 20 := by
    rw [hi, hj]
    calc
      _ ≤ parabolicNorm ((x : ParabolicSpace) - y) + 8 / (2 : ℝ) ^ 0 := hd
      _ = parabolicNorm ((x : ParabolicSpace) - y) + 8 := by norm_num
      _ ≤ 12 := by linarith [hxy]
      _ ≤ 20 := by norm_num
  have hd' : parabolicNorm
      ((hsParabolicCellRepresentative S 0 i : ParabolicSpace) -
        hsParabolicCellRepresentative S 0 j) ≤ 20 / (2 : ℝ) ^ 0 := by
    simpa only [pow_zero, div_one] using hd0
  rw [gammaProductCellSup]
  apply le_iSup_of_le i
  apply le_iSup_of_le j
  rw [ite_eq_left hd']
  simpa only [hi, hj] using
    (le_refl (‖F (hsParabolicCellApprox S 0 x)
      (hsParabolicCellApprox S 0 y) ω‖ₑ))

omit [MeasurableSpace Ω] in
theorem gammaProductCellApprox_step_le_of_box
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (F : S → S → Ω → ℝ) (n : ℕ) (x y : S) (ω : Ω) :
    ‖F (hsParabolicCellApprox S n x) (hsParabolicCellApprox S n y) ω -
        F (hsParabolicCellApprox S (n + 1) x)
          (hsParabolicCellApprox S (n + 1) y) ω‖ₑ ≤
      gammaProductLeftStepSupAnnulus S F 0 n ω +
        gammaProductRightStepSupAnnulus S F 0 n ω := by
  have hleft : gammaProductLeftStepSup S F n ω ≤
      gammaProductLeftStepSupAnnulus S F 0 n ω := by
    unfold gammaProductLeftStepSup gammaProductLeftStepSupAnnulus
    apply iSup_le
    intro a
    apply iSup_le
    intro b
    have hab := gammaSplit_box_distance_le_four S hbox
      (hsParabolicCellRepresentative S n
        (hsParabolicCellParent S n a))
      (hsParabolicCellRepresentative S (n + 1) b)
    apply le_iSup_of_le a
    apply le_iSup_of_le b
    have hab' : parabolicNorm
        ((hsParabolicCellRepresentative S n
          (hsParabolicCellParent S n a) : ParabolicSpace) -
          hsParabolicCellRepresentative S (n + 1) b) ≤
        20 / (2 : ℝ) ^ 0 := by
      have hab'' : parabolicNorm
          ((hsParabolicCellRepresentative S n
            (hsParabolicCellParent S n a) : ParabolicSpace) -
            hsParabolicCellRepresentative S (n + 1) b) ≤ 20 := by
        linarith [hab]
      simpa only [pow_zero, div_one] using hab''
    rw [ite_eq_left hab']
  have hright : gammaProductRightStepSup S F n ω ≤
      gammaProductRightStepSupAnnulus S F 0 n ω := by
    unfold gammaProductRightStepSup gammaProductRightStepSupAnnulus
    apply iSup_le
    intro a
    apply iSup_le
    intro b
    have hab := gammaSplit_box_distance_le_four S hbox
      (hsParabolicCellRepresentative S n
        (hsParabolicCellParent S n a))
      (hsParabolicCellRepresentative S (n + 1) b)
    apply le_iSup_of_le a
    apply le_iSup_of_le b
    have hab' : parabolicNorm
        ((hsParabolicCellRepresentative S n
          (hsParabolicCellParent S n a) : ParabolicSpace) -
          hsParabolicCellRepresentative S (n + 1) b) ≤
        20 / (2 : ℝ) ^ 0 := by
      have hab'' : parabolicNorm
          ((hsParabolicCellRepresentative S n
            (hsParabolicCellParent S n a) : ParabolicSpace) -
            hsParabolicCellRepresentative S (n + 1) b) ≤ 20 := by
        linarith [hab]
      simpa only [pow_zero, div_one] using hab''
    rw [ite_eq_left hab']
    simpa only [hsParabolicCellParentRepresentative] using (le_refl _)
  exact (gammaProductCellApprox_step_le S hbox F n x y ω).trans
    (add_le_add hleft hright)

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem gammaSplit_pointwise_bound_of_envelopes_global
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (F : S → S → Ω → ℝ) (β δ : ℝ) (ω : Ω)
    (A G B : ℝ≥0∞) (hGB : G + B ≠ ∞) (hβ : 0 ≤ β) (hδ : 0 < δ)
    (hcont : Continuous (fun z : S × S => F z.1 z.2 ω))
    (hvalue : ∀ N : ℕ, ∀ x y : S,
      parabolicNorm ((x : ParabolicSpace) - y) ≤ 1 / (2 : ℝ) ^ N →
      ‖F (hsParabolicCellApprox S N x)
          (hsParabolicCellApprox S N y) ω‖ₑ ≤ A * dyadicBase N ^ β)
    (hstepN : ∀ N l : ℕ, ∀ x y : S,
      parabolicNorm ((x : ParabolicSpace) - y) ≤ 1 / (2 : ℝ) ^ N →
      ‖F (hsParabolicCellApprox S (N + l) x)
          (hsParabolicCellApprox S (N + l) y) ω -
        F (hsParabolicCellApprox S (N + l + 1) x)
          (hsParabolicCellApprox S (N + l + 1) y) ω‖ₑ ≤
        (G + B) * dyadicBase N ^ β * dyadicBase l ^ δ)
    (hvalue0 : ∀ x y : S,
      ‖F (hsParabolicCellApprox S 0 x)
          (hsParabolicCellApprox S 0 y) ω‖ₑ ≤ A)
    (hstep0 : ∀ x y : S, ∀ l : ℕ,
      ‖F (hsParabolicCellApprox S l x)
          (hsParabolicCellApprox S l y) ω -
        F (hsParabolicCellApprox S (l + 1) x)
          (hsParabolicCellApprox S (l + 1) y) ω‖ₑ ≤
        (G + B) * dyadicBase 0 ^ β * dyadicBase l ^ δ)
    (x y : S) (hd0 : 0 < parabolicNorm ((x : ParabolicSpace) - y)) :
    ‖F x y ω‖ₑ ≤
      (A + (G + B) / (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)) *
        (2 : ℝ≥0∞) ^ β * ENNReal.ofReal
          (parabolicNorm ((x : ParabolicSpace) - y)) ^ β := by
  by_cases hd1 : parabolicNorm ((x : ParabolicSpace) - y) ≤ 1
  · exact gammaSplit_pointwise_bound_of_envelopes S hbox F β δ ω A G B
      hGB hβ hδ hcont hvalue hstepN x y hd0 hd1
  have htail := gammaSplitCellApprox_tail_le_of_fixed_coarse_scale
    S hbox F β δ 0 ω hcont x y (G + B) hGB hδ
      (fun l => by simpa only [Nat.zero_add] using hstep0 x y l)
  have hsum : ‖F x y ω‖ₑ ≤
      (A + (G + B) / (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)) := by
    calc
      ‖F x y ω‖ₑ ≤ ‖F x y ω -
          F (hsParabolicCellApprox S 0 x)
            (hsParabolicCellApprox S 0 y) ω‖ₑ +
          ‖F (hsParabolicCellApprox S 0 x)
            (hsParabolicCellApprox S 0 y) ω‖ₑ := by
        calc
          _ = ‖(F x y ω -
              F (hsParabolicCellApprox S 0 x)
                (hsParabolicCellApprox S 0 y) ω) +
              F (hsParabolicCellApprox S 0 x)
                (hsParabolicCellApprox S 0 y) ω‖ₑ := by
            congr 1
            ring
          _ ≤ _ := enorm_add_le _ _
      _ ≤ (G + B) / (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ) + A := by
        have htail' : ‖F x y ω -
              F (hsParabolicCellApprox S 0 x)
                (hsParabolicCellApprox S 0 y) ω‖ₑ ≤
            (G + B) / (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ) := by
          calc
            ‖F x y ω - F (hsParabolicCellApprox S 0 x)
                (hsParabolicCellApprox S 0 y) ω‖ₑ =
                ‖-(F (hsParabolicCellApprox S 0 x)
                  (hsParabolicCellApprox S 0 y) ω - F x y ω)‖ₑ := by
              congr 1
              ring
            _ = ‖F (hsParabolicCellApprox S 0 x)
                  (hsParabolicCellApprox S 0 y) ω - F x y ω‖ₑ :=
              enorm_neg _
            _ ≤ (G + B) / (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ) := by
              simpa [dyadicBase] using htail
        exact add_le_add htail' (hvalue0 x y)
      _ = _ := by rw [add_comm]
  have hscale : (1 : ℝ≥0∞) ≤
      ENNReal.ofReal (2 * parabolicNorm ((x : ParabolicSpace) - y)) ^ β := by
    have hlarge : 1 ≤ 2 * parabolicNorm ((x : ParabolicSpace) - y) := by
      linarith
    have hbase : (ENNReal.ofReal (1 : ℝ)) ^ β ≤
        ENNReal.ofReal (2 * parabolicNorm ((x : ParabolicSpace) - y)) ^ β :=
      ENNReal.rpow_le_rpow
        (ENNReal.ofReal_le_ofReal hlarge) hβ
    simpa only [ENNReal.ofReal_one, ENNReal.one_rpow] using hbase
  calc
    _ ≤ (A + (G + B) / (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)) * 1 := by simpa using hsum
    _ ≤ (A + (G + B) / (1 - ((2 : ℝ≥0∞)⁻¹) ^ δ)) *
        ENNReal.ofReal (2 * parabolicNorm ((x : ParabolicSpace) - y)) ^ β := by
      exact mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by
      rw [gammaSplit_rpow_ofReal_mul _ (le_of_lt hd0) β hβ]
      simp only [mul_assoc]

end RegularityStructures

end
