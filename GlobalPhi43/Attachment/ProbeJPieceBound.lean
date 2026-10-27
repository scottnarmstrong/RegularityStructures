module

public import GlobalPhi43.Attachment.ProbeJWindow
public import GlobalPhi43.Attachment.ProbePieceLarge
public import GlobalPhi43.Attachment.ProbeFiniteFolding
public import GlobalPhi43.Attachment.ProbeDyadicCosts

/-! The summable Gaussian-piece estimate for the actual J. Constants
precede all realisation data. No annular or Gaussian-test estimate is supplied. -/

@[expose] public noncomputable section

open RegularityStructures RegularityStructures.Phi43 MeasureTheory Set

namespace GlobalPhi43.Attachment

theorem probeJ_piece_bound (N : ℕ) (κ : Kappa) : ∃ D : ℝ, 0 < D ∧
    ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsSmoothOnSpaceTime f → Statements.HasPhi43NoiseGrowth f →
      Statements.IsModeratePhi43ModelOf N κ f C Z →
    ∀ S : Set ParabolicSpace, IsCompact S → ∀ z ∈ S,
    ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ n : ℕ,
    |∫ w, treeJ N f (spaceTimeProj w)*probeGaussianPiece r n (z-w)| ≤
      D*(1/4 : ℝ)^n*(1+(Z.normOn (gamma κ) {y | ∃ z ∈ S, Local.pdist z y ≤ 3}).toReal)^3 *
        r^homogeneity κ .psi := by
  classical
  obtain ⟨A, hA, ha⟩ := probeJ_compact_test N κ
  obtain ⟨B, hB, hb⟩ := probePieceTest_C4
  obtain ⟨E, hE, he⟩ := probeGaussianPiece_folded_C4
  let H := 1+B+E
  have hH : 0 < H := by dsimp [H]; linarith
  refine ⟨343*(A*H), by positivity, ?_⟩
  intro f C Z hf hg hZ S hS z hz r hr hr1 n
  let M := (1+(Z.normOn (gamma κ) {y | ∃ z ∈ S, Local.pdist z y ≤ 3}).toReal)^3
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hc : 0 < probePieceFactor n := lt_of_lt_of_le (by norm_num) (probePieceFactor_ge_two _)
  have hw : 0 ≤ ((probePieceFactor n)⁻¹)^5 := by positivity
  have hη : homogeneity κ .psi ≤ 0 := by simp only [homogeneity]; linarith [kappa_pos κ]
  have hpow : 0 ≤ r^homogeneity κ .psi := Real.rpow_nonneg hr.le _
  have hnormsmall : ∀ k ≤ 4, ∀ v,
      ‖iteratedFDeriv ℝ k (probePieceTest n) v‖ ≤ H*((probePieceFactor n)⁻¹)^5 := by
    intro k hk v
    exact (hb n k hk v).trans (mul_le_mul_of_nonneg_right (by dsimp [H]; linarith) hw)
  by_cases hT : probePieceFactor n*r ≤ 1
  · have hi : (∫ w, treeJ N f (spaceTimeProj w)*probeGaussianPiece r n (z-w)) =
        ∫ w, treeJ N f (spaceTimeProj w)*
          rescaledTestFunction (probePieceTest n) (probePieceFactor n*r) z w := by
      simp_rw [probeGaussianPiece_rescaled hr]
    rw [hi]
    have hh := ha f C Z hf hg hZ S hS z hz _ ⟨mul_pos hc hr, hT⟩ _
      (probePieceTest_smooth n) (probePieceTest_compact n) (probePieceTest_support n)
      (H*((probePieceFactor n)⁻¹)^5) (mul_nonneg hH.le hw) hnormsmall
    have hscale : (probePieceFactor n*r)^homogeneity κ .psi ≤ r^homogeneity κ .psi :=
      Real.rpow_le_rpow_of_nonpos hr
        (by nlinarith [probePieceFactor_ge_two n]) hη
    calc _ ≤ A*(H*((probePieceFactor n)⁻¹)^5)*M*(probePieceFactor n*r)^homogeneity κ .psi := hh
      _ ≤ A*(H*((probePieceFactor n)⁻¹)^5)*M*r^homogeneity κ .psi :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ ≤ A*(H*(1/4 : ℝ)^n)*M*r^homogeneity κ .psi := by
        gcongr
        exact probe_small_geometric_cost n
      _ ≤ (343*(A*H))*(1/4 : ℝ)^n*M*r^homogeneity κ .psi := by
        have hp : 0 ≤ A*H*(1/4 : ℝ)^n*M*r^homogeneity κ .psi := by positivity
        calc
          _ = A*H*(1/4 : ℝ)^n*M*r^homogeneity κ .psi := by ring
          _ ≤ 343*(A*H*(1/4 : ℝ)^n*M*r^homogeneity κ .psi) :=
            le_mul_of_one_le_left hp (by norm_num)
          _ = _ := by ring
  · have hT' : 1 ≤ probePieceFactor n*r := (lt_of_not_ge hT).le
    have ht := probeGaussianPiece_time_support hr hr1 n
    have hi := probe_fold_pairing_sum ((continuous_treeJ hf).comp continuous_spaceTimeProj)
      (probeGaussianPiece_smooth hr n) ht (probe_lift_integer_periodic (treeJ N f)) hr1
      (probeGaussianPiece_space_support hr n) z
    dsimp only [Function.comp_def] at hi
    rw [hi]
    have hterm (m : Fin 3 → ℤ) :
        |∫ w, treeJ N f (spaceTimeProj w)*
          rescaledTestFunction (probeFoldedProfile (probeGaussianPiece r n) m) 1 z w| ≤
          A*(H*((probePieceFactor n)⁻¹)^5)*M := by
      have hh := ha f C Z hf hg hZ S hS z hz 1 ⟨zero_lt_one, le_refl _⟩ _
        (probeFoldedProfile_smooth (probeGaussianPiece_smooth hr n) m)
        (probeFoldedProfile_compact ht m) (probeFoldedProfile_support ht m)
        (H*((probePieceFactor n)⁻¹)^5) (mul_nonneg hH.le hw)
        (fun k hk v => (he r hr n hT' m k hk v).trans
          (mul_le_mul_of_nonneg_right (by dsimp [H]; linarith) hw))
      simpa only [Real.one_rpow, mul_one] using hh
    have hcard : ((probeFoldCells n).card : ℝ) ≤ 343*(2 : ℝ)^(3*n) := by
      exact_mod_cast probeFoldCells_card_bound n
    have hrpow : 1 ≤ r^homogeneity κ .psi := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 hη
    calc _ ≤ ∑ m ∈ probeFoldCells n, |∫ w, treeJ N f (spaceTimeProj w)*
          rescaledTestFunction (probeFoldedProfile (probeGaussianPiece r n) m) 1 z w| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m ∈ probeFoldCells n, A*(H*((probePieceFactor n)⁻¹)^5)*M :=
        Finset.sum_le_sum (fun m _ => hterm m)
      _ = ((probeFoldCells n).card : ℝ)*(A*(H*((probePieceFactor n)⁻¹)^5)*M) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (343*(2 : ℝ)^(3*n))*(A*(H*((probePieceFactor n)⁻¹)^5)*M) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (343*(A*H))*((2 : ℝ)^(3*n)*((probePieceFactor n)⁻¹)^5)*M := by ring
      _ = (343*(A*H))*(1/32 : ℝ)*(1/4 : ℝ)^n*M := by
        rw [probe_folded_geometric_cost]
        ring
      _ ≤ (343*(A*H))*(1/4 : ℝ)^n*M*r^homogeneity κ .psi := by
        have hp : 0 ≤ (343*(A*H))*(1/4 : ℝ)^n*M := by positivity
        calc
          _ = ((343*(A*H))*(1/4 : ℝ)^n*M)*(1/32 : ℝ) := by ring
          _ ≤ ((343*(A*H))*(1/4 : ℝ)^n*M)*1 :=
            mul_le_mul_of_nonneg_left (by norm_num) hp
          _ ≤ _ := (mul_one _).le.trans (le_mul_of_one_le_right hp hrpow)

end GlobalPhi43.Attachment
