module

public import GlobalPhi43.Attachment.ProbeJPieceBound
public import GlobalPhi43.Attachment.ProbeJPairingLimit

/-! Bound for the actual full Gaussian pairing, with the exact source
radius-three model window and constants chosen before all realization data. -/

@[expose] public noncomputable section

open RegularityStructures RegularityStructures.Phi43 MeasureTheory Set Filter Topology

namespace GlobalPhi43.Attachment

theorem probe_geometric_partial_le_two (n : ℕ) :
    ∑ j ∈ Finset.range (n+1), (1/4 : ℝ)^j ≤ 2 := by
  have hs : ∀ m : ℕ, ∑ j ∈ Finset.range m, (1/4 : ℝ)^j ≤ 4/3 := by
    intro m
    rw [geom_sum_eq (by norm_num : (1/4 : ℝ) ≠ 1)]
    have hp : 0 ≤ (1/4 : ℝ)^m := by positivity
    apply (div_le_iff_of_neg (by norm_num : (1/4 : ℝ)-1 < 0)).mpr
    linarith
  exact (hs (n+1)).trans (by norm_num)

theorem probeJ_gaussian_pairing_bound (N : ℕ) (κ : Kappa) : ∃ D : ℝ, 0 < D ∧
    ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsSmoothOnSpaceTime f → Statements.HasPhi43NoiseGrowth f →
      Statements.IsModeratePhi43ModelOf N κ f C Z →
    ∀ s r : ℝ, 0 < r → r ≤ 1 → ∀ z ∈ probeModelWindow s, z.1 = s+r^2 →
    |∫ w, treeJ N f (spaceTimeProj w)*probeGaussianKernel (r^2) (z-w)| ≤
      D*(1+(Z.normOn (gamma κ)
        {y | ∃ z ∈ probeModelWindow s, Local.pdist z y ≤ 3}).toReal)^3 *
        r^homogeneity κ .psi := by
  classical
  obtain ⟨D, hD, hb⟩ := probeJ_piece_bound N κ
  refine ⟨2*D, mul_pos (by norm_num) hD, ?_⟩
  intro f C Z hf hg hZ s r hr hr1 z hz hzt
  let M := (1+(Z.normOn (gamma κ)
    {y | ∃ z ∈ probeModelWindow s, Local.pdist z y ≤ 3}).toReal)^3
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hp : 0 ≤ r^homogeneity κ .psi := Real.rpow_nonneg hr.le _
  have ht := (probeJ_pairing_tendsto (N := N) hf s hr hr1 z hzt).abs
  apply le_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro n
  calc _ ≤ ∑ j ∈ Finset.range (n+1),
        |∫ w, treeJ N f (spaceTimeProj w)*probeGaussianPiece r j (z-w)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (n+1), D*(1/4 : ℝ)^j*M*r^homogeneity κ .psi :=
      Finset.sum_le_sum (fun j _ => hb f C Z hf hg hZ _ (probeModelWindow_compact s) z hz r hr hr1 j)
    _ = D*(∑ j ∈ Finset.range (n+1), (1/4 : ℝ)^j)*M*r^homogeneity κ .psi := by
      simp only [Finset.sum_mul, Finset.mul_sum]
    _ ≤ D*2*M*r^homogeneity κ .psi := by
      gcongr
      exact probe_geometric_partial_le_two n
    _ = _ := by ring

end GlobalPhi43.Attachment
