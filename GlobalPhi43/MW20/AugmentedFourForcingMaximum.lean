module

public import GlobalPhi43.MW20.FourForcingMaximum

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

/-- The actual four signed forcing terms and the additional negative defect.
The source equation, not the desired maximum bound, is the analytic input. -/
theorem source_augmented_four_forcing_maximum (w A B C D E : ParabolicSpace → ℝ)
    {S R : ℝ} (hS : 0 ≤ S) (hSR : S < R) (hR : R ≤ 1 / 2)
    (hw : ∀ z ∈ sourceCylinder S, ContDiffAt ℝ 2 w z)
    (hA : BddAbove ((fun z => |A z|) '' sourceCylinder S))
    (hB : BddAbove ((fun z => |B z|) '' sourceCylinder S))
    (hC : BddAbove ((fun z => |C z|) '' sourceCylinder S))
    (hD : BddAbove ((fun z => |D z|) '' sourceCylinder S))
    (hE : BddAbove ((fun z => |E z|) '' sourceCylinder S))
    (hpde : ∀ z ∈ sourceCylinder S,
      sourceHeat w z = -w z ^ 3 - 3 * A z - 3 * B z - C z + D z - E z) :
    sourceSup w R ≤ 45 * max (1 / (R - S))
      (max (fourForcingRoot A B C D S) (sourceSup E S ^ (1 / 3 : ℝ))) := by
  let N := max (fourForcingRoot A B C D S) (sourceSup E S ^ (1 / 3 : ℝ))
  have hS1 : S ∈ Icc (0 : ℝ) (1 / 2) := ⟨hS, hSR.le.trans hR⟩
  have hAr : sourceSup A S ^ (1 / 3 : ℝ) ≤ N := by
    dsimp [N, fourForcingRoot]
    exact ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)
  have hBr : sourceSup B S ^ (1 / 3 : ℝ) ≤ N := by
    dsimp [N, fourForcingRoot]
    exact ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)
  have hCr : sourceSup C S ^ (1 / 3 : ℝ) ≤ N := by
    dsimp [N, fourForcingRoot]
    exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
  have hDr : sourceSup D S ^ (1 / 3 : ℝ) ≤ N := by
    dsimp [N, fourForcingRoot]
    exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
  have hN : 0 ≤ N := (Real.rpow_nonneg (sourceSup_nonneg_of_bddAbove A hS1 hA) _).trans hAr
  have hcube (f : ParabolicSpace → ℝ)
      (hf : BddAbove ((fun z => |f z|) '' sourceCylinder S))
      (hroot : sourceSup f S ^ (1 / 3 : ℝ) ≤ N) : sourceSup f S ≤ N ^ 3 := by
    have hn := sourceSup_nonneg_of_bddAbove f hS1 hf
    have he : (sourceSup f S ^ (1 / 3 : ℝ)) ^ 3 = sourceSup f S := by
      simpa using Real.rpow_inv_natCast_pow (n := 3) hn (by norm_num)
    simpa only [he] using pow_le_pow_left₀ (Real.rpow_nonneg hn _) hroot 3
  have ha := hcube A hA hAr
  have hb := hcube B hB hBr
  have hc := hcube C hC hCr
  have hd := hcube D hD hDr
  have he := hcube E hE (le_max_right _ _)
  let g := fun z => -3 * A z - 3 * B z - C z + D z - E z
  have hg : ∀ z ∈ sourceCylinder S, |g z| ≤ (3 * N) ^ 3 := by
    intro z hz
    have haz := (le_csSup hA ⟨z, hz, rfl⟩).trans ha
    have hbz := (le_csSup hB ⟨z, hz, rfl⟩).trans hb
    have hcz := (le_csSup hC ⟨z, hz, rfl⟩).trans hc
    have hdz := (le_csSup hD ⟨z, hz, rfl⟩).trans hd
    have hez := (le_csSup hE ⟨z, hz, rfl⟩).trans he
    have hab := abs_sub (-3 * A z) (3 * B z)
    have habc := abs_sub (-3 * A z - 3 * B z) (C z)
    have habcd := abs_add_le (-3 * A z - 3 * B z - C z) (D z)
    simp only [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at hab
    have habcde := abs_sub (-3 * A z - 3 * B z - C z + D z) (E z)
    dsimp [g]
    nlinarith [pow_nonneg hN 3]
  apply csSup_le ((sourceCylinder_nonempty ⟨hS.trans hSR.le, hR⟩).image _)
  rintro b ⟨x, hx, rfl⟩
  have hp : ∀ z ∈ sourceCylinder S, sourceHeat w z = -w z ^ 3 + g z := by
    intro z hz; rw [hpde z hz]; dsimp [g]; ring
  have h := source_interior_cubic_maximum w g hS hSR (by positivity : 0 ≤ 3 * N) hw hp hg hx
  have hmax : max (1 / (R - S)) (3 * N) ≤ 3 * max (1 / (R - S)) N := by
    have hpos : 0 ≤ max (1 / (R - S)) N := hN.trans (le_max_right _ _)
    exact max_le (by nlinarith [le_max_left (1 / (R - S)) N])
      (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))
  exact h.trans (by nlinarith)

end GlobalPhi43.MW20
