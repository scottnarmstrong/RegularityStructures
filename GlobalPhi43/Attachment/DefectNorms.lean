module

public import GlobalPhi43.Attachment.DefectDerivativeBound

/-! The literal C1 seminorm estimate for all three source defects. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43
open RegularityStructures.Potential RegularityStructures.Inhomogeneity GlobalPhi43.Local

/-- Source C1 norm: supremum of value, time derivative and spatial gradient together.
An empty-domain supremum is zero. -/
def defectC1ENorm (e : ParabolicSpace → ℝ) (S : Set ParabolicSpace) : ENNReal :=
  ⨆ x ∈ S, ENNReal.ofReal (|e x| + |ddv 0 e x| + ‖fun j : Fin 3 => ddv j.succ e x‖)

/-- A radius-three defect norm bound, before enlarging the norm to radius four.
The actual renormalised V and W stay inside the remainder convolution. -/
theorem defect_C1_bound (N : ℕ) (κ : Kappa) :
    ∃ c : ℝ, 0 < c ∧
    ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsSmoothOnSpaceTime f → Statements.HasPhi43NoiseGrowth f →
      Statements.IsModeratePhi43ModelOf N κ f C Z →
    ∀ S : Set ParabolicSpace, IsCompact S →
      (∑ i : Fin 3, defectC1ENorm (defectField N f C i) S) ≤
        ENNReal.ofReal (c * (1 +
          (Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3}).toReal) ^ 3) := by
  let word : Option (Fin 4) → List (Fin 4) := fun j => j.elim [] (fun k => [k])
  choose d hd h using fun j : Option (Fin 4) => defect_derivative_bound N κ (word j)
  let K := d none + d (some 0) + ∑ j : Fin 3, d (some j.succ)
  have hd0 (j) : 0 ≤ d j := (hd j).le
  have hsum : 0 ≤ ∑ j : Fin 3, d (some j.succ) := Finset.sum_nonneg fun j _ => hd0 _
  have hK : 0 < K := by dsimp [K]; linarith [hd none, hd (some 0)]
  refine ⟨3 * K, by positivity, ?_⟩
  intro f C Z hf hg hZ S hS
  let M := (1 + (Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3}).toReal) ^ 3
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hb (i : Fin 3) : defectC1ENorm (defectField N f C i) S ≤ ENNReal.ofReal (K * M) := by
    apply iSup₂_le
    intro x hx
    apply ENNReal.ofReal_le_ofReal
    have hv : |defectField N f C i x| ≤ d none * M := by
      simpa only [word, Option.elim_none, ddA] using h none f C Z hf hg hZ S hS x hx i
    have ht : |ddv 0 (defectField N f C i) x| ≤ d (some 0) * M := by
      simpa only [word, Option.elim_some, ddA] using h (some 0) f C Z hf hg hZ S hS x hx i
    have hxj (j : Fin 3) : |ddv j.succ (defectField N f C i) x| ≤ d (some j.succ) * M := by
      simpa only [word, Option.elim_some, ddA] using
        h (some j.succ) f C Z hf hg hZ S hS x hx i
    have hgrad : ‖fun j : Fin 3 => ddv j.succ (defectField N f C i) x‖ ≤
        (∑ j : Fin 3, d (some j.succ)) * M := by
      apply (pi_norm_le_iff_of_nonneg (mul_nonneg hsum hM)).mpr
      intro j
      rw [Real.norm_eq_abs]
      exact (hxj j).trans (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun k : Fin 3 => d (some k.succ))
          (fun k _ => hd0 _) (Finset.mem_univ j)) hM)
    change |defectField N f C i x| + |ddv 0 (defectField N f C i) x| +
      ‖fun j : Fin 3 => ddv j.succ (defectField N f C i) x‖ ≤ K * M
    dsimp [K]
    nlinarith
  calc (∑ i : Fin 3, defectC1ENorm (defectField N f C i) S)
      ≤ ∑ _i : Fin 3, ENNReal.ofReal (K * M) := Finset.sum_le_sum fun i _ => hb i
    _ = ENNReal.ofReal ((3 * K) * M) := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      convert (ENNReal.ofReal_mul (q := K * M) (show (0 : ℝ) ≤ 3 by norm_num)).symm using 1 <;>
        norm_num [mul_assoc]

/-- Defect norm bounds on the exact radius-four enlargement.
The model norm is finite by the moderate predicate and compactness, so its real value is genuine. -/
theorem defect_norms (N : ℕ) (κ : Kappa) :
    ∃ c : ℝ, 0 < c ∧
    ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsSmoothOnSpaceTime f → Statements.HasPhi43NoiseGrowth f →
      Statements.IsModeratePhi43ModelOf N κ f C Z →
    ∀ S : Set ParabolicSpace, IsCompact S →
      (∑ i : Fin 3, defectC1ENorm (defectField N f C i) S) ≤
        ENNReal.ofReal (c * (1 +
          (Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 4}).toReal) ^ 3) := by
  obtain ⟨c, hc, h⟩ := defect_C1_bound N κ
  refine ⟨c, hc, ?_⟩
  intro f C Z hf hg hZ S hS
  refine (h f C Z hf hg hZ S hS).trans (ENNReal.ofReal_le_ofReal ?_)
  have hfin : Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 4} ≠ ⊤ := by
    obtain ⟨noise, hn, hm⟩ := hZ
    exact hm.2.2.1 _ (isCompact_parabolic_enlargement hS (by norm_num))
  have hm : Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3} ≤
      Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 4} := by
    have hs : {y | ∃ z ∈ S, pdist z y ≤ 3} ⊆ {y | ∃ z ∈ S, pdist z y ≤ 4} := by
      rintro y ⟨z, hz, hd⟩
      exact ⟨z, hz, by linarith⟩
    unfold Model.normOn Model.piNormOn Model.gammaNormOn
    apply add_le_add
    · exact le_iInf₂ fun B hB => iInf₂_le B fun i hi t ht x hx => hB i hi t ht x (hs hx)
    · exact le_iInf₂ fun B hB => iInf₂_le B fun i j hi hj x hx y hy =>
        hB i j hi hj x (hs hx) y (hs hy)
  have hr := ENNReal.toReal_mono hfin hm
  gcongr

end GlobalPhi43.Attachment
