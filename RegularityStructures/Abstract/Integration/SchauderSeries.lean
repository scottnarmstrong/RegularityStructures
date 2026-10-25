/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.SchauderLarge
public import RegularityStructures.Analysis.Heat.Schauder.DTaylorSeries

/-!
# Multilevel Schauder: bound for the series of the `X^k` component

`exists_abs_tsum_polyU_le`: for `d = ‖y − x‖_𝔰 > 0`, `|∑_n polyU n| ≤ c C_Π C_f max(C_Γ, 1) d^{γ+2−|k|}`.
Large scales `2^{-n} ≥ d` use the Taylor remainder of `D^k K_n` (`polyU_eq_large`,
`exists_abs_pairing_dTaylorKernel_le`) and the partial sums of the pairings of `Π_y e_i`,
`|k| ≥ deg i + 2` with `i` outside the finite set `S` of polynomial components (whose pairings
vanish by hypothesis, see `PolyPairing.Main`); small scales `2^{-n} < d` use the term by term bounds; the sums are done by
`series_core_triple`.  [Hai14, proof of Theorem 5.12].
-/

public section

open Set

namespace RegularityStructures

theorem sum_toList_map {α β : Type*} (s : Finset α) (F : α → β) (G : β → ℝ) :
    ((s.toList.map F).map G).sum = ∑ i ∈ s, G (F i) := by
  rw [List.map_map]
  exact Finset.sum_map_toList s (G ∘ F)

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  {M : Model 𝒯 parabolicSemigroup} {γ CPi CGam Cf : ℝ} {f : ParabolicSpace → ι → ℝ}

open scoped ContDiff

/-- Basic facts on `τ = f(y) − Γ_{yx} f(x)`: it has no component of degree `≥ γ`, and
`|τ_i| ≤ C_f d(y,x)^{γ − deg i}` otherwise. -/
theorem tau_bounds (hf : f ∈ M.modelledDistributions γ) (hfb : M.ModelledBoundOn γ Cf univ f)
    (x y : ParabolicSpace) (i : ι) :
    (𝒯.deg i < γ → |(f y - M.gammaMap y x (f x)) i| ≤
      Cf * parabolicNorm (y - x) ^ (γ - 𝒯.deg i)) ∧
    (¬ 𝒯.deg i < γ → (f y - M.gammaMap y x (f x)) i = 0) := by
  constructor
  · intro hi
    exact hfb.2 x (mem_univ x) y (mem_univ y) i hi
  · intro hi
    have hτl : f y - M.gammaMap y x (f x) ∈ lowerSubspace 𝒯.deg γ :=
      Submodule.sub_mem _ (hf.2.1 y) ((M.isGradedUnipotent_gammaMap y x).map_lowerSubspace
        (hf.2.1 x))
    exact hτl i (not_lt.1 hi)

section Small

variable (hγ : 0 < γ) (hdeg4 : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
  (hPi : M.PiBoundOn γ CPi univ) (hGam : M.GammaBoundOn γ CGam univ) (hCPi : 0 ≤ CPi)
  (hf : f ∈ M.modelledDistributions γ) (hfb : M.ModelledBoundOn γ Cf univ f) (hCf : 0 ≤ Cf)
  (N : ℕ) (x y : ParabolicSpace) (k : Fin 4 →₀ ℕ) (n : ℕ)

include hγ hdeg4 hPi hGam hCPi hf hfb hCf

omit hγ in
theorem abs_polyU_A_le :
    |∑ i ∈ Finset.univ.filter (fun i => (multiDeg k : ℝ) < 𝒯.deg i + 2),
      (f y - M.gammaMap y x (f x)) i *
        derivShellPairing (fun t z => M.regPi y (Pi.single i 1) t z) (annKernel0 N) k y n| ≤
      ∑ i ∈ Finset.univ.filter (fun i => (multiDeg k : ℝ) < 𝒯.deg i + 2 ∧ 𝒯.deg i < γ),
        Cf * parabolicNorm (y - x) ^ (γ - 𝒯.deg i) *
          (derivShellConst (annKernel0 N) k (𝒯.degreesBelowLe γ (𝒯.deg i)) *
            (max CGam 1 * CPi * Fintype.card ι) *
            (2 : ℝ) ^ (((multiDeg k : ℝ) - 𝒯.deg i - 2) * n)) := by
  classical
  have hCw : 0 ≤ max CGam 1 * CPi * Fintype.card ι :=
    mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_right _ _)) hCPi) (Nat.cast_nonneg _)
  have hh0 := contDiff_annKernel0 N
  have hhs : ∀ z, 1 < parabolicNorm z → annKernel0 N z = 0 := fun _ hz => annKernel0_eq_zero N hz
  have hd0 : 0 ≤ parabolicNorm (y - x) := parabolicNorm_nonneg _
  have hsub : Finset.univ.filter (fun i => (multiDeg k : ℝ) < 𝒯.deg i + 2 ∧ 𝒯.deg i < γ) ⊆
      Finset.univ.filter (fun i => (multiDeg k : ℝ) < 𝒯.deg i + 2) := fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi.1
  have hzero : ∀ i ∈ Finset.univ.filter (fun i => (multiDeg k : ℝ) < 𝒯.deg i + 2),
      i ∉ Finset.univ.filter (fun i => (multiDeg k : ℝ) < 𝒯.deg i + 2 ∧ 𝒯.deg i < γ) →
      (f y - M.gammaMap y x (f x)) i *
        derivShellPairing (fun t z => M.regPi y (Pi.single i 1) t z) (annKernel0 N) k y n = 0 := by
    intro i hi hni
    have : ¬ 𝒯.deg i < γ := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hni
      exact fun h => hni ⟨hi, h⟩
    rw [(tau_bounds hf hfb x y i).2 this, zero_mul]
  rw [← Finset.sum_subset hsub hzero]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hlt : 𝒯.deg i < γ := (Finset.mem_filter.1 hi).2.2
  rw [abs_mul]
  have h1 := (tau_bounds hf hfb x y i).1 hlt
  have h2 := abs_pairing_lineIter_scaledShell_le (M.regPi_mem y _)
    (fun _ hu => M.measurable_regPi y _ hu) hh0 hhs k (degreesBelowLe_bounds 𝒯 hdeg4 i) hCw
    (M.isLocalOrder_regPi_single hPi hGam hCPi hlt y) n
  exact mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hCf (Real.rpow_nonneg hd0 _))

omit hGam in
theorem abs_polyU_B_le (z : ParabolicSpace) (k' : Fin 4 →₀ ℕ) :
    |derivShellPairing (M.reconstructSubAt f z) (annKernel0 N) k' z n| ≤
      derivShellConst (annKernel0 N) k' (insert γ (𝒯.degreesBelow γ)) *
        ((modelReconstructionConst 𝒯 parabolicSemigroup γ + Fintype.card ι) * CPi * Cf) *
        (2 : ℝ) ^ (((multiDeg k' : ℝ) - γ - 2) * n) := by
  have hCx : 0 ≤ (modelReconstructionConst 𝒯 parabolicSemigroup γ + Fintype.card ι) * CPi * Cf :=
    mul_nonneg (mul_nonneg (add_nonneg (modelReconstructionConst_nonneg 𝒯 _ hγ.le)
      (Nat.cast_nonneg _)) hCPi) hCf
  exact abs_pairing_lineIter_scaledShell_le (M.reconstructSubAt_mem hγ hPi hCPi hf hfb hCf z)
    (fun (u : ℝ) (hu : 0 < u) => M.measurable_reconstructSubAt hγ hPi hCPi hf hfb hCf z hu)
    (contDiff_annKernel0 N) (fun _ hz => annKernel0_eq_zero N hz) k'
    (exponents_reconstructSubAt hγ hdeg4) hCx
    (M.isLocalOrder_reconstructSubAt hγ hPi hCPi hf hfb hCf z) n

omit hGam in
theorem abs_polyU_E_le :
    |∑ l ∈ taylorIdx (γ + 2 - multiDeg k), coeffT (parabolicCoords (y - x)) l *
      derivShellPairing (M.reconstructSubAt f x) (annKernel0 N) (k + l) x n| ≤
      ∑ l ∈ taylorIdx (γ + 2 - multiDeg k), parabolicNorm (y - x) ^ multiDeg l *
        (derivShellConst (annKernel0 N) (k + l) (insert γ (𝒯.degreesBelow γ)) *
          ((modelReconstructionConst 𝒯 parabolicSemigroup γ + Fintype.card ι) * CPi * Cf) *
          (2 : ℝ) ^ (((multiDeg (k + l) : ℝ) - γ - 2) * n)) := by
  have hd0 : 0 ≤ parabolicNorm (y - x) := parabolicNorm_nonneg _
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [abs_mul]
  have hz : ∀ i, |parabolicCoords (y - x) i| ≤ parabolicNorm (y - x) ^ parabolicWeight i := fun i =>
    abs_parabolicCoords_le i
  exact mul_le_mul (abs_coeffT_le hz l)
    (abs_polyU_B_le hγ hdeg4 hPi hCPi hf hfb hCf N n x (k + l))
    (abs_nonneg _) (pow_nonneg hd0 _)

theorem abs_polyU_le_small :
    |polyU M N γ f x y k n| ≤
      (∑ i ∈ Finset.univ.filter (fun i => (multiDeg k : ℝ) < 𝒯.deg i + 2 ∧ 𝒯.deg i < γ),
        Cf * parabolicNorm (y - x) ^ (γ - 𝒯.deg i) *
          (derivShellConst (annKernel0 N) k (𝒯.degreesBelowLe γ (𝒯.deg i)) *
            (max CGam 1 * CPi * Fintype.card ι) *
            (2 : ℝ) ^ (((multiDeg k : ℝ) - 𝒯.deg i - 2) * n))) +
      derivShellConst (annKernel0 N) k (insert γ (𝒯.degreesBelow γ)) *
        ((modelReconstructionConst 𝒯 parabolicSemigroup γ + Fintype.card ι) * CPi * Cf) *
        (2 : ℝ) ^ (((multiDeg k : ℝ) - γ - 2) * n) +
      ∑ l ∈ taylorIdx (γ + 2 - multiDeg k), parabolicNorm (y - x) ^ multiDeg l *
        (derivShellConst (annKernel0 N) (k + l) (insert γ (𝒯.degreesBelow γ)) *
          ((modelReconstructionConst 𝒯 parabolicSemigroup γ + Fintype.card ι) * CPi * Cf) *
          (2 : ℝ) ^ (((multiDeg (k + l) : ℝ) - γ - 2) * n)) := by
  have hA := abs_polyU_A_le hdeg4 hPi hGam hCPi hf hfb hCf N x y k n
  have hB := abs_polyU_B_le hγ hdeg4 hPi hCPi hf hfb hCf N n y k
  have hE := abs_polyU_E_le hγ hdeg4 hPi hCPi hf hfb hCf N x y k n
  unfold polyU
  exact le_trans (abs_sub _ _) (le_trans (add_le_add_left (abs_add_le _ _) _)
    (add_le_add (add_le_add hA hB) hE))

theorem abs_polyU_le_large (hdeg2 : ∀ j, 𝒯.deg j < γ → -2 < 𝒯.deg j) (S : Finset ι)
    (hS0 : ∀ i ∈ S, derivShellPairing (fun t z => M.regPi y (Pi.single i 1) t z) (annKernel0 N) k y n
      = 0) {Q : ℝ}
    (hP : |parabolicSemigroup.pairing (M.reconstructSubAt f x)
      (dTaylorKernel (annKernel0 N) k n (γ + 2 - multiDeg k) x y)| ≤ Q) :
    |polyU M N γ f x y k n| ≤ Q +
      ∑ i ∈ Finset.univ.filter (fun i => ¬ (multiDeg k : ℝ) < 𝒯.deg i + 2 ∧ 𝒯.deg i < γ ∧ i ∉ S),
        Cf * parabolicNorm (y - x) ^ (γ - 𝒯.deg i) *
          (derivShellConst (annKernel0 N) k (𝒯.degreesBelowLe γ (𝒯.deg i)) *
            (max CGam 1 * CPi * Fintype.card ι) *
            (2 : ℝ) ^ (((multiDeg k : ℝ) - 𝒯.deg i - 2) * n)) := by
  classical
  have hCw : 0 ≤ max CGam 1 * CPi * Fintype.card ι :=
    mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_right _ _)) hCPi) (Nat.cast_nonneg _)
  have hh0 := contDiff_annKernel0 N
  have hhs : ∀ z, 1 < parabolicNorm z → annKernel0 N z = 0 := fun _ hz => annKernel0_eq_zero N hz
  have hd0 : 0 ≤ parabolicNorm (y - x) := parabolicNorm_nonneg _
  rw [polyU_eq_large hγ hdeg2 hPi hGam hCPi hf hfb hCf N x y k n]
  have hsub : Finset.univ.filter (fun i => ¬ (multiDeg k : ℝ) < 𝒯.deg i + 2 ∧ 𝒯.deg i < γ ∧ i ∉ S) ⊆
      Finset.univ.filter (fun i => ¬ (multiDeg k : ℝ) < 𝒯.deg i + 2) := fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi.1
  have hzero : ∀ i ∈ Finset.univ.filter (fun i => ¬ (multiDeg k : ℝ) < 𝒯.deg i + 2),
      i ∉ Finset.univ.filter (fun i => ¬ (multiDeg k : ℝ) < 𝒯.deg i + 2 ∧ 𝒯.deg i < γ ∧ i ∉ S) →
      (f y - M.gammaMap y x (f x)) i *
        derivShellPairing (fun t z => M.regPi y (Pi.single i 1) t z) (annKernel0 N) k y n = 0 := by
    intro i hi hni
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hni
    by_cases hlt : 𝒯.deg i < γ
    · have hiS : i ∈ S := by
        by_contra hS
        exact hni ⟨hi, hlt, hS⟩
      rw [hS0 i hiS, mul_zero]
    · rw [(tau_bounds hf hfb x y i).2 hlt, zero_mul]
  rw [← Finset.sum_subset hsub hzero]
  have hS : |∑ i ∈ Finset.univ.filter (fun i => ¬ (multiDeg k : ℝ) < 𝒯.deg i + 2 ∧ 𝒯.deg i < γ ∧ i ∉ S),
      (f y - M.gammaMap y x (f x)) i *
        derivShellPairing (fun t z => M.regPi y (Pi.single i 1) t z) (annKernel0 N) k y n| ≤
      ∑ i ∈ Finset.univ.filter (fun i => ¬ (multiDeg k : ℝ) < 𝒯.deg i + 2 ∧ 𝒯.deg i < γ ∧ i ∉ S),
        Cf * parabolicNorm (y - x) ^ (γ - 𝒯.deg i) *
          (derivShellConst (annKernel0 N) k (𝒯.degreesBelowLe γ (𝒯.deg i)) *
            (max CGam 1 * CPi * Fintype.card ι) *
            (2 : ℝ) ^ (((multiDeg k : ℝ) - 𝒯.deg i - 2) * n)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hlt : 𝒯.deg i < γ := (Finset.mem_filter.1 hi).2.2.1
    rw [abs_mul]
    have h1 := (tau_bounds hf hfb x y i).1 hlt
    have h2 := abs_pairing_lineIter_scaledShell_le (M.regPi_mem y _)
      (fun _ hu => M.measurable_regPi y _ hu) hh0 hhs k (degreesBelowLe_bounds 𝒯 hdeg4 i) hCw
      (M.isLocalOrder_regPi_single hPi hGam hCPi hlt y) n
    exact mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hCf (Real.rpow_nonneg hd0 _))
  exact le_trans (abs_sub _ _) (add_le_add hP hS)

end Small

/-- The constants of the series bound: all lists below depend only on `𝒯, γ, N, k`. -/
theorem exists_abs_tsum_polyU_le {γ : ℝ} (hγ : 0 < γ) (hdeg2 : ∀ j, 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (N : ℕ) (k : Fin 4 →₀ ℕ) (hk : (multiDeg k : ℝ) < γ + 2) (S : Finset ι)
    (hnat1 : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) ≠ γ + 2 - multiDeg k)
    (hnat2 : ∀ i, i ∉ S → 𝒯.deg i < γ → (multiDeg k : ℝ) ≠ 𝒯.deg i + 2) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (M : Model 𝒯 parabolicSemigroup) {CPi CGam Cf : ℝ}
      {f : ParabolicSpace → ι → ℝ},
      (∀ i ∈ S, ∀ (y : ParabolicSpace) (n : ℕ),
        derivShellPairing (fun t z => M.regPi y (Pi.single i 1) t z) (annKernel0 N) k y n = 0) →
      M.PiBoundOn γ CPi univ → M.GammaBoundOn γ CGam univ → 0 ≤ CPi →
      f ∈ M.modelledDistributions γ → M.ModelledBoundOn γ Cf univ f → 0 ≤ Cf →
      ∀ x y : ParabolicSpace, 0 < parabolicNorm (y - x) → Summable (polyU M N γ f x y k) →
      |∑' n, polyU M N γ f x y k n| ≤
        c * CPi * Cf * max CGam 1 * parabolicNorm (y - x) ^ (γ + 2 - multiDeg k) := by
  classical
  have hdeg4 : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j := fun j hj => by linarith [hdeg2 j hj]
  have hAγ := exponents_reconstructSubAt (𝒯 := 𝒯) hγ hdeg4
  have hσk : 0 < γ + 2 - (multiDeg k : ℝ) := by linarith
  obtain ⟨𝔈, κ, hκ, hdegE, hbE⟩ := exists_abs_pairing_dTaylorKernel_le
    (contDiff_annKernel0 N) (fun z hz => annKernel0_eq_zero N hz) k (γ + 2 - (multiDeg k : ℝ)) hAγ
  set σk : ℝ := γ + 2 - (multiDeg k : ℝ) with hσkdef
  set K₀ : ℝ := modelReconstructionConst 𝒯 parabolicSemigroup γ + Fintype.card ι with hK₀def
  have hK₀ : 0 ≤ K₀ := add_nonneg (modelReconstructionConst_nonneg 𝒯 _ hγ.le) (Nat.cast_nonneg _)
  set D : ι → ℝ := fun i => derivShellConst (annKernel0 N) k (𝒯.degreesBelowLe γ (𝒯.deg i))
    with hDdef
  set Db : ℝ := derivShellConst (annKernel0 N) k (insert γ (𝒯.degreesBelow γ)) with hDbdef
  set D' : (Fin 4 →₀ ℕ) → ℝ := fun l => derivShellConst (annKernel0 N) (k + l)
    (insert γ (𝒯.degreesBelow γ)) with hD'def
  have hD : ∀ i, 0 ≤ D i := fun i => derivShellConst_nonneg _ _ (degreesBelowLe_bounds 𝒯 hdeg4 i)
  have hDb : 0 ≤ Db := derivShellConst_nonneg _ _ hAγ
  have hD' : ∀ l, 0 ≤ D' l := fun l => derivShellConst_nonneg _ _ hAγ
  set F₁c : Finset ι := Finset.univ.filter (fun i => (multiDeg k : ℝ) < 𝒯.deg i + 2 ∧ 𝒯.deg i < γ)
    with hF₁c
  set F₂c : Finset ι := Finset.univ.filter
    (fun i => ¬ (multiDeg k : ℝ) < 𝒯.deg i + 2 ∧ 𝒯.deg i < γ ∧ i ∉ S) with hF₂c
  set L₁c : List (ℝ × ℝ × ℝ) :=
    (𝔈.map fun ℓ => (K₀ * κ ℓ, (indexWeight ℓ : ℝ), (indexWeight ℓ : ℝ) + multiDeg k - γ - 2)) ++
    (F₂c.toList.map fun i => (D i * Fintype.card ι, γ - 𝒯.deg i,
      (multiDeg k : ℝ) - 𝒯.deg i - 2)) with hL₁c
  set L₂c : List (ℝ × ℝ × ℝ) :=
    (Db * K₀, 0, σk) :: ((taylorIdx σk).toList.map fun l =>
      (D' l * K₀, (multiDeg l : ℝ), σk - multiDeg l)) ++
    (F₁c.toList.map fun i => (D i * Fintype.card ι, γ - 𝒯.deg i,
      𝒯.deg i + 2 - (multiDeg k : ℝ))) with hL₂c
  have hL₁ok : ∀ q ∈ L₁c, 0 ≤ q.1 ∧ 0 < q.2.2 ∧ q.2.1 - q.2.2 = σk := by
    intro q hq
    rcases List.mem_append.1 hq with h | h
    · obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.1 h
      refine ⟨mul_nonneg hK₀ (hκ ℓ), ?_, by simp only [hσkdef]; ring⟩
      have := (hdegE ℓ hℓ).2 (fun l => by simpa [hσkdef] using hnat1 l)
      simp only; linarith
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
      have hi' := Finset.mem_toList.1 hi
      simp only [hF₂c, Finset.mem_filter, Finset.mem_univ, true_and] at hi'
      refine ⟨mul_nonneg (hD i) (Nat.cast_nonneg _), ?_, by simp only [hσkdef]; ring⟩
      have h1 := hnat2 i hi'.2.2 hi'.2.1
      have h2 := hi'.1
      simp only
      rcases lt_or_gt_of_ne h1 with h | h
      · exact absurd h h2
      · linarith
  have hL₂ok : ∀ q ∈ L₂c, 0 ≤ q.1 ∧ 0 < q.2.2 ∧ q.2.1 + q.2.2 = σk := by
    intro q hq
    simp only [hL₂c, List.mem_append, List.mem_cons, List.mem_map] at hq
    rcases hq with (rfl | ⟨l, hl, rfl⟩) | ⟨i, hi, rfl⟩
    · exact ⟨mul_nonneg hDb hK₀, hσk, by simp⟩
    · have hl' := (mem_taylorIdx_iff _).1 (Finset.mem_toList.1 hl)
      exact ⟨mul_nonneg (hD' l) hK₀, by simp only; linarith, by simp only; ring⟩
    · have hi' := Finset.mem_toList.1 hi
      simp only [hF₁c, Finset.mem_filter, Finset.mem_univ, true_and] at hi'
      exact ⟨mul_nonneg (hD i) (Nat.cast_nonneg _), by simp only; linarith,
        by simp only [hσkdef]; ring⟩
  set c : ℝ := (L₁c.map fun q => q.1 * ((2 : ℝ) ^ q.2.2 / ((2 : ℝ) ^ q.2.2 - 1))).sum +
    (L₂c.map fun q => q.1 / (1 - (2 : ℝ) ^ (-q.2.2))).sum with hcdef
  have hc0 : 0 ≤ c := by
    refine add_nonneg (List.sum_nonneg fun v hv => ?_) (List.sum_nonneg fun v hv => ?_)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hv
      obtain ⟨h1, h2, -⟩ := hL₁ok q hq
      have : 1 < (2 : ℝ) ^ q.2.2 := Real.one_lt_rpow (by norm_num) h2
      exact mul_nonneg h1 (div_nonneg (by linarith) (by linarith))
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hv
      obtain ⟨h1, h2, -⟩ := hL₂ok q hq
      have : (2 : ℝ) ^ (-q.2.2) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      exact div_nonneg h1 (by linarith)
  refine ⟨c, hc0, ?_⟩
  intro M CPi CGam Cf f hS0 hPi hGam hCPi hf hfb hCf x y hd hU
  set d := parabolicNorm (y - x) with hdd
  have hd0 : 0 ≤ d := hd.le
  obtain ⟨m, hm1, hm2, hm3⟩ := exists_splitIndex' hd
  set Cw : ℝ := max CGam 1 with hCwdef
  have hCw1 : 1 ≤ Cw := le_max_right _ _
  set X : ℝ := CPi * Cf * Cw with hXdef
  have hX : 0 ≤ X := mul_nonneg (mul_nonneg hCPi hCf) (zero_le_one.trans hCw1)
  have hCxX : K₀ * CPi * Cf ≤ K₀ * X := by
    have : CPi * Cf ≤ CPi * Cf * Cw := le_mul_of_one_le_right (mul_nonneg hCPi hCf) hCw1
    calc K₀ * CPi * Cf = K₀ * (CPi * Cf) := by ring
      _ ≤ K₀ * X := mul_le_mul_of_nonneg_left this hK₀
  set L₁ : List (ℝ × ℝ × ℝ) := L₁c.map (fun q => (q.1 * X, q.2)) with hL₁
  set L₂ : List (ℝ × ℝ × ℝ) := L₂c.map (fun q => (q.1 * X, q.2)) with hL₂
  have hu : ∀ p ∈ L₁, 0 ≤ p.1 ∧ 0 < p.2.2 ∧ p.2.1 - p.2.2 = σk := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨h1, h2, h3⟩ := hL₁ok q hq
    exact ⟨mul_nonneg h1 hX, h2, h3⟩
  have hv : ∀ p ∈ L₂, 0 ≤ p.1 ∧ 0 < p.2.2 ∧ p.2.1 + p.2.2 = σk := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨h1, h2, h3⟩ := hL₂ok q hq
    exact ⟨mul_nonneg h1 hX, h2, h3⟩
  have hR1 : ∀ n : ℕ, (L₁.map fun p => p.1 * d ^ p.2.1 * (2 : ℝ) ^ (p.2.2 * (n : ℝ))).sum =
      (𝔈.map fun ℓ => (K₀ * κ ℓ * X) * (d ^ indexWeight ℓ *
        (2 : ℝ) ^ (((indexWeight ℓ : ℝ) + multiDeg k - γ - 2) * n))).sum +
      ∑ i ∈ F₂c, (D i * Fintype.card ι * X) * (d ^ (γ - 𝒯.deg i) *
        (2 : ℝ) ^ (((multiDeg k : ℝ) - 𝒯.deg i - 2) * n)) := by
    intro n
    simp only [hL₁, hL₁c, List.map_append, List.sum_append, List.map_map]
    congr 1
    · congr 1
      refine List.map_congr_left fun ℓ _ => ?_
      simp only [Function.comp, Real.rpow_natCast]
      ring
    · refine (Finset.sum_map_toList F₂c _).trans (Finset.sum_congr rfl fun i _ => ?_)
      simp only [Function.comp]
      ring
  have hR2 : ∀ n : ℕ, (L₂.map fun p => p.1 * d ^ p.2.1 * (2 : ℝ) ^ (-p.2.2 * (n : ℝ))).sum =
      (Db * K₀ * X) * (2 : ℝ) ^ (((multiDeg k : ℝ) - γ - 2) * n) +
      ∑ l ∈ taylorIdx σk, (D' l * K₀ * X) * (d ^ multiDeg l *
        (2 : ℝ) ^ (((multiDeg (k + l) : ℝ) - γ - 2) * n)) +
      ∑ i ∈ F₁c, (D i * Fintype.card ι * X) * (d ^ (γ - 𝒯.deg i) *
        (2 : ℝ) ^ (((multiDeg k : ℝ) - 𝒯.deg i - 2) * n)) := by
    intro n
    simp only [hL₂, hL₂c, List.map_append, List.sum_append, List.map_map, List.map_cons,
      List.sum_cons]
    congr 1
    congr 1
    · rw [Real.rpow_zero, mul_one]
      congr 2
      rw [hσkdef]; ring
    · refine (Finset.sum_map_toList (taylorIdx σk) _).trans (Finset.sum_congr rfl fun l _ => ?_)
      simp only [Function.comp, Real.rpow_natCast]
      have : -(σk - (multiDeg l : ℝ)) * n = (((multiDeg (k + l) : ℕ) : ℝ) - γ - 2) * n := by
        have hadd : multiDeg (k + l) = multiDeg k + multiDeg l := map_add _ _ _
        rw [hadd, hσkdef]; push_cast; ring
      rw [this]
      ring
    · refine (Finset.sum_map_toList F₁c _).trans (Finset.sum_congr rfl fun i _ => ?_)
      simp only [Function.comp]
      have : -((𝒯.deg i + 2 - (multiDeg k : ℝ))) * n = ((multiDeg k : ℝ) - 𝒯.deg i - 2) * n := by
        ring
      rw [this]
      ring
  have hdeg4' := hdeg4
  have hL : ∀ n < m, |polyU M N γ f x y k n| ≤
      (L₁.map fun p => p.1 * d ^ p.2.1 * (2 : ℝ) ^ (p.2.2 * (n : ℝ))).sum := by
    intro n hn
    rw [hR1 n]
    have hdn : d ≤ (2 : ℝ)⁻¹ ^ n := by
      have h2 : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
      have h3 := hm1 n hn
      rw [inv_pow]
      calc d = (d * 2 ^ n) * ((2 : ℝ) ^ n)⁻¹ := by field_simp
        _ ≤ 1 * ((2 : ℝ) ^ n)⁻¹ := mul_le_mul_of_nonneg_right h3 (inv_nonneg.2 h2.le)
        _ = _ := one_mul _
    have hCx0 : 0 ≤ K₀ * CPi * Cf := mul_nonneg (mul_nonneg hK₀ hCPi) hCf
    have hP := hbE (M.reconstructSubAt_mem hγ hPi hCPi hf hfb hCf x)
      (fun (u : ℝ) (hu : 0 < u) => M.measurable_reconstructSubAt hγ hPi hCPi hf hfb hCf x hu)
      hCx0 (M.isLocalOrder_reconstructSubAt hγ hPi hCPi hf hfb hCf x) n hdn
    have hbound := abs_polyU_le_large hγ hdeg4 hPi hGam hCPi hf hfb hCf N x y k n hdeg2 S (fun i hi => hS0 i hi y n) hP
    refine hbound.trans (add_le_add ?_ (le_of_eq ?_))
    · have hg0 : 0 ≤ (𝔈.map fun ℓ => κ ℓ * (d ^ indexWeight ℓ *
          (2 : ℝ) ^ (((indexWeight ℓ : ℝ) + multiDeg k - γ - 2) * n))).sum :=
        List.sum_nonneg fun v hv => by
          obtain ⟨ℓ, -, rfl⟩ := List.mem_map.1 hv
          exact mul_nonneg (hκ ℓ) (mul_nonneg (pow_nonneg hd0 _) (Real.rpow_nonneg (by norm_num) _))
      calc (K₀ * CPi * Cf) * (𝔈.map fun ℓ => κ ℓ * (d ^ indexWeight ℓ *
          (2 : ℝ) ^ (((indexWeight ℓ : ℝ) + multiDeg k - γ - 2) * n))).sum
          ≤ (K₀ * X) * (𝔈.map fun ℓ => κ ℓ * (d ^ indexWeight ℓ *
          (2 : ℝ) ^ (((indexWeight ℓ : ℝ) + multiDeg k - γ - 2) * n))).sum :=
            mul_le_mul_of_nonneg_right hCxX hg0
        _ = _ := by
            rw [← List.sum_map_mul_left]
            congr 1
            refine List.map_congr_left fun ℓ _ => ?_
            ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hXdef, hCwdef]
      ring
  have hS : ∀ n, m ≤ n → |polyU M N γ f x y k n| ≤
      (L₂.map fun p => p.1 * d ^ p.2.1 * (2 : ℝ) ^ (-p.2.2 * (n : ℝ))).sum := by
    intro n _
    rw [hR2 n]
    have h := abs_polyU_le_small hγ hdeg4 hPi hGam hCPi hf hfb hCf N x y k n
    have hA'' : (∑ i ∈ F₁c, Cf * d ^ (γ - 𝒯.deg i) *
        (derivShellConst (annKernel0 N) k (𝒯.degreesBelowLe γ (𝒯.deg i)) *
          (max CGam 1 * CPi * Fintype.card ι) *
          (2 : ℝ) ^ (((multiDeg k : ℝ) - 𝒯.deg i - 2) * n))) =
        ∑ i ∈ F₁c, (D i * Fintype.card ι * X) * (d ^ (γ - 𝒯.deg i) *
          (2 : ℝ) ^ (((multiDeg k : ℝ) - 𝒯.deg i - 2) * n)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hXdef, hCwdef]
      ring
    have hB'' : Db * (K₀ * CPi * Cf) * (2 : ℝ) ^ (((multiDeg k : ℝ) - γ - 2) * n) ≤
        (Db * K₀ * X) * (2 : ℝ) ^ (((multiDeg k : ℝ) - γ - 2) * n) := by
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by norm_num) _)
      calc Db * (K₀ * CPi * Cf) ≤ Db * (K₀ * X) := mul_le_mul_of_nonneg_left hCxX hDb
        _ = _ := by ring
    have hE'' : (∑ l ∈ taylorIdx σk, d ^ multiDeg l * (D' l * (K₀ * CPi * Cf) *
        (2 : ℝ) ^ (((multiDeg (k + l) : ℝ) - γ - 2) * n))) ≤
        ∑ l ∈ taylorIdx σk, (D' l * K₀ * X) * (d ^ multiDeg l *
          (2 : ℝ) ^ (((multiDeg (k + l) : ℝ) - γ - 2) * n)) := by
      refine Finset.sum_le_sum fun l _ => ?_
      have h2 : 0 ≤ (2 : ℝ) ^ (((multiDeg (k + l) : ℝ) - γ - 2) * n) :=
        Real.rpow_nonneg (by norm_num) _
      have h3 : D' l * (K₀ * CPi * Cf) ≤ D' l * K₀ * X := by
        calc D' l * (K₀ * CPi * Cf) ≤ D' l * (K₀ * X) := mul_le_mul_of_nonneg_left hCxX (hD' l)
          _ = _ := by ring
      calc d ^ multiDeg l * (D' l * (K₀ * CPi * Cf) *
            (2 : ℝ) ^ (((multiDeg (k + l) : ℝ) - γ - 2) * n))
          ≤ d ^ multiDeg l * ((D' l * K₀ * X) *
            (2 : ℝ) ^ (((multiDeg (k + l) : ℝ) - γ - 2) * n)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 h2) (pow_nonneg hd0 _)
        _ = _ := by ring
    have hh := h
    linarith [hh, hA'', hB'', hE'']
  have hser := series_core_triple L₁ L₂ σk hu hv hd hm2 hm3 hU hL hS
  have hS1 : (L₁.map fun p => p.1 * ((2 : ℝ) ^ p.2.2 / ((2 : ℝ) ^ p.2.2 - 1))).sum =
      X * (L₁c.map fun q => q.1 * ((2 : ℝ) ^ q.2.2 / ((2 : ℝ) ^ q.2.2 - 1))).sum := by
    rw [hL₁, List.map_map, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    simp only [Function.comp]; ring
  have hS2 : (L₂.map fun p => p.1 / (1 - (2 : ℝ) ^ (-p.2.2))).sum =
      X * (L₂c.map fun q => q.1 / (1 - (2 : ℝ) ^ (-q.2.2))).sum := by
    rw [hL₂, List.map_map, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    simp only [Function.comp]; ring
  rw [hS1, hS2] at hser
  refine hser.trans (le_of_eq ?_)
  rw [hcdef, hXdef, hCwdef]
  ring

end Model

end RegularityStructures

end
