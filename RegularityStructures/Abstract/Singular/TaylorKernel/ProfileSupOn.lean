/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.TaylorKernel.ProfileSup
public import RegularityStructures.Analysis.Heat.Schauder.TaylorRegime

/-!
# Pointwise bound for the parabolic Taylor remainder from derivative bounds on a region

Localised version of `exists_abs_taylorProfile_le_sup`: the derivative bounds
`|D^ℓ φ| ≤ B ℓ` are only needed on a set `R`, namely at the points of the coordinate box
`{u + ∑ⱼ τⱼ zⱼ eⱼ : τ ∈ [0,1]⁴}` between `u` and `u + z`; then
`|taylorProfile φ σ z u| ≤ ∑_{ℓ ∈ E} d^{|ℓ|_𝔰} B ℓ` (`exists_abs_taylorProfile_le_sup_on`).

Source: [Hai14] = arXiv:1303.5113v4, proof of Lemma 5.18.
-/

public section

open scoped ContDiff

namespace RegularityStructures

/-- The point `∑ⱼ (τⱼ sⱼ) eⱼ` of the coordinate box. -/
@[expose] def boxPt (s τ : Fin 4 → ℝ) : ParabolicSpace := ∑ j, (τ j * s j) • coordDir j

theorem boxPt_add_single (s τ : Fin 4 → ℝ) (j : Fin 4) :
    boxPt s (τ + (Pi.single j (1 : ℝ) : Fin 4 → ℝ)) = boxPt s τ + s j • coordDir j := by
  unfold boxPt
  have h : ∀ i, ((τ + (Pi.single j (1 : ℝ) : Fin 4 → ℝ)) i * s i) • coordDir i =
      (τ i * s i) • coordDir i + ((Pi.single j (1 : ℝ) : Fin 4 → ℝ) i * s i) • coordDir i := by
    intro i; simp [add_mul, add_smul]
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [hij]
  · simp

theorem boxPt_single (s : Fin 4 → ℝ) (j : Fin 4) (t : ℝ) :
    boxPt s (Pi.single j t : Fin 4 → ℝ) = (t * s j) • coordDir j := by
  unfold boxPt
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [hij]
  · simp

theorem abs_remOp_le_of_sup_on {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : ParabolicSpace) (s : ℝ) (m : ℕ) (B : ℝ) (w : ParabolicSpace)
    (hB : ∀ t : ℝ, 0 < t → t ≤ 1 → |(dirDeriv e)^[m + 1] φ (w + (t * s) • e)| ≤ B) :
    |remOp e s m φ w| ≤ |s| ^ (m + 1) * B := by
  refine (abs_remOp_le hφ e s m w).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ => |(dirDeriv e)^[m + 1] φ (w + (t * s) • e)|) (C := B)
    (fun t ht => by
      rw [Real.norm_eq_abs, abs_abs]
      have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by simpa using ht
      exact hB t ht'.1 ht'.2)
  simp only [sub_zero, abs_one, mul_one] at h
  exact (le_abs_self _).trans (by simpa using h)

/-- Localised pointwise bound for the box Taylor remainder. -/
theorem exists_abs_remJ_le_sup_on (m : Fin 4 → ℕ) : ∀ (J : List (Fin 4)),
    ∃ E : List (List (Fin 4)), (∀ ℓ ∈ E, ∃ j ∈ J, m j + 1 ≤ ℓ.count j) ∧
      ∀ (s : Fin 4 → ℝ) (d : ℝ), 0 ≤ d → (∀ j, |s j| ≤ d ^ parabolicWeight j) →
        ∀ {φ : ParabolicSpace → ℝ}, ContDiff ℝ ∞ φ → ∀ B : List (Fin 4) → ℝ,
          ∀ {R : Set ParabolicSpace}, (∀ ℓ u, u ∈ R →
            |lineIter (ℓ.map coordDir) φ u| ≤ B ℓ) → ∀ w : ParabolicSpace,
          (∀ τ : Fin 4 → ℝ, (∀ j, 0 ≤ τ j ∧ τ j ≤ (J.count j : ℝ)) → w + boxPt s τ ∈ R) →
          |remJ s m J φ w| ≤ (E.map fun ℓ => d ^ indexWeight ℓ * B ℓ).sum
  | [] => ⟨[], by simp, by
      intro s d _ _ φ _ B R _ w _
      simp [remJ, tyOp, disp]⟩
  | j :: J => by
    obtain ⟨E', hE'p, hE'⟩ := exists_abs_remJ_le_sup_on m J
    obtain ⟨W, hW⟩ := exists_abs_tyOp_le m J
    refine ⟨E' ++ W.map fun K => List.replicate (m j + 1) j ++ K, ?_, ?_⟩
    · intro ℓ hℓ
      rcases List.mem_append.1 hℓ with h | h
      · obtain ⟨j', hj', hc⟩ := hE'p ℓ h
        exact ⟨j', List.mem_cons_of_mem _ hj', hc⟩
      · obtain ⟨K, _, rfl⟩ := List.mem_map.1 h
        refine ⟨j, List.mem_cons_self .., ?_⟩
        rw [List.count_append, List.count_replicate_self]
        omega
    intro s d hd hs φ hφ B R hB w hw
    set a : ParabolicSpace := s j • coordDir j with ha
    have hcnt : ∀ i : Fin 4, (((j :: J).count i : ℕ) : ℝ) =
        (J.count i : ℝ) + ((Pi.single j (1 : ℝ) : Fin 4 → ℝ) i) := by
      intro i
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    have hSφ : ContDiff ℝ ∞ fun u => φ (u + a) := hφ.comp (contDiff_id.add contDiff_const)
    have hrem := contDiff_remOp hφ (coordDir j) (s j) (m j) 
    rw [remJ_cons s m j J hφ]
    simp only
    have h1 : |remJ s m J (fun u => φ (u + a)) w +
        tyOp s m J (remOp (coordDir j) (s j) (m j) φ) w| ≤
        |remJ s m J (fun u => φ (u + a)) w| +
          |tyOp s m J (remOp (coordDir j) (s j) (m j) φ) w| := abs_add_le _ _
    refine h1.trans ?_
    rw [List.map_append, List.sum_append]
    refine add_le_add ?_ ?_
    · refine hE' s d hd hs hSφ B (R := {u | u + a ∈ R}) (fun ℓ u hu => ?_) w (fun τ hτ => ?_)
      · rw [lineIter_shift]
        exact hB ℓ _ hu
      · have hτ' : ∀ i, 0 ≤ (τ + (Pi.single j (1 : ℝ) : Fin 4 → ℝ)) i ∧
            (τ + (Pi.single j (1 : ℝ) : Fin 4 → ℝ)) i ≤ (((j :: J).count i : ℕ) : ℝ) := by
          intro i
          obtain ⟨h0, h1⟩ := hτ i
          have hs1 : (0 : ℝ) ≤ (Pi.single j (1 : ℝ) : Fin 4 → ℝ) i := by
            by_cases hij : i = j
            · subst hij; simp
            · simp [hij]
          rw [hcnt i]
          simp only [Pi.add_apply]
          exact ⟨by linarith, by linarith⟩
        have := hw _ hτ'
        rw [boxPt_add_single, ← add_assoc] at this
        exact this
    · set ψ := remOp (coordDir j) (s j) (m j) φ with hψ
      refine (hW s d hd hs hrem w).trans ?_
      rw [List.map_map]
      refine List.sum_le_sum fun K _ => ?_
      simp only [Function.comp]
      have e1 : lineIter (K.map coordDir) ψ = remOp (coordDir j) (s j) (m j)
          (lineIter (K.map coordDir) φ) := lineIter_remOp hφ _ _ _ _
      have e2 : (dirDeriv (coordDir j))^[m j + 1] (lineIter (K.map coordDir) φ) =
          lineIter ((List.replicate (m j + 1) j ++ K).map coordDir) φ := by
        rw [List.map_append, List.map_replicate, lineIter_append, lineIter_replicate]
      have hwt : ∀ t : ℝ, 0 < t → t ≤ 1 → w + (t * s j) • coordDir j ∈ R := by
        intro t ht0 ht1
        have := hw (Pi.single j t : Fin 4 → ℝ) (fun i => by
          rw [hcnt i]
          by_cases hij : i = j
          · subst hij
            simp only [Pi.single_eq_same]
            have : (0 : ℝ) ≤ (J.count i : ℝ) := Nat.cast_nonneg _
            exact ⟨ht0.le, by linarith⟩
          · simp [hij])
        rwa [boxPt_single] at this
      have h3 := abs_remOp_le_of_sup_on (contDiff_lineIter hφ (K.map coordDir)) (coordDir j)
        (s j) (m j) (B (List.replicate (m j + 1) j ++ K)) w (fun t ht0 ht1 => by
          rw [e2]
          exact hB _ _ (hwt t ht0 ht1))
      rw [e1]
      have h4 : |s j| ^ (m j + 1) ≤ d ^ ((m j + 1) * parabolicWeight j) := by
        rw [mul_comm, pow_mul]
        exact pow_le_pow_left₀ (abs_nonneg _) (hs j) _
      have h5 : 0 ≤ B (List.replicate (m j + 1) j ++ K) := by
        have h0 := hw 0 (fun i => ⟨le_rfl, Nat.cast_nonneg _⟩)
        have : boxPt s 0 = 0 := by simp [boxPt]
        rw [this, add_zero] at h0
        exact (abs_nonneg _).trans (hB _ w h0)
      have h6 := h3.trans (mul_le_mul_of_nonneg_right h4 h5)
      have h7 := mul_le_mul_of_nonneg_left h6 (pow_nonneg hd (indexWeight K))
      rw [indexWeight_append, indexWeight_replicate, pow_add]
      calc _ ≤ _ := h7
        _ = _ := by ring

theorem exists_abs_taylorProfile_le_sup_on (σ : ℝ) :
    ∃ E : List (List (Fin 4)), (∀ ℓ ∈ E, σ ≤ (indexWeight ℓ : ℝ)) ∧
      ∀ {φ : ParabolicSpace → ℝ}, ContDiff ℝ ∞ φ → ∀ B : List (Fin 4) → ℝ,
        ∀ {R : Set ParabolicSpace}, (∀ ℓ u, u ∈ R → |lineIter (ℓ.map coordDir) φ u| ≤ B ℓ) →
        ∀ (z u : ParabolicSpace) (d : ℝ), 0 ≤ d →
        (∀ i, |parabolicCoords z i| ≤ d ^ parabolicWeight i) →
        (∀ τ : Fin 4 → ℝ, (∀ j, 0 ≤ τ j ∧ τ j ≤ 1) → u + boxPt (parabolicCoords z) τ ∈ R) →
        |taylorProfile φ σ z u| ≤ (E.map fun ℓ => d ^ indexWeight ℓ * B ℓ).sum := by
  classical
  obtain ⟨E, hEp, hE⟩ := exists_abs_remJ_le_sup_on (fun _ : Fin 4 => ⌈σ⌉₊) (List.finRange 4)
  set Out : List (List (Fin 4)) := (taylorOut σ).toList.map fun k => (Finsupp.toMultiset k).toList
    with hOut
  refine ⟨E ++ Out, ?_, ?_⟩
  · intro ℓ hℓ
    rcases List.mem_append.1 hℓ with hE' | hO
    · obtain ⟨j, -, hj⟩ := hEp ℓ hE'
      have h1 := count_le_indexWeight j ℓ
      have h2 : σ ≤ ⌈σ⌉₊ := Nat.le_ceil σ
      have h3 : (⌈σ⌉₊ : ℝ) + 1 ≤ (indexWeight ℓ : ℝ) := by exact_mod_cast hj.trans h1
      linarith
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hO
      have hk' := Finset.mem_toList.1 hk
      have : ¬ (multiDeg k : ℝ) < σ := by
        unfold taylorOut at hk'
        exact (Finset.mem_filter.1 hk').2
      rw [indexWeight_toList]
      exact not_lt.1 this
  · intro φ hφ B R hB z u d hd hz hbox
    have hφ' : ContDiff ℝ ∞ fun w => φ (-w) := hφ.comp contDiff_neg
    have hconv : ∀ F : List (Fin 4) → ℝ,
        ∑ k ∈ taylorOut σ, F ((Finsupp.toMultiset k).toList) = (Out.map F).sum := by
      intro F
      rw [hOut, List.map_map]
      exact (Finset.sum_map_toList (taylorOut σ)
        (fun k => F ((Finsupp.toMultiset k).toList))).symm
    have hu0 : u ∈ R := by
      have := hbox 0 (fun j => ⟨le_rfl, zero_le_one⟩)
      have e : boxPt (parabolicCoords z) 0 = 0 := by simp [boxPt]
      rwa [e, add_zero] at this
    rw [taylorProfile_eq hφ, List.map_append, List.sum_append]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine hE (fun i => -parabolicCoords z i) d hd (fun i => by rw [abs_neg]; exact hz i) hφ' B
        (R := (fun v => -v) ⁻¹' R) (fun ℓ v hv => ?_) _ (fun τ hτ => ?_)
      · rw [lineIter_reflect hφ, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        exact hB ℓ _ hv
      · have hc : ∀ j : Fin 4, (((List.finRange 4).count j : ℕ) : ℝ) = 1 := by
          intro j
          have : (List.finRange 4).count j = 1 :=
            List.count_eq_one_of_mem (List.nodup_finRange 4) (List.mem_finRange j)
          rw [this]; norm_num
        have hτ' : ∀ j, 0 ≤ τ j ∧ τ j ≤ 1 := fun j => by
          have := hτ j; rw [hc j] at this; exact this
        have := hbox τ hτ'
        have e : -(-u + boxPt (fun i => -parabolicCoords z i) τ) =
            u + boxPt (parabolicCoords z) τ := by
          unfold boxPt
          rw [neg_add, neg_neg, ← Finset.sum_neg_distrib]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_neg, neg_smul]
          simp
        show -(-u + boxPt (fun i => -parabolicCoords z i) τ) ∈ R
        rwa [e]
    · rw [← hconv]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul, indexWeight_toList]
      have hc := abs_coeffT_le hz k
      have := hB (Finsupp.toMultiset k).toList u hu0
      rw [← multiDirs_eq_map] at this
      exact mul_le_mul hc this (abs_nonneg _) (pow_nonneg hd _)

end RegularityStructures

end
