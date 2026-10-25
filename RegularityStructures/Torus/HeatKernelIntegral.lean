/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HeatKernelFacts
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Gaussian periodisation on the three-torus

The normalization and locally uniform convergence of the periodised Gaussian are recorded here. This
is the unfolding of the periodised heat kernel (2.1) of the statement.
-/

public section

open MeasureTheory Real Set Submodule

namespace RegularityStructures

noncomputable def integerLatticeAddEquiv :
    (Fin 3 → ℤ) ≃ (span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))).toAddSubgroup := by
  let e : (Fin 3 → ℤ) →
      (span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))).toAddSubgroup :=
    fun k => ⟨fun i => (k i : ℝ), by
      change (fun i => (k i : ℝ)) ∈ span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))
      rw [Module.Basis.mem_span_iff_repr_mem]
      simp [Pi.basisFun_repr]
      ⟩
  apply Equiv.ofBijective e
  constructor
  · intro k l h
    have h' : (fun i => (k i : ℝ)) = fun i => (l i : ℝ) := congrArg Subtype.val h
    funext i
    exact_mod_cast congrFun h' i
  · intro x
    have hx' : ∀ i, ∃ n : ℤ, x.1 i = (n : ℝ) := by
      have hmem := (Pi.basisFun ℝ (Fin 3)).mem_span_iff_repr_mem ℤ (x : Fin 3 → ℝ)
        |>.mp x.2
      simp [Pi.basisFun_repr] at hmem
      intro i
      rcases hmem i with ⟨n, hn⟩
      exact ⟨n, hn.symm⟩
    choose k hk using hx'
    refine ⟨k, ?_⟩
    apply Subtype.ext
    funext i
    dsimp [e]
    exact (hk i).symm

theorem integerLatticeAddEquiv_apply (k : Fin 3 → ℤ) (i : Fin 3) :
    (integerLatticeAddEquiv k).1 i = (k i : ℝ) := by
  rfl

noncomputable instance integerLatticeCountable :
    Countable (span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))).toAddSubgroup :=
  Countable.of_equiv (Fin 3 → ℤ) integerLatticeAddEquiv

theorem fundamentalDomain_ae_eq_pi_Ioc :
    ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3)) =ᵐ[volume]
      Set.pi Set.univ (fun _ : Fin 3 => Set.Ioc (0 : ℝ) 1) := by
  rw [ZSpan.fundamentalDomain_pi_basisFun]
  have hco := Measure.univ_pi_Ico_ae_eq_Icc
    (μ := fun _ : Fin 3 => (volume : Measure ℝ))
    (f := fun _ : Fin 3 => (0 : ℝ)) (g := fun _ : Fin 3 => (1 : ℝ))
  have hoc := Measure.univ_pi_Ioc_ae_eq_Icc
    (μ := fun _ : Fin 3 => (volume : Measure ℝ))
    (f := fun _ : Fin 3 => (0 : ℝ)) (g := fun _ : Fin 3 => (1 : ℝ))
  have h := hco.trans hoc.symm
  simpa only [volume_pi] using h

theorem summable_exp_neg_mul_sq_int {a b : ℝ} (ha : 0 < a)
    (hb : b ∈ Set.Ico (0 : ℝ) 1) :
    Summable (fun n : ℤ => exp (-a * (b + n) ^ 2)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · apply summable_exp_nat_mul_of_ge (neg_lt_zero.mpr ha)
    intro n
    have hnat : (n : ℝ) ≤ (n : ℝ) * n := by
      exact_mod_cast Nat.le_mul_self n
    have hn : (n : ℝ) ≤ (b + n) ^ 2 := by
      nlinarith [sq_nonneg b, mul_nonneg hb.1 (Nat.cast_nonneg n), hnat]
    exact hn
  · rw [← summable_nat_add_iff 2]
    apply summable_exp_nat_mul_of_ge (neg_lt_zero.mpr ha)
    intro n
    have hmag : (n : ℝ) + 1 ≤ (n : ℝ) + 2 - b := by
      linarith [hb.2]
    have hnonneg : 0 ≤ (n : ℝ) + 1 := by positivity
    have hsquare : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 2 - b) ^ 2 :=
      (sq_le_sq₀ hnonneg (by linarith)).2 hmag
    have hn : (n : ℝ) ≤ (b - ((n : ℕ) + 2 : ℕ)) ^ 2 := by
      rw [show b - ((n : ℕ) + 2 : ℕ) = -((n : ℝ) + 2 - b) by norm_num]
      nlinarith [hsquare]
    simpa [Int.cast_neg, Nat.cast_add, add_comm, sub_eq_add_neg] using hn

theorem summable_gaussian_vector {t : ℝ} (ht : 0 < t) (x : Fin 3 → ℝ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1) :
    Summable (fun k : Fin 3 → ℤ =>
      ∏ i, exp (-((4 * t)⁻¹) * (x i + (k i : ℝ)) ^ 2)) := by
  classical
  let f : Fin 3 → ℤ → ℝ := fun i k => exp (-((4 * t)⁻¹) * (x i + (k : ℝ)) ^ 2)
  have hf : ∀ i, Summable (f i) := by
    intro i
    exact summable_exp_neg_mul_sq_int (by positivity) (hx i)
  have h01 : Summable (fun p : ℤ × ℤ => f 0 p.1 * f 1 p.2) :=
    (hf 0).mul_of_nonneg (hf 1) (by intro; positivity) (by intro; positivity)
  have h012 : Summable (fun q : (ℤ × ℤ) × ℤ =>
      (f 0 q.1.1 * f 1 q.1.2) * f 2 q.2) :=
    h01.mul_of_nonneg (hf 2) (by intro; positivity) (by intro; positivity)
  let e2 : (ℤ × ℤ) ≃ (Fin 2 → ℤ) :=
    (piFinTwoEquiv (fun _ : Fin 2 => ℤ)).symm
  let e3 : ((ℤ × ℤ) × ℤ) ≃ (Fin 3 → ℤ) :=
    ((Equiv.prodAssoc ℤ ℤ ℤ).trans
      (Equiv.prodCongr (Equiv.refl ℤ) e2)).trans
      (Fin.consEquiv (fun _ : Fin 3 => ℤ))
  rw [← e3.summable_iff]
  convert h012 using 1
  funext q
  simp [f, e3, e2, Fin.prod_univ_succ, piFinTwoEquiv]
  ring

theorem summable_gaussKernel_shift {t : ℝ} (ht : 0 < t) (x : Fin 3 → ℝ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1) :
    Summable (fun k : Fin 3 → ℤ => gaussKernel t (x + fun i => (k i : ℝ))) := by
  have h := summable_gaussian_vector ht x hx
  have h' := h.mul_left ((4 * π * t) ^ (-(3 : ℝ) / 2))
  apply h'.congr
  intro k
  rw [gaussKernel_eq_prod]
  rfl

theorem torusRep_torusProj_of_mem_Ico {x : Fin 3 → ℝ}
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1) : torusRep (torusProj x) = x := by
  funext i
  dsimp [torusRep, torusProj]
  exact congrArg Subtype.val (AddCircle.equivIco_coe_eq (by simpa using hx i))

theorem lintegral_heatKernel_preimage_eq_gauss {t : ℝ} (ht : 0 < t) :
    (∫⁻ (x : Fin 3 → ℝ) in {x | ∀ i : Fin 3, x i ∈ Set.Ioc (0 : ℝ) 1},
        ENNReal.ofReal (heatKernel t (fun i => (x i : UnitAddCircle)))) =
      ∫⁻ y : Fin 3 → ℝ, ENNReal.ofReal (gaussKernel t y) := by
  let D : Set (Fin 3 → ℝ) := ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3))
  let Doc : Set (Fin 3 → ℝ) := {x | ∀ i : Fin 3, x i ∈ Set.Ioc (0 : ℝ) 1}
  have hset : D =ᵐ[volume] Doc := by
    dsimp [D, Doc]
    exact fundamentalDomain_ae_eq_pi_Ioc.trans <| Filter.Eventually.of_forall fun x => by
      apply propext
      constructor
      · intro hx i
        exact (Set.mem_pi.mp hx) i (Set.mem_univ i)
      · intro hx
        exact Set.mem_pi.mpr fun i _ => hx i
  have hrestrict : volume.restrict D = volume.restrict Doc :=
    MeasureTheory.Measure.restrict_congr_set hset
  rw [← hrestrict]
  have hDmeas : MeasurableSet D := by
    dsimp [D]
    rw [ZSpan.fundamentalDomain_pi_basisFun]
    exact (measurableSet_pi Set.countable_univ).2 <| Or.inl fun i _ => measurableSet_Ico
  have hDmem : ∀ x ∈ D, ∀ i, x i ∈ Set.Ico (0 : ℝ) 1 := by
    intro x hx i
    dsimp [D] at hx
    rw [ZSpan.fundamentalDomain_pi_basisFun] at hx
    exact (Set.mem_pi.mp hx) i (Set.mem_univ i)
  have hheat : ∀ x ∈ D,
      ENNReal.ofReal (heatKernel t (fun i => (x i : UnitAddCircle))) =
        ENNReal.ofReal (∑' k : Fin 3 → ℤ,
          gaussKernel t (x + fun i => (k i : ℝ))) := by
    intro x hx
    congr 1
    change heatKernel t (torusProj x) = _
    rw [heatKernel, torusRep_torusProj_of_mem_Ico (hDmem x hx)]
  rw [MeasureTheory.setLIntegral_congr_fun hDmeas hheat]
  have hsum : ∀ x ∈ D,
      ENNReal.ofReal (∑' k : Fin 3 → ℤ,
          gaussKernel t (x + fun i => (k i : ℝ))) =
        ∑' k : Fin 3 → ℤ,
          ENNReal.ofReal (gaussKernel t (x + fun i => (k i : ℝ))) := by
    intro x hx
    exact ENNReal.ofReal_tsum_of_nonneg
      (fun k => gaussKernel_nonneg ht _) (summable_gaussKernel_shift ht x (hDmem x hx))
  rw [MeasureTheory.setLIntegral_congr_fun hDmeas hsum]
  have hmeas : ∀ k : Fin 3 → ℤ,
      AEMeasurable (fun x : Fin 3 → ℝ =>
        ENNReal.ofReal (gaussKernel t (x + fun i => (k i : ℝ))))
        (volume.restrict D) := by
    intro k
    exact (((continuous_gaussKernel_fixed ht).measurable.comp
      (measurable_id.add measurable_const)).ennreal_ofReal.aemeasurable)
  rw [MeasureTheory.lintegral_tsum hmeas]
  calc
    (∑' k : Fin 3 → ℤ,
        ∫⁻ (x : Fin 3 → ℝ) in D,
          ENNReal.ofReal (gaussKernel t (x + fun i => (k i : ℝ)))) =
        ∫⁻ y : Fin 3 → ℝ, ENNReal.ofReal (gaussKernel t y) := by
      symm
      calc
        ∫⁻ y : Fin 3 → ℝ, ENNReal.ofReal (gaussKernel t y) =
            ∑' k : (span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))).toAddSubgroup,
              ∫⁻ y : Fin 3 → ℝ in D,
                ENNReal.ofReal (gaussKernel t (k + y)) := by
          exact (ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin 3)) volume).lintegral_eq_tsum'' _
        _ = ∑' k : Fin 3 → ℤ,
              ∫⁻ y : Fin 3 → ℝ in D,
                ENNReal.ofReal (gaussKernel t (y + fun i => (k i : ℝ))) := by
          rw [← integerLatticeAddEquiv.tsum_eq]
          apply tsum_congr
          intro k
          congr 2
          funext y
          congr 2
          funext i
          simp [integerLatticeAddEquiv_apply, add_comm]

theorem integral_heatKernel {t : ℝ} (ht : 0 < t) :
    ∫ x : Torus3, heatKernel t x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (heatKernel_nonneg ht))
    (measurable_heatKernel_fixed t).aestronglyMeasurable]
  have hpre :
      (∫⁻ x : Torus3, ENNReal.ofReal (heatKernel t x) ∂(volume : Measure Torus3)) =
        ∫⁻ (x : Fin 3 → ℝ) in {x | ∀ i : Fin 3, x i ∈ Set.Ioc (0 : ℝ) 1},
          ENNReal.ofReal (heatKernel t (fun i => (x i : UnitAddCircle))) := by
    simpa only [Set.mem_pi, Set.mem_univ, true_implies, zero_add,
      MeasureSpace.volume, instMeasureSpaceUnitAddCircle,
      AddCircle.measureSpace, AddCircle.haarAddCircle, ENNReal.ofReal_one, one_smul] using
      UnitAddTorus.lintegral_preimage
      (fun x : Torus3 => ENNReal.ofReal (heatKernel t x)) (fun _ : Fin 3 => (0 : ℝ))
  rw [congrArg ENNReal.toReal hpre]
  rw [lintegral_heatKernel_preimage_eq_gauss ht]
  rw [← integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (gaussKernel_nonneg ht))
    (integrable_gaussKernel ht).aestronglyMeasurable]
  rw [integral_gaussKernel ht]

end RegularityStructures

end
