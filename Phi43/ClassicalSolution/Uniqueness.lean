/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.ClassicalSolution.CubicMonotonicity
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Uniqueness of classical solutions

This file records the periodic integration-by-parts input used in the `L²` energy proof of the
uniqueness part of W4.  The endpoint terms cancel because a periodic function and its derivative
have the same values at the two endpoints of one period.

The PDE application is the uniqueness of the classical solutions of Definition 2.6 of
the statement.
-/

public section

open MeasureTheory Set Function intervalIntegral Metric Filter
open scoped ContDiff
open scoped Topology

namespace RegularityStructures.Phi43

private theorem torusProj_update_add_period (i : Fin 3) (y : Fin 3 → ℝ) :
    torusProj (Function.update y i (y i + 1)) = torusProj y := by
  funext j
  by_cases h : j = i
  · subst j
    simp only [torusProj]
    simp [Function.update]
  · change ((Function.update y i (y i + 1)) j : UnitAddCircle) = (y j : UnitAddCircle)
    simp [Function.update, h]

private theorem contDiff_insertNth {F : (Fin 3 → ℝ) → ℝ} (hF : ContDiff ℝ 2 F)
    (i : Fin 3) (x : Fin 2 → ℝ) :
    ContDiff ℝ 2 (fun s : ℝ => F (i.insertNth s x)) := by
  apply hF.comp
  refine contDiff_pi' ?_
  rw [i.forall_iff_succAbove]
  constructor
  · simp only [Fin.insertNth_apply_same]
    fun_prop
  · intro j
    simpa only [Fin.insertNth_apply_succAbove] using
      (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => x j))

private noncomputable def cubeMeasure : Measure (Fin 3 → ℝ) :=
  Measure.pi (fun _ : Fin 3 => volume.restrict (Ioc (0 : ℝ) 1))

private noncomputable def partialDeriv (F : (Fin 3 → ℝ) → ℝ) (i : Fin 3) (y : Fin 3 → ℝ) : ℝ :=
  deriv (fun r => F (Function.update y i r)) (y i)

private theorem insertNth_update (i : Fin 3) (x : Fin 2 → ℝ) (s r : ℝ) :
    Function.update (i.insertNth (α := fun _ : Fin 3 => ℝ) s x) i r =
      i.insertNth (α := fun _ : Fin 3 => ℝ) r x := by
  funext j
  cases j using i.succAboveCases with
  | x => simp [Function.update]
  | p j => simp [Function.update]

private theorem periodic_insertNth_section {F : (Fin 3 → ℝ) → ℝ}
    (hper : ∀ (i : Fin 3) (y : Fin 3 → ℝ),
      F (Function.update y i (y i + 1)) = F y)
    (i : Fin 3) (x : Fin 2 → ℝ) :
    Function.Periodic (fun s : ℝ => F (i.insertNth (α := fun _ : Fin 3 => ℝ) s x)) 1 := by
  intro s
  have hs : (i.insertNth (α := fun _ : Fin 3 => ℝ) s x) i = s := by simp
  change F (i.insertNth (α := fun _ : Fin 3 => ℝ) (s + 1) x) =
    F (i.insertNth (α := fun _ : Fin 3 => ℝ) s x)
  rw [show i.insertNth (α := fun _ : Fin 3 => ℝ) (s + 1) x =
      Function.update (i.insertNth (α := fun _ : Fin 3 => ℝ) s x) i
        ((i.insertNth (α := fun _ : Fin 3 => ℝ) s x) i + 1) by
        rw [hs, insertNth_update]]
  exact hper i (i.insertNth (α := fun _ : Fin 3 => ℝ) s x)

private theorem partialDeriv_insertNth {F : (Fin 3 → ℝ) → ℝ} (i : Fin 3) (x : Fin 2 → ℝ)
    (s : ℝ) :
    partialDeriv F i (i.insertNth (α := fun _ : Fin 3 => ℝ) s x) =
      deriv (fun r => F (i.insertNth (α := fun _ : Fin 3 => ℝ) r x)) s := by
  unfold partialDeriv
  rw [show (fun r => F (Function.update
      (i.insertNth (α := fun _ : Fin 3 => ℝ) s x) i r)) =
      (fun r => F (i.insertNth (α := fun _ : Fin 3 => ℝ) r x)) by
        funext r
        rw [insertNth_update]]
  simp only [Fin.insertNth_apply_same]

private theorem partialDeriv_eq_fderiv {F : (Fin 3 → ℝ) → ℝ} (hF : ContDiff ℝ 2 F)
    (i : Fin 3) (y : Fin 3 → ℝ) :
    partialDeriv F i y = (fderiv ℝ F y) (Pi.single i (1 : ℝ)) := by
  unfold partialDeriv
  have hFy : DifferentiableAt ℝ F (Function.update y i (y i)) := by
    simpa [Function.update] using (hF.differentiable (by norm_num) y)
  have h := fderiv_comp_deriv (x := y i) (l := F) (f := Function.update y i)
    hFy
    (hasDerivAt_update y i (y i)).differentiableAt
  simpa [Function.comp_def, Function.update, deriv_update] using h

private theorem continuous_partialDeriv {F : (Fin 3 → ℝ) → ℝ} (hF : ContDiff ℝ 2 F)
    (i : Fin 3) : Continuous (partialDeriv F i) := by
  have heq : partialDeriv F i = fun y => (fderiv ℝ F y) (Pi.single i (1 : ℝ)) := by
    funext y
    exact partialDeriv_eq_fderiv hF i y
  rw [heq]
  have hfd : ContDiff ℝ 1 (fderiv ℝ F) := by
    exact hF.fderiv_right (m := 1) (by norm_num)
  exact (hfd.clm_apply contDiff_const).continuous

private theorem contDiff_partialDeriv {F : (Fin 3 → ℝ) → ℝ} (hF : ContDiff ℝ 2 F)
    (i : Fin 3) : ContDiff ℝ 1 (partialDeriv F i) := by
  have heq : partialDeriv F i = fun y => (fderiv ℝ F y) (Pi.single i (1 : ℝ)) := by
    funext y
    unfold partialDeriv
    have hFy : DifferentiableAt ℝ F (Function.update y i (y i)) := by
      simpa [Function.update] using (hF.differentiable (by norm_num) y)
    have h := fderiv_comp_deriv (x := y i) (l := F) (f := Function.update y i)
      hFy
      (hasDerivAt_update y i (y i)).differentiableAt
    simpa [Function.comp_def, Function.update, deriv_update] using h
  rw [heq]
  have hfd : ContDiff ℝ 1 (fderiv ℝ F) := by
    exact hF.fderiv_right (m := 1) (by norm_num)
  exact hfd.clm_apply contDiff_const

private noncomputable def secondPartial (F : (Fin 3 → ℝ) → ℝ) (i : Fin 3)
    (y : Fin 3 → ℝ) : ℝ :=
  (fderiv ℝ (partialDeriv F i) y) (Pi.single i (1 : ℝ))

private theorem continuous_secondPartial {F : (Fin 3 → ℝ) → ℝ} (hF : ContDiff ℝ 2 F)
    (i : Fin 3) : Continuous (secondPartial F i) := by
  unfold secondPartial
  have hp := contDiff_partialDeriv hF i
  have hfd : ContDiff ℝ 0 (fderiv ℝ (partialDeriv F i)) := by
    exact hp.fderiv_right (m := 0) (by norm_num)
  exact (hfd.clm_apply contDiff_const).continuous

private theorem secondPartial_eq_deriv {F : (Fin 3 → ℝ) → ℝ} (hF : ContDiff ℝ 2 F)
    (i : Fin 3) (y : Fin 3 → ℝ) :
    secondPartial F i y =
      deriv (deriv (fun r => F (Function.update y i r))) (y i) := by
  have hfirst : ∀ r : ℝ,
      deriv (fun s => F (Function.update y i s)) r =
        partialDeriv F i (Function.update y i r) := by
    intro r
    rw [partialDeriv_eq_fderiv hF i]
    have hFy : DifferentiableAt ℝ F (Function.update y i r) := by
      exact hF.differentiable (by norm_num) _
    have h := fderiv_comp_deriv (x := r) (l := F) (f := Function.update y i)
      hFy (hasDerivAt_update y i r).differentiableAt
    simpa [Function.comp_def, Function.update, deriv_update] using h
  have hfun : deriv (fun r => F (Function.update y i r)) =
      (fun r => partialDeriv F i (Function.update y i r)) := by
    funext r
    exact hfirst r
  rw [hfun]
  unfold secondPartial
  have hp : DifferentiableAt ℝ (partialDeriv F i)
      (Function.update y i (y i)) := by
    simpa [Function.update] using
      (contDiff_partialDeriv hF i).differentiable (by norm_num) y
  have h := fderiv_comp_deriv (x := y i) (l := partialDeriv F i)
    (f := Function.update y i) hp
    (hasDerivAt_update y i (y i)).differentiableAt
  simpa [Function.comp_def, Function.update, deriv_update] using h.symm

private theorem secondPartial_insertNth {F : (Fin 3 → ℝ) → ℝ} (hF : ContDiff ℝ 2 F)
    (i : Fin 3) (x : Fin 2 → ℝ) (s : ℝ) :
    secondPartial F i (i.insertNth (α := fun _ : Fin 3 => ℝ) s x) =
      deriv (deriv (fun r => F (i.insertNth (α := fun _ : Fin 3 => ℝ) r x))) s := by
  rw [secondPartial_eq_deriv hF i]
  simp only [Fin.insertNth_apply_same]
  congr 2
  funext r
  rw [insertNth_update]

private theorem cubeMeasure_eq_restrict :
    cubeMeasure = volume.restrict (Set.univ.pi (fun _ : Fin 3 => Ioc (0 : ℝ) 1)) := by
  rw [cubeMeasure, ← Measure.restrict_pi_pi]
  rfl

private theorem integrable_cube_of_continuous {H : (Fin 3 → ℝ) → ℝ} (hH : Continuous H) :
    Integrable H cubeMeasure := by
  rw [cubeMeasure_eq_restrict]
  apply (hH.continuousOn.integrableOn_compact
    (isCompact_univ_pi fun _ => isCompact_Icc)).mono_set
  intro y hy i hi
  exact Ioc_subset_Icc_self (hy i hi)

private theorem periodic_deriv {g : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (deriv g x) x)
    (hper : Function.Periodic g 1) : Function.Periodic (deriv g) 1 := by
  intro x
  have hshift : HasDerivAt (fun y : ℝ => g (y + 1)) (deriv g (x + 1)) x := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (hg (x + 1)).comp x ((hasDerivAt_id x).add_const 1)
  have hsame : HasDerivAt g (deriv g (x + 1)) x :=
    hshift.congr_of_eventuallyEq <| Filter.Eventually.of_forall fun y => (hper y).symm
  exact hsame.unique (hg x)

/-- Integration by parts for a twice differentiable periodic real function on one period. -/
private theorem intervalIntegral_periodic_mul_secondDeriv
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hper : Function.Periodic g 1) :
    (∫ x in (0 : ℝ)..1, g x * deriv (deriv g) x) =
      -∫ x in (0 : ℝ)..1, (deriv g x) ^ 2 := by
  have h₁ : ∀ x, HasDerivAt g (deriv g x) x := fun x =>
    (hg.contDiffAt.differentiableAt (by norm_num)).hasDerivAt
  have h₂ : ∀ x, HasDerivAt (deriv g) (deriv (deriv g) x) x := by
    intro x
    exact (hg.differentiable_deriv_two x).hasDerivAt
  have hper' : Function.Periodic (deriv g) 1 := periodic_deriv h₁ hper
  have hderiv : ContDiff ℝ 1 (deriv g) := by
    have hg' : ContDiff ℝ (1 + 1) g := by
      convert hg using 1
      norm_num
    exact (contDiff_succ_iff_deriv.mp hg').2.2
  have hfirst : IntervalIntegrable (fun x => deriv g x) volume 0 1 :=
    (hg.continuous_deriv (by norm_num)).intervalIntegrable 0 1
  have hsecond : IntervalIntegrable (fun x => deriv (deriv g) x) volume 0 1 :=
    (hderiv.continuous_deriv (by norm_num)).intervalIntegrable 0 1
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := g) (v := deriv g) (u' := deriv g) (v' := fun x => deriv (deriv g) x)
    (fun x _ => h₁ x) (fun x _ => h₂ x) hfirst hsecond
  rw [h]
  have h0 : g 1 = g 0 := by simpa using hper 0
  have h0' : deriv g 1 = deriv g 0 := by simpa using hper' 0
  rw [h0, h0']
  ring_nf

private theorem cube_integral_mul_secondPartial
    {F : (Fin 3 → ℝ) → ℝ} (hF : ContDiff ℝ 2 F)
    (hper : ∀ (i : Fin 3) (y : Fin 3 → ℝ),
      F (Function.update y i (y i + 1)) = F y) (i : Fin 3) :
    (∫ y, F y * secondPartial F i y ∂cubeMeasure) =
      -∫ y, (partialDeriv F i y) ^ 2 ∂cubeMeasure := by
  have hL : Integrable (fun y => F y * secondPartial F i y) cubeMeasure :=
    integrable_cube_of_continuous (hF.continuous.mul (continuous_secondPartial hF i))
  have hR : Integrable (fun y => (partialDeriv F i y) ^ 2) cubeMeasure :=
    integrable_cube_of_continuous ((continuous_partialDeriv hF i).pow 2)
  let e : ℝ × (Fin 2 → ℝ) ≃ᵐ (Fin 3 → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i).symm
  have he : MeasurePreserving e
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod
        (Measure.pi (fun _ : Fin 2 => volume.restrict (Ioc (0 : ℝ) 1)))) cubeMeasure := by
    exact (measurePreserving_piFinSuccAbove
      (fun _ : Fin 3 => volume.restrict (Ioc (0 : ℝ) 1)) i).symm
  rw [← he.integral_comp' (fun y => F y * secondPartial F i y)]
  conv_rhs =>
    rw [← he.integral_comp' (fun y => (partialDeriv F i y) ^ 2)]
  have hLp : Integrable (fun z : ℝ × (Fin 2 → ℝ) =>
      F (e z) * secondPartial F i (e z))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod
        (Measure.pi (fun _ : Fin 2 => volume.restrict (Ioc (0 : ℝ) 1)))) := by
    simpa [Function.comp_def] using he.integrable_comp_of_integrable hL
  have hRp : Integrable (fun z : ℝ × (Fin 2 → ℝ) =>
      (partialDeriv F i (e z)) ^ 2)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod
        (Measure.pi (fun _ : Fin 2 => volume.restrict (Ioc (0 : ℝ) 1)))) := by
    simpa [Function.comp_def] using he.integrable_comp_of_integrable hR
  rw [integral_prod_symm _ hLp]
  rw [integral_prod_symm _ hRp]
  simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk]
  rw [← MeasureTheory.integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp
  rw [← intervalIntegral.integral_of_le (μ := volume) (by norm_num)]
  rw [← intervalIntegral.integral_of_le (μ := volume) (by norm_num)]
  have hsec : ∀ s : ℝ,
      secondPartial F i (i.insertNth (α := fun _ : Fin 3 => ℝ) s x) =
        deriv (deriv (fun r => F (i.insertNth (α := fun _ : Fin 3 => ℝ) r x))) s :=
    fun s => secondPartial_insertNth hF i x s
  have hfirst : ∀ s : ℝ,
      partialDeriv F i (i.insertNth (α := fun _ : Fin 3 => ℝ) s x) =
        deriv (fun r => F (i.insertNth (α := fun _ : Fin 3 => ℝ) r x)) s :=
    fun s => partialDeriv_insertNth i x s
  simp_rw [hsec, hfirst]
  exact intervalIntegral_periodic_mul_secondDeriv
    (contDiff_insertNth hF i x) (periodic_insertNth_section hper i x)

private noncomputable def energy (W : (ℝ × (Fin 3 → ℝ)) → ℝ) (t : ℝ) : ℝ :=
  ∫ y, W (t, y) ^ 2 ∂cubeMeasure

private noncomputable def timeDeriv (W : (ℝ × (Fin 3 → ℝ)) → ℝ)
    (p : ℝ × (Fin 3 → ℝ)) : ℝ :=
  (fderiv ℝ W p) (1, 0)

private theorem hasDerivAt_energy
    {W : (ℝ × (Fin 3 → ℝ)) → ℝ}
    (hW : ContDiffOn ℝ ∞ W (Ioi 0 ×ˢ Set.univ)) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (energy W)
      (∫ y, 2 * W (t, y) * timeDeriv W (t, y) ∂cubeMeasure) t := by
  let S : Set (ℝ × (Fin 3 → ℝ)) := Ioi 0 ×ˢ Set.univ
  let s : Set ℝ := ball t (t / 2)
  have hs : s ∈ 𝓝 t := ball_mem_nhds t (half_pos ht)
  have hball_bounds : ∀ {x : ℝ}, x ∈ s → t / 2 < x ∧ x < 3 * t / 2 := by
    intro x hx
    have hdist : |x - t| < t / 2 := by
      simpa [Real.dist_eq] using (mem_ball.1 hx)
    rcases (abs_lt.mp hdist) with ⟨hlo, hhi⟩
    constructor <;> linarith [ht]
  have hSopen : IsOpen S := isOpen_Ioi.prod isOpen_univ
  have hfd : ContinuousOn (fderiv ℝ W) S :=
    hW.continuousOn_fderiv_of_isOpen hSopen (by norm_num)
  have hD : ContinuousOn (timeDeriv W) S := by
    unfold timeDeriv
    exact hfd.clm_apply continuousOn_const
  have hJ : ContinuousOn (fun p => 2 * W p * timeDeriv W p) S :=
    ((hW.continuousOn).const_mul 2).mul hD
  have hK : IsCompact (Icc (t / 2) (3 * t / 2) ×ˢ
      Set.univ.pi (fun _ : Fin 3 => Icc (0 : ℝ) 1)) :=
    isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have hKsub : Icc (t / 2) (3 * t / 2) ×ˢ
      Set.univ.pi (fun _ : Fin 3 => Icc (0 : ℝ) 1) ⊆ S := by
    intro p hp
    rcases hp with ⟨hp_t, hp_y⟩
    exact ⟨lt_of_lt_of_le (half_pos ht) hp_t.1, mem_univ p.2⟩
  rcases hK.bddAbove_image (hJ.mono hKsub).norm with ⟨M, hM⟩
  have hM_int : Integrable (fun _ : Fin 3 → ℝ => M) cubeMeasure := by
    rw [cubeMeasure_eq_restrict]
    exact integrableOn_const
      (measure_ne_top_of_subset
        (s := Set.univ.pi (fun _ : Fin 3 => Icc (0 : ℝ) 1))
        (t := Set.univ.pi (fun _ : Fin 3 => Ioc (0 : ℝ) 1))
        (fun y hy i hi => Ioc_subset_Icc_self (hy i hi))
        (isCompact_univ_pi (fun _ => isCompact_Icc)).measure_ne_top)
      (by finiteness)
  have hF_meas : ∀ᶠ x in 𝓝 t,
      AEStronglyMeasurable (fun y => W (x, y) ^ 2) cubeMeasure := by
    filter_upwards [hs] with x hx
    have hxpos : 0 < x := by
      exact lt_of_lt_of_le (by linarith [ht]) (le_of_lt (hball_bounds hx).1)
    have hcont : Continuous (fun y => W (x, y)) := by
      rw [← continuousOn_univ]
      exact hW.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
        (fun y _ => ⟨hxpos, mem_univ y⟩)
    exact (hcont.pow 2).aestronglyMeasurable
  have hF_int : Integrable (fun y => W (t, y) ^ 2) cubeMeasure := by
    have hcont : Continuous (fun y => W (t, y)) := by
      rw [← continuousOn_univ]
      exact hW.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
        (fun y _ => ⟨ht, mem_univ y⟩)
    exact integrable_cube_of_continuous (hcont.pow 2)
  have hF'_meas : AEStronglyMeasurable
      (fun y => 2 * W (t, y) * timeDeriv W (t, y)) cubeMeasure := by
    have hcont : Continuous (fun y => 2 * W (t, y) * timeDeriv W (t, y)) := by
      rw [← continuousOn_univ]
      exact hJ.comp (continuousOn_const.prodMk continuousOn_id)
        (fun y _ => ⟨ht, mem_univ y⟩)
    exact hcont.aestronglyMeasurable
  have hbound : ∀ᵐ y ∂cubeMeasure, ∀ x ∈ s,
      ‖2 * W (x, y) * timeDeriv W (x, y)‖ ≤ M := by
    rw [cubeMeasure_eq_restrict]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi (fun _ => measurableSet_Ioc))] with y hy
    intro x hx
    apply hM
    refine mem_image_of_mem _ ⟨?_, ?_⟩
    · exact ⟨le_of_lt (hball_bounds hx).1, le_of_lt (hball_bounds hx).2⟩
    · intro i hi
      exact Ioc_subset_Icc_self (hy i hi)
  have hdiff : ∀ᵐ y ∂cubeMeasure, ∀ x ∈ s,
      HasDerivAt (fun z => W (z, y) ^ 2)
        (2 * W (x, y) * timeDeriv W (x, y)) x := by
    filter_upwards with y
    intro x hx
    have hxpos : 0 < x := by
      exact lt_of_lt_of_le (by linarith [ht]) (le_of_lt (hball_bounds hx).1)
    have hWy : ContDiffAt ℝ ∞ W (x, y) := by
      exact (hW (x, y) ⟨hxpos, mem_univ y⟩).contDiffAt
        (hSopen.mem_nhds ⟨hxpos, mem_univ y⟩)
    have hpath : HasDerivAt (fun z : ℝ => (z, y)) (1, 0) x :=
      (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
    have htime : HasDerivAt (fun z : ℝ => W (z, y))
        (timeDeriv W (x, y)) x := by
      simpa [timeDeriv, Function.comp_def] using
        (hWy.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x hpath
    convert (HasDerivAt.pow htime 2) using 1
    simp
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := cubeMeasure) (F := fun x y => W (x, y) ^ 2)
    (F' := fun x y => 2 * W (x, y) * timeDeriv W (x, y)) hs hF_meas hF_int hF'_meas
    hbound hM_int hdiff
  change HasDerivAt (fun n => ∫ y, W (n, y) ^ 2 ∂cubeMeasure)
    (∫ y, 2 * W (t, y) * timeDeriv W (t, y) ∂cubeMeasure) t
  exact h.2

private theorem continuousOn_energy {W : (ℝ × (Fin 3 → ℝ)) → ℝ} {a b : ℝ}
    (hW : ContinuousOn W (Icc a b ×ˢ Set.univ)) :
    ContinuousOn (energy W) (Icc a b) := by
  have hmeas : ∀ t ∈ Icc a b,
      AEStronglyMeasurable (fun y => W (t, y) ^ 2) cubeMeasure := by
    intro t ht
    have hcont : Continuous (fun y => W (t, y)) := by
      rw [← continuousOn_univ]
      exact hW.comp (continuousOn_const.prodMk continuousOn_id)
        (fun y _ => ⟨ht, mem_univ y⟩)
    exact (hcont.pow 2).aestronglyMeasurable
  have hcompact : IsCompact (Icc a b ×ˢ Set.univ.pi (fun _ : Fin 3 => Icc (0 : ℝ) 1)) :=
    isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have hcont : ContinuousOn (fun p => W p ^ 2)
      (Icc a b ×ˢ Set.univ.pi (fun _ : Fin 3 => Icc (0 : ℝ) 1)) := by
    exact (hW.mono (fun p hp => ⟨hp.1, mem_univ p.2⟩)).pow 2
  rcases hcompact.bddAbove_image hcont.norm with ⟨M, hM⟩
  have hbound : ∀ t ∈ Icc a b, ∀ᵐ y ∂cubeMeasure, ‖W (t, y) ^ 2‖ ≤ M := by
    intro t ht
    rw [cubeMeasure_eq_restrict]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi (fun _ => measurableSet_Ioc))] with y hy
    apply hM
    exact mem_image_of_mem _ ⟨ht, fun i _ => Ioc_subset_Icc_self (hy i ‹_›)⟩
  have hM_int : Integrable (fun _ : Fin 3 → ℝ => M) cubeMeasure := by
    rw [cubeMeasure_eq_restrict]
    exact integrableOn_const
      (measure_ne_top_of_subset
      (s := Set.univ.pi (fun _ : Fin 3 => Icc (0 : ℝ) 1))
      (t := Set.univ.pi (fun _ : Fin 3 => Ioc (0 : ℝ) 1))
      (fun y hy i hi => Ioc_subset_Icc_self (hy i hi))
      (isCompact_univ_pi (fun _ => isCompact_Icc)).measure_ne_top)
      (by finiteness)
  have hparam : ∀ᵐ y ∂cubeMeasure,
      ContinuousOn (fun t => W (t, y) ^ 2) (Icc a b) := by
    filter_upwards with y
    exact (hW.comp (continuousOn_id.prodMk continuousOn_const)
      (fun t ht => ⟨ht, mem_univ y⟩)).pow 2
  change ContinuousOn (fun t => ∫ y, W (t, y) ^ 2 ∂cubeMeasure) (Icc a b)
  exact continuousOn_of_dominated hmeas hbound hM_int hparam

/-- Two classical solutions with the same data agree at every nonnegative time. -/
theorem classicalSolution_unique (c : ℝ) {f : SpaceTime → ℝ}
    {u₀ : C(Torus3, ℝ)} {u u' : ℝ → C(Torus3, ℝ)}
    (hu : IsClassicalSolution c f u₀ u) (hu' : IsClassicalSolution c f u₀ u') :
    ∀ t, 0 ≤ t → u t = u' t := by
  let S : Set (ℝ × (Fin 3 → ℝ)) := Ioi 0 ×ˢ Set.univ
  let U : (ℝ × (Fin 3 → ℝ)) → ℝ := fun p => u p.1 (torusProj p.2)
  let V : (ℝ × (Fin 3 → ℝ)) → ℝ := fun p => u' p.1 (torusProj p.2)
  let W : (ℝ × (Fin 3 → ℝ)) → ℝ := fun p => U p - V p
  have hU : ContDiffOn ℝ ∞ U S := by
    simpa [U, S] using hu.contDiffOn
  have hV : ContDiffOn ℝ ∞ V S := by
    simpa [V, S] using hu'.contDiffOn
  have hW : ContDiffOn ℝ ∞ W S := by
    exact hU.sub hV
  have hperiod : ∀ (t : ℝ) (i : Fin 3) (y : Fin 3 → ℝ),
      W (t, Function.update y i (y i + 1)) = W (t, y) := by
    intro t i y
    simp only [W, U, V, torusProj_update_add_period]
  have htorus : Continuous torusProj :=
    continuous_pi fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)
  have hmap : Continuous (fun p : ℝ × (Fin 3 → ℝ) => (p.1, torusProj p.2)) :=
    continuous_fst.prodMk (htorus.comp continuous_snd)
  have hUc : ContinuousOn U (Ici 0 ×ˢ Set.univ) := by
    change ContinuousOn (fun p : ℝ × (Fin 3 → ℝ) => u p.1 (torusProj p.2))
      (Ici 0 ×ˢ Set.univ)
    exact hu.continuousOn.comp hmap.continuousOn
      (fun p hp => ⟨hp.1, mem_univ p.2⟩)
  have hVc : ContinuousOn V (Ici 0 ×ˢ Set.univ) := by
    change ContinuousOn (fun p : ℝ × (Fin 3 → ℝ) => u' p.1 (torusProj p.2))
      (Ici 0 ×ˢ Set.univ)
    exact hu'.continuousOn.comp hmap.continuousOn
      (fun p hp => ⟨hp.1, mem_univ p.2⟩)
  have hWc : ContinuousOn W (Ici 0 ×ˢ Set.univ) := by
    exact hUc.sub hVc
  have hWzero : ∀ y : Fin 3 → ℝ, W (0, y) = 0 := by
    intro y
    simp [W, U, V, hu.initial, hu'.initial]
  have hUspace {t : ℝ} (ht : 0 < t) :
      ContDiff ℝ 2 (fun y : Fin 3 → ℝ => U (t, y)) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    have hAt : ContDiffAt ℝ ∞ U (t, y) :=
      (hU (t, y) ⟨ht, mem_univ y⟩).contDiffAt
        ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht, mem_univ y⟩)
    exact (hAt.comp y (contDiff_const.prodMk contDiff_id).contDiffAt).of_le
      (by norm_num)
  have hVspace {t : ℝ} (ht : 0 < t) :
      ContDiff ℝ 2 (fun y : Fin 3 → ℝ => V (t, y)) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    have hAt : ContDiffAt ℝ ∞ V (t, y) :=
      (hV (t, y) ⟨ht, mem_univ y⟩).contDiffAt
        ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht, mem_univ y⟩)
    exact (hAt.comp y (contDiff_const.prodMk contDiff_id).contDiffAt).of_le
      (by norm_num)
  have hsecond {t : ℝ} (ht : 0 < t) (i : Fin 3) (y : Fin 3 → ℝ) :
      secondPartial (fun y => W (t, y)) i y =
        deriv (deriv (fun r => U (t, Function.update y i r))) (y i) -
          deriv (deriv (fun r => V (t, Function.update y i r))) (y i) := by
    have hUs : ContDiff ℝ 2 (fun r => U (t, Function.update y i r)) :=
      (hUspace ht).comp (contDiff_update 2 y i)
    have hVs : ContDiff ℝ 2 (fun r => V (t, Function.update y i r)) :=
      (hVspace ht).comp (contDiff_update 2 y i)
    have hWsp : ContDiff ℝ 2 (fun y => W (t, y)) :=
      (hUspace ht).sub (hVspace ht)
    have hWs : ContDiff ℝ 2 (fun r => W (t, Function.update y i r)) := by
      simpa [W] using hUs.sub hVs
    rw [secondPartial_eq_deriv hWsp i y]
    have hUd : ContDiff ℝ 1 (fun r => deriv (fun s => U (t, Function.update y i s)) r) := by
      unfold deriv
      exact (hUs.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    have hVd : ContDiff ℝ 1 (fun r => deriv (fun s => V (t, Function.update y i s)) r) := by
      unfold deriv
      exact (hVs.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    have hinner : (fun r => deriv (fun s => W (t, Function.update y i s)) r) =
        (fun r => deriv (fun s => U (t, Function.update y i s)) r -
          deriv (fun s => V (t, Function.update y i s)) r) := by
      funext r
      rw [show (fun s => W (t, Function.update y i s)) =
          (fun s => U (t, Function.update y i s) - V (t, Function.update y i s)) by
            funext s; rfl]
      exact deriv_fun_sub (hUs.differentiable (by norm_num) _)
        (hVs.differentiable (by norm_num) _)
    change deriv (fun r => deriv (fun s => W (t, Function.update y i s)) r) (y i) = _
    calc
      deriv (fun r => deriv (fun s => W (t, Function.update y i s)) r) (y i) =
          deriv (fun r => deriv (fun s => U (t, Function.update y i s)) r -
            deriv (fun s => V (t, Function.update y i s)) r) (y i) := by rw [hinner]
      _ = deriv (deriv (fun r => U (t, Function.update y i r))) (y i) -
          deriv (deriv (fun r => V (t, Function.update y i r))) (y i) := by
        exact deriv_fun_sub (hUd.differentiable (by norm_num) _)
          (hVd.differentiable (by norm_num) _)
  have htimeW {t : ℝ} (ht : 0 < t) (y : Fin 3 → ℝ) :
      HasDerivAt (fun s => W (s, y)) (timeDeriv W (t, y)) t := by
    have hAt : ContDiffAt ℝ ∞ W (t, y) :=
      (hW (t, y) ⟨ht, mem_univ y⟩).contDiffAt
        ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht, mem_univ y⟩)
    have hpath : HasDerivAt (fun s : ℝ => (s, y)) (1, 0) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
    simpa [timeDeriv, Function.comp_def] using
      (hAt.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
        hpath
  have hEq {t : ℝ} (ht : 0 < t) (y : Fin 3 → ℝ) :
      deriv (fun s => W (s, y)) t =
        (∑ i, secondPartial (fun y => W (t, y)) i y) -
          (U (t, y) ^ 3 - V (t, y) ^ 3) + c * W (t, y) := by
    have hAtU : ContDiffAt ℝ ∞ U (t, y) :=
      (hU (t, y) ⟨ht, mem_univ y⟩).contDiffAt
        ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht, mem_univ y⟩)
    have hAtV : ContDiffAt ℝ ∞ V (t, y) :=
      (hV (t, y) ⟨ht, mem_univ y⟩).contDiffAt
        ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht, mem_univ y⟩)
    have hpathU : ContDiffAt ℝ ∞ (fun s => U (s, y)) t :=
      hAtU.comp t (contDiff_id.prodMk contDiff_const).contDiffAt
    have hpathV : ContDiffAt ℝ ∞ (fun s => V (s, y)) t :=
      hAtV.comp t (contDiff_id.prodMk contDiff_const).contDiffAt
    have heqU := hu.equation t ht y
    have heqV := hu'.equation t ht y
    change deriv (fun s => U (s, y)) t =
      (∑ i, deriv (deriv (fun r => U (t, Function.update y i r))) (y i)) -
        U (t, y) ^ 3 + c * U (t, y) + f (t, torusProj y) at heqU
    change deriv (fun s => V (s, y)) t =
      (∑ i, deriv (deriv (fun r => V (t, Function.update y i r))) (y i)) -
        V (t, y) ^ 3 + c * V (t, y) + f (t, torusProj y) at heqV
    calc
      deriv (fun s => W (s, y)) t =
          deriv (fun s => U (s, y)) t - deriv (fun s => V (s, y)) t := by
        exact deriv_fun_sub (hpathU.differentiableAt (by norm_num))
          (hpathV.differentiableAt (by norm_num))
      _ = ((∑ i, deriv (deriv (fun r => U (t, Function.update y i r))) (y i)) -
          U (t, y) ^ 3 + c * U (t, y) + f (t, torusProj y)) -
          ((∑ i, deriv (deriv (fun r => V (t, Function.update y i r))) (y i)) -
          V (t, y) ^ 3 + c * V (t, y) + f (t, torusProj y)) := by rw [heqU, heqV]
      _ = (∑ i, secondPartial (fun y => W (t, y)) i y) -
          (U (t, y) ^ 3 - V (t, y) ^ 3) + c * W (t, y) := by
        simp_rw [hsecond ht]
        simp only [Finset.sum_sub_distrib]
        simp [W]
        ring
  have henergy_nonneg : ∀ t : ℝ, 0 ≤ energy W t := by
    intro t
    unfold energy
    exact integral_nonneg (fun y => sq_nonneg (W (t, y)))
  have hEderiv_le {t : ℝ} (ht : 0 < t) :
      (∫ y, 2 * W (t, y) * timeDeriv W (t, y) ∂cubeMeasure) ≤
        2 * c * energy W t := by
    have hWsp : ContDiff ℝ 2 (fun y => W (t, y)) :=
      (hUspace ht).sub (hVspace ht)
    have hsumCont : Continuous (fun y => ∑ i, secondPartial (fun y => W (t, y)) i y) :=
      continuous_finsetSum Finset.univ (fun i hi => continuous_secondPartial hWsp i)
    have hspCont : Continuous
        (fun y => 2 * W (t, y) * ∑ i, secondPartial (fun y => W (t, y)) i y) :=
      ((hWsp.continuous.const_mul 2).mul hsumCont)
    have hcubCont : Continuous
        (fun y => 2 * W (t, y) * (U (t, y) ^ 3 - V (t, y) ^ 3)) := by
      exact (hWsp.continuous.const_mul 2).mul
        ((hUspace ht).continuous.pow 3 |>.sub ((hVspace ht).continuous.pow 3))
    have hsqCont : Continuous (fun y => 2 * c * W (t, y) ^ 2) := by
      exact continuous_const.mul (hWsp.continuous.pow 2)
    have hsp_int : Integrable
        (fun y => 2 * W (t, y) * ∑ i, secondPartial (fun y => W (t, y)) i y) cubeMeasure :=
      integrable_cube_of_continuous hspCont
    have hcub_int : Integrable
        (fun y => 2 * W (t, y) * (U (t, y) ^ 3 - V (t, y) ^ 3)) cubeMeasure :=
      integrable_cube_of_continuous hcubCont
    have hsq_int : Integrable (fun y => 2 * c * W (t, y) ^ 2) cubeMeasure :=
      integrable_cube_of_continuous hsqCont
    have hrewrite :
        (∫ y, 2 * W (t, y) * timeDeriv W (t, y) ∂cubeMeasure) =
          ∫ y, 2 * W (t, y) *
            ((∑ i, secondPartial (fun y => W (t, y)) i y) -
              (U (t, y) ^ 3 - V (t, y) ^ 3) + c * W (t, y)) ∂cubeMeasure := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      have htime := (htimeW ht y).deriv
      rw [show timeDeriv W (t, y) =
          (∑ i, secondPartial (fun y => W (t, y)) i y) -
            (U (t, y) ^ 3 - V (t, y) ^ 3) + c * W (t, y) by
          calc
            timeDeriv W (t, y) = deriv (fun s => W (s, y)) t := htime.symm
            _ = _ := hEq ht y]
    have hsplit :
        (∫ y, 2 * W (t, y) *
            ((∑ i, secondPartial (fun y => W (t, y)) i y) -
              (U (t, y) ^ 3 - V (t, y) ^ 3) + c * W (t, y)) ∂cubeMeasure) =
          (∫ y, 2 * W (t, y) * ∑ i, secondPartial (fun y => W (t, y)) i y
            ∂cubeMeasure) -
            (∫ y, 2 * W (t, y) * (U (t, y) ^ 3 - V (t, y) ^ 3)
              ∂cubeMeasure) +
            ∫ y, 2 * c * W (t, y) ^ 2 ∂cubeMeasure := by
      have hfun : (fun y => 2 * W (t, y) *
          ((∑ i, secondPartial (fun y => W (t, y)) i y) -
            (U (t, y) ^ 3 - V (t, y) ^ 3) + c * W (t, y))) =
          (fun y => 2 * W (t, y) * ∑ i, secondPartial (fun y => W (t, y)) i y -
            2 * W (t, y) * (U (t, y) ^ 3 - V (t, y) ^ 3) +
            2 * c * W (t, y) ^ 2) := by
        funext y
        ring
      rw [hfun]
      calc
        _ = (∫ y, (2 * W (t, y) * ∑ i,
              secondPartial (fun y => W (t, y)) i y -
              2 * W (t, y) * (U (t, y) ^ 3 - V (t, y) ^ 3)) ∂cubeMeasure) +
              ∫ y, 2 * c * W (t, y) ^ 2 ∂cubeMeasure := by
          simpa only [Pi.add_apply, Pi.sub_apply] using
            (MeasureTheory.integral_add (hsp_int.sub hcub_int) hsq_int)
        _ = _ := by
          rw [MeasureTheory.integral_sub hsp_int hcub_int]
    have hprod_int (i : Fin 3) : Integrable
        (fun y => W (t, y) * secondPartial (fun y => W (t, y)) i y) cubeMeasure :=
      integrable_cube_of_continuous
        (hWsp.continuous.mul (continuous_secondPartial hWsp i))
    have hsp_eq :
        (∫ y, 2 * W (t, y) * ∑ i, secondPartial (fun y => W (t, y)) i y
            ∂cubeMeasure) =
          -2 * ∑ i, ∫ y, (partialDeriv (fun y => W (t, y)) i y) ^ 2 ∂cubeMeasure := by
      have hsum : (fun y => W (t, y) * ∑ i, secondPartial (fun y => W (t, y)) i y) =
          (fun y => ∑ i, W (t, y) * secondPartial (fun y => W (t, y)) i y) := by
        funext y
        rw [Finset.mul_sum]
      rw [show (fun y => 2 * W (t, y) * ∑ i,
          secondPartial (fun y => W (t, y)) i y) =
          (fun y => 2 * (W (t, y) * ∑ i,
            secondPartial (fun y => W (t, y)) i y)) by
            funext y; ring]
      rw [MeasureTheory.integral_const_mul, hsum,
        MeasureTheory.integral_finsetSum Finset.univ (fun i hi => hprod_int i)]
      simp_rw [cube_integral_mul_secondPartial hWsp (fun i y => hperiod t i y)]
      simp_rw [Finset.sum_neg_distrib]
      ring_nf
    have hsp_nonpos :
        (∫ y, 2 * W (t, y) * ∑ i, secondPartial (fun y => W (t, y)) i y
            ∂cubeMeasure) ≤ 0 := by
      rw [hsp_eq]
      have hnonneg (i : Fin 3) : 0 ≤
          ∫ y, (partialDeriv (fun y => W (t, y)) i y) ^ 2 ∂cubeMeasure := by
        exact integral_nonneg (fun y => sq_nonneg _)
      calc
        -2 * ∑ i, ∫ y, (partialDeriv (fun y => W (t, y)) i y) ^ 2 ∂cubeMeasure =
            -(2 * ∑ i, ∫ y, (partialDeriv (fun y => W (t, y)) i y) ^ 2 ∂cubeMeasure) := by ring
        _ ≤ 0 := neg_nonpos.mpr
          (mul_nonneg (by norm_num) (Finset.sum_nonneg fun i hi => hnonneg i))
    have hcub_nonneg : 0 ≤
        ∫ y, 2 * W (t, y) * (U (t, y) ^ 3 - V (t, y) ^ 3) ∂cubeMeasure := by
      exact integral_nonneg (fun y => by
        calc
          0 ≤ 2 * ((U (t, y) ^ 3 - V (t, y) ^ 3) *
              (U (t, y) - V (t, y))) :=
            mul_nonneg (by norm_num) (cubic_difference_mul_nonneg _ _)
          _ = 2 * W (t, y) * (U (t, y) ^ 3 - V (t, y) ^ 3) := by simp [W]; ring)
    rw [hrewrite, hsplit]
    rw [show (∫ y, 2 * c * W (t, y) ^ 2 ∂cubeMeasure) =
        2 * c * energy W t by
          change (∫ y, 2 * c * W (t, y) ^ 2 ∂cubeMeasure) =
            2 * c * (∫ y, W (t, y) ^ 2 ∂cubeMeasure)
          rw [MeasureTheory.integral_const_mul]]
    linarith
  have hEzero : energy W 0 = 0 := by
    unfold energy
    have hz : (fun y => W (0, y) ^ 2) = (fun _ => 0) := by
      funext y
      rw [hWzero y]
      simp
    rw [hz, MeasureTheory.integral_zero]
  let K : ℝ := max (2 * c) 0
  have hG {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
      ∀ x ∈ Icc a b, energy W x ≤ gronwallBound (energy W a) K 0 (x - a) := by
    apply le_gronwallBound_of_liminf_deriv_right_le
    · apply continuousOn_energy
      exact hWc.mono (by
        intro p hp
        exact ⟨le_trans (le_of_lt ha) hp.1.1, mem_univ p.2⟩)
    · intro x hx r hr
      have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
      have hdx : HasDerivWithinAt (energy W)
          (∫ y, 2 * W (x, y) * timeDeriv W (x, y) ∂cubeMeasure) (Ici x) x :=
        (hasDerivAt_energy hW hxpos).hasDerivWithinAt
      exact hdx.liminf_right_slope_le hr
    · exact le_rfl
    · intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
      have hder := hEderiv_le hxpos
      calc
        (∫ y, 2 * W (x, y) * timeDeriv W (x, y) ∂cubeMeasure) ≤
            2 * c * energy W x := hder
        _ ≤ K * energy W x + 0 := by
          calc
            2 * c * energy W x ≤ K * energy W x :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (henergy_nonneg x)
            _ ≤ K * energy W x + 0 := by simp
  intro T hT
  by_cases hT0 : T = 0
  · subst T
    apply ContinuousMap.ext
    intro x
    simp [hu.initial, hu'.initial]
  have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
  have hEcont0 : ContinuousWithinAt (energy W) (Icc 0 T) 0 := by
    have hcont : ContinuousOn (energy W) (Icc 0 T) := by
      apply continuousOn_energy
      exact hWc.mono (by
        intro p hp
        exact ⟨hp.1.1, mem_univ p.2⟩)
    exact hcont 0 ⟨le_rfl, hT⟩
  have henergy_T : energy W T = 0 := by
    have hE_nonneg_T : 0 ≤ energy W T := henergy_nonneg T
    apply le_antisymm
    · by_contra hnot
      have hETpos : 0 < energy W T := lt_of_not_ge hnot
      let A : ℝ := Real.exp (K * T)
      have hApos : 0 < A := by
        dsimp [A]
        exact Real.exp_pos _
      let ε : ℝ := energy W T / (2 * A)
      have hεpos : 0 < ε := by
        dsimp [ε]
        exact div_pos hETpos (mul_pos (by norm_num) hApos)
      have hmem : energy W ⁻¹' Iio ε ∈ 𝓝[Icc 0 T] 0 := by
        apply hEcont0
        apply isOpen_Iio.mem_nhds
        simpa [hEzero] using hεpos
      rcases Metric.mem_nhdsWithin_iff.1 hmem with ⟨r, hr, hball⟩
      let δ : ℝ := min (r / 2) (T / 2)
      have hδpos : 0 < δ := by
        dsimp [δ]
        exact lt_min (half_pos hr) (half_pos hTpos)
      have hδT : δ ≤ T := by
        dsimp [δ]
        exact le_trans (min_le_right _ _) (le_of_lt (half_lt_self hTpos))
      have hδball : δ ∈ ball (0 : ℝ) r := by
        rw [mem_ball, Real.dist_eq]
        rw [sub_zero, abs_of_pos hδpos]
        exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr)
      have hδε : energy W δ < ε := hball ⟨hδball, ⟨le_of_lt hδpos, hδT⟩⟩
      have hbound := hG hδpos hδT T ⟨hδT, le_rfl⟩
      rw [gronwallBound_ε0] at hbound
      have htime : K * (T - δ) ≤ K * T := by
        exact mul_le_mul_of_nonneg_left (sub_le_self T (le_of_lt hδpos))
          (le_max_right _ _)
      have hexp : Real.exp (K * (T - δ)) ≤ Real.exp (K * T) :=
        Real.exp_le_exp.mpr htime
      have hsmall : energy W T ≤ ε * A := by
        calc
          energy W T ≤ energy W δ * Real.exp (K * (T - δ)) := hbound
          _ ≤ ε * Real.exp (K * (T - δ)) :=
            mul_le_mul_of_nonneg_right (le_of_lt hδε) (le_of_lt (Real.exp_pos _))
          _ ≤ ε * A := by
            exact mul_le_mul_of_nonneg_left hexp (le_of_lt hεpos)
      have hhalf : ε * A = energy W T / 2 := by
        dsimp [ε, A]
        field_simp
      rw [hhalf] at hsmall
      linarith
    · exact hE_nonneg_T
  have hzero_ae : (fun y => W (T, y) ^ 2) =ᵐ[cubeMeasure] 0 := by
    apply (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg (W (T, y)))
      (integrable_cube_of_continuous
        (((hUspace hTpos).sub (hVspace hTpos)).continuous.pow 2))).mp
    exact henergy_T
  let D : Set (Fin 3 → ℝ) := Set.univ.pi (fun _ : Fin 3 => Ioc (0 : ℝ) 1)
  have hzero_on_D : ∀ y ∈ D, W (T, y) = 0 := by
    intro y hy
    have hsq : W (T, y) ^ 2 = 0 := by
      have hzero_ae' : (fun y => W (T, y) ^ 2) =ᵐ[volume.restrict D] 0 := by
        simpa [cubeMeasure_eq_restrict, D] using hzero_ae
      have hDc : D ⊆ closure (interior D) := by
        intro z hz
        rw [interior_pi_set Set.finite_univ, closure_pi_set]
        intro i hi
        exact (Ioc_subset_closure_interior 0 1) (hz i hi)
      have heq := MeasureTheory.Measure.eqOn_of_ae_eq hzero_ae'
        (((hUspace hTpos).sub (hVspace hTpos)).continuous.pow 2).continuousOn
        continuousOn_const hDc hy
      exact heq
    exact (sq_eq_zero_iff.mp hsq)
  apply ContinuousMap.ext
  intro x
  let y : Fin 3 → ℝ := fun i => (AddCircle.equivIoc (1 : ℝ) 0 (x i) : ℝ)
  have hy : y ∈ D := by
    intro i hi
    change (AddCircle.equivIoc (1 : ℝ) 0 (x i) : ℝ) ∈ Ioc 0 1
    simpa using (AddCircle.equivIoc (1 : ℝ) 0 (x i)).property
  have hproj : torusProj y = x := by
    funext i
    dsimp [torusProj, y]
    exact AddCircle.coe_equivIoc
  have hwy : W (T, y) = 0 := hzero_on_D y hy
  have hdiff : u T x - u' T x = 0 := by
    simpa [W, U, V, hproj] using hwy
  exact sub_eq_zero.mp hdiff

end RegularityStructures.Phi43

end
