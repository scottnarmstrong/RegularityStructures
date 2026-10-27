module

public import GlobalPhi43.Flow.ClassicalTranslation
public import GlobalPhi43.Flow.ClassicalComparison
public import Mathlib.Topology.CompactOpen

/-! Differential inputs of the independent-data classical stability estimate. -/

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43
open scoped ContDiff

namespace GlobalPhi43.Flow

theorem second_deriv_sub {u v : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (hv : ContDiff ℝ 2 v) (x : ℝ) :
    deriv (deriv (fun r => u r - v r)) x = deriv (deriv u) x - deriv (deriv v) x := by
  have hu' : ContDiff ℝ 1 (deriv u) := by
    unfold deriv
    exact (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hv' : ContDiff ℝ 1 (deriv v) := by
    unfold deriv
    exact (hv.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have he : deriv (fun r => u r - v r) = fun r => deriv u r - deriv v r := by
    funext r
    exact deriv_fun_sub (hu.differentiable (by norm_num) r) (hv.differentiable (by norm_num) r)
  rw [he]
  exact deriv_fun_sub (hu'.differentiable (by norm_num) x) (hv'.differentiable (by norm_num) x)

theorem classical_time_hasDerivAt {b : ℝ} {f : SpaceTime → ℝ}
    {x : C(Torus3, ℝ)} {u : ℝ → C(Torus3, ℝ)}
    (hu : IsClassicalSolution b f x u) {t : ℝ} (ht : 0 < t) (z : Torus3) :
    HasDerivAt (fun r => u r z) (deriv (fun r => u r z) t) t := by
  have hc : ContDiffAt ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => u p.1 (torusProj p.2))
      (t, torusRep z) := (hu.contDiffOn (t, torusRep z) ⟨ht, mem_univ _⟩).contDiffAt
        ((isOpen_Ioi.prod isOpen_univ).mem_nhds
          (show (t, torusRep z) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (Fin 3 → ℝ)) from ⟨ht, mem_univ _⟩))
  have hh := hc.comp t (contDiff_id.prodMk contDiff_const).contDiffAt
  have hd := (hh.differentiableAt (by norm_num)).hasDerivAt
  simpa only [Function.comp_def, id_eq, PDE.torusProj_torusRep] using hd

/-- The actual difference satisfies the comparison inequality at its positive
points, with the sharper coefficient max(b,0). Data are independent. -/
theorem classical_difference_subsolution {b : ℝ} {f g : SpaceTime → ℝ}
    {x y : C(Torus3, ℝ)} {u v : ℝ → C(Torus3, ℝ)}
    (hu : IsClassicalSolution b f x u) (hv : IsClassicalSolution b g y v)
    {t : ℝ} (ht : 0 < t) (z : Fin 3 → ℝ)
    (hp : 0 ≤ u t (torusProj z) - v t (torusProj z)) :
    deriv (fun r => u r (torusProj z) - v r (torusProj z)) t ≤
      (∑ i : Fin 3, deriv (deriv (fun a =>
        u t (torusProj (Function.update z i a)) - v t (torusProj (Function.update z i a)))) (z i)) +
        max b 0 * (u t (torusProj z) - v t (torusProj z)) +
          |f (t, torusProj z) - g (t, torusProj z)| := by
  have huS : ContDiff ℝ 2 (fun z => u t (torusProj z)) :=
    (isSmoothOnTorus_of_classical hu ht).of_le (by norm_num)
  have hvS : ContDiff ℝ 2 (fun z => v t (torusProj z)) :=
    (isSmoothOnTorus_of_classical hv ht).of_le (by norm_num)
  have hsecond (i : Fin 3) := second_deriv_sub
    (huS.comp (contDiff_update 2 z i)) (hvS.comp (contDiff_update 2 z i)) (z i)
  rw [deriv_fun_sub (classical_time_hasDerivAt hu ht _).differentiableAt
    (classical_time_hasDerivAt hv ht _).differentiableAt,
    hu.equation t ht z, hv.equation t ht z]
  simp only [Function.comp_def] at hsecond
  simp_rw [hsecond]
  rw [Finset.sum_sub_distrib]
  have hcube' : 0 ≤ u t (torusProj z) ^ 3 - v t (torusProj z) ^ 3 := by
    exact sub_nonneg.mpr ((Odd.strictMono_pow (by decide : Odd (3 : ℕ))).monotone (sub_nonneg.mp hp))
  have hb := mul_le_mul_of_nonneg_right (le_max_left b 0) hp
  have hf := le_abs_self (f (t, torusProj z) - g (t, torusProj z))
  linarith only [hcube', hb, hf]

/-- The smooth forcing as a continuous curve in the spatial supremum norm. -/
@[expose] def forcingCurve (f : SpaceTime → ℝ) (hf : IsSmoothOnSpaceTime f) :
    C(ℝ, C(Torus3, ℝ)) :=
  ContinuousMap.curry ⟨f, continuous_of_isSmoothOnSpaceTime hf⟩

theorem forcingNorm_continuous {f g : SpaceTime → ℝ}
    (hf : IsSmoothOnSpaceTime f) (hg : IsSmoothOnSpaceTime g) :
    Continuous (fun t => ‖forcingCurve f hf t - forcingCurve g hg t‖) :=
  ((forcingCurve f hf).continuous.sub (forcingCurve g hg).continuous).norm

end GlobalPhi43.Flow
