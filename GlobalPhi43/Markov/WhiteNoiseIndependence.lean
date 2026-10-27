module

public import RegularityStructures.Probability.WhiteNoise
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

public noncomputable section

open MeasureTheory ProbabilityTheory Set
open RegularityStructures

namespace GlobalPhi43.Markov

/-- Every indexed square-integrable test family of white noise is a Gaussian process. -/
theorem whiteNoise_isGaussianProcess {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (h : I → SpaceTime → ℝ) (hh : ∀ i, MemLp (h i) 2) :
    IsGaussianProcess (fun i => W (h i)) P := by
  classical
  constructor
  intro S
  let e := Fintype.equivFin S
  let v : Fin (Fintype.card S) → SpaceTime → ℝ := fun j => h (e.symm j).val
  have hv := hW.2 (Fintype.card S) v (fun j => hh (e.symm j).val)
  have hg : HasGaussianLaw (fun ω j => W (v j) ω) P := ⟨hv.1, hv.2.1⟩
  let L : (Fin (Fintype.card S) → ℝ) →L[ℝ] (S → ℝ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (e i)
  have he := hg.map_fun L
  convert he using 1
  funext ω i
  simp [L, v]

/-- White noise evaluated on two orthogonal test families gives independent processes. -/
theorem whiteNoise_indep_processes {Ω I J : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (h : I → SpaceTime → ℝ) (g : J → SpaceTime → ℝ)
    (hh : ∀ i, MemLp (h i) 2) (hg : ∀ j, MemLp (g j) 2)
    (horth : ∀ i j, (∫ z, h i z * g j z) = 0) :
    IndepFun (fun ω i => W (h i) ω) (fun ω j => W (g j) ω) P := by
  have heq : (fun i => W (Sum.elim h g i)) = Sum.elim (fun i => W (h i)) (fun j => W (g j)) := by
    funext i
    cases i <;> rfl
  have hp : IsGaussianProcess (Sum.elim (fun i => W (h i)) (fun j => W (g j))) P := by
    rw [← heq]
    exact whiteNoise_isGaussianProcess P hW (Sum.elim h g) (fun i => by cases i <;> simp_all)
  apply hp.indepFun_of_covariance_eq_zero
    (fun i => (hW.1 _ (hh i)).aemeasurable) (fun j => (hW.1 _ (hg j)).aemeasurable)
  intro i j
  let v : Fin 2 → SpaceTime → ℝ := fun k => if k = 0 then h i else g j
  have hv : ∀ k, MemLp (v k) 2 := by
    intro k
    fin_cases k <;> simp [v, hh, hg]
  have hz := hW.2 2 v hv
  have hmeanH : (∫ ω, W (h i) ω ∂P) = 0 := by simpa [v] using hz.2.2.1 0
  have hmeanG : (∫ ω, W (g j) ω ∂P) = 0 := by simpa [v] using hz.2.2.1 1
  have hprod : (∫ ω, W (h i) ω * W (g j) ω ∂P) = 0 := by
    simpa [v, horth i j] using hz.2.2.2 0 1
  simp only [covariance, hmeanH, hmeanG, sub_zero]
  exact hprod

end GlobalPhi43.Markov
