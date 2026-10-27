module

public import RegularityStructures.Analysis.Semigroup.PairingGrowth.Main
public import RegularityStructures.Analysis.Kernel.GeneratorIdentity
public import RegularityStructures.Analysis.Kernel.GeneratorProps
public import RegularityStructures.Abstract.Model

@[expose] public section

namespace GlobalPhi43.Attachment

open MeasureTheory Filter
open scoped ContDiff Topology
open RegularityStructures

/-- `L_Q φ` vanishes wherever `φ` vanishes on a neighbourhood. -/
theorem parabolicGenerator_eq_zero_of_eventuallyEq {φ : ParabolicSpace → ℝ} {y : ParabolicSpace}
    (h : φ =ᶠ[𝓝 y] 0) : parabolicGenerator φ y = 0 := by
  have h2 := (h.iteratedFDeriv ℝ 2).eq_of_nhds
  have h4 := (h.iteratedFDeriv ℝ 4).eq_of_nhds
  simp only [parabolicGenerator, h2, h4]
  simp

/-- **Support of `ψ = L_Q φ`.** If a smooth compactly supported `φ` is
supported in the `scaleDist`-ball of radius `lam` about `x₀`, so is `L_Q φ`. -/
theorem isSupported_parabolicGenerator {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) {x₀ : ParabolicSpace} {lam : ℝ}
    (hs : parabolicSemigroup.IsSupported φ x₀ lam) :
    parabolicSemigroup.IsSupported (parabolicGenerator φ) x₀ lam where
  meas := (continuous_parabolicGenerator hφ).measurable
  integrable := (continuous_parabolicGenerator hφ).integrable_of_hasCompactSupport
    (hasCompactSupport_parabolicGenerator hφ hc)
  supp y hy := by
    apply parabolicGenerator_eq_zero_of_eventuallyEq
    have ho : IsOpen {w : ParabolicSpace | lam < parabolicSemigroup.scaleDist w x₀} := by
      simp only [parabolicSemigroup]
      exact isOpen_lt continuous_const (continuous_parabolicNorm.comp (continuous_id.sub continuous_const))
    filter_upwards [ho.mem_nhds hy] with w hw
    exact hs.supp w hw

/-- **Small-scale pairing bound** at the parabolic semigroup.
For `Λ` with the local homogeneity bound in `LocalBall` (ball constant `C`, exponents `A`, all
`> −4`) and kernel integrability, and a smooth test `φ` supported in the ball
of radius `lam ≤ 1` with `∫|φ| ≤ B₀`, `∫|L_Q φ| ≤ B₁ lam^{−4}`, the pairing `lim_{s↓0} ∫ Λ_s φ`
exists and is at most `C · pairingConst A · (B₀ + B₁) · lam^γ`. -/
theorem pairing_le {Λ : ℝ → ParabolicSpace → ℝ} {x₀ : ParabolicSpace} {γ : ℝ} {A : Finset ℝ}
    {C lam : ℝ} (hΛ : parabolicSemigroup.LocalBall Λ x₀ γ A C lam) (hA : ∀ a ∈ A, -4 < a)
    {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) {B₀ B₁ : ℝ}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hs : parabolicSemigroup.IsSupported φ x₀ lam)
    (hφ1 : ∫ y, |φ y| ≤ B₀) (hψ1 : ∫ y, |parabolicGenerator φ y| ≤ B₁ * lam ^ (-4 : ℝ)) :
    ∃ L : ℝ, Tendsto (fun s => ∫ y, Λ s y * φ y) (𝓝[>] 0) (𝓝 L) ∧
      |L| ≤ C * parabolicSemigroup.pairingConst A * (B₀ + B₁) * lam ^ γ :=
  hΛ.exists_tendsto_abs_le parabolicSemigroup_isSymmetric parabolicSemigroup_isJointMeasurable
    hA hlam hlam1 hs (isSupported_parabolicGenerator hφ hc hs) hφ1 hψ1
    (parabolicSemigroup_isGeneratorPair hφ hc)

/-- The model data Λ_u = Q_u Π_x e_τ satisfy the membership and measurability
conditions of LocalBall. The local homogeneity bound and kernel integrability
provide its ball and kernel_int conditions with the required quantifiers. -/
theorem localBall_of_model {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
    (M : Model 𝒯 parabolicSemigroup) (x : ParabolicSpace) (i : ι) {γ : ℝ} {A : Finset ℝ}
    {C lam : ℝ} (hC : 0 ≤ C) (hle : ∀ a ∈ A, a ≤ γ)
    (hball : ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∀ y, parabolicSemigroup.scaleDist y x ≤ lam →
      |M.regPi x (Pi.single i 1) u y| ≤ C * ∑ a ∈ A, u ^ (a / parabolicSemigroup.order) * lam ^ (γ - a))
    (hint : ∀ s ∈ Set.Ioc (0 : ℝ) 1, ∀ h₀ : ℝ, ∃ W : ℝ, ∀ v ∈ Set.Ioc (0 : ℝ) h₀, ∀ y,
      parabolicSemigroup.scaleDist y x ≤ lam →
        ∫ z, |parabolicSemigroup.kernel v y z| * |M.regPi x (Pi.single i 1) s z| ≤ W) :
    parabolicSemigroup.LocalBall (fun u y => M.regPi x (Pi.single i 1) u y) x γ A C lam where
  mem := (M.pi x (Pi.single i 1)).2
  meas _ hu := M.measurable_pi x i hu
  nonneg := hC
  le := hle
  ball := hball
  kernel_int := hint

end GlobalPhi43.Attachment

end
