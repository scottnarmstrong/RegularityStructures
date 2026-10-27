module

public import GlobalPhi43.Attachment.FlowCovariance
public import GlobalPhi43.Attachment.TranslatePredicate
public import GlobalPhi43.Attachment.NoiseGrowthTranslate
public import GlobalPhi43.Attachment.MassiveTranslation

/-! Joint transport of the deterministic restart inputs. -/

public section

namespace GlobalPhi43.Attachment
open RegularityStructures RegularityStructures.Phi43

/-- The translated lift satisfies the same model, noise-growth and massive-potential premises.
All three clauses refer to the same translated forcing, model and potential. -/
theorem restart_inputs_time_translate {N : ℕ} {κ : Kappa} {f : SpaceTime → ℝ}
    {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    {ψ : ℝ → C(Torus3, ℝ)}
    (hZ : Statements.IsModeratePhi43ModelOf N κ f C Z)
    (hg : Statements.HasPhi43NoiseGrowth f) (hψ : IsMassivePotential f ψ) (s : ℝ) :
    Statements.IsModeratePhi43ModelOf N κ (fun z => f (z.1 + s, z.2)) C
        (Z.translate (s, 0)) ∧
      Statements.HasPhi43NoiseGrowth (fun z => f (z.1 + s, z.2)) ∧
      IsMassivePotential (fun z => f (z.1 + s, z.2)) (fun t => ψ (s + t)) := by
  refine ⟨moderatePhi43Model_translate hZ s, noiseGrowth_time_translate hg s, ?_⟩
  simpa only [add_comm s] using massivePotential_time_translate hψ s

end GlobalPhi43.Attachment
