import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSmoothCarrier

/-!
# Both calibrated rectangles enter one passive allocation

The source is restored on a common effective carrier before taking its
one centered difference.  The complete difference, with its original
normalizer and Fourier variable, is then expanded into the computed
nonempty passive allocations.  No energy or whole-polynomial identity
is supplied as an input; only the individual atom calibrations and
their actual effective supports enter the proof.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

namespace CanonicalLiteralCenteredPassive

open CanonicalLiteralPassiveDeletion CanonicalLiteralProfileCarrier
open CanonicalLiteralCalibratedDeletion

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ω ψ : HeckeCharacter K} {k : ℕ}

theorem joint_normalized_difference {I : Type*} (columns : Finset I)
    (normalizer : ℂ) (a b : I → ℂ) (x : I → V) (ξ : V) :
    jointFourierColumn columns (fun i => normalizer * (a i - b i)) x ξ =
      normalizer * (jointFourierColumn columns a x ξ -
        jointFourierColumn columns b x ξ) := by
  simp only [jointFourierColumn, mul_assoc, sub_mul, mul_sub,
    Finset.mul_sum, Finset.sum_sub_distrib]

/-- The two effective-support transports are joined before the
Moebius sum.  Hence there is one label and one actual allocation for
both original rectangles, including the absent comparison rectangle. -/
theorem calibrated_centered_allocations
    (old T : FixedChildCharacters K k) (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (d : Bool → MomentData K ω ψ) (count : ∀ r, (d r).geometry.slotCount = k)
    (length : Fin k → ℝ)
    (hlength : ∀ r i, ((d r).geometry.slots i).length = length (Fin.cast (count r) i))
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (g h' : A.R)
    (Dold : ∀ r, old.Calibration (σ := σ) (d r) (count r) u g h')
    (Dpaid : ∀ r, (T.deleteMask M).Calibration (σ := σ) (d r) (count r) u g h')
    (N₁ N₂ : Bool → ℝ) (Z t : ℝ)
    (S₁ S₂ U₁ U₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K))
    (S U : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (hS₁ : ∀ r, EffectivePlainSupport (d r) (d r).plainTest₁ u (N₁ r) t S₁)
    (hS₂ : ∀ r, EffectivePlainSupport (d r) (d r).plainTest₂ u (N₂ r) t S₂)
    (hS : ∀ r i, EffectivePrimeSupport (d r) i u Z t (S (Fin.cast (count r) i)))
    (hU₁ : ∀ r, EffectivePlainSupport (d r) (d r).plainTest₁ u (N₁ r) t U₁)
    (hU₂ : ∀ r, EffectivePlainSupport (d r) (d r).plainTest₂ u (N₂ r) t U₂)
    (hU : ∀ r i, EffectivePrimeSupport (d r) i u Z t (U (Fin.cast (count r) i)))
    (w₁ w₂ : Bool → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal K → V)
    (x : Fin k → HeightOneSpectrum (𝓞 K) → V) (normalizer : ℂ) (ξ : V)
    (hW₁ : ∀ r I, w₁ r I * jointPhase ξ (x₁ I) =
      (d r).plainTest₁.profile u t (idealNorm K I / N₁ r))
    (hW₂ : ∀ r I, w₂ r I * jointPhase ξ (x₂ I) =
      (d r).plainTest₂.profile u t (idealNorm K I / N₂ r))
    (hW : ∀ r i p, w (Fin.cast (count r) i) p *
        jointPhase ξ (x (Fin.cast (count r) i) p) =
      ((d r).geometry.slots i).profile t
        ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ ((d r).geometry.slots i).length)) :
    jointFourierColumn (childCartesianColumns S₁ S₂ S)
      (fun i => normalizer *
        (old.coefficient (σ := σ) g h' (N₁ false) (N₂ false) Z length
            (w₁ false) (w₂ false) w i -
          old.coefficient (σ := σ) g h' (N₁ true) (N₂ true) Z length
            (w₁ true) (w₂ true) w i))
      (childCartesianLocation x₁ x₂ x) ξ =
      ∑ a ∈ (liveLabels M.val (idealCarrier U₁) (idealCarrier U₂) U
        id id HeightOneSpectrum.asIdeal).attach,
        sign a.val * jointFourierColumn
          (allocation M.val (idealCarrier U₁) (idealCarrier U₂) U
            (idealCarrier_nonzero U₁) (idealCarrier_nonzero U₂) a).columns
          (fun i => normalizer *
            (rawSourceCoefficient (σ := σ) T g h' (N₁ false) (N₂ false) Z length
                (w₁ false) (w₂ false) w i -
              rawSourceCoefficient (σ := σ) T g h' (N₁ true) (N₂ true) Z length
                (w₁ true) (w₂ true) w i))
          (rawSourceLocation x₁ x₂ x) ξ := by
  have hcarrier (r : Bool) :
      jointFourierColumn (childCartesianColumns S₁ S₂ S)
        (old.coefficient (σ := σ) g h' (N₁ r) (N₂ r) Z length (w₁ r) (w₂ r) w)
        (childCartesianLocation x₁ x₂ x) ξ =
      jointFourierColumn (childCartesianColumns (idealCarrier U₁) (idealCarrier U₂) U)
        (rawSourceCoefficient (σ := σ) (T.deleteMask M) g h'
          (N₁ r) (N₂ r) Z length (w₁ r) (w₂ r) w)
        (rawSourceLocation x₁ x₂ x) ξ := by
    rw [raw_joint_idealCarrier]
    have hsource := fixed_child_polynomial_from_effective_terms old (d r) (count r)
      length (hlength r) u g h' (Dold r) (N₁ r) (N₂ r) Z t S₁ S₂ S
      (hS₁ r) (hS₂ r) (hS r) (w₁ r) (w₂ r) w x₁ x₂ x ξ
      (fun I _ => hW₁ r I) (fun I _ => hW₂ r I) (fun i p _ => hW r i p)
    have hfull := fixed_child_polynomial_from_effective_terms (T.deleteMask M) (d r)
      (count r) length (hlength r) u g h' (Dpaid r) (N₁ r) (N₂ r) Z t U₁ U₂ U
      (hU₁ r) (hU₂ r) (hU r) (w₁ r) (w₂ r) w x₁ x₂ x ξ
      (fun I _ => hW₁ r I) (fun I _ => hW₂ r I) (fun i p _ => hW r i p)
    exact hsource.trans hfull.symm
  rw [joint_normalized_difference, hcarrier false, hcarrier true,
    ← joint_normalized_difference]
  exact raw_centered_joint_allocations T M g h'
    (N₁ false) (N₂ false) (N₁ true) (N₂ true) Z length
    (idealCarrier U₁) (idealCarrier U₂) U (idealCarrier_nonzero U₁)
    (idealCarrier_nonzero U₂) (w₁ false) (w₂ false) (w₁ true) (w₂ true) w
    x₁ x₂ x normalizer ξ

end CanonicalLiteralCenteredPassive
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralCenteredPassive.joint_normalized_difference
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralCenteredPassive.calibrated_centered_allocations
