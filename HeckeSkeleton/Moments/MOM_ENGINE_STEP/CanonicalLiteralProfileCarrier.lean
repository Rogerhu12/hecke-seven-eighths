import HeckeSkeleton.Moments.MOM_ENGINE_STEP.EffectiveChildSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveDeletion

/-!
# Restoring the full smooth finite carrier before passive deletion

The original finite source already has exact single-occurrence
arithmetic and effective-support dictionaries. These suffice to replace
its filtered carrier by the full finite support of the same smooth
profiles. No allowed-row, cutoff, capacity or support-norm budget is
needed for this equality.

After this equality the finite passive-mask expansion acts on the
unfiltered profile carrier. Its divisor branches therefore contain the
actual quotient ideals, rather than disappearing merely because the
old maximal-valuation carrier already avoided every deleted prime.
The original Fourier variable and every individual profile are fixed.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

namespace CanonicalLiteralProfileCarrier

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ω ψ : HeckeCharacter K} {k : ℕ}

/-- Forget only the nonzero proof, retaining every original ideal in
the finite smooth-profile support. -/
def idealCarrier (S : Finset (HeckeGeneral.Analysis.NonzeroIdeal K)) :
    Finset (Ideal (𝓞 K)) := S.image Subtype.val

theorem idealCarrier_nonzero (S : Finset (HeckeGeneral.Analysis.NonzeroIdeal K)) :
    ∀ I ∈ idealCarrier S, I ≠ 0 := by
  intro I hI
  obtain ⟨J, _, rfl⟩ := Finset.mem_image.mp hI
  exact nonZeroDivisors.coe_ne_zero J

/-- The raw ideal presentation is exactly the nonzero-ideal source,
including its complete frequency and every original column location. -/
theorem raw_joint_idealCarrier
    (T : FixedChildCharacters K k) (g h' : A.R)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (S₁ S₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal K → V)
    (x : Fin k → HeightOneSpectrum (𝓞 K) → V) (ξ : V) :
    jointFourierColumn (childCartesianColumns (idealCarrier S₁) (idealCarrier S₂) S)
      (rawSourceCoefficient (σ := σ) T g h' N₁ N₂ Z length w₁ w₂ w)
      (rawSourceLocation x₁ x₂ x) ξ =
      jointFourierColumn (childCartesianColumns S₁ S₂ S)
        (T.coefficient (σ := σ) g h' N₁ N₂ Z length w₁ w₂ w)
        (childCartesianLocation x₁ x₂ x) ξ := by
  simp only [jointFourierColumn, childCartesianColumns, Finset.product_eq_sprod,
    Finset.sum_product, idealCarrier]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro I _
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro J _
      apply Finset.sum_congr rfl
      intro v _
      simp only [rawSourceCoefficient, rawSourceLocation, sourceMomentIdeal_coe]
    · intro I _ J _ h
      exact Subtype.ext h
  · intro I _ J _ h
    exact Subtype.ext h

/-- Changing only finite carriers follows from the actual calibrated
single atoms. The larger carriers need contain only their corresponding
smooth profile supports. -/
theorem calibrated_support_change
    (T : FixedChildCharacters K k) (d : MomentData K ω ψ)
    (count : d.geometry.slotCount = k) (length : Fin k → ℝ)
    (hlength : ∀ i, (d.geometry.slots i).length = length (Fin.cast count i))
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (g h' : A.R)
    (D : T.Calibration (σ := σ) d count u g h')
    (N₁ N₂ Z t : ℝ)
    (S₁ S₂ U₁ U₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K))
    (S U : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (hS₁ : EffectivePlainSupport d d.plainTest₁ u N₁ t S₁)
    (hS₂ : EffectivePlainSupport d d.plainTest₂ u N₂ t S₂)
    (hS : ∀ i, EffectivePrimeSupport d i u Z t (S (Fin.cast count i)))
    (hU₁ : d.plainTest₁.support u t N₁ ⊆ U₁)
    (hU₂ : d.plainTest₂.support u t N₂ ⊆ U₂)
    (hU : ∀ i, (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length) ⊆
      U (Fin.cast count i))
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal K → V)
    (x : Fin k → HeightOneSpectrum (𝓞 K) → V) (ξ : V)
    (hW₁ : ∀ I, w₁ I * jointPhase ξ (x₁ I) =
      d.plainTest₁.profile u t (idealNorm K I / N₁))
    (hW₂ : ∀ I, w₂ I * jointPhase ξ (x₂ I) =
      d.plainTest₂.profile u t (idealNorm K I / N₂))
    (hW : ∀ i p, w (Fin.cast count i) p * jointPhase ξ (x (Fin.cast count i) p) =
      (d.geometry.slots i).profile t
        ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length)) :
    jointFourierColumn (childCartesianColumns S₁ S₂ S)
      (T.coefficient (σ := σ) g h' N₁ N₂ Z length w₁ w₂ w)
      (childCartesianLocation x₁ x₂ x) ξ =
      jointFourierColumn (childCartesianColumns U₁ U₂ U)
        (T.coefficient (σ := σ) g h' N₁ N₂ Z length w₁ w₂ w)
        (childCartesianLocation x₁ x₂ x) ξ := by
  have hs := fixed_child_polynomial_from_effective_terms T d count length hlength
    u g h' D N₁ N₂ Z t S₁ S₂ S hS₁ hS₂ hS w₁ w₂ w x₁ x₂ x ξ
    (fun I _ => hW₁ I) (fun I _ => hW₂ I) (fun i p _ => hW i p)
  have hu := fixed_child_polynomial_from_effective_terms T d count length hlength
    u g h' D N₁ N₂ Z t U₁ U₂ U
    (effectivePlainSupport_of_profile d d.plainTest₁ u N₁ t U₁ hU₁)
    (effectivePlainSupport_of_profile d d.plainTest₂ u N₂ t U₂ hU₂)
    (fun i => effectivePrimeSupport_of_profile d i u Z t (U (Fin.cast count i)) (hU i))
    w₁ w₂ w x₁ x₂ x ξ
    (fun I _ => hW₁ I) (fun I _ => hW₂ I) (fun i p _ => hW i p)
  exact hs.trans hu.symm

/-- In particular the source may use its full finite profile supports
before the nonzero-ideal proofs are forgotten and divisors allocated. -/
theorem calibrated_full_profile_carrier
    (d : MomentData K ω ψ) (T : FixedChildCharacters K d.geometry.slotCount)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (g h' : A.R)
    (D : T.Calibration (σ := σ) d rfl u g h')
    (N₁ N₂ Z t : ℝ)
    (S₁ S₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K))
    (S : Fin d.geometry.slotCount → Finset (HeightOneSpectrum (𝓞 K)))
    (hS₁ : EffectivePlainSupport d d.plainTest₁ u N₁ t S₁)
    (hS₂ : EffectivePlainSupport d d.plainTest₂ u N₂ t S₂)
    (hS : ∀ i, EffectivePrimeSupport d i u Z t (S i))
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 K) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal K → V)
    (x : Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 K) → V) (ξ : V)
    (hW₁ : ∀ I, w₁ I * jointPhase ξ (x₁ I) =
      d.plainTest₁.profile u t (idealNorm K I / N₁))
    (hW₂ : ∀ I, w₂ I * jointPhase ξ (x₂ I) =
      d.plainTest₂.profile u t (idealNorm K I / N₂))
    (hW : ∀ i p, w i p * jointPhase ξ (x i p) =
      (d.geometry.slots i).profile t
        ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length)) :
    jointFourierColumn (childCartesianColumns S₁ S₂ S)
      (T.coefficient (σ := σ) g h' N₁ N₂ Z
        (fun i => (d.geometry.slots i).length) w₁ w₂ w)
      (childCartesianLocation x₁ x₂ x) ξ =
      jointFourierColumn
        (childCartesianColumns
          (idealCarrier (d.plainTest₁.support u t N₁))
          (idealCarrier (d.plainTest₂.support u t N₂))
          (fun i => (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length)))
        (rawSourceCoefficient (σ := σ) T g h' N₁ N₂ Z
          (fun i => (d.geometry.slots i).length) w₁ w₂ w)
        (rawSourceLocation x₁ x₂ x) ξ := by
  rw [raw_joint_idealCarrier]
  exact calibrated_support_change T d rfl (fun i => (d.geometry.slots i).length)
    (fun _ => rfl) u g h' D N₁ N₂ Z t S₁ S₂
    (d.plainTest₁.support u t N₁) (d.plainTest₂.support u t N₂)
    S (fun i => (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length))
    hS₁ hS₂ hS (fun _ h => h) (fun _ h => h) (fun _ _ h => h)
    w₁ w₂ w x₁ x₂ x ξ hW₁ hW₂ hW

end CanonicalLiteralProfileCarrier
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralProfileCarrier.idealCarrier_nonzero
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralProfileCarrier.raw_joint_idealCarrier
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralProfileCarrier.calibrated_support_change
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralProfileCarrier.calibrated_full_profile_carrier
