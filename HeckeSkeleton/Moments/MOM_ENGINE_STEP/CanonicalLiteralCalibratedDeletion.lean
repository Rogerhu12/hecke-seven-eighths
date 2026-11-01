import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralProfileCarrier

/-!
# Calibrated finite sources enter the passive divisor expansion

The equality of the old source and the reduced source is supplied only
by their single-ideal and single-prime calibration dictionaries. The
complete polynomial identity is proved here, after restoring the full
finite smooth-profile carrier. No allowed-row or norm window is used.

The centered raw theorem retains its one original subtraction and its
common Gauss normalizer. Every surviving label constructs the genuine
allocation consumed by `ActualColumnAllocation.centered_joint_polynomial`.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments
open CanonicalOriginalPhaseCalibration

namespace CanonicalLiteralCalibratedDeletion

open CanonicalLiteralPassiveDeletion CanonicalLiteralProfileCarrier

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {k : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ω ψ : HeckeCharacter K}

/-- The actual moving frequency is unchanged by factoring the fixed
coprimality mask out of a complete source coefficient. -/
theorem coefficient_deleteMask
    (T : FixedChildCharacters K k) (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (g h' : A.R) (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (v : (HeckeGeneral.Analysis.NonzeroIdeal K × HeckeGeneral.Analysis.NonzeroIdeal K) ×
      (Fin k → HeightOneSpectrum (𝓞 K))) :
    (T.deleteMask M).coefficient (σ := σ) g h' N₁ N₂ Z length w₁ w₂ w v =
      T.coefficient (σ := σ) g h' N₁ N₂ Z length w₁ w₂ w v *
        originalCoprimeMask M (childIndexIdeal v) := by
  have hb := T.rawBare_deleteMask M N₁ N₂ Z length w₁ w₂ w
    ((v.1.1.val, v.1.2.val), v.2)
    (nonZeroDivisors.coe_ne_zero v.1.1) (nonZeroDivisors.coe_ne_zero v.1.2)
  simp only [rawBareSourceCoefficient, sourceMomentIdeal_coe] at hb
  change (T.deleteMask M).bareCoefficient N₁ N₂ Z length w₁ w₂ w v =
    T.bareCoefficient N₁ N₂ Z length w₁ w₂ w v *
      originalCoprimeMask M (childIndexIdeal v) at hb
  rw [FixedChildCharacters.coefficient_eq_bare_mul_residue,
    FixedChildCharacters.coefficient_eq_bare_mul_residue, hb]
  ring

theorem raw_coefficient_deleteMask
    (T : FixedChildCharacters K k) (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (g h' : A.R) (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) (h₁ : i.1.1 ≠ 0) (h₂ : i.1.2 ≠ 0) :
    rawSourceCoefficient (σ := σ) (T.deleteMask M) g h' N₁ N₂ Z length w₁ w₂ w i =
      rawSourceCoefficient (σ := σ) T g h' N₁ N₂ Z length w₁ w₂ w i *
        originalCoprimeMask M (allocationColumnIdeal i) := by
  simpa only [rawSourceCoefficient, childIndexIdeal, allocationColumnIdeal,
    sourceMomentIdeal_val_of_ne_zero _ h₁, sourceMomentIdeal_val_of_ne_zero _ h₂] using
    coefficient_deleteMask T M g h' N₁ N₂ Z length w₁ w₂ w
      ((sourceMomentIdeal i.1.1, sourceMomentIdeal i.1.2), i.2)

theorem raw_joint_allocations
    (T : FixedChildCharacters K k) (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (g h' : A.R) (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ I ∈ S₂, I ≠ 0)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal K → V)
    (x : Fin k → HeightOneSpectrum (𝓞 K) → V) (ξ : V) :
    jointFourierColumn (childCartesianColumns S₁ S₂ S)
      (rawSourceCoefficient (σ := σ) (T.deleteMask M) g h' N₁ N₂ Z length w₁ w₂ w)
      (rawSourceLocation x₁ x₂ x) ξ =
      ∑ a ∈ (liveLabels M.val S₁ S₂ S id id HeightOneSpectrum.asIdeal).attach,
        sign a.val * jointFourierColumn (allocation M.val S₁ S₂ S hS₁ hS₂ a).columns
          (rawSourceCoefficient (σ := σ) T g h' N₁ N₂ Z length w₁ w₂ w)
          (rawSourceLocation x₁ x₂ x) ξ := by
  calc
    _ = jointFourierColumn (childCartesianColumns S₁ S₂ S)
        (fun v => (if IsCoprime (allocationColumnIdeal v) M.val then (1 : ℂ) else 0) *
          rawSourceCoefficient (σ := σ) T g h' N₁ N₂ Z length w₁ w₂ w v)
        (rawSourceLocation x₁ x₂ x) ξ := by
      unfold jointFourierColumn
      apply Finset.sum_congr rfl
      intro v hv
      have hp := Finset.mem_product.mp (Finset.mem_product.mp hv).1
      rw [raw_coefficient_deleteMask T M g h' N₁ N₂ Z length w₁ w₂ w v
        (hS₁ _ hp.1) (hS₂ _ hp.2)]
      change (_ * (if IsCoprime (allocationColumnIdeal v) M.val then 1 else 0)) * _ = _
      ring
    _ = _ := joint_mask_allocations M.val (nonZeroDivisors.coe_ne_zero M)
      S₁ S₂ S hS₁ hS₂ (rawSourceCoefficient (σ := σ) T g h' N₁ N₂ Z length w₁ w₂ w)
      (rawSourceLocation x₁ x₂ x) ξ

/-- Both rectangles have the same finite label and the same frozen
scalar. Their subtraction and original Gauss normalizer stay intact. -/
theorem raw_centered_joint_allocations
    (T : FixedChildCharacters K k) (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (g h' : A.R) (X₁ X₂ Y₁ Y₂ Z : ℝ) (length : Fin k → ℝ)
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ I ∈ S₂, I ≠ 0)
    (w₁ w₂ v₁ v₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal K → V)
    (x : Fin k → HeightOneSpectrum (𝓞 K) → V) (normalizer : ℂ) (ξ : V) :
    jointFourierColumn (childCartesianColumns S₁ S₂ S)
      (fun i => normalizer *
        (rawSourceCoefficient (σ := σ) (T.deleteMask M) g h' X₁ X₂ Z length w₁ w₂ w i -
         rawSourceCoefficient (σ := σ) (T.deleteMask M) g h' Y₁ Y₂ Z length v₁ v₂ w i))
      (rawSourceLocation x₁ x₂ x) ξ =
      ∑ a ∈ (liveLabels M.val S₁ S₂ S id id HeightOneSpectrum.asIdeal).attach,
        sign a.val * jointFourierColumn (allocation M.val S₁ S₂ S hS₁ hS₂ a).columns
          (fun i => normalizer *
            (rawSourceCoefficient (σ := σ) T g h' X₁ X₂ Z length w₁ w₂ w i -
             rawSourceCoefficient (σ := σ) T g h' Y₁ Y₂ Z length v₁ v₂ w i))
          (rawSourceLocation x₁ x₂ x) ξ := by
  calc
    _ = jointFourierColumn (childCartesianColumns S₁ S₂ S)
        (fun i => (if IsCoprime (allocationColumnIdeal i) M.val then (1 : ℂ) else 0) *
          (normalizer *
            (rawSourceCoefficient (σ := σ) T g h' X₁ X₂ Z length w₁ w₂ w i -
             rawSourceCoefficient (σ := σ) T g h' Y₁ Y₂ Z length v₁ v₂ w i)))
        (rawSourceLocation x₁ x₂ x) ξ := by
      unfold jointFourierColumn
      apply Finset.sum_congr rfl
      intro i hi
      have hp := Finset.mem_product.mp (Finset.mem_product.mp hi).1
      rw [raw_coefficient_deleteMask T M g h' X₁ X₂ Z length w₁ w₂ w i
          (hS₁ _ hp.1) (hS₂ _ hp.2),
        raw_coefficient_deleteMask T M g h' Y₁ Y₂ Z length v₁ v₂ w i
          (hS₁ _ hp.1) (hS₂ _ hp.2)]
      change (normalizer *
        (_ * (if IsCoprime (allocationColumnIdeal i) M.val then 1 else 0) -
         _ * (if IsCoprime (allocationColumnIdeal i) M.val then 1 else 0))) * _ = _
      ring
    _ = _ := joint_mask_allocations M.val (nonZeroDivisors.coe_ne_zero M)
      S₁ S₂ S hS₁ hS₂ _ (rawSourceLocation x₁ x₂ x) ξ

/-- The old source's actual atom dictionaries and its effective support
give the enlarged masked polynomial. The new divisor labels and their
nonempty witnesses are then constructed internally on that carrier. -/
theorem calibrated_passive_allocations
    (old T : FixedChildCharacters K k) (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (d : MomentData K ω ψ) (count : d.geometry.slotCount = k)
    (length : Fin k → ℝ)
    (hlength : ∀ i, (d.geometry.slots i).length = length (Fin.cast count i))
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (g h' : A.R)
    (Dold : old.Calibration (σ := σ) d count u g h')
    (Dpaid : (T.deleteMask M).Calibration (σ := σ) d count u g h')
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
      (old.coefficient (σ := σ) g h' N₁ N₂ Z length w₁ w₂ w)
      (childCartesianLocation x₁ x₂ x) ξ =
      ∑ a ∈ (liveLabels M.val (idealCarrier U₁) (idealCarrier U₂) U
        id id HeightOneSpectrum.asIdeal).attach,
        sign a.val * jointFourierColumn
          (allocation M.val (idealCarrier U₁) (idealCarrier U₂) U
            (idealCarrier_nonzero U₁) (idealCarrier_nonzero U₂) a).columns
          (rawSourceCoefficient (σ := σ) T g h' N₁ N₂ Z length w₁ w₂ w)
          (rawSourceLocation x₁ x₂ x) ξ := by
  have hsource := fixed_child_polynomial_from_effective_terms old d count length hlength
    u g h' Dold N₁ N₂ Z t S₁ S₂ S hS₁ hS₂ hS w₁ w₂ w x₁ x₂ x ξ
    (fun I _ => hW₁ I) (fun I _ => hW₂ I) (fun i p _ => hW i p)
  have hfull := fixed_child_polynomial_from_effective_terms (T.deleteMask M) d count
    length hlength u g h' Dpaid N₁ N₂ Z t U₁ U₂ U
    (effectivePlainSupport_of_profile d d.plainTest₁ u N₁ t U₁ hU₁)
    (effectivePlainSupport_of_profile d d.plainTest₂ u N₂ t U₂ hU₂)
    (fun i => effectivePrimeSupport_of_profile d i u Z t (U (Fin.cast count i)) (hU i))
    w₁ w₂ w x₁ x₂ x ξ
    (fun I _ => hW₁ I) (fun I _ => hW₂ I) (fun i p _ => hW i p)
  rw [hsource.trans hfull.symm,
    ← raw_joint_idealCarrier (T.deleteMask M) g h' N₁ N₂ Z length U₁ U₂ U]
  exact raw_joint_allocations T M g h' N₁ N₂ Z length
    (idealCarrier U₁) (idealCarrier U₂) U
    (idealCarrier_nonzero U₁) (idealCarrier_nonzero U₂) w₁ w₂ w x₁ x₂ x ξ

end CanonicalLiteralCalibratedDeletion
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralCalibratedDeletion.coefficient_deleteMask
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralCalibratedDeletion.raw_centered_joint_allocations
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralCalibratedDeletion.calibrated_passive_allocations
