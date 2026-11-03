import HeckeGeneral.Analysis.IdealSquarefreeAmplification

/-!
Reindex an actual finitely supported ideal sum by its squarefree prime subsets.
The envelope is an explicitly constructed finite union of actual prime supports.
All non-squarefree terms vanish by the actual ideal Moebius function.
-/

noncomputable section

namespace HeckeGeneral.Analysis.SquarefreeAmplification

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Arithmetic.IdealMobiusMask HeckeGeneral.Characters
open UniqueFactorizationMonoid
open scoped BigOperators Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

def idealPrimeSupport (I : NonzeroIdeal K) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (primeExponents I).support

theorem mem_idealPrimeSupport_iff (I : NonzeroIdeal K)
    (p : HeightOneSpectrum (𝓞 K)) :
    p ∈ idealPrimeSupport K I ↔ p.asIdeal ∣ I.val := by
  simp only [idealPrimeSupport, Finsupp.mem_support_iff, primeExponents_apply,
    Multiset.count_ne_zero, mem_normalizedFactors_iff (nonZeroDivisors.coe_ne_zero I),
    p.prime, true_and]

theorem primeExponents_squarefreeIdeal (T : Finset (HeightOneSpectrum (𝓞 K)))
    (p : HeightOneSpectrum (𝓞 K)) :
    primeExponents (squarefreeIdeal K T) p = if p ∈ T then 1 else 0 := by
  rw [primeExponents_apply]
  change (normalizedFactors (primeProduct T)).count p.asIdeal = _
  rw [normalizedFactors_primeProduct,
    Multiset.count_map_eq_count' _ _ HeightOneSpectrum.asIdeal_injective]
  by_cases hp : p ∈ T
  · rw [if_pos hp]
    exact Multiset.count_eq_one_of_mem T.nodup hp
  · rw [if_neg hp]
    exact Multiset.count_eq_zero_of_notMem hp

@[simp] theorem idealPrimeSupport_squarefreeIdeal
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    idealPrimeSupport K (squarefreeIdeal K T) = T := by
  ext p
  simp only [idealPrimeSupport, Finsupp.mem_support_iff,
    primeExponents_squarefreeIdeal]
  by_cases hp : p ∈ T <;> simp [hp]

theorem squarefreeIdeal_injective : Function.Injective (squarefreeIdeal K) := by
  intro P Q h
  simpa using congrArg (idealPrimeSupport K) h

theorem squarefreeIdeal_primeSupport (I : NonzeroIdeal K) (hI : Squarefree I.val) :
    squarefreeIdeal K (idealPrimeSupport K I) = I := by
  apply (primeExponentEquiv (R := 𝓞 K)).injective
  ext p
  change primeExponents (squarefreeIdeal K (idealPrimeSupport K I)) p = primeExponents I p
  rw [primeExponents_squarefreeIdeal]
  have hcount : primeExponents I p ≤ 1 :=
    Multiset.nodup_iff_count_le_one.mp
      ((squarefree_iff_nodup_normalizedFactors (nonZeroDivisors.coe_ne_zero I)).mp hI)
      p.asIdeal
  by_cases hp : p ∈ idealPrimeSupport K I
  · rw [if_pos hp]
    have hne : primeExponents I p ≠ 0 := Finsupp.mem_support_iff.mp hp
    omega
  · rw [if_neg hp]
    exact (Finsupp.notMem_support_iff.mp hp).symm

/-- The minimal prime envelope of a finite set of actual nonzero ideals. -/
def finitePrimeEnvelope (F : Finset (NonzeroIdeal K)) : Finset (HeightOneSpectrum (𝓞 K)) :=
  F.biUnion (idealPrimeSupport K)

theorem idealPrimeSupport_subset_envelope (F : Finset (NonzeroIdeal K))
    (I : NonzeroIdeal K) (hI : I ∈ F) :
    idealPrimeSupport K I ⊆ finitePrimeEnvelope K F := by
  intro p hp
  exact Finset.mem_biUnion.mpr ⟨I, hI, hp⟩

def idealMoebiusSum (η : HeckeCharacter K) (F : Finset (NonzeroIdeal K))
    (D : ℝ) (W : ℝ → ℂ) : ℂ :=
  ∑ I ∈ F, (moebius I.val : ℂ) * heckeIdealCoefficient K η I *
    W (idealNorm K I / D)

/-- The envelope can be enlarged freely, provided it covers every ideal in F.
The support condition is on the same profile W, with no additional mask. -/
theorem idealMoebiusSum_eq_squarefreeSum (η : HeckeCharacter K)
    (F : Finset (NonzeroIdeal K)) (E : Finset (HeightOneSpectrum (𝓞 K)))
    (D : ℝ) (W : ℝ → ℂ)
    (hcover : ∀ I ∈ F, idealPrimeSupport K I ⊆ E)
    (hsupport : ∀ I, idealPrimeSupport K I ⊆ E → I ∉ F →
      W (idealNorm K I / D) = 0) :
    idealMoebiusSum K η F D W = squarefreeSum K η E D W := by
  unfold idealMoebiusSum squarefreeSum
  have hsq : ∀ I : NonzeroIdeal K,
      (moebius I.val : ℂ) * heckeIdealCoefficient K η I *
        W (idealNorm K I / D) ≠ 0 → Squarefree I.val := by
    intro I hn
    by_contra h
    simp [moebius_of_not_squarefree h] at hn
  apply Finset.sum_bij_ne_zero (fun I _ _ => idealPrimeSupport K I)
  · intro I hI _
    exact Finset.mem_powerset.mpr (hcover I hI)
  · intro I _ hi J _ hj hij
    calc
      I = squarefreeIdeal K (idealPrimeSupport K I) :=
        (squarefreeIdeal_primeSupport K I (hsq I hi)).symm
      _ = squarefreeIdeal K (idealPrimeSupport K J) := congrArg _ hij
      _ = J := squarefreeIdeal_primeSupport K J (hsq J hj)
  · intro T hTE hT
    have hmem : squarefreeIdeal K T ∈ F := by
      by_contra h
      have hsub : idealPrimeSupport K (squarefreeIdeal K T) ⊆ E := by
        simpa using Finset.mem_powerset.mp hTE
      exact hT (by rw [hsupport _ hsub h, mul_zero])
    exact ⟨squarefreeIdeal K T, hmem, hT, idealPrimeSupport_squarefreeIdeal K T⟩
  · intro I _ hi
    rw [squarefreeIdeal_primeSupport K I (hsq I hi)]

/-- Canonical reindexing uses the actual prime envelope constructed from F. -/
theorem idealMoebiusSum_eq_envelope (η : HeckeCharacter K)
    (F : Finset (NonzeroIdeal K)) (D : ℝ) (W : ℝ → ℂ)
    (hsupport : ∀ I, idealPrimeSupport K I ⊆ finitePrimeEnvelope K F →
      I ∉ F → W (idealNorm K I / D) = 0) :
    idealMoebiusSum K η F D W =
      squarefreeSum K η (finitePrimeEnvelope K F) D W :=
  idealMoebiusSum_eq_squarefreeSum K η F _ D W
    (idealPrimeSupport_subset_envelope K F) hsupport

end HeckeGeneral.Analysis.SquarefreeAmplification
