import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstBlocks
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFirstZero

/-!
# Zero Gauss sums for arbitrary actual generators

At frequency zero the trace character is one. Changing the generator of
the same exterior ideal therefore changes only the presentation of its
finite quotient. The complete sum is transported by the literal quotient
equivalence. An exact normalized-factor recipe is then constructed for
every exterior ideal, so the local zero-frequency support theorem applies
to the original chosen generators without any calibration assumption.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckePort.Moments HeckePort.Moments.CommonSupport
open HeckePort.IdealMobiusDivisorSum UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

theorem generated_zero_gauss_generator_change
    (T : NonzeroModulusTrace A.R) (I : A.Exterior) (a b : A.R)
    (ha : A.Generates I a) (hb : A.Generates I b)
    [Fintype (A.R ⧸ Ideal.span {a})] [Fintype (A.R ⧸ Ideal.span {b})] :
    completeResidueGauss T a (generatedIdealCharacter (σ := σ) I a ha) 0 =
      completeResidueGauss T b (generatedIdealCharacter (σ := σ) I b hb) 0 := by
  simp only [completeResidueGauss, zero_mul, AddChar.map_zero_eq_one, mul_one]
  let e := Ideal.quotEquivOfEq (ha.2.trans hb.2.symm)
  apply Fintype.sum_equiv e.toEquiv
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [e, Ideal.quotEquivOfEq_mk, generatedIdealCharacter_mk]

/-- Every original exterior ideal has its exact positive prime-power recipe. -/
theorem exterior_support_primePowerProduct (I : A.Exterior) :
    primePowerProduct (exteriorPrimeOfSupport I)
      (fun P : primeSupport I.val => (normalizedFactors I.val).count P.val) = I := by
  apply Subtype.ext
  change (∏ P : primeSupport I.val, P.val ^ (normalizedFactors I.val).count P.val) = I.val
  rw [Finset.prod_coe_sort (s := primeSupport I.val)
    (f := fun P => P ^ (normalizedFactors I.val).count P)]
  change (∏ P ∈ (normalizedFactors I.val).toFinset,
    P ^ (normalizedFactors I.val).count P) = I.val
  rw [← Finset.prod_multiset_count]
  exact Ideal.prod_normalizedFactors_eq_self I.property.1

theorem actual_zero_gauss_nonzero_powerful_of_generates
    (C : A.GeneralArithmeticContext σ η hS) (T : NonzeroModulusTrace A.R)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    [Fintype (A.R ⧸ Ideal.span {a})]
    (hzero : completeResidueGauss T a (generatedIdealCharacter (σ := σ) I a ha) 0 ≠ 0) :
    Powerful I.val := by
  let p := exteriorPrimeOfSupport I
  let n := fun P : primeSupport I.val => (normalizedFactors I.val).count P.val
  have hp : Function.Injective p := by
    intro P Q hPQ
    apply Subtype.ext
    exact congrArg (fun q : ExteriorPrime A => q.val.asIdeal) hPQ
  have hn : ∀ P : primeSupport I.val, 0 < n P := by
    intro P
    exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.property)
  have hrecipe : primePowerProduct p n = I := exterior_support_primePowerProduct I
  let b := primePowerProductGenerator C p n
  have hb : A.Generates I b := hrecipe ▸ primePowerProduct_generates C p n
  letI : Finite (A.R ⧸ Ideal.span {b}) := by
    rw [hb.2]
    exact A.exteriorResidue_finite I
  letI := Fintype.ofFinite (A.R ⧸ Ideal.span {b})
  have hbzero : completeResidueGauss T b
      (generatedIdealCharacter (σ := σ) I b hb) 0 ≠ 0 := by
    rw [← generated_zero_gauss_generator_change T I a b ha hb]
    exact hzero
  have hbzero' : completeResidueGauss T (primePowerProductGenerator C p n)
      (generatedIdealCharacter (σ := σ) (primePowerProduct p n)
        (primePowerProductGenerator C p n) (primePowerProduct_generates C p n)) 0 ≠ 0 := by
    simpa only [b, hrecipe] using hbzero
  simpa only [hrecipe] using actual_zero_gauss_nonzero_powerful C T p hp n hn hbzero'

theorem actual_sInteger_zero_gauss_nonzero_powerful
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → localDifferentExponent K v = 0)
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (hzero : actualSIntegerGauss K (A.Sf : Set _) hDiff a ha.1
      (generatedIdealCharacter (σ := σ) I a ha) 0 ≠ 0) :
    Powerful I.val := by
  letI := finite_sIntegerPrincipalResidue K (A.Sf : Set _) a ha.1
  letI := Fintype.ofFinite (A.R ⧸ Ideal.span {a})
  apply actual_zero_gauss_nonzero_powerful_of_generates C
    (actualSIntegerTrace K (A.Sf : Set _) hDiff) I a ha
  simpa only [actualSIntegerGauss, map_zero] using hzero

variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)

/-- The literal first finite transform at zero forces both original
residual ideals to be powerful, for arbitrary actual generators. -/
theorem originalTriple_zero_powerful_residuals
    (C : A.GeneralArithmeticContext σ η hS)
    (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → localDifferentExponent K v = 0)
    (I J : A.Exterior) (a b : A.R) (ha : A.Generates I a) (hb : A.Generates J b)
    (r : OrbitalGaussColumn K A.Sf Γ)
    (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (habr : IsCoprime a (b * r.modulus)) (hbr : IsCoprime b r.modulus) (δ : A.R)
    (hzero : sIntegerPeriodicDivisorFourier K (A.Sf : Set _) hDiff
      ((generatedOriginalColumn (σ := σ) hΓ I a ha).originalTriple
        (generatedOriginalColumn (σ := σ) hΓ J b hb) r φ).modulus
      ((generatedOriginalColumn (σ := σ) hΓ I a ha).originalTriple
        (generatedOriginalColumn (σ := σ) hΓ J b hb) r φ).modulus_ne_zero
      ((generatedOriginalColumn (σ := σ) hΓ I a ha).originalTriple
        (generatedOriginalColumn (σ := σ) hΓ J b hb) r φ).residue δ 0 ≠ 0) :
    Powerful I.val ∧ Powerful J.val := by
  have he := originalTriple_divisor_fourier hDiff
    (generatedOriginalColumn (σ := σ) hΓ I a ha)
    (generatedOriginalColumn (σ := σ) hΓ J b hb) r φ habr hbr δ 0
  simp only [map_zero, neg_zero] at he
  rw [he] at hzero
  have hpair := (mul_ne_zero_iff.mp hzero).2
  constructor
  · exact actual_sInteger_zero_gauss_nonzero_powerful C hDiff I a ha
      (mul_ne_zero_iff.mp hpair).1
  · apply actual_sInteger_zero_gauss_nonzero_powerful C hDiff J b hb
    intro hz
    apply (mul_ne_zero_iff.mp hpair).2
    rw [hz, star_zero]

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.generated_zero_gauss_generator_change
#print axioms HeckeSkeleton.Moments.EngineStep.actual_zero_gauss_nonzero_powerful_of_generates
#print axioms HeckeSkeleton.Moments.EngineStep.originalTriple_zero_powerful_residuals

