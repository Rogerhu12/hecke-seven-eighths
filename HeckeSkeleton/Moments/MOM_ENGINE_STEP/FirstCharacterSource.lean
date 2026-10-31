import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstResidualSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualFirstCharacters

/-!
# The original first source on all subgroup orbits

The original generated characters are evaluated through the genuine
normalized residue family. Thus the first common-support decomposition
does not require a chosen generator to equal a canonical prime product.
Principal factors remain the literal orbital avoidance mask.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments HeckePort.Moments.CommonSupport HeckePort.Moments.Active

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

include hΓ in
theorem generated_character_subgroup_value (I : A.Exterior)
    (a : A.R) (ha : A.Generates I a) (u : Γ) :
    σ (A.sexticResidue I (A.unitEquiv u.val : A.R)) = 1 := by
  have h1 : σ (A.sexticResidue I 1) = 1 := by
    simpa only [map_one] using (generatedIdealCharacter_mk (σ := σ) I a ha 1).symm
  obtain ⟨v, hv⟩ := hΓ u
  rw [hv, map_pow, Units.val_pow_eq_pow_val]
  simpa only [one_mul] using
    (congrArg σ (A.sexticResidue_sixth_unit_translate I 1 v)).trans h1

def generatedOriginalColumn (I : A.Exterior) (a : A.R) (ha : A.Generates I a) :
    OrbitalGaussColumn K A.Sf Γ where
  modulus := a
  nonzero := ha.1
  character := generatedIdealCharacter (σ := σ) I a ha
  invariant u := by
    rw [generatedIdealCharacter_mk]
    exact generated_character_subgroup_value hΓ I a ha u

theorem firstReciprocalPhase_allowed (C : A.GeneralArithmeticContext σ η hS)
    (I J : A.Exterior) (a b : A.R) (ha : A.Generates I a) (hb : A.Generates J b)
    (ua ub : Kˣ) (hua : (ua : K) = (a : K)) (hub : (ub : K) = (b : K))
    (hallowed_a : A.IsAllowed C.correction.B ua)
    (hallowed_b : A.IsAllowed C.correction.B ub) (hcop : IsCoprime I.val J.val) :
    firstReciprocalPhase (generatedOriginalColumn (σ := σ) hΓ I a ha)
      (generatedOriginalColumn (σ := σ) hΓ J b hb) = 1 := by
  letI := finite_sIntegerPrincipalResidue K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) b hb.1
  have hrec := congrArg σ
    (C.reciprocity.1 I J a b ua ub ha hb hua hub hallowed_a hallowed_b hcop.sup_eq)
  have he : generatedIdealCharacter (σ := σ) I a ha (Ideal.Quotient.mk _ b) =
      generatedIdealCharacter (σ := σ) J b hb (Ideal.Quotient.mk _ a) := by
    simpa only [generatedIdealCharacter_mk] using hrec
  change generatedIdealCharacter (σ := σ) I a ha (Ideal.Quotient.mk _ b) *
    star (generatedIdealCharacter (σ := σ) J b hb (Ideal.Quotient.mk _ a)) = 1
  rw [he, MulChar.star_apply', MulChar.inv_apply_eq_inv']
  apply mul_inv_cancel₀
  exact MulChar.apply_ne_zero_iff.mpr
    (isUnit_residue_of_coprime b a
      (generated_elements_coprime I J a b ha hb hcop).symm)

/-- The original two multiplicative columns, before the first Poisson operation. -/
def OrbitalGaussColumn.originalPair {S : Finset (HeightOneSpectrum (𝓞 K))}
    {Γ₀ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
    (a b : OrbitalGaussColumn K S Γ₀) (φ : SchwartzMap V ℂ) :
    ParentPeriodicPair K S Γ₀ where
  modulus := a.modulus * b.modulus
  modulus_ne_zero := mul_ne_zero a.nonzero b.nonzero
  residue x :=
    a.character (completeFrequencyReduction a.modulus (a.modulus * b.modulus)
      (dvd_mul_right _ _) x) *
    star (b.character (completeFrequencyReduction b.modulus (a.modulus * b.modulus)
      (dvd_mul_left _ _) x))
  invariant u x := by
    simp only [completeFrequencyReduction_mk, map_mul, a.invariant, b.invariant,
      star_one, one_mul]
  profile := φ

@[simp] theorem OrbitalGaussColumn.originalPair_orbit_mk
    {S : Finset (HeightOneSpectrum (𝓞 K))}
    {Γ₀ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
    (a b : OrbitalGaussColumn K S Γ₀) (φ : SchwartzMap V ℂ)
    (x : NonzeroRingElements (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)) :
    (a.originalPair b φ).orbitWeight (Quotient.mk _ x) =
      a.character (Ideal.Quotient.mk _ x.val) *
        star (b.character (Ideal.Quotient.mk _ x.val)) := by
  simp only [ParentPeriodicPair.orbitWeight, OrbitalGaussColumn.originalPair,
    sIntegerPeriodicOrbitWeight_mk, completeFrequencyReduction_mk]

@[simp] theorem OrbitalGaussColumn.originalTriple_orbit_mk
    {S : Finset (HeightOneSpectrum (𝓞 K))}
    {Γ₀ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
    (a b r : OrbitalGaussColumn K S Γ₀) (φ : SchwartzMap V ℂ)
    (x : NonzeroRingElements (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)) :
    (a.originalTriple b r φ).orbitWeight (Quotient.mk _ x) =
      a.character (Ideal.Quotient.mk _ x.val) *
        star (b.character (Ideal.Quotient.mk _ x.val)) *
          r.character (Ideal.Quotient.mk _ x.val) := by
  letI := finite_sIntegerPrincipalResidue K (S : Set (HeightOneSpectrum (𝓞 K))) b.modulus b.nonzero
  simp only [ParentPeriodicPair.orbitWeight, OrbitalGaussColumn.originalTriple,
    sIntegerPeriodicOrbitWeight_mk, completeFrequencyReduction_mk, MulChar.star_apply']

section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def actualActiveColumn (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ) :
    OrbitalGaussColumn K A.Sf Γ where
  modulus := firstActiveGenerator C p m n
  nonzero := (firstActiveGenerator_generates C p m n).1
  character := actualFirstActiveCharacter C p hp m n
  invariant u := by
    rw [actualFirstActiveCharacter_mk]
    apply Finset.prod_eq_one
    intro i _
    rw [MulChar.pow_apply' _ (netExponent_ne_zero Finset.univ m n i),
      actual_prime_character_value C]
    rw [generated_character_subgroup_value hΓ (primeIdeal (p i.val))
      (generator C (p i.val)) (generator_generates C (p i.val)) u, one_pow]

def actualExteriorSPrime (p : ExteriorPrime A) : HeightOneSpectrum A.R where
  asIdeal := A.extendIdeal (primeIdeal p)
  isPrime := (CanonicalLocalGaussTable.primeResidueMaximal p).isPrime
  ne_bot := A.extendIdeal_ne_zero _

def firstPrincipalPrimeMask (p : ι → ExteriorPrime A) (m n : ι → ℕ) :
    Finset (HeightOneSpectrum A.R) :=
  (principalSupport Finset.univ m n).image (fun i => actualExteriorSPrime (p i))

theorem firstPrincipalMask_eq_orbit_mask (C : A.GeneralArithmeticContext σ η hS)
    (p : ι → ExteriorPrime A) (m n : ι → ℕ) (x : NonzeroRingElements A.R) :
    firstPrincipalMask C p m n x.val =
      sIntegerOrbitAvoidanceMask K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
        (firstPrincipalPrimeMask p m n) (Quotient.mk _ x) := by
  unfold firstPrincipalMask sIntegerOrbitAvoidanceMask
  simp only [sIntegerOrbitIdealMembership_mk]
  have he :
      (∀ q ∈ firstPrincipalPrimeMask p m n, x.val ∉ q.asIdeal) ↔
        ¬ ∃ i ∈ principalSupport Finset.univ m n, generator C (p i) ∣ x.val := by
    simp only [firstPrincipalPrimeMask, Finset.mem_image, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂, not_exists]
    apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    change x.val ∉ A.extendIdeal (primeIdeal (p i)) ↔ ¬ generator C (p i) ∣ x.val
    rw [← (generator_generates C (p i)).2, Ideal.mem_span_singleton]
  rw [he]
  by_cases hp : ∃ i ∈ principalSupport Finset.univ m n, generator C (p i) ∣ x.val <;>
    simp only [hp, if_true, if_false, not_true_eq_false, not_false_eq_true]

end Product

theorem sIntegerOrbitAvoidanceMask_union
    {S : Finset (HeightOneSpectrum (𝓞 K))}
    {Γ₀ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
    (M N : Finset (HeightOneSpectrum
      (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)))
    (q : SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ₀) :
    sIntegerOrbitAvoidanceMask K (S : Set (HeightOneSpectrum (𝓞 K))) Γ₀ (M ∪ N) q =
      sIntegerOrbitAvoidanceMask K (S : Set (HeightOneSpectrum (𝓞 K))) Γ₀ M q *
        sIntegerOrbitAvoidanceMask K (S : Set (HeightOneSpectrum (𝓞 K))) Γ₀ N q := by
  refine Quotient.inductionOn q ?_
  intro x
  simp only [sIntegerOrbitAvoidanceMask, sIntegerOrbitIdealMembership_mk,
    Finset.mem_union, or_imp, forall_and]
  split_ifs <;> simp_all

variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]

theorem actual_first_character_source_term
    (C : A.GeneralArithmeticContext σ η hS)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i)
    (IA IB IFull JFull : A.Exterior)
    (hI : IFull.val = (primePowerProduct p m).val * IA.val)
    (hJ : JFull.val = (primePowerProduct p n).val * IB.val)
    (a b afull bfull : A.R)
    (ha : A.Generates IA a) (hb : A.Generates IB b)
    (hafull : A.Generates IFull afull) (hbfull : A.Generates JFull bfull)
    (φ : SchwartzMap V ℂ)
    (ψ : ((v : (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R)) (q : Q) :
    ((generatedOriginalColumn (σ := σ) hΓ IFull afull hafull).originalPair
      (generatedOriginalColumn (σ := σ) hΓ JFull bfull hbfull) φ).maskedTerm ψ radius M q =
    ((generatedOriginalColumn (σ := σ) hΓ IA a ha).originalTriple
      (generatedOriginalColumn (σ := σ) hΓ IB b hb)
      (actualActiveColumn hΓ C p hp m n) φ).maskedTerm ψ radius
        (M ∪ firstPrincipalPrimeMask p m n) q := by
  refine Quotient.inductionOn q ?_
  intro x
  have he := actual_full_pair_active C p hp m n hm hn IA IB IFull JFull hI hJ x.val
  unfold ParentPeriodicPair.maskedTerm
  rw [OrbitalGaussColumn.originalPair_orbit_mk, OrbitalGaussColumn.originalTriple_orbit_mk,
    sIntegerOrbitAvoidanceMask_union, ← firstPrincipalMask_eq_orbit_mask C p m n x]
  simp only [generatedOriginalColumn, generatedIdealCharacter_mk, actualActiveColumn]
  rw [he]
  change _ * _ * sUnitOrbitalProfile K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) _ _ =
    _ * _ * sUnitOrbitalProfile K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) _ _
  ring

theorem actual_first_character_source_series
    (C : A.GeneralArithmeticContext σ η hS)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ExteriorPrime A) (hp : Function.Injective p) (m n : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i)
    (IA IB IFull JFull : A.Exterior)
    (hI : IFull.val = (primePowerProduct p m).val * IA.val)
    (hJ : JFull.val = (primePowerProduct p n).val * IB.val)
    (a b afull bfull : A.R)
    (ha : A.Generates IA a) (hb : A.Generates IB b)
    (hafull : A.Generates IFull afull) (hbfull : A.Generates JFull bfull)
    (φ : SchwartzMap V ℂ)
    (ψ : ((v : (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R)) :
    ((generatedOriginalColumn (σ := σ) hΓ IFull afull hafull).originalPair
      (generatedOriginalColumn (σ := σ) hΓ JFull bfull hbfull) φ).maskedSeries ψ radius M =
    ((generatedOriginalColumn (σ := σ) hΓ IA a ha).originalTriple
      (generatedOriginalColumn (σ := σ) hΓ IB b hb)
      (actualActiveColumn hΓ C p hp m n) φ).maskedSeries ψ radius
        (M ∪ firstPrincipalPrimeMask p m n) := by
  change (∑' q, _.maskedTerm ψ radius M q) = ∑' q, _.maskedTerm ψ radius _ q
  apply tsum_congr
  intro q
  exact actual_first_character_source_term hΓ C p hp m n hm hn
    IA IB IFull JFull hI hJ a b afull bfull ha hb hafull hbfull φ ψ radius M q

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.firstPrincipalMask_eq_orbit_mask
#print axioms HeckeSkeleton.Moments.EngineStep.actual_first_character_source_series

