import HeckeGeneral.Arithmetic.SIntegerOrbitMask
import HeckeGeneral.Characters.SIntegerSexticPowerMask

/-!
# Canonical puncture primes as actual localized Poisson masks

The arithmetic labels are ordinary exterior ideals, whereas the genuine
masked orbital Poisson theorem uses primes of the S-integer ring.  This
module constructs the map between those prime sets, proves its injectivity,
and identifies the resulting avoidance mask with ordinary prime avoidance
of the actual row contraction.  Thus no equality of the two kinds of masks
has to be postulated.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.LocalizedMasks

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "OS" => S.integer K

abbrev ExteriorPrime := {p : HeightOneSpectrum (𝓞 K) // p ∉ S}

private theorem integerToSInteger_injective :
    Function.Injective (algebraMap (𝓞 K) OS) := by
  intro a b hab
  apply RingOfIntegers.coe_injective
  exact congrArg (fun z : OS => (z : K)) hab

/-- The actual exterior residue homomorphism has precisely the mapped
ordinary prime as kernel. -/
theorem residueMap_ker (p : ExteriorPrime K S) :
    RingHom.ker (sIntegerSexticResidueMap K S p.val p.property) =
      p.val.asIdeal.map (algebraMap (𝓞 K) OS) := by
  ext a
  change sIntegerSexticResidueMap K S p.val p.property a = 0 ↔ _
  exact sIntegerSexticResidueMap_eq_zero_iff_mem_map K S p.val p.property a

/-- An actual exterior prime, extended to the genuine S-integer ring. -/
def localizePrime (p : ExteriorPrime K S) : HeightOneSpectrum OS where
  asIdeal := p.val.asIdeal.map (algebraMap (𝓞 K) OS)
  isPrime := by
    letI : Field (𝓞 K ⧸ p.val.asIdeal) := Ideal.Quotient.field _
    rw [← residueMap_ker K S p]
    exact RingHom.ker_isPrime _
  ne_bot := by
    intro hz
    exact p.val.ne_bot
      ((Ideal.map_eq_bot_iff_of_injective (integerToSInteger_injective K S)).mp hz)

@[simp] theorem localizePrime_asIdeal (p : ExteriorPrime K S) :
    (localizePrime K S p).asIdeal = p.val.asIdeal.map (algebraMap (𝓞 K) OS) := rfl

@[simp] theorem localizePrime_under (p : ExteriorPrime K S) :
    (localizePrime K S p).asIdeal.under (𝓞 K) = p.val.asIdeal :=
  under_map_coprime_sIntegerIdeal K S p.val.asIdeal
    (sIntegerSexticResidue_coprime K S p.val p.property)

theorem localizePrime_injective : Function.Injective (localizePrime K S) := by
  intro p q hpq
  apply Subtype.ext
  apply HeightOneSpectrum.ext
  have he := congrArg (fun P : HeightOneSpectrum OS => P.asIdeal.under (𝓞 K)) hpq
  simpa only [localizePrime_under] using he

def localizePrimeEmbedding : ExteriorPrime K S ↪ HeightOneSpectrum OS :=
  ⟨localizePrime K S, localizePrime_injective K S⟩

/-- The actual finite mask retains every exterior prime exactly once. -/
def localizeMask (P : Finset (ExteriorPrime K S)) : Finset (HeightOneSpectrum OS) :=
  P.map (localizePrimeEmbedding K S)

@[simp] theorem card_localizeMask (P : Finset (ExteriorPrime K S)) :
    (localizeMask K S P).card = P.card := Finset.card_map _

/-- Membership in the localized prime is ordinary prime divisibility of
the actual contraction; this includes nonunit and zero numerators. -/
theorem mem_localizePrime_iff (p : ExteriorPrime K S) (a : OS) :
    a ∈ (localizePrime K S p).asIdeal ↔
      p.val.asIdeal ∣ sIntegerModulusContraction K S a :=
  (sIntegerSexticResidueMap_eq_zero_iff_mem_map K S p.val p.property a).symm.trans
    (sIntegerSexticResidueMap_eq_zero_iff_dvd_contraction K S p.val p.property a)

variable (Γ : Subgroup (S.unit K))

theorem orbitMembership_localizePrime_mk
    (p : ExteriorPrime K S) (a : NonzeroRingElements OS) :
    sIntegerOrbitIdealMembership K S Γ (localizePrime K S p).asIdeal
        (Quotient.mk _ a) ↔
      p.val.asIdeal ∣ sIntegerModulusContraction K S a.val := by
  rw [sIntegerOrbitIdealMembership_mk, mem_localizePrime_iff]

/-- The mask used by Poisson is exactly the prescribed ordinary prime
avoidance condition in every original subgroup sector. -/
theorem avoidanceMask_localize_mk (P : Finset (ExteriorPrime K S))
    (a : NonzeroRingElements OS) :
    sIntegerOrbitAvoidanceMask K S Γ (localizeMask K S P) (Quotient.mk _ a) =
      if ∀ p ∈ P, ¬ p.val.asIdeal ∣ sIntegerModulusContraction K S a.val
      then 1 else 0 := by
  have hcond :
      (∀ p ∈ localizeMask K S P,
        ¬ sIntegerOrbitIdealMembership K S Γ p.asIdeal (Quotient.mk _ a)) ↔
      (∀ p ∈ P, ¬ p.val.asIdeal ∣ sIntegerModulusContraction K S a.val) := by
    simp only [localizeMask, Finset.forall_mem_map, localizePrimeEmbedding,
      Function.Embedding.coeFn_mk, orbitMembership_localizePrime_mk]
  simp only [sIntegerOrbitAvoidanceMask, hcond]

theorem avoidanceMask_localize (P : Finset (ExteriorPrime K S))
    (q : SIntegerOrbits K S Γ) :
    sIntegerOrbitAvoidanceMask K S Γ (localizeMask K S P) q =
      if ∀ p ∈ P, ¬ p.val.asIdeal ∣ sIntegerModulusContraction K S q.out.val
      then 1 else 0 := by
  have he := avoidanceMask_localize_mk K S Γ P q.out
  simpa only [Quotient.out_eq] using he

/-- The same localization for an ordinary prime support with its proved
exteriority, as produced by the exact conductor-digit split. -/
def localizeSupportedMask (P : Finset (HeightOneSpectrum (𝓞 K)))
    (hP : ∀ p ∈ P, p ∉ S) : Finset (HeightOneSpectrum OS) :=
  P.attach.image (fun p => localizePrime K S ⟨p.val, hP p.val p.property⟩)

theorem avoidanceMask_localizeSupported_mk
    (P : Finset (HeightOneSpectrum (𝓞 K))) (hP : ∀ p ∈ P, p ∉ S)
    (a : NonzeroRingElements OS) :
    sIntegerOrbitAvoidanceMask K S Γ (localizeSupportedMask K S P hP) (Quotient.mk _ a) =
      if ∀ p ∈ P, ¬ p.asIdeal ∣ sIntegerModulusContraction K S a.val then 1 else 0 := by
  have hcond :
      (∀ p ∈ localizeSupportedMask K S P hP,
        ¬ sIntegerOrbitIdealMembership K S Γ p.asIdeal (Quotient.mk _ a)) ↔
      (∀ p ∈ P, ¬ p.asIdeal ∣ sIntegerModulusContraction K S a.val) := by
    constructor
    · intro h p hp
      have hm : localizePrime K S ⟨p, hP p hp⟩ ∈ localizeSupportedMask K S P hP :=
        Finset.mem_image.mpr ⟨⟨p, hp⟩, Finset.mem_attach _ _, rfl⟩
      simpa only [orbitMembership_localizePrime_mk] using h _ hm
    · intro h p hp
      obtain ⟨q, _hq, rfl⟩ := Finset.mem_image.mp hp
      simpa only [orbitMembership_localizePrime_mk] using h q.val q.property
  simp only [sIntegerOrbitAvoidanceMask, hcond]

/-- Overlapping external and principal masks combine by union; shared
primes introduce no extra multiplicity. -/
theorem avoidanceMask_union (M P : Finset (HeightOneSpectrum OS))
    (q : SIntegerOrbits K S Γ) :
    sIntegerOrbitAvoidanceMask K S Γ (M ∪ P) q =
      sIntegerOrbitAvoidanceMask K S Γ M q * sIntegerOrbitAvoidanceMask K S Γ P q := by
  simp only [sIntegerOrbitAvoidanceMask, Finset.forall_mem_union]
  by_cases hM : ∀ p ∈ M, ¬ sIntegerOrbitIdealMembership K S Γ p.asIdeal q <;>
    by_cases hP : ∀ p ∈ P, ¬ sIntegerOrbitIdealMembership K S Γ p.asIdeal q <;>
      simp [hM, hP]

end HeckeSkeleton.Moments.MOM_INV_STEP.LocalizedMasks
