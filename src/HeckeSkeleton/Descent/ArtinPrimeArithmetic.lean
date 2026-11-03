import HeckeSkeleton.Descent.ArtinFrobenius
import HeckeGeneral.Characters.FiniteRamification
import HeckeGeneral.Analysis.IdealSquarefreeSupport
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SupportedBridge
import Mathlib.Tactic.NormNum

/-!
Adapted from the 2026-10-11 cache candidate; see DESCENT_CODEX_REPORT_2.md for checks.

The bad-prime set is constructed from the actual finite ramification set
of the continuous Hecke character and the actual extension. No finite-
bad-set assumption is supplied. Actual contraction fibres are identified
with the actual ideals lying above v; the ideal fundamental identity then
proves their cardinality and exact quotient formula. Absolute norms and
the project's residueCard satisfy the actual inertia-degree power formula.
No Euler-product rearrangement or local Euler-factor identity is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeSkeleton.Descent.ArtinPrimeArithmetic

open NumberField IsDedekindDomain HeckeGeneral.Characters
open HeckeSkeleton.Descent.ArtinFrobenius
open scoped NumberField Classical nonZeroDivisors

variable (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
variable [Algebra F K] [FiniteDimensional F K] [IsAbelianGalois F K]

/-- The nonzero principal ideal `(6)`, used only to include all places above
the rational primes two and three in the deleted set. -/
private def sixIdeal : (Ideal (𝓞 F))⁰ :=
  ⟨Ideal.span ({(6 : 𝓞 F)} : Set (𝓞 F)), mem_nonZeroDivisors_of_ne_zero (by
    intro h
    have h6 : (6 : 𝓞 F) = 0 := Ideal.span_singleton_eq_bot.mp h
    exact (by norm_num : (6 : 𝓞 F) ≠ 0) h6)⟩

/-- The genuine finite prime support of `(6)`. -/
def placesAboveSix : Finset (HeightOneSpectrum (𝓞 F)) :=
  HeckeGeneral.Analysis.SquarefreeAmplification.idealPrimeSupport F (sixIdeal F)

theorem mem_placesAboveSix_iff (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ placesAboveSix F ↔ (6 : 𝓞 F) ∈ v.asIdeal := by
  rw [placesAboveSix,
    HeckeGeneral.Analysis.SquarefreeAmplification.mem_idealPrimeSupport_iff]
  change v.asIdeal ∣ Ideal.span ({(6 : 𝓞 F)} : Set (𝓞 F)) ↔ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]

theorem mem_placesAboveSix_of_two_mem (v : HeightOneSpectrum (𝓞 F))
    (hv : (2 : 𝓞 F) ∈ v.asIdeal) : v ∈ placesAboveSix F := by
  apply (mem_placesAboveSix_iff F v).mpr
  convert v.asIdeal.mul_mem_left (3 : 𝓞 F) hv using 1 <;> norm_num

theorem mem_placesAboveSix_of_three_mem (v : HeightOneSpectrum (𝓞 F))
    (hv : (3 : 𝓞 F) ∈ v.asIdeal) : v ∈ placesAboveSix F := by
  apply (mem_placesAboveSix_iff F v).mpr
  convert v.asIdeal.mul_mem_left (2 : 𝓞 F) hv using 1 <;> norm_num

/-- Every character-ramified or extension-ramified base prime, in one
genuine finite set, together with every place above two or three. -/
def artinBadPrimes (χ : HeckeCharacter F) : Finset (HeightOneSpectrum (𝓞 F)) :=
  ((finite_ramifiedPlaces F χ).toFinset ∪
    _root_.ramifiedBaseFinitePlaces (K := F) (L := K)) ∪ placesAboveSix F

theorem mem_artinBadPrimes_of_mem_placesAboveSix
    (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∈ placesAboveSix F) : v ∈ artinBadPrimes F K χ :=
  Finset.mem_union.mpr (Or.inr hv)

theorem unramifiedAt_of_not_mem_artinBadPrimes
    (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ artinBadPrimes F K χ) : UnramifiedAt F χ v := by
  by_contra hram
  apply hv
  apply Finset.mem_union.mpr
  apply Or.inl
  apply Finset.mem_union.mpr
  exact Or.inl ((Set.Finite.mem_toFinset (finite_ramifiedPlaces F χ)).mpr hram)

theorem chosenUnramified_of_not_mem_artinBadPrimes
    (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ artinBadPrimes F K χ) :
    _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v := by
  apply _root_.chosenFinitePlaceIsUnramified_of_isUnramifiedAt (K := F) (L := K) v
  by_contra hram
  apply hv
  apply Finset.mem_union.mpr
  apply Or.inl
  apply Finset.mem_union.mpr
  apply Or.inr
  rw [_root_.mem_ramifiedBaseFinitePlaces_iff]
  exact ⟨_root_.finitePlaceExtensionCentre (K := F) (L := K) v
      (_root_.chosenFinitePlaceExtension (L := K) v),
    _root_.finitePlaceExtensionCentre_liesOver (K := F) (L := K) v
      (_root_.chosenFinitePlaceExtension (L := K) v), hram⟩

theorem good_of_not_mem_artinBadPrimes
    (χ : HeckeCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ artinBadPrimes F K χ) :
    UnramifiedAt F χ v ∧ _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v :=
  ⟨unramifiedAt_of_not_mem_artinBadPrimes F K χ v hv,
    chosenUnramified_of_not_mem_artinBadPrimes F K χ v hv⟩

/-- The literal fibre of the actual finite-place contraction map. -/
abbrev PrimeFiber (v : HeightOneSpectrum (𝓞 F)) :=
  {w : HeightOneSpectrum (𝓞 K) // _root_.finitePlaceBelow (K := F) w = v}

theorem primeFiber_liesOver (v : HeightOneSpectrum (𝓞 F)) (W : PrimeFiber F K v) :
    W.1.asIdeal.LiesOver v.asIdeal := by
  constructor
  have h := congrArg HeightOneSpectrum.asIdeal W.2
  simpa only [_root_.finitePlaceBelow_asIdeal] using h.symm

/-- An explicit bijection with the actual ideal-theoretic fibre. -/
def primeFiberEquivPrimesOver (v : HeightOneSpectrum (𝓞 F)) :
    PrimeFiber F K v ≃ v.asIdeal.primesOver (𝓞 K) where
  toFun W := ⟨W.1.asIdeal, W.1.isPrime, primeFiber_liesOver F K v W⟩
  invFun P := by
    let W : HeightOneSpectrum (𝓞 K) :=
      { asIdeal := P.1
        isPrime := P.2.1
        ne_bot := Ideal.ne_bot_of_mem_primesOver v.ne_bot P.2 }
    refine ⟨W, ?_⟩
    apply HeightOneSpectrum.ext
    change P.1.under (𝓞 F) = v.asIdeal
    exact (P.1.over_def v.asIdeal).symm
  left_inv W := by
    apply Subtype.ext
    apply HeightOneSpectrum.ext
    rfl
  right_inv P := by
    apply Subtype.ext
    rfl

theorem natCard_primeFiber_eq_ncard_primesOver (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (PrimeFiber F K v) = (v.asIdeal.primesOver (𝓞 K)).ncard :=
  (Nat.card_congr (primeFiberEquivPrimesOver F K v)).trans (Nat.card_coe_set_eq _)

/-- The ramification-index term in the ideal fundamental identity is one
at a genuinely unramified chosen completion. -/
theorem ramificationIdxIn_eq_one_of_chosenUnramified
    (v : HeightOneSpectrum (𝓞 F))
    (hunram : _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v) :
    v.asIdeal.ramificationIdxIn (𝓞 K) = 1 := by
  let w := _root_.chosenFinitePlaceExtension (L := K) v
  let W := _root_.finitePlaceExtensionCentre (K := F) (L := K) v w
  letI : W.asIdeal.LiesOver v.asIdeal :=
    _root_.finitePlaceExtensionCentre_liesOver (K := F) (L := K) v w
  letI : IsGaloisGroup (K ≃ₐ[F] K) (𝓞 F) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (K ≃ₐ[F] K) (𝓞 F) (𝓞 K) F K
  letI : Algebra.IsUnramifiedAt (𝓞 F) W.asIdeal :=
    _root_.isUnramifiedAt_of_chosenFinitePlaceIsUnramified (K := F) (L := K) v hunram
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal W.asIdeal (K ≃ₐ[F] K)]
  exact Ideal.ramificationIdx_eq_one W.asIdeal (𝓞 F)

/-- Exact degree identity for the actual prime fibre and actual qprime.
This is derived from ideal decomposition, not a cardinality hypothesis. -/
theorem natCard_primeFiber_mul_orderOf_qprime
    (v : HeightOneSpectrum (𝓞 F))
    (hunram : _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v) :
    Nat.card (PrimeFiber F K v) * orderOf (qprime F K v) = Module.finrank F K := by
  letI : IsGaloisGroup (K ≃ₐ[F] K) (𝓞 F) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (K ≃ₐ[F] K) (𝓞 F) (𝓞 K) F K
  have horder : orderOf (qprime F K v) = v.asIdeal.inertiaDegIn (𝓞 K) :=
    (orderOf_qprime_eq_localDegree F K v hunram).trans
      (localDegree_eq_inertiaDegIn F K v hunram)
  rw [natCard_primeFiber_eq_ncard_primesOver, horder]
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    v.asIdeal (𝓞 K) (K ≃ₐ[F] K)
  rw [ramificationIdxIn_eq_one_of_chosenUnramified F K v hunram, one_mul] at h
  exact h.trans (IsGalois.card_aut_eq_finrank F K)

/-- In particular the actual Frobenius order is positive. -/
theorem orderOf_qprime_pos
    (v : HeightOneSpectrum (𝓞 F))
    (hunram : _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v) :
    0 < orderOf (qprime F K v) := by
  apply Nat.pos_of_ne_zero
  intro hz
  have h := natCard_primeFiber_mul_orderOf_qprime F K v hunram
  rw [hz, mul_zero] at h
  exact (Module.finrank_pos (R := F) (M := K)).ne' h.symm

/-- Requested exact quotient formula for the number of actual primes above v. -/
theorem natCard_primeFiber_eq_finrank_div_orderOf_qprime
    (v : HeightOneSpectrum (𝓞 F))
    (hunram : _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v) :
    Nat.card (PrimeFiber F K v) = Module.finrank F K / orderOf (qprime F K v) := by
  rw [← natCard_primeFiber_mul_orderOf_qprime F K v hunram]
  exact (Nat.mul_div_cancel _ (orderOf_qprime_pos F K v hunram)).symm

/-- Version usable under any Fintype instance on the actual prime fibre. -/
theorem card_primeFiber_eq_finrank_div_orderOf_qprime
    (v : HeightOneSpectrum (𝓞 F)) [Fintype (PrimeFiber F K v)]
    (hunram : _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v) :
    Fintype.card (PrimeFiber F K v) = Module.finrank F K / orderOf (qprime F K v) := by
  rw [← Nat.card_eq_fintype_card]
  exact natCard_primeFiber_eq_finrank_div_orderOf_qprime F K v hunram

/-- Actual ideal norm formula; extension-unramifiedness is unnecessary. -/
theorem absNorm_primeFiber (v : HeightOneSpectrum (𝓞 F)) (W : PrimeFiber F K v) :
    W.1.asIdeal.absNorm = v.asIdeal.absNorm ^ W.1.asIdeal.inertiaDeg (𝓞 F) := by
  letI := primeFiber_liesOver F K v W
  exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal W.1.asIdeal).symm

/-- The same formula in the project's literal Euler-factor residueCard. -/
theorem residueCard_primeFiber (v : HeightOneSpectrum (𝓞 F)) (W : PrimeFiber F K v) :
    residueCard K W.1 = residueCard F v ^ W.1.asIdeal.inertiaDeg (𝓞 F) :=
  absNorm_primeFiber F K v W

/-- The exponent can consequently be expressed as the actual qprime order. -/
theorem residueCard_primeFiber_eq_pow_orderOf_qprime
    (v : HeightOneSpectrum (𝓞 F)) (W : PrimeFiber F K v)
    (hunram : _root_.ChosenFinitePlaceIsUnramified (K := F) (L := K) v) :
    residueCard K W.1 = residueCard F v ^ orderOf (qprime F K v) := by
  rw [residueCard_primeFiber, orderOf_qprime_eq_inertiaDeg F K v W hunram]

end HeckeSkeleton.Descent.ArtinPrimeArithmetic
