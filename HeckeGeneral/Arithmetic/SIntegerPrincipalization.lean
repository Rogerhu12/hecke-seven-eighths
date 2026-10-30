import HeckeGeneral.Arithmetic.SIntegerLocalization
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Choose

/-!
# Principalizing the actual ring of S-integers

Every number field admits a finite set of finite primes, containing any
prescribed finite set, whose actual valuation-defined S-integer ring is a
principal ideal ring. We choose one nonzero integral ideal in each ideal
class and invert a nonzero element of each representative. Localization
then turns all those representatives into the unit ideal. Ideal-class
inverses and contraction-extension imply that every localized ideal is
principal. No class-group localization theorem, PID input, or finite
generation of S-units is assumed.

Build and declaration-audit evidence is tracked in docs/NEXT_POISSON.md.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

/-- Enlarging any finite set of finite primes yields an actual principal
S-integer ring. The integral-domain instance is inherited from `K`, so this
is a principal ideal domain in Mathlib's two-instance convention. -/
theorem exists_finite_sInteger_isPrincipalIdealRing
    (S₀ : Set (HeightOneSpectrum (𝓞 K))) (hS₀ : S₀.Finite) :
    ∃ S : Set (HeightOneSpectrum (𝓞 K)),
      S.Finite ∧ S₀ ⊆ S ∧ IsPrincipalIdealRing (S.integer K) := by
  classical
  letI : Fintype S₀ := hS₀.fintype
  -- These are actual nonzero integral ideals, one for each ideal class.
  choose J hJ using (ClassGroup.mk0_surjective (R := 𝓞 K))
  have hJbot : ∀ c : ClassGroup (𝓞 K), (J c : Ideal (𝓞 K)) ≠ ⊥ := by
    intro c
    simpa only [Ideal.zero_eq_bot] using
      (nonZeroDivisors.ne_zero (J c).property)
  choose r hrmem hrzero using fun c : ClassGroup (𝓞 K) =>
    Submodule.exists_mem_ne_zero_of_ne_bot (hJbot c)
  -- The additional factors ensure that all initially prescribed primes
  -- belong to the support of the integer being inverted.
  choose b hbmem hbzero using fun v : S₀ =>
    Submodule.exists_mem_ne_zero_of_ne_bot v.val.ne_bot
  let a : 𝓞 K := (∏ c : ClassGroup (𝓞 K), r c) * (∏ v : S₀, b v)
  have ha : a ≠ 0 := by
    apply mul_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr fun c _ => hrzero c
    · exact Finset.prod_ne_zero_iff.mpr fun v _ => hbzero v
  have hrdiv : ∀ c : ClassGroup (𝓞 K), r c ∣ a := by
    intro c
    exact (Finset.dvd_prod_of_mem r (Finset.mem_univ c)).trans
      (dvd_mul_right _ _)
  have hbdiv : ∀ v : S₀, b v ∣ a := by
    intro v
    exact (Finset.dvd_prod_of_mem b (Finset.mem_univ v)).trans
      (dvd_mul_left _ _)
  have hcontains : S₀ ⊆ integerPrimeSupport a := by
    intro v hv
    exact v.asIdeal.mem_of_dvd (hbdiv ⟨v, hv⟩) (hbmem ⟨v, hv⟩)
  let A := (integerPrimeSupport a).integer K
  letI : IsLocalization.Away a A := integerPrimeSupport_isLocalizationAway K a ha
  let f : 𝓞 K →+* A := algebraMap (𝓞 K) A
  have hJmap : ∀ c : ClassGroup (𝓞 K),
      (J c : Ideal (𝓞 K)).map f = ⊤ := by
    intro c
    apply Ideal.eq_top_of_isUnit_mem _
      (Ideal.mem_map_of_mem f (hrmem c))
    exact IsLocalization.Away.isUnit_of_dvd a (hrdiv c)
  have hprincipal : IsPrincipalIdealRing A := by
    refine ⟨fun L => ?_⟩
    let I : Ideal (𝓞 K) := L.under (𝓞 K)
    have hmapI : I.map f = L :=
      IsLocalization.map_under (Submonoid.powers a) A L
    by_cases hI : I = 0
    · rw [← hmapI, hI, Ideal.zero_eq_bot, Ideal.map_bot]
      infer_instance
    let I₀ : (Ideal (𝓞 K))⁰ := ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩
    let c : ClassGroup (𝓞 K) := (ClassGroup.mk0 I₀)⁻¹
    have hc : ClassGroup.mk0 I₀ = (ClassGroup.mk0 (J c))⁻¹ := by
      simp only [hJ, c, inv_inv]
    obtain ⟨z, _hz, hIJ⟩ := ClassGroup.mk0_eq_mk0_inv_iff.mp hc
    change I * (J c : Ideal (𝓞 K)) = Ideal.span {z} at hIJ
    have heq : I.map f = (Ideal.span ({z} : Set (𝓞 K))).map f := by
      calc
        I.map f = I.map f * (J c : Ideal (𝓞 K)).map f := by
          rw [hJmap, ← Ideal.one_eq_top, mul_one]
        _ = (I * (J c : Ideal (𝓞 K))).map f := (Ideal.map_mul f _ _).symm
        _ = (Ideal.span ({z} : Set (𝓞 K))).map f := congrArg (Ideal.map f) hIJ
    rw [← hmapI, heq]
    letI : (Ideal.span ({z} : Set (𝓞 K))).IsPrincipal := ⟨z, rfl⟩
    infer_instance
  exact ⟨integerPrimeSupport a, finite_integerPrimeSupport a ha, hcontains, hprincipal⟩

end HeckeGeneral.Arithmetic
