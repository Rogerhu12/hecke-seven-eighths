import HeckeGeneral.Arithmetic.SIntegerIntegralNorm
import HeckeGeneral.Arithmetic.SIntegerModulus

/-!
# Actual S-integer modulus cardinality and product norm

Clearing denominators multiplies an S-integer by a genuine S-unit. It
preserves both its principal ideal and its actual S-local product norm.
The ordinary integral case then identifies the residue cardinality with
that product norm. No principal-ideal assumption on the ordinary integer
ring or replacement of the original finite set is used.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- One actual S-unit clears the denominators while preserving the principal
modulus. The returned unit is in the original S-unit group. -/
theorem exists_integer_sUnit_modulus_representative
    (c : S.integer K) (hc : c ≠ 0) :
    ∃ d : 𝓞 K, ∃ hd : d ≠ 0, ∃ u : S.unit K,
      (d : K) = ((u : Kˣ) : K) * (c : K) ∧
      Ideal.span ({algebraMap (𝓞 K) (S.integer K) d} : Set (S.integer K)) =
        Ideal.span ({c} : Set (S.integer K)) := by
  letI := sInteger_isLocalizationAway_finiteDenominator K S
  obtain ⟨⟨d, m⟩, hm⟩ :=
    IsLocalization.surj (Submonoid.powers (finiteSIntegerDenominator K S)) c
  obtain ⟨u, hu⟩ := IsLocalization.map_units (S.integer K) m
  rw [← hu] at hm
  have hd : d ≠ 0 := by
    intro hd
    rw [hd, map_zero] at hm
    exact (mul_ne_zero hc u.ne_zero) hm
  refine ⟨d, hd, (S.unitEquivUnitsInteger K).symm u, ?_, ?_⟩
  · have hfield : (d : K) = (c : K) * ((u : S.integer K) : K) :=
      congrArg (fun z : S.integer K => (z : K)) hm.symm
    exact hfield.trans (mul_comm _ _)
  · rw [← hm]
    exact Ideal.span_singleton_mul_right_unit u.isUnit c

/-- The cardinality of the genuine principal residue ring is the original
S-local arithmetic norm of the modulus, including all denominator factors. -/
theorem natCard_sIntegerPrincipalResidue_eq_productNorm
    (c : S.integer K) (hc : c ≠ 0) :
    (Nat.card (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) : ℝ) =
      (sIntegerElementNorm K S ⟨c, hc⟩).val := by
  obtain ⟨d, hd, u, hfield, hspan⟩ :=
    exists_integer_sUnit_modulus_representative K S c hc
  have hdS : algebraMap (𝓞 K) (S.integer K) d ≠ 0 := by
    intro h
    apply hd
    apply RingOfIntegers.coe_injective
    exact congrArg (fun z : S.integer K => (z : K)) h
  let dS : NonzeroRingElements (S.integer K) :=
    ⟨algebraMap (𝓞 K) (S.integer K) d, hdS⟩
  let I := nonzeroIntegralPrincipalIdeal K d hd
  have hmap : I.val.map (algebraMap (𝓞 K) (S.integer K)) =
      Ideal.span ({c} : Set (S.integer K)) := by
    change (Ideal.span ({d} : Set (𝓞 K))).map (algebraMap (𝓞 K) (S.integer K)) = _
    rw [Ideal.map_span, Set.image_singleton]
    exact hspan
  have hcontraction : sIntegerModulusContraction K S c =
      (outsideSIdeal K S I).val := by
    unfold sIntegerModulusContraction
    rw [← hmap]
    exact under_map_ideal_eq_outsideSIdeal K S I
  have hnorm : (sIntegerElementNorm K S dS).val =
      (sIntegerElementNorm K S ⟨c, hc⟩).val := by
    change sLocalProductNorm K S (sLocalNonzeroIntegerDiagonal K S dS) = _
    rw [sLocalNonzeroIntegerDiagonal_eq_of_unit_mul K S dS ⟨c, hc⟩ u hfield.symm]
    exact sLocalProductNorm_diagonal_mul K S u _
  have hintegral : (sIntegerElementNorm K S dS).val =
      ((outsideSIdeal K S I).val.absNorm : ℝ) := by
    change mixedEmbedding.norm (mixedEmbedding K (d : K)) *
      (∏ v : S, ‖FinitePlace.embedding v.val (d : K)‖) = _
    exact sLocalProductNorm_integral_eq_absNorm_outsideSIdeal K S d hd
  rw [natCard_sIntegerPrincipalResidue K S c hc, hcontraction]
  exact hintegral.symm.trans hnorm

/-- Nonzero S-integers have arithmetic norm at least one because the actual
finite residue ring is nonempty. -/
theorem one_le_sIntegerElementNorm (c : NonzeroRingElements (S.integer K)) :
    1 ≤ (sIntegerElementNorm K S c).val := by
  letI := finite_sIntegerPrincipalResidue K S c.val c.property
  rw [← natCard_sIntegerPrincipalResidue_eq_productNorm K S c.val c.property]
  exact_mod_cast (Nat.succ_le_of_lt
    (Nat.card_pos (α := S.integer K ⧸ Ideal.span ({c.val} : Set (S.integer K)))))

end HeckeGeneral.Arithmetic
