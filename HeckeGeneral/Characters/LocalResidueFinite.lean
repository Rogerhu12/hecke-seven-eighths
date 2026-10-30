import HeckeGeneral.Characters.PrincipalUnits

/-!
# The finite residue rings of a number-field completion

Global integers approximate every local integer to arbitrary positive valuation
depth. This constructs the residue-ring isomorphism with `𝓞 K / v^n` and proves
finiteness; no local compactness or finite-residue-field hypothesis is supplied.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

theorem localInteger_norm_le_one (v : HeightOneSpectrum (𝓞 K))
    (x : LocalIntegerRing K v) : ‖(x : v.adicCompletion K)‖ ≤ 1 := by
  have h := (localNorm_le_inv_residueCard_pow_iff K v (x : v.adicCompletion K) 0).mpr
    (by simpa only [Int.natCast_zero, neg_zero, WithZero.exp_zero] using
      (show Valued.v (x : v.adicCompletion K) ≤ 1 from x.property))
  simpa using h

/-- A global integer approximates a local integer to any prescribed integer depth. -/
theorem exists_globalInteger_close (v : HeightOneSpectrum (𝓞 K))
    (x : LocalIntegerRing K v) (n : ℕ) :
    ∃ r : 𝓞 K, ‖((algebraMap (𝓞 K) (LocalIntegerRing K v) r : LocalIntegerRing K v) :
      v.adicCompletion K) - (x : v.adicCompletion K)‖ < (residueCard K v : ℝ)⁻¹ ^ n := by
  have hq : (1 : ℝ) < residueCard K v := by exact_mod_cast one_lt_residueCard K v
  have hq0 : (0 : ℝ) < residueCard K v := zero_lt_one.trans hq
  have hδpos : 0 < (residueCard K v : ℝ)⁻¹ ^ n := pow_pos (inv_pos.mpr hq0) n
  have hδle : (residueCard K v : ℝ)⁻¹ ^ n ≤ 1 :=
    pow_le_one₀ (inv_nonneg.mpr hq0.le) (inv_lt_one_of_one_lt₀ hq).le
  obtain ⟨a, ha⟩ := (v.denseRange_algebraMap K).exists_dist_lt (x : v.adicCompletion K) hδpos
  have ha' : ‖algebraMap K (v.adicCompletion K) a - (x : v.adicCompletion K)‖ <
      (residueCard K v : ℝ)⁻¹ ^ n := by simpa [dist_eq_norm, norm_sub_rev] using ha
  have hna : ‖algebraMap K (v.adicCompletion K) a‖ ≤ 1 := by
    calc
      _ = ‖(algebraMap K (v.adicCompletion K) a - (x : v.adicCompletion K)) + x‖ := by
        rw [sub_add_cancel]
      _ ≤ max ‖algebraMap K (v.adicCompletion K) a - (x : v.adicCompletion K)‖
          ‖(x : v.adicCompletion K)‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le (ha'.le.trans hδle) (localInteger_norm_le_one K v x)
  have hva : v.valuation K a ≤ 1 := by
    have h := (localNorm_le_inv_residueCard_pow_iff K v
      (algebraMap K (v.adicCompletion K) a) 0).mp (by simpa using hna)
    change Valued.v (a : v.adicCompletion K) ≤ 1 at h
    rwa [valuedAdicCompletion_eq_valuation'] at h
  obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer hva
    (Units.mk0 (WithZero.exp (-(n : ℤ))) WithZero.exp_ne_zero)
  have hr' : ‖algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K r - a)‖ <
      (residueCard K v : ℝ)⁻¹ ^ n := by
    apply (localNorm_lt_inv_residueCard_pow_iff K v _ n).mpr
    change Valued.v ((algebraMap (𝓞 K) K r - a : K) : v.adicCompletion K) < _
    rw [valuedAdicCompletion_eq_valuation']
    exact hr
  refine ⟨r, ?_⟩
  have heq : ((algebraMap (𝓞 K) (LocalIntegerRing K v) r : LocalIntegerRing K v) :
      v.adicCompletion K) - (x : v.adicCompletion K) =
      algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K r - a) +
        (algebraMap K (v.adicCompletion K) a - (x : v.adicCompletion K)) := by
    change algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K r) -
      (x : v.adicCompletion K) = _
    rw [map_sub]
    ring
  rw [heq]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hr' ha')

def globalToLocalResidue (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    𝓞 K →+* LocalResidueRing K v n :=
  (Ideal.Quotient.mk (localMaximalIdeal K v ^ n)).comp
    (algebraMap (𝓞 K) (LocalIntegerRing K v))

theorem globalToLocalResidue_surjective (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Function.Surjective (globalToLocalResidue K v n) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨r, hr⟩ := exists_globalInteger_close K v x n
  refine ⟨r, ?_⟩
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  apply (local_mem_maximalIdeal_pow_iff_norm K v _ n).mpr
  exact hr.le

theorem globalToLocalResidue_eq_zero_iff (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (r : 𝓞 K) : globalToLocalResidue K v n r = 0 ↔ r ∈ v.asIdeal ^ n := by
  change Ideal.Quotient.mk (localMaximalIdeal K v ^ n)
    (algebraMap (𝓞 K) (LocalIntegerRing K v) r) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change algebraMap (𝓞 K) (v.adicCompletionIntegers K) r ∈
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n ↔ _
  rw [local_mem_maximalIdeal_pow_iff_valuation]
  change Valued.v ((algebraMap (𝓞 K) K r : K) : v.adicCompletion K) ≤ _ ↔ _
  rw [valuedAdicCompletion_eq_valuation', valuation_of_algebraMap]
  exact v.intValuation_le_pow_iff_mem r n

theorem globalToLocalResidue_ker (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    RingHom.ker (globalToLocalResidue K v n) = v.asIdeal ^ n := by
  ext r
  exact globalToLocalResidue_eq_zero_iff K v n r

/-- Completion does not change the residue ring at any finite depth. -/
def localResidueRingEquivGlobal (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (𝓞 K ⧸ v.asIdeal ^ n) ≃+* LocalResidueRing K v n :=
  (Ideal.quotEquivOfEq (globalToLocalResidue_ker K v n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (globalToLocalResidue_surjective K v n))

instance finite_localResidueRing (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Finite (LocalResidueRing K v n) := by
  have hne : v.asIdeal ^ n ≠ ⊥ := pow_ne_zero n v.ne_bot
  have : Finite (𝓞 K ⧸ v.asIdeal ^ n) := Ring.HasFiniteQuotients.finiteQuotient hne
  exact Finite.of_equiv (𝓞 K ⧸ v.asIdeal ^ n) (localResidueRingEquivGlobal K v n).toEquiv

instance finite_localResidueUnits (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Finite (LocalResidueRing K v n)ˣ := inferInstance

instance finite_principalUnitsQuotient (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Finite ((LocalIntegerRing K v)ˣ ⧸ principalUnits K v n) :=
  Finite.of_equiv (LocalResidueRing K v n)ˣ (principalUnitsQuotientEquiv K v n).symm.toEquiv

end HeckeGeneral.Characters
