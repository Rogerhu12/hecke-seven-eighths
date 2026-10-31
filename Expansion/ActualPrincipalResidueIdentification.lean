import Expansion.ActualPrincipalResidueKernels

/-!
# Exact arithmetic identification of the double principal residue

The unit-ideal, trivial-sector row is specialized in the actual Euler
tables.  The complete finite-subset correction then equals the original
compensated principal correction.  The final identity cancels the actual
nonzero residue normalizer and retains the literal prime normalizer and
deleted target L-function, including their total-division values.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open HeckeSkeleton.Expansion.PrincipalRows
open HighBinVerified HighBinVerified.NormFormFullCorrection
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem actual_principal_residue_mem_region (s : ℂ) (hs : 7 / 8 < s.re) :
    (s, (1 : ℂ), (1 / 6 : ℂ)) ∈ rowEulerRegion := by
  apply principal_rectangle_mem_rowEulerRegion s 1 (1 / 6) hs.le <;> norm_num

/-- The rational local table agrees with the original normalized literal
sum at the actual principal residue; no Gauss polynomial is cancelled. -/
theorem localRowCorrection_principal_eq (P : ProbeData K S) (psi : HeckeCharacter K)
    (p : ExteriorPrime K S) (s : ℂ) (hs : 1 / 2 < s.re) :
    localRowCorrection K S P psi 1 p s 1 (1 / 6) =
      localPrincipalCorrection K S P psi p s := by
  let q : ℝ := p.val.asIdeal.absNorm
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast one_lt_primeIdeal_absNorm K p.val
  have hV : 1 - (q : ℂ)⁻¹ ≠ 0 := by
    apply one_sub_ne_zero_of_norm_lt_one
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < q)]
    exact inv_lt_one_of_one_lt₀ hq
  have hden := phaseRowEuler_denominators_ne_zero_of_re hq
    (primeCoefficient K psi p.val) (primeCoefficient K (thetaPeriod K S P psi) p.val ^ 6)
    s (1 / 6) (norm_primeCoefficient_le_one K psi p.val)
    (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_primeCoefficient_le_one K _ p.val))
    (by linarith) (by norm_num; linarith)
  have hpow : (-6 : ℂ) * (1 / 6) = -1 := by norm_num
  simp only [hpow, Complex.cpow_neg_one] at hden
  have hid := rowEulerLiteral_eq_rational (q : ℂ) (q : ℂ)⁻¹
    (q : ℂ)⁻¹ (q : ℂ)⁻¹ (primeCoefficient K psi p.val * (q : ℂ) ^ (-s))
    (primeCoefficient K (thetaPeriod K S P psi) p.val ^ 6 * (q : ℂ) ^ (4 - 6 * s) * (q : ℂ)⁻¹)
    hV hV hden.2 hden.1
  simpa only [localRowCorrection, localPrincipalCorrection, localProbeEulerSum,
    primeCoefficient_one, map_one, one_mul, mul_one, hpow, Complex.cpow_neg_one,
    q, Complex.ofReal_natCast] using hid.symm

theorem actualLocalUnmarked_principal_eq (P : ProbeData K S) (psi : HeckeCharacter K)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (p : ExteriorPrime K S) (s : ℂ) (hs : 1 / 2 < s.re) :
    actualLocalUnmarked K S P psi (physicalPrincipalRow K S) s 1 (1 / 6) p =
      localPrincipalCorrection K S P psi p s := by
  simp only [actualLocalUnmarked, localFactor, rowExceptionalPrimes, physicalPrincipalRow_support,
    Finset.union_empty, Finset.notMem_empty, dif_neg, physicalPrincipalRow_character K S P hP]
  exact localRowCorrection_principal_eq K S P psi p s hs

theorem actualLocalMarked_principal_eq (P : ProbeData K S) (psi : HeckeCharacter K)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (p : ExteriorPrime K S) (s : ℂ) (hs : 7 / 8 < s.re) :
    actualLocalMarked K S P psi (physicalPrincipalRow K S) s 1 (1 / 6) p =
      localPrincipalCorrection K S P psi p s -
        (1 - (p.val.asIdeal.absNorm : ℂ)⁻¹ * (p.val.asIdeal.absNorm : ℂ)⁻¹) /
          (1 - primeCoefficient K psi p.val * (p.val.asIdeal.absNorm : ℂ) ^ (-s)) := by
  have hphase : phaseRowEuler (p.val.asIdeal.absNorm : ℝ) 1
      (primeCoefficient K psi p.val) (primeCoefficient K (thetaPeriod K S P psi) p.val ^ 6)
      s 1 (1 / 6) = localPrincipalCorrection K S P psi p s := by
    simpa only [localRowCorrection, phaseRowEuler, primeCoefficient_one, map_one, mul_one,
      one_mul, Complex.ofReal_natCast] using localRowCorrection_principal_eq K S P psi p s (by linarith)
  unfold actualLocalMarked
  rw [localFactor_eq_explicit_rowEulerRegion K S P psi {p} (physicalPrincipalRow K S) p
    (s, 1, 1 / 6) (actual_principal_residue_mem_region s hs)]
  simp only [explicitLocalEuler, physicalPrincipalRow_support, Finset.notMem_empty, if_false,
    Finset.mem_singleton, if_true, rowW, rowD, rowE,
    physicalPrincipalRow_character K S P hP, primeCoefficient_one, map_one, mul_one, hphase,
    unmarkedZeroPart, one_mul, show (-6 : ℂ) * (1 / 6) = -1 by norm_num,
    Complex.cpow_neg_one, Complex.ofReal_natCast]

theorem actualLocalCompensation_principal_eq (P : ProbeData K S) (psi : HeckeCharacter K)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (p : ExteriorPrime K S) (s : ℂ) (hs : 7 / 8 < s.re) :
    actualLocalCompensation K S P psi (physicalPrincipalRow K S) s 1 (1 / 6) p =
      (p.val.asIdeal.absNorm : ℂ) ^ (-(5 / 6 : ℂ)) *
        localCompensatedEulerCorrection K S P psi 1 p s 1 (1 / 6) /
          localPrincipalCorrection K S P psi p s := by
  let q : ℂ := p.val.asIdeal.absNorm
  have hq : q ≠ 0 := by
    dsimp [q]
    exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one (one_lt_primeIdeal_absNorm K p.val)))
  have hV : 1 - q⁻¹ ≠ 0 := by
    apply one_sub_ne_zero_of_norm_lt_one
    rw [norm_inv]
    have hqnorm : 1 < ‖q‖ := by
      dsimp [q]
      rw [Complex.norm_natCast]
      exact_mod_cast one_lt_primeIdeal_absNorm K p.val
    exact inv_lt_one_of_one_lt₀ hqnorm
  have hqR : (1 : ℝ) < p.val.asIdeal.absNorm := by
    exact_mod_cast one_lt_primeIdeal_absNorm K p.val
  have hD : 1 - primeCoefficient K psi p.val * q ^ (-s) ≠ 0 :=
    (phaseRowEuler_denominators_ne_zero_of_re hqR
      (primeCoefficient K psi p.val) (primeCoefficient K (thetaPeriod K S P psi) p.val ^ 6)
      s (1 / 6) (norm_primeCoefficient_le_one K psi p.val)
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_primeCoefficient_le_one K _ p.val))
      (by linarith) (by norm_num; linarith)).1
  have hA : slotMarkedScalar K S psi s (1 / 6) p =
      q ^ (-(5 / 6 : ℂ)) * (conj (primeCoefficient K psi p.val) * q ^ s) := by
    unfold slotMarkedScalar
    rw [show s + (1 / 6 : ℂ) - 1 = -(5 / 6) + s by ring,
      Complex.cpow_add _ _ hq]
    ring
  have hB : slotSelectedScalar K S 1 (1 / 6) p = q ^ (-(5 / 6 : ℂ)) * q⁻¹ := by
    unfold slotSelectedScalar
    rw [show (1 / 6 : ℂ) - 1 - 1 = -(5 / 6) + -1 by ring,
      Complex.cpow_add _ _ hq, Complex.cpow_neg_one]
  rw [actualLocalCompensation, hA, hB,
    actualLocalUnmarked_principal_eq K S P psi hP p s (by linarith),
    actualLocalMarked_principal_eq K S P psi hP p s hs]
  have hid :
      conj (primeCoefficient K psi p.val) * q ^ s *
          (localPrincipalCorrection K S P psi p s -
            (1 - q⁻¹ * q⁻¹) / (1 - primeCoefficient K psi p.val * q ^ (-s))) -
        q⁻¹ * localPrincipalCorrection K S P psi p s =
      localCompensatedEulerCorrection K S P psi 1 p s 1 (1 / 6) := by
    unfold localPrincipalCorrection localCompensatedEulerCorrection localMarkedProbeEulerSum
    simp only [primeCoefficient_one, map_one, mul_one, one_mul,
      show (-6 : ℂ) * (1 / 6) = -1 by norm_num, Complex.cpow_neg_one]
    change _ = _
    dsimp only [q] at hV hD ⊢
    field_simp [hV, hD]
    <;> ring
  calc
    _ = q ^ (-(5 / 6 : ℂ)) *
        (conj (primeCoefficient K psi p.val) * q ^ s *
          (localPrincipalCorrection K S P psi p s -
            (1 - q⁻¹ * q⁻¹) / (1 - primeCoefficient K psi p.val * q ^ (-s))) -
          q⁻¹ * localPrincipalCorrection K S P psi p s) /
          localPrincipalCorrection K S P psi p s := by ring
    _ = _ := by rw [hid]

theorem actualFullCorrection_principal_eq (P : ProbeData K S) (psi : HeckeCharacter K)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) (Z : ℝ)
    (s : ℂ) (hs : 7 / 8 < s.re) :
    compensatedRowFullCorrection K S P psi (arithmeticHighEulerData K S P psi)
      g T (physicalPrincipalRow K S) Z s 1 (1 / 6) =
        compensatedPrincipalCorrection K S P psi g T Z s := by
  let H : ExteriorPrime K S → ℂ := fun p => localPrincipalCorrection K S P psi p s
  have hH : ∀ p, H p ≠ 0 := fun p => localPrincipalCorrection_ne_zero K S P psi p (by linarith)
  have hprod : HasProd H (principalCorrection K S P psi s) :=
    (multipliable_localPrincipalCorrection K S P psi (by linarith : 2 / 3 < s.re)).hasProd
  have hbase : rowCorrection K S P psi (arithmeticHighEulerData K S P psi)
      ∅ (physicalPrincipalRow K S) s 1 (1 / 6) = principalCorrection K S P psi s := by
    apply tprod_congr
    intro p
    exact actualLocalUnmarked_principal_eq K S P psi hP p s (by linarith)
  unfold compensatedRowFullCorrection compensatedPrincipalCorrection
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Fintype.mem_piFinset.mp hp
  have hinj := actual_primeWindow_tuple_injective K S g T Z p hp'
  have htuple := actual_compensation_tuple_factorization_region K S P psi g T
    (physicalPrincipalRow K S) Z s 1 (1 / 6)
    (actual_principal_residue_mem_region s hs) p hp' (fun i => by
      rw [actualLocalUnmarked_principal_eq K S P psi hP (p i) s (by linarith)]
      exact hH (p i))
  rw [htuple, hbase]
  simp_rw [actualLocalCompensation_principal_eq K S P psi hP _ s hs]
  have hdel : (∏' q, if q ∈ Finset.univ.image p then (1 : ℂ) else H q) =
      principalCorrection K S P psi s * ∏ i : Fin g.slots, (H (p i))⁻¹ := by
    have h := NormForm.markedEulerProduct_eq H (fun _ => 1)
      (principalCorrection K S P psi s) hprod (Finset.univ.image p) (fun q _ => hH q)
    have heq : (∏ q ∈ Finset.univ.image p, (1 : ℂ) / H q) =
        ∏ i : Fin g.slots, (H (p i))⁻¹ := by
      rw [Finset.prod_image hinj.injOn]
      simp only [one_div]
    simpa only [NormForm.markedEulerProduct, heq] using h
  change _ = (∏' q, if q ∈ Finset.univ.image p then (1 : ℂ) else H q) * _
  rw [hdel]
  simp only [div_eq_mul_inv, Finset.prod_mul_distrib, H]
  ring

end Expansion.Project

namespace Expansion.Project

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K Sset)]
variable [BorelSpace (sLocalNormOneGroup K Sset)]
local notation "muS" => (fun p : Sset => mu p.val)

/-- The double residue has coefficient exactly one after the actual
Poisson/Mellin normalization.  The prime and L denominators are not cancelled. -/
theorem actualPrincipal_double_residue_eq (P : ProbeData K Sset) (psi : HeckeCharacter K)
    (hP : AllowedGeneratorInput K Sset P.arithmetic)
    (hN : physicalResidueNormalizer K Sset muS P ≠ 0)
    (g : PrimeWindowGeometry) (Z : ℝ) (hZ : 0 < Z) (s : ℂ) (hs : 7 / 8 < s.re) :
    actualPrincipalZRegularPart K S mu P psi g Z s (1 / 6) *
      (deletedZetaResidue K Sset / 6) =
      actualPrincipalWeightedTerm K Sset psi Z s
        (actualNormalizedPrincipalCorrection K Sset P psi g Z s) := by
  have hZc : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hscale : ((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - 1 / 6) *
      (Z : ℂ) ^ (s + 1 / 6 - 1) =
      (Z : ℂ) ^ (s - 11 / 16) * ((Z : ℂ) ^ (1 / 36 : ℂ))⁻¹ := by
    rw [← Complex.cpow_mul_ofReal_nonneg hZ.le, ← Complex.cpow_neg,
      ← Complex.cpow_add _ _ hZc, ← Complex.cpow_add _ _ hZc]
    congr 1
    push_cast
    ring
  have hgauss : s + (1 / 6 : ℂ) - 1 = s - 5 / 6 := by ring
  have hcancel : physicalResidueNormalizer K Sset muS P *
      (physicalResidueNormalizer K Sset muS P)⁻¹ = 1 := mul_inv_cancel₀ hN
  unfold actualPrincipalZRegularPart
  rw [actualFullCorrection_principal_eq K Sset P psi hP g ∅ Z s hs]
  calc
    _ = (physicalResidueNormalizer K Sset muS P *
          (physicalResidueNormalizer K Sset muS P)⁻¹) *
        Complex.exp ((s + 1 / 6 - 1) ^ 2) *
        (((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - 1 / 6) *
          (Z : ℂ) ^ (s + 1 / 6 - 1)) *
        compensatedPrincipalCorrection K Sset P psi g ∅ Z s *
        (primeNormalizer K Sset g ∅ Z)⁻¹ *
        (heckeDeletedContinuation K psi (exceptionalPrimes K Sset) s)⁻¹ := by
      simp only [physicalResidueNormalizer, div_eq_mul_inv, mul_inv]
      ring
    _ = _ := by
      rw [hcancel, one_mul, hscale, hgauss]
      simp only [actualPrincipalWeightedTerm, actualNormalizedPrincipalCorrection,
        div_eq_mul_inv, mul_inv]
      ring

end Expansion.Project

#print axioms Expansion.Project.actualFullCorrection_principal_eq
#print axioms Expansion.Project.actualPrincipal_double_residue_eq
