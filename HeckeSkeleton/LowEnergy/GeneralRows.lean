import HeckeSkeleton.LowEnergy.ActualReflectionReindex

/-!
# Actual rows with a label and a puncture

The valuation-one primes supported on the label or puncture are frozen
with the complete powerful part.  The remaining valuation-one primes are
the moving row.  These are actual ideal factorizations, including rows
meeting the label or puncture; no coprimality of the original row with
either fixed ideal is assumed.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GeneralRows

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckePort.CenteredMomentGenerator
open HeckeSkeleton.LowEnergy.IdealRows HeckeSkeleton.LowEnergy.FrozenIdealRows
open HeckeSkeleton.LowEnergy.ActualReflection HeckeSkeleton.LowEnergy.ActualFrozenCube
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualSymbols
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def fixedSupport (label puncture : ExteriorIdeal K S) : Finset (ExteriorPrime K S) :=
  exteriorSupport K S label ∪ exteriorSupport K S puncture

def supportedRow (k label puncture : ExteriorIdeal K S) : ExteriorIdeal K S :=
  supportedExterior K S (fixedSupport K S label puncture) (exteriorResidualPart K S k)

def movingRow (k label puncture : ExteriorIdeal K S) : ExteriorIdeal K S :=
  awayExterior K S (fixedSupport K S label puncture) (exteriorResidualPart K S k)

/-- R in the paper: the full powerful part times the supported simple primes. -/
def frozenRow (k label puncture : ExteriorIdeal K S) : ExteriorIdeal K S :=
  exteriorMul K S (exteriorPowerfulPart K S k) (supportedRow K S k label puncture)

theorem moving_supported_eq (k label puncture : ExteriorIdeal K S) :
    exteriorMul K S (movingRow K S k label puncture)
      (supportedRow K S k label puncture) = exteriorResidualPart K S k := by
  apply Subtype.ext
  change awayIdeal _ (residualPart k.val) * supportedIdeal _ (residualPart k.val) =
    residualPart k.val
  rw [mul_comm]
  exact supported_away_decomposition _ _

/-- The decomposition retains every prime power of the original row. -/
theorem moving_frozenRow_eq (k label puncture : ExteriorIdeal K S) :
    exteriorMul K S (movingRow K S k label puncture)
      (frozenRow K S k label puncture) = k := by
  let T : Finset (HeightOneSpectrum (𝓞 K)) := (fixedSupport K S label puncture).image Subtype.val
  apply Subtype.ext
  change awayIdeal T (residualPart k.val) *
      (powerfulPart k.val * supportedIdeal T (residualPart k.val)) = k.val
  calc
    _ = powerfulPart k.val *
        (supportedIdeal T (residualPart k.val) * awayIdeal T (residualPart k.val)) := by
      ac_rfl
    _ = k.val := by
      rw [supported_away_decomposition, powerful_residual_decomposition]

theorem moving_frozenRow_norm (k label puncture : ExteriorIdeal K S) :
    exteriorNorm K S k = exteriorNorm K S (movingRow K S k label puncture) *
      exteriorNorm K S (frozenRow K S k label puncture) := by
  have h := congrArg (exteriorNorm K S) (moving_frozenRow_eq K S k label puncture)
  rw [exteriorNorm_mul] at h
  exact h.symm

/-- The first conductor comparison: the moving norm and the original
powerful norm fit inside the original row norm. -/
theorem moving_powerful_norm_le (k label puncture : ExteriorIdeal K S) :
    exteriorNorm K S (movingRow K S k label puncture) *
      exteriorNorm K S (exteriorPowerfulPart K S k) ≤ exteriorNorm K S k := by
  have hs : 1 ≤ exteriorNorm K S (supportedRow K S k label puncture) := by
    have hn : 1 ≤ (supportedRow K S k label puncture).val.val.absNorm :=
      Ideal.absNorm_pos_of_nonZeroDivisors (supportedRow K S k label puncture).val
    change (1 : ℝ) ≤ ((supportedRow K S k label puncture).val.val.absNorm : ℝ)
    exact_mod_cast hn
  have hf : exteriorNorm K S (exteriorPowerfulPart K S k) ≤
      exteriorNorm K S (frozenRow K S k label puncture) := by
    rw [frozenRow, exteriorNorm_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hs
      (exteriorNorm_pos K S (exteriorPowerfulPart K S k)).le
  calc
    _ ≤ exteriorNorm K S (movingRow K S k label puncture) *
        exteriorNorm K S (frozenRow K S k label puncture) :=
      mul_le_mul_of_nonneg_left hf (exteriorNorm_pos K S _).le
    _ = exteriorNorm K S k := (moving_frozenRow_norm K S k label puncture).symm

/-- Fixing R leaves an injective moving-row parametrization. -/
theorem movingRow_injective_on_fibre (label puncture R : ExteriorIdeal K S) :
    Set.InjOn (fun k => movingRow K S k label puncture)
      {k | frozenRow K S k label puncture = R} := by
  intro k hk l hl hmoving
  calc
    k = exteriorMul K S (movingRow K S k label puncture)
        (frozenRow K S k label puncture) := (moving_frozenRow_eq K S k label puncture).symm
    _ = exteriorMul K S (movingRow K S l label puncture)
        (frozenRow K S l label puncture) := by rw [hk, hl, hmoving]
    _ = l := moving_frozenRow_eq K S l label puncture

theorem movingRow_norm_le (k label puncture : ExteriorIdeal K S) {X : ℝ}
    (hcut : exteriorNorm K S k ≤ X) :
    exteriorNorm K S (movingRow K S k label puncture) ≤
      X / exteriorNorm K S (frozenRow K S k label puncture) := by
  apply (le_div_iff₀ (exteriorNorm_pos K S _)).mpr
  rw [← moving_frozenRow_norm]
  exact hcut

theorem movingRow_dvd (k label puncture : ExteriorIdeal K S) :
    (movingRow K S k label puncture).val.val ∣ k.val.val :=
  dvd_trans (awayIdeal_dvd _ (residualPart k.val)) (residualPart_dvd k.val)

theorem supportedRow_dvd (k label puncture : ExteriorIdeal K S) :
    (supportedRow K S k label puncture).val.val ∣ k.val.val :=
  dvd_trans (supportedIdeal_dvd _ (residualPart k.val)) (residualPart_dvd k.val)

theorem frozenRow_dvd (k label puncture : ExteriorIdeal K S) :
    (frozenRow K S k label puncture).val.val ∣ k.val.val := by
  have h : (movingRow K S k label puncture).val.val *
      (frozenRow K S k label puncture).val.val = k.val.val :=
    congrArg (fun I : ExteriorIdeal K S => I.val.val) (moving_frozenRow_eq K S k label puncture)
  exact ⟨(movingRow K S k label puncture).val.val, by simpa only [mul_comm] using h.symm⟩

theorem movingRow_squarefree (k label puncture : ExteriorIdeal K S) :
    Squarefree (movingRow K S k label puncture).val.val := by
  intro P hP
  exact residualPart_squarefree k.val P
    (dvd_trans hP (awayIdeal_dvd _ (residualPart k.val)))

theorem supportedRow_squarefree (k label puncture : ExteriorIdeal K S) :
    Squarefree (supportedRow K S k label puncture).val.val := by
  intro P hP
  exact residualPart_squarefree k.val P
    (dvd_trans hP (supportedIdeal_dvd _ (residualPart k.val)))

/-- Disjoint actual prime exponent supports imply ideal coprimality. -/
theorem coprime_of_exponent_disjoint (I J : (Ideal (𝓞 K))⁰)
    (h : ∀ p : HeightOneSpectrum (𝓞 K),
      primeExponents I p = 0 ∨ primeExponents J p = 0) : IsCoprime I.val J.val := by
  apply Ideal.coprime_of_no_prime_ge
  intro P hI hJ hP
  have hP0 : P ≠ ⊥ := by
    intro hz
    exact nonZeroDivisors.coe_ne_zero I (le_bot_iff.mp (hz ▸ hI))
  let p : HeightOneSpectrum (𝓞 K) := ⟨P, hP, hP0⟩
  have hi := (exponent_ne_zero_iff_dvd I p).mpr (Ideal.dvd_iff_le.mpr hI)
  have hj := (exponent_ne_zero_iff_dvd J p).mpr (Ideal.dvd_iff_le.mpr hJ)
  exact (h p).elim hi hj

theorem movingRow_frozenRow_coprime (k label puncture : ExteriorIdeal K S) :
    IsCoprime (movingRow K S k label puncture).val.val
      (frozenRow K S k label puncture).val.val := by
  apply coprime_of_exponent_disjoint
  intro p
  simp only [movingRow, frozenRow, supportedRow, awayExterior, supportedExterior,
    exteriorMul, exteriorResidualPart, exteriorPowerfulPart, primeExponents_mul,
    Finsupp.add_apply, exponent_awayIdeal, exponent_supportedIdeal,
    exponent_residualPart, exponent_powerfulPart]
  split_ifs <;> omega

theorem away_coprime_of_support_subset (F : Finset (ExteriorPrime K S))
    (I J : ExteriorIdeal K S) (hJ : exteriorSupport K S J ⊆ F) :
    IsCoprime (awayExterior K S F I).val.val J.val.val := by
  apply coprime_of_exponent_disjoint
  intro p
  by_cases hp : primeExponents J.val p = 0
  · exact Or.inr hp
  · left
    have hd : p.asIdeal ∣ J.val.val := (exponent_ne_zero_iff_dvd J.val p).mp hp
    let ep : ExteriorPrime K S := ⟨p, J.property p hd⟩
    have hep : ep ∈ F := hJ ((mem_exteriorSupport_iff K S J ep).mpr hd)
    have hf : p ∈ F.image Subtype.val := Finset.mem_image.mpr ⟨ep, hep, rfl⟩
    change primeExponents (awayIdeal (F.image Subtype.val) I.val) p = 0
    rw [exponent_awayIdeal, if_neg (not_not.mpr hf)]

theorem movingRow_label_coprime (k label puncture : ExteriorIdeal K S) :
    IsCoprime (movingRow K S k label puncture).val.val label.val.val :=
  away_coprime_of_support_subset K S (fixedSupport K S label puncture)
    (exteriorResidualPart K S k) label Finset.subset_union_left

theorem movingRow_puncture_coprime (k label puncture : ExteriorIdeal K S) :
    IsCoprime (movingRow K S k label puncture).val.val puncture.val.val :=
  away_coprime_of_support_subset K S (fixedSupport K S label puncture)
    (exteriorResidualPart K S k) puncture Finset.subset_union_right

/-- Freezing the supported simple primes does not change the powerful part. -/
theorem powerfulPart_frozenRow (k label puncture : ExteriorIdeal K S) :
    exteriorPowerfulPart K S (frozenRow K S k label puncture) =
      exteriorPowerfulPart K S k := by
  apply Subtype.ext
  apply (primeExponentEquiv (R := 𝓞 K)).injective
  ext p
  change primeExponents (powerfulPart (frozenRow K S k label puncture).val) p =
    primeExponents (powerfulPart k.val) p
  simp only [frozenRow, exteriorMul, supportedRow, supportedExterior,
    exteriorPowerfulPart, exteriorResidualPart, exponent_powerfulPart,
    primeExponents_mul, Finsupp.add_apply, exponent_supportedIdeal, exponent_residualPart]
  split_ifs <;> omega

/-- The frequency includes the full fourth power of the squarefree label. -/
def reflectedFrozen (k label puncture : ExteriorIdeal K S) : ExteriorIdeal K S :=
  exteriorMul K S (frozenRow K S k label puncture) (exteriorPower K S label 4)

theorem moving_reflectedFrozen_eq (k label puncture : ExteriorIdeal K S) :
    exteriorMul K S (movingRow K S k label puncture)
      (reflectedFrozen K S k label puncture) =
      exteriorMul K S k (exteriorPower K S label 4) := by
  have h : (movingRow K S k label puncture).val *
      (frozenRow K S k label puncture).val = k.val :=
    congrArg (fun I : ExteriorIdeal K S => I.val) (moving_frozenRow_eq K S k label puncture)
  apply Subtype.ext
  change (movingRow K S k label puncture).val *
      ((frozenRow K S k label puncture).val * label.val ^ 4) = k.val * label.val ^ 4
  rw [← mul_assoc, h]

theorem movingRow_reflectedFrozen_coprime (k label puncture : ExteriorIdeal K S) :
    IsCoprime (movingRow K S k label puncture).val.val
      (reflectedFrozen K S k label puncture).val.val :=
  (movingRow_frozenRow_coprime K S k label puncture).mul_right
    (movingRow_label_coprime K S k label puncture).pow_right

/-- The actual marked datum for every noncolliding tuple.  Squarefreeness
is needed for the puncture; the row split itself works for every label. -/
def markedDatum (k label puncture : ExteriorIdeal K S)
    (hpuncture : Squarefree puncture.val.val) (u : S.unit K)
    (marks : Finset (ExteriorPrime K S))
    (hmarks : ∀ p ∈ marks, ¬p.val.asIdeal ∣ k.val.val ∧
      ¬p.val.asIdeal ∣ label.val.val ∧ ¬p.val.asIdeal ∣ puncture.val.val) :
    MarkedDatum K S where
  moving := movingRow K S k label puncture
  frozen := reflectedFrozen K S k label puncture
  puncture := puncture
  moving_squarefree := movingRow_squarefree K S k label puncture
  puncture_squarefree := hpuncture
  moving_frozen_coprime := movingRow_reflectedFrozen_coprime K S k label puncture
  moving_puncture_coprime := movingRow_puncture_coprime K S k label puncture
  rowUnit := u
  marks := marks
  marks_coprime := by
    intro p hp
    refine ⟨fun hd => (hmarks p hp).1 (dvd_trans hd (movingRow_dvd K S k label puncture)),
      ?_, (hmarks p hp).2.2⟩
    intro hd
    rcases p.val.prime.dvd_mul.mp hd with hR | hf
    · exact (hmarks p hp).1 (dvd_trans hR (frozenRow_dvd K S k label puncture))
    · exact (hmarks p hp).2.1 (p.val.prime.dvd_of_dvd_pow hf)

theorem markedDatum_rowElement (D : ThetaArithmeticData K S)
    (k label puncture : ExteriorIdeal K S)
    (hpuncture : Squarefree puncture.val.val) (u : S.unit K)
    (marks : Finset (ExteriorPrime K S))
    (hmarks : ∀ p ∈ marks, ¬p.val.asIdeal ∣ k.val.val ∧
      ¬p.val.asIdeal ∣ label.val.val ∧ ¬p.val.asIdeal ∣ puncture.val.val) :
    rowElement K S D (markedDatum K S k label puncture hpuncture u marks hmarks) =
      (S.unitEquivUnitsInteger K u).val *
        D.generator (exteriorMul K S k (exteriorPower K S label 4)) := by
  change (S.unitEquivUnitsInteger K u).val * D.generator
      (exteriorMul K S (movingRow K S k label puncture)
        (reflectedFrozen K S k label puncture)) = _
  rw [moving_reflectedFrozen_eq]

/-- The allowed sixth-unit generator errors vanish in the actual symbol,
including at common-prime zeros. -/
theorem actualSymbol_fourth (D : ThetaArithmeticData K S)
    (hD : AllowedGeneratorInput K S D) (I label : ExteriorIdeal K S) :
    idealSymbol K S D I (D.generator (exteriorPower K S label 4)) =
      idealSymbol K S D I (D.generator label) ^ 4 := by
  have hfour : exteriorPower K S label 4 = exteriorMul K S
      (exteriorMul K S label label) (exteriorMul K S label label) := by
    apply Subtype.ext
    change label.val ^ 4 = (label.val * label.val) * (label.val * label.val)
    simpa only [pow_two] using (pow_mul label.val 2 2)
  rw [hfour]
  simp only [actualSymbol_mul_right K S D hD]
  ring

/-- The exact canonical row-label phase of the constructed marked datum. -/
theorem markedDatum_symbol (D : ThetaArithmeticData K S)
    (hD : AllowedGeneratorInput K S D) (I k label puncture : ExteriorIdeal K S)
    (hpuncture : Squarefree puncture.val.val) (u : S.unit K)
    (marks : Finset (ExteriorPrime K S))
    (hmarks : ∀ p ∈ marks, ¬p.val.asIdeal ∣ k.val.val ∧
      ¬p.val.asIdeal ∣ label.val.val ∧ ¬p.val.asIdeal ∣ puncture.val.val) :
    idealSymbol K S D I
        (rowElement K S D (markedDatum K S k label puncture hpuncture u marks hmarks)) =
      idealSymbol K S D I (S.unitEquivUnitsInteger K u).val *
        idealSymbol K S D I (D.generator k) *
        idealSymbol K S D I (D.generator label) ^ 4 := by
  rw [markedDatum_rowElement]
  change (elementSymbolHom K S D I)
    ((S.unitEquivUnitsInteger K u).val *
      D.generator (exteriorMul K S k (exteriorPower K S label 4))) = _
  rw [map_mul]
  change idealSymbol K S D I (S.unitEquivUnitsInteger K u).val *
    idealSymbol K S D I (D.generator (exteriorMul K S k (exteriorPower K S label 4))) = _
  rw [actualSymbol_mul_right K S D hD, actualSymbol_fourth K S D hD]
  ring

#print axioms moving_frozenRow_eq
#print axioms moving_frozenRow_norm
#print axioms moving_powerful_norm_le
#print axioms movingRow_injective_on_fibre
#print axioms movingRow_frozenRow_coprime
#print axioms movingRow_label_coprime
#print axioms movingRow_puncture_coprime
#print axioms powerfulPart_frozenRow
#print axioms moving_reflectedFrozen_eq
#print axioms markedDatum
#print axioms markedDatum_rowElement
#print axioms actualSymbol_fourth
#print axioms markedDatum_symbol

end HeckeSkeleton.LowEnergy.GeneralRows
