import ActualProbeAmplitudeMellin
import HeckeSkeleton.ActualProbeRowFinite
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
UNCOMPILED / native 0. At fixed t, X>0 and Y>0, the original denominator
annulus gives a finite ideal envelope. Compact support of the actual tensor
and discreteness of nonzero S-integer diagonals give a common finite frequency
envelope for those ideals. This proves, rather than assumes, the ideal/row
interchange and connects the original probeIntegrand to the c=1 amplitude.
There is no interchange of frequency and Fourier integration, and no Haar
integration or Cauchy/Gram estimate in this source.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualProbeLogDraft

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramDraft
open scoped Classical BigOperators FourierTransform

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "NZ" => NonzeroRingElements (S.integer K)

/-- The literal coefficient outside the original inner row sum. -/
def probeWeightedRowTerm (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (X Y Z : ℝ)
    (t : sLocalNormOneGroup K S) (I : ExteriorIdeal K S) (m : NZ) : ℂ :=
  (Y : ℂ)⁻¹ * P.denominator.toFun (exteriorNorm K S I / Y) *
    (Real.sqrt (exteriorNorm K S I * X) : ℂ)⁻¹ *
      probeRowTerm K S P ψ Q X Z t I m

theorem probeDenominatorTerm_eq_tsum_weightedRow (P : ProbeData K S)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S)) (X Y Z : ℝ)
    (t : sLocalNormOneGroup K S) (I : ExteriorIdeal K S) :
    probeDenominatorTerm K S P ψ Q X Y Z t I =
      ∑' m : NZ, probeWeightedRowTerm K S P ψ Q X Y Z t I m := by
  unfold probeDenominatorTerm probeWeightedRowTerm
  exact tsum_mul_left.symm

theorem probeWeightedRowTerm_eq_zero_outside_idealSupport (P : ProbeData K S)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S))
    (X Y Z : ℝ) (hY : 0 < Y) (t : sLocalNormOneGroup K S)
    (I : ExteriorIdeal K S) (m : NZ)
    (hI : I ∉ additiveGramIdealSupport K S P.denominator.toSmoothAnnularTest Y) :
    probeWeightedRowTerm K S P ψ Q X Y Z t I m = 0 := by
  have hW : P.denominator.toFun (exteriorNorm K S I / Y) = 0 := by
    by_contra hW
    apply hI
    apply (mem_additiveGramIdealSupport_iff K S P.denominator.toSmoothAnnularTest Y hY I).mpr
    exact (div_le_iff₀ hY).mp (P.denominator.support hW).2
  simp only [probeWeightedRowTerm, hW, mul_zero, zero_mul]

/-- Compact tensor support supplies actual row finiteness; Z need not be positive. -/
theorem probeWeightedRowTerm_hasFiniteSupport (P : ProbeData K S)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S))
    (X Y Z : ℝ) (hX : 0 < X) (t : sLocalNormOneGroup K S)
    (I : ExteriorIdeal K S) :
    Function.HasFiniteSupport (probeWeightedRowTerm K S P ψ Q X Y Z t I) := by
  have hq : 0 < exteriorNorm K S I := by
    change (0 : ℝ) < (I.val.val.absNorm : ℝ)
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I.val
  apply (finite_additiveTest_nonzeroSInteger_row K S P.additive
    ((t : sLocalMultiplicativeGroup K S) *
      sLocalNormSection K S ⟨exteriorNorm K S I * X, mul_pos hq hX⟩)).subset
  intro m hm
  change probeWeightedRowTerm K S P ψ Q X Y Z t I m ≠ 0 at hm
  intro htest
  apply hm
  simp only [probeWeightedRowTerm, probeRowTerm, dif_pos (mul_pos hq hX),
    htest, mul_zero, zero_mul]

/-- One finite m-set works for all actual contributing denominator ideals. -/
theorem exists_probeWeightedRow_joint_support (P : ProbeData K S)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S))
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (t : sLocalNormOneGroup K S) :
    ∃ M : Finset NZ, ∀ (I : ExteriorIdeal K S) (m : NZ),
      I ∉ additiveGramIdealSupport K S P.denominator.toSmoothAnnularTest Y ∨ m ∉ M →
        probeWeightedRowTerm K S P ψ Q X Y Z t I m = 0 := by
  let E := additiveGramIdealSupport K S P.denominator.toSmoothAnnularTest Y
  have hf (I : ExteriorIdeal K S) :=
    probeWeightedRowTerm_hasFiniteSupport K S P ψ Q X Y Z hX t I
  let M : Finset NZ := E.biUnion (fun I => (hf I).toFinset)
  refine ⟨M, ?_⟩
  intro I m hIm
  rcases hIm with hI | hm
  · exact probeWeightedRowTerm_eq_zero_outside_idealSupport K S P ψ Q X Y Z hY t I m hI
  · by_cases hI : I ∈ E
    · by_contra hne
      apply hm
      apply Finset.mem_biUnion.mpr
      exact ⟨I, hI, (hf I).mem_toFinset.mpr hne⟩
    · exact probeWeightedRowTerm_eq_zero_outside_idealSupport K S P ψ Q X Y Z hY t I m hI

theorem probeWeightedRowTerm_joint_hasFiniteSupport (P : ProbeData K S)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S))
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (t : sLocalNormOneGroup K S) :
    Function.HasFiniteSupport (fun p : ExteriorIdeal K S × NZ =>
      probeWeightedRowTerm K S P ψ Q X Y Z t p.1 p.2) := by
  obtain ⟨M, hM⟩ := exists_probeWeightedRow_joint_support K S P ψ Q X Y Z hX hY t
  apply ((additiveGramIdealSupport K S P.denominator.toSmoothAnnularTest Y).product M).finite_toSet.subset
  intro p hp
  change probeWeightedRowTerm K S P ψ Q X Y Z t p.1 p.2 ≠ 0 at hp
  change p ∈ (additiveGramIdealSupport K S P.denominator.toSmoothAnnularTest Y).product M
  apply Finset.mem_product.mpr
  constructor
  · by_contra hI
    exact hp (hM p.1 p.2 (Or.inl hI))
  · by_contra hm
    exact hp (hM p.1 p.2 (Or.inr hm))

theorem summable_probeWeightedRowTerm_joint (P : ProbeData K S)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S))
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (t : sLocalNormOneGroup K S) :
    Summable (fun p : ExteriorIdeal K S × NZ =>
      probeWeightedRowTerm K S P ψ Q X Y Z t p.1 p.2) :=
  summable_of_hasFiniteSupport
    (probeWeightedRowTerm_joint_hasFiniteSupport K S P ψ Q X Y Z hX hY t)

/-- Actual ideal/frequency Fubini, justified by constructed finite joint support. -/
theorem probeIntegrand_eq_tsum_weightedRows (P : ProbeData K S)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S))
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (t : sLocalNormOneGroup K S) :
    probeIntegrand K S P ψ Q X Y Z t =
      ∑' m : NZ, ∑' I : ExteriorIdeal K S,
        probeWeightedRowTerm K S P ψ Q X Y Z t I m := by
  unfold probeIntegrand
  simp_rw [probeDenominatorTerm_eq_tsum_weightedRow]
  exact (summable_probeWeightedRowTerm_joint K S P ψ Q X Y Z hX hY t).tsum_comm.symm

/-- The original probeIntegrand is a genuine finite double sum at fixed t. -/
theorem exists_probeIntegrand_finite_frequency_expansion (P : ProbeData K S)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S))
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (t : sLocalNormOneGroup K S) :
    ∃ M : Finset NZ,
      (∀ (I : ExteriorIdeal K S) (m : NZ),
        I ∉ additiveGramIdealSupport K S P.denominator.toSmoothAnnularTest Y ∨ m ∉ M →
          probeWeightedRowTerm K S P ψ Q X Y Z t I m = 0) ∧
      probeIntegrand K S P ψ Q X Y Z t =
        ∑ m ∈ M, ∑ I ∈ additiveGramIdealSupport K S P.denominator.toSmoothAnnularTest Y,
          probeWeightedRowTerm K S P ψ Q X Y Z t I m := by
  obtain ⟨M, hM⟩ := exists_probeWeightedRow_joint_support K S P ψ Q X Y Z hX hY t
  refine ⟨M, hM, ?_⟩
  rw [probeIntegrand_eq_tsum_weightedRows K S P ψ Q X Y Z hX hY t]
  have hz (m : NZ) (hm : m ∉ M) :
      (∑' I : ExteriorIdeal K S, probeWeightedRowTerm K S P ψ Q X Y Z t I m) = 0 := by
    calc
      _ = ∑' _I : ExteriorIdeal K S, (0 : ℂ) :=
        tsum_congr (fun I => hM I m (Or.inr hm))
      _ = 0 := tsum_zero
  rw [tsum_eq_sum (s := M) hz]
  apply Finset.sum_congr rfl
  intro m hm
  exact tsum_eq_sum (fun I hI => hM I m (Or.inl hI))

/-- First actual probe-to-Am identity. The Fourier integral remains inside the
frequency sum; c=1 and the original theta coefficient are unchanged. -/
theorem probeIntegrand_eq_tsum_amplitude_integrals (P : ProbeData K S)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S))
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (t : sLocalNormOneGroup K S) :
    probeIntegrand K S P ψ Q X Y Z t =
      ∑' m : NZ,
        ((((X * Y) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∫ ξ : ℝ,
            (𝓕 (probeLogSchwartz K S P (probeColumnBasePoint K S m t X Y hX hY))) ξ *
              actualAdditiveGramAmplitude K S P (fun _ => 1)
                P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) m.val) *
          completedThetaSum K S P.arithmetic (thetaPeriod K S P ψ) m.val
            (primeSetIdeal K S ∅) Q logGaussianProfile Z := by
  rw [probeIntegrand_eq_tsum_weightedRows K S P ψ Q X Y Z hX hY t]
  apply tsum_congr
  intro m
  exact probe_row_column_eq_amplitude_integral K S P ψ Q m t X Y Z hX hY

/-- The integrated spectral rows, not their unintegrated integrands, have actual
finite support. No frequency/Fourier-integral exchange is inferred from this. -/
theorem probe_amplitude_integral_rows_hasFiniteSupport (P : ProbeData K S)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S))
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (t : sLocalNormOneGroup K S) :
    Function.HasFiniteSupport (fun m : NZ =>
      ((((X * Y) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∫ ξ : ℝ,
          (𝓕 (probeLogSchwartz K S P (probeColumnBasePoint K S m t X Y hX hY))) ξ *
            actualAdditiveGramAmplitude K S P (fun _ => 1)
              P.denominator.toSmoothAnnularTest Y (2 * Real.pi * ξ) m.val) *
        completedThetaSum K S P.arithmetic (thetaPeriod K S P ψ) m.val
          (primeSetIdeal K S ∅) Q logGaussianProfile Z) := by
  obtain ⟨M, hM⟩ := exists_probeWeightedRow_joint_support K S P ψ Q X Y Z hX hY t
  apply M.finite_toSet.subset
  intro m hm
  by_contra hnot
  apply hm
  have hz :
      (∑' I : ExteriorIdeal K S, probeWeightedRowTerm K S P ψ Q X Y Z t I m) = 0 := by
    calc
      _ = ∑' _I : ExteriorIdeal K S, (0 : ℂ) :=
        tsum_congr (fun I => hM I m (Or.inr hnot))
      _ = 0 := tsum_zero
  exact (probe_row_column_eq_amplitude_integral K S P ψ Q m t X Y Z hX hY).symm.trans hz

end HeckeGeneral.ThetaSkeleton.Physical.ActualProbeLogDraft
