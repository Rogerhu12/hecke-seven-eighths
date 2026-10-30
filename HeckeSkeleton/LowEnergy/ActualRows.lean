import HeckeGeneral.Analysis.ActualSIntegerAmplifierRows
import HeckeGeneral.Analysis.PhysicalProbeData
import HeckeGeneral.Characters.SIntegerSexticPowerMask

/-!
# Actual row dictionary for the low marked energy

This file uses the literal `ExteriorIdeal`, chosen generator, whole-index
completed sum, and original sixth-power S-unit quotient.  It constructs a
canonical bijection from ALL exterior ideals and ALL original unit sectors
to actual rows, proves exact row-norm reindexing, and removes whole-index
mark collisions on the primal side.  No energy estimate is assumed here.

The transitive project dependencies are not all included in LOW_ENERGY.zip;
this project adapter must be checked in the complete project.  The separate
Mathlib-only assembly modules have their own compilation records.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.ActualRows

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.ActualSIntegerMoments
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "NZ" => NonzeroRingElements (S.integer K)
local notation "Orb" => ActualSIntegerOrbit K S

/-- The original orbit contraction is an exterior ideal.  This uses the
actual contraction directly and does not pass through a sixth-free row or
its amplifier decomposition. -/
def orbitExteriorIdeal (q : Orb) : ExteriorIdeal K S :=
  ⟨actualSIntegerOrbitIdeal K S q, by
    refine Quotient.inductionOn q ?_
    intro a p hp hpin
    have hcop := sIntegerModulusContraction_coprime K S a.val a.property p hpin
    have hle := Ideal.dvd_iff_le.mp hp
    exact p.isPrime.ne_top ((sup_of_le_right hle).symm.trans hcop)⟩

/-- Invariance under the original global S-units raised to the sixth power. -/
def SixthInvariant (f : S.integer K → ℂ) : Prop :=
  ∀ (u : S.unit K) (a : S.integer K),
    f ((S.unitEquivUnitsInteger K u).val ^ 6 * a) = f a

/-- The two representatives belong to one actual sixth-unit orbit. -/
theorem value_eq_of_orbit_eq (f : S.integer K → ℂ) (hf : SixthInvariant K S f)
    (a b : NZ) (hab : (Quotient.mk _ a : Orb) = Quotient.mk _ b) :
    f a.val = f b.val := by
  obtain ⟨γ, hγ⟩ := (sIntegerOrbitRelation_iff K S (sixthPowerSUnitSubgroup K S)
    a b).mp (Quotient.exact hab)
  have heq : (S.unitEquivUnitsInteger K γ.val).val * b.val = a.val := Subtype.ext hγ
  obtain ⟨u, hu⟩ := γ.property
  change u ^ 6 = γ.val at hu
  rw [← hu, map_pow, Units.val_pow_eq_pow_val] at heq
  rw [← heq]
  exact hf u b.val

/-- The literal ideal-sector representative uses `generator I`, not just
`generator (sixthFree I) * generator (sixthAmplifier I)^6`. -/
def idealSectorElement (D : ThetaArithmeticData K S)
    (x : ExteriorIdeal K S × SixthUnitClasses K S) : NZ :=
  ⟨(S.unitEquivUnitsInteger K (Quotient.out x.2)).val * D.generator x.1,
    mul_ne_zero (Units.ne_zero _) (D.generator_ne_zero x.1)⟩

def idealSectorOrbit (D : ThetaArithmeticData K S)
    (x : ExteriorIdeal K S × SixthUnitClasses K S) : Orb :=
  Quotient.mk _ (idealSectorElement K S D x)

/-- Contraction recovers the complete exterior ideal exactly. -/
theorem idealSectorOrbit_contraction (D : ThetaArithmeticData K S)
    (x : ExteriorIdeal K S × SixthUnitClasses K S) :
    actualSIntegerOrbitContraction K S (idealSectorOrbit K S D x) = x.1.val.val := by
  change sIntegerModulusContraction K S
    ((S.unitEquivUnitsInteger K (Quotient.out x.2)).val * D.generator x.1) = _
  unfold sIntegerModulusContraction
  rw [Ideal.span_singleton_mul_left_unit
    (S.unitEquivUnitsInteger K (Quotient.out x.2)).isUnit]
  exact contraction_thetaGenerator K S D x.1

theorem idealSectorOrbit_ideal (D : ThetaArithmeticData K S)
    (x : ExteriorIdeal K S × SixthUnitClasses K S) :
    actualSIntegerOrbitIdeal K S (idealSectorOrbit K S D x) = x.1.val :=
  Subtype.ext (idealSectorOrbit_contraction K S D x)

/-- No bounded representative is substituted for the actual orbit norm. -/
theorem idealSectorOrbit_norm (D : ThetaArithmeticData K S)
    (x : ExteriorIdeal K S × SixthUnitClasses K S) :
    actualSIntegerOrbitNorm K S (idealSectorOrbit K S D x) = exteriorNorm K S x.1 := by
  rw [actualSIntegerOrbitNorm_eq_absNorm_contraction, idealSectorOrbit_contraction]
  rfl

/-- The complete ideal and the original sixth-unit sector are both recovered. -/
theorem idealSectorOrbit_injective (D : ThetaArithmeticData K S) :
    Function.Injective (idealSectorOrbit K S D) := by
  intro x y hxy
  have hI : x.1 = y.1 := by
    apply Subtype.ext
    have h := congrArg (actualSIntegerOrbitIdeal K S) hxy
    simpa only [idealSectorOrbit_ideal] using h
  obtain ⟨γ, hγ⟩ := (sIntegerOrbitRelation_iff K S (sixthPowerSUnitSubgroup K S)
    (idealSectorElement K S D x) (idealSectorElement K S D y)).mp (Quotient.exact hxy)
  have hg : (D.generator y.1 : K) ≠ 0 := by
    intro hz
    exact D.generator_ne_zero y.1 (Subtype.ext hz)
  have he : γ.val * Quotient.out y.2 = Quotient.out x.2 := by
    apply Subtype.ext
    apply Units.ext
    apply mul_right_cancel₀ hg
    change (((γ.val : Kˣ) : K) * (((Quotient.out y.2 : S.unit K) : Kˣ) : K)) *
        (D.generator y.1 : K) =
      (((Quotient.out x.2 : S.unit K) : Kˣ) : K) * (D.generator y.1 : K)
    change ((γ.val : Kˣ) : K) *
        ((((Quotient.out y.2 : S.unit K) : Kˣ) : K) * (D.generator y.1 : K)) =
      (((Quotient.out x.2 : S.unit K) : Kˣ) : K) * (D.generator x.1 : K) at hγ
    rw [hI] at hγ
    exact (mul_assoc _ _ _).trans hγ
  have hq : QuotientGroup.mk' (sixthPowerSUnitSubgroup K S) (Quotient.out y.2) =
      QuotientGroup.mk' (sixthPowerSUnitSubgroup K S) (Quotient.out x.2) := by
    apply (QuotientGroup.mk'_eq_mk' (sixthPowerSUnitSubgroup K S)).mpr
    exact ⟨γ.val, γ.property, (mul_comm _ _).trans he⟩
  have hqx : QuotientGroup.mk' (sixthPowerSUnitSubgroup K S) (Quotient.out x.2) = x.2 :=
    Quotient.out_eq x.2
  have hqy : QuotientGroup.mk' (sixthPowerSUnitSubgroup K S) (Quotient.out y.2) = y.2 :=
    Quotient.out_eq y.2
  exact Prod.ext hI (hqx.symm.trans (hq.symm.trans hqy))

/-- Every actual row occurs; no sixth-power descendant or unit sector is omitted. -/
theorem idealSectorOrbit_surjective (D : ThetaArithmeticData K S) :
    Function.Surjective (idealSectorOrbit K S D) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro a
  let I := orbitExteriorIdeal K S (Quotient.mk _ a)
  have hspan : Ideal.span ({D.generator I} : Set (S.integer K)) =
      Ideal.span ({a.val} : Set (S.integer K)) := by
    rw [D.generator_span]
    change (sIntegerModulusContraction K S a.val).map
      (algebraMap (𝓞 K) (S.integer K)) = _
    exact map_sIntegerModulusContraction K S a.val
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  let u : S.unit K := (S.unitEquivUnitsInteger K).symm v
  let ξ : SixthUnitClasses K S := QuotientGroup.mk' (sixthPowerSUnitSubgroup K S) u
  have hξ : QuotientGroup.mk' (sixthPowerSUnitSubgroup K S) (Quotient.out ξ) =
      QuotientGroup.mk' (sixthPowerSUnitSubgroup K S) u := Quotient.out_eq ξ
  obtain ⟨γ, hγ, hγu⟩ :=
    (QuotientGroup.mk'_eq_mk' (sixthPowerSUnitSubgroup K S)).mp hξ
  refine ⟨(I, ξ), ?_⟩
  symm
  apply Quotient.sound
  apply (sIntegerOrbitRelation_iff K S (sixthPowerSUnitSubgroup K S) _ _).mpr
  refine ⟨⟨γ, hγ⟩, ?_⟩
  have huv : S.unitEquivUnitsInteger K u = v :=
    (S.unitEquivUnitsInteger K).apply_symm_apply v
  have hfield : (D.generator I : K) * (((u : Kˣ) : K)) = (a.val : K) := by
    have h := congrArg (fun z : S.integer K => (z : K)) hv
    rw [← huv] at h
    exact h
  have hγfield : (((Quotient.out ξ : S.unit K) : Kˣ) : K) *
      ((γ : Kˣ) : K) = ((u : Kˣ) : K) :=
    congrArg (fun z : S.unit K => ((z : Kˣ) : K)) hγu
  change ((γ : Kˣ) : K) *
      ((((Quotient.out ξ : S.unit K) : Kˣ) : K) * (D.generator I : K)) = (a.val : K)
  calc
    _ = (D.generator I : K) *
        ((((Quotient.out ξ : S.unit K) : Kˣ) : K) * ((γ : Kˣ) : K)) := by ring
    _ = (D.generator I : K) * ((u : Kˣ) : K) := by rw [hγfield]
    _ = _ := hfield

/-- Complete actual ideal/sector reindexing with the literal chosen generator. -/
def idealSectorsEquivOrbits (D : ThetaArithmeticData K S) :
    (ExteriorIdeal K S × SixthUnitClasses K S) ≃ Orb :=
  Equiv.ofBijective (idealSectorOrbit K S D)
    ⟨idealSectorOrbit_injective K S D, idealSectorOrbit_surjective K S D⟩

/-- Evaluation at `Quotient.out` agrees with the canonical representative
once the original sixth-power invariance has actually been established. -/
theorem idealSectorOrbit_out_value (D : ThetaArithmeticData K S)
    (f : S.integer K → ℂ) (hf : SixthInvariant K S f)
    (x : ExteriorIdeal K S × SixthUnitClasses K S) :
    f (idealSectorOrbit K S D x).out.val = f (idealSectorElement K S D x).val :=
  value_eq_of_orbit_eq K S f hf _ _ (Quotient.out_eq (idealSectorOrbit K S D x))

/-- Exact energy identity: the orbital cutoff becomes the complete ideal norm
cutoff, and every original sixth-unit sector remains inside the sum. -/
theorem orbital_energy_eq_ideal_sector_energy (D : ThetaArithmeticData K S)
    (f : S.integer K → ℂ) (hf : SixthInvariant K S f) (R : ℝ) :
    (∑' q : Orb, if actualSIntegerOrbitNorm K S q ≤ R then ‖f q.out.val‖ ^ 2 else 0) =
      ∑' x : ExteriorIdeal K S × SixthUnitClasses K S,
        if exteriorNorm K S x.1 ≤ R then ‖f (idealSectorElement K S D x).val‖ ^ 2
        else 0 := by
  rw [← (idealSectorsEquivOrbits K S D).tsum_eq
    (fun q : Orb => if actualSIntegerOrbitNorm K S q ≤ R then ‖f q.out.val‖ ^ 2 else 0)]
  apply tsum_congr
  intro x
  change (if actualSIntegerOrbitNorm K S (idealSectorOrbit K S D x) ≤ R
    then ‖f (idealSectorOrbit K S D x).out.val‖ ^ 2 else 0) = _
  rw [idealSectorOrbit_norm, idealSectorOrbit_out_value K S D f hf]

/-- This invariance holds for any test function and any scale; it uses no
reflection or convergence argument. -/
theorem completedThetaSum_sixthInvariant (D : ThetaArithmeticData K S)
    (θ : HeckeCharacter K) (r : ExteriorIdeal K S) (Q : Finset (ExteriorPrime K S))
    (V : ℝ → ℂ) (X : ℝ) :
    SixthInvariant K S (fun m => completedThetaSum K S D θ m r Q V X) := by
  intro u m
  apply tsum_congr
  intro cn
  simp only [completedTerm, idealSymbol,
    sIntegerSexticIdealEvaluation_mul_sixth_power_unit]

/-- A common prime is a genuine zero of the actual denominator symbol,
including when its exponent is divisible by six. -/
theorem idealSymbol_eq_zero_of_common_prime (D : ThetaArithmeticData K S)
    (A : ExteriorIdeal K S) (m : S.integer K) (p : ExteriorPrime K S)
    (hpA : p.val.asIdeal ∣ A.val.val)
    (hpm : p.val.asIdeal ∣ sIntegerModulusContraction K S m) :
    idealSymbol K S D A m = 0 := by
  apply sIntegerSexticIdealEvaluation_eq_zero_of_badPrime K S D.root6 D.primitive6
    D.embedding A.val.val (nonZeroDivisors.coe_ne_zero A.val) A.property
    (fun q hq => D.away_six q (A.property q hq)) m p.val hpA
  exact (sIntegerSexticResidueMap_eq_zero_iff_dvd_contraction
    K S p.val (A.property p.val hpA) m).mpr hpm

/-- Whole-index marks, not just marks of the squarefree column: an overlap
with the row kills the literal primal term.  The cube may share primes with c. -/
theorem completedTerm_eq_zero_of_mark_overlap (D : ThetaArithmeticData K S)
    (θ : HeckeCharacter K) (m : S.integer K) (r : ExteriorIdeal K S)
    (Q : Finset (ExteriorPrime K S)) (V : ℝ → ℂ) (X : ℝ)
    (p : ExteriorPrime K S) (hpQ : p ∈ Q)
    (hpm : p.val.asIdeal ∣ sIntegerModulusContraction K S m)
    (cn : ExteriorIdeal K S × ExteriorIdeal K S) :
    completedTerm K S D θ m r Q V X cn = 0 := by
  unfold completedTerm
  split_ifs with h
  · have hpA := h.2.2 p hpQ
    rw [idealSymbol_eq_zero_of_common_prime K S D _ m p hpA hpm]
    simp
  · rfl

/-- A colliding marked tuple is removed before invoking the reflection formula. -/
theorem completedThetaSum_eq_zero_of_mark_overlap (D : ThetaArithmeticData K S)
    (θ : HeckeCharacter K) (m : S.integer K) (r : ExteriorIdeal K S)
    (Q : Finset (ExteriorPrime K S)) (V : ℝ → ℂ) (X : ℝ)
    (p : ExteriorPrime K S) (hpQ : p ∈ Q)
    (hpm : p.val.asIdeal ∣ sIntegerModulusContraction K S m) :
    completedThetaSum K S D θ m r Q V X = 0 := by
  apply tsum_eq_zero
  intro cn
  exact completedTerm_eq_zero_of_mark_overlap K S D θ m r Q V X p hpQ hpm cn

/-- Literal completed marked row, generalized only by making the test explicit.
At `V = logGaussianProfile` this is definitionally the row in LowCauchy. -/
def markedRowWithTest (P : ProbeData K S) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z : ℝ) (p : Fin g.slots → ExteriorPrime K S)
    (J : Finset (Fin g.slots)) (V : ℝ → ℂ) (m : S.integer K) : ℂ :=
  ∑ p' ∈ Fintype.piFinset (fun i => primeWindow K S g T Z i),
    if ∀ i ∈ J, p' i = p i then
      (∏ i ∈ Finset.univ \ J, windowWeight K S g Z i (p' i)) *
      conj (heckeIdealCoefficient K ψ (subsetPrimeIdeal K S p' (Finset.univ \ J)).val) *
      completedThetaSum K S P.arithmetic (thetaPeriod K S P ψ) m
        (primeSetIdeal K S ∅) ((Finset.univ \ J).image p') V
        (Z * exteriorNorm K S (subsetPrimeIdeal K S p' (Finset.univ \ J)))
    else 0

theorem markedRowWithTest_sixthInvariant (P : ProbeData K S) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z : ℝ) (p : Fin g.slots → ExteriorPrime K S)
    (J : Finset (Fin g.slots)) (V : ℝ → ℂ) :
    SixthInvariant K S (markedRowWithTest K S P ψ g T Z p J V) := by
  intro u m
  apply Finset.sum_congr rfl
  intro p' _
  split_ifs
  · rw [completedThetaSum_sixthInvariant K S P.arithmetic (thetaPeriod K S P ψ)
      (primeSetIdeal K S ∅) ((Finset.univ \ J).image p') V
      (Z * exteriorNorm K S (subsetPrimeIdeal K S p' (Finset.univ \ J))) u m]
  · rfl

/-- Exact transport of the actual marked-row energy at any real cutoff. -/
theorem marked_energy_eq_ideal_sector_energy (P : ProbeData K S) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (Z : ℝ) (p : Fin g.slots → ExteriorPrime K S)
    (J : Finset (Fin g.slots)) (V : ℝ → ℂ) (R : ℝ) :
    (∑' q : Orb, if actualSIntegerOrbitNorm K S q ≤ R then
        ‖markedRowWithTest K S P ψ g T Z p J V q.out.val‖ ^ 2 else 0) =
      ∑' x : ExteriorIdeal K S × SixthUnitClasses K S,
        if exteriorNorm K S x.1 ≤ R then
          ‖markedRowWithTest K S P ψ g T Z p J V
            (idealSectorElement K S P.arithmetic x).val‖ ^ 2 else 0 :=
  orbital_energy_eq_ideal_sector_energy K S P.arithmetic _
    (markedRowWithTest_sixthInvariant K S P ψ g T Z p J V) R

end HeckeSkeleton.LowEnergy.ActualRows
