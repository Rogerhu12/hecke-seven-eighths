import ActualSexticJointChartFiber

/-! UNCOMPILED / native 0. Actual nonzero S-integer representatives of
fixed ordinary S residue fibers, and transfer of their complete joint
mean to the literal raw sextic times actual RCorrection times residual
extension. The same Mobius divisor d is used throughout. -/

noncomputable section
namespace HeckeGeneral.Characters
namespace ActualGramJointChartCoverDraft
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open ActualGramJointMeanDraft ActualGramJointChartDraft
open scoped Classical BigOperators ComplexConjugate
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6)
local notation "D" => finiteSIntegerDenominator K S
local notation "OS" => S.integer K
local notation "NZ" => NonzeroRingElements OS
local notation "MS" => sIntegerSexticSPlaceModulus K S ζ hζ

private theorem integerMap_ne_zero (z : 𝓞 K) (hz : z ≠ 0) :
    algebraMap (𝓞 K) OS z ≠ 0 := by
  intro he
  apply hz
  apply IsFractionRing.injective (𝓞 K) K
  simpa using congrArg (fun x : OS => (x : K)) he

/-- The actual exact-S denominator is a unit in the original S-integer ring. -/
def commonDenominatorUnit (M : ℕ) : OSˣ := by
  letI : IsLocalization.Away D OS := sInteger_isLocalizationAway_finiteDenominator K S
  exact ((IsLocalization.Away.algebraMap_isUnit D (S := OS)).pow M).unit

@[simp] theorem commonDenominatorUnit_val (M : ℕ) :
    (commonDenominatorUnit K S M : OS) = algebraMap (𝓞 K) OS (D ^ M) := by
  unfold commonDenominatorUnit
  rw [IsUnit.unit_spec, map_pow]

/-- Clearing data exists for every actual S-integer; it is not an input estimate. -/
theorem exists_exactS_clear (m : OS) :
    ∃ M : ℕ, ∃ z : 𝓞 K, algebraMap (𝓞 K) OS (D ^ M) * m = algebraMap (𝓞 K) OS z := by
  letI : IsLocalization.Away D OS := sInteger_isLocalizationAway_finiteDenominator K S
  exact ⟨(IsLocalization.Away.sec D m).2, (IsLocalization.Away.sec D m).1,
    by simpa only [mul_comm] using IsLocalization.Away.sec_spec D m⟩

/-- Any ordinary quotient by a nonzero ideal has a nonzero representative,
even the zero class. No residue class is discarded. -/
private theorem exists_nonzero_representative (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (q : 𝓞 K ⧸ I) : ∃ z : 𝓞 K, z ≠ 0 ∧ Ideal.Quotient.mk I z = q := by
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective q
  by_cases hzne : z ≠ 0
  · exact ⟨z, hzne, hz⟩
  · have hz0 : z = 0 := not_ne_iff.mp hzne
    obtain ⟨t, ht, htne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    refine ⟨t, htne, ?_⟩
    rw [(Ideal.Quotient.eq_zero_iff_mem).mpr ht]
    simpa only [hz0, map_zero] using hz

variable (C J : Ideal (𝓞 K)) (hC : C ≠ 0) (hJ : J ≠ 0)
variable (hCS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ C → p ∉ S)
variable (hJS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ J → p ∉ S)
local notation "P" => jointPlaces K C J hC hJ
local notation "A" => jointResidues K C J hC hJ
local notation "red" => jointReduction K S C J hC hJ hCS hJS
local instance ActualSexticChartRepresentatives_residueField (p : P) : Field (residue K C J hC hJ p) := Ideal.Quotient.field _
local instance ActualSexticChartRepresentatives_residueFintype (p : P) : Fintype (residue K C J hC hJ p) := Fintype.ofFinite _
local instance ActualSexticChartRepresentatives_fiberFintype (N : ℕ) (a : 𝓞 K ⧸ clearedSModulus K S ζ hζ N) :
    Fintype (chartFiber K S ζ hζ C J hC hJ hCS hJS N a) :=
  Fintype.ofEquiv A (chartFiberEquiv K S ζ hζ C J hC hJ hCS hJS N a).symm

/-- A concrete ordinary representative for every point of the actual period quotient. -/
def ordinaryRepresentative (N : ℕ) (q : periodQuotient K S ζ hζ C J hC hJ N) : 𝓞 K :=
  (exists_nonzero_representative K _
    (mul_ne_zero (clearedSModulus_ne_zero K S ζ hζ N)
      (jointRadical_ne_zero K C J hC hJ)) q).choose

theorem ordinaryRepresentative_spec (N : ℕ) (q : periodQuotient K S ζ hζ C J hC hJ N) :
    ordinaryRepresentative K S ζ hζ C J hC hJ N q ≠ 0 ∧
      Ideal.Quotient.mk _ (ordinaryRepresentative K S ζ hζ C J hC hJ N q) = q :=
  (exists_nonzero_representative K _
    (mul_ne_zero (clearedSModulus_ne_zero K S ζ hζ N)
      (jointRadical_ne_zero K C J hC hJ)) q).choose_spec

/-- The selected representative is the actual z/D^M in the original ring. -/
def fiberRepresentative (N M : ℕ) (a : 𝓞 K ⧸ clearedSModulus K S ζ hζ N)
    (q : chartFiber K S ζ hζ C J hC hJ hCS hJS N a) : NZ :=
  ⟨(↑(commonDenominatorUnit K S M)⁻¹ : OS) * algebraMap (𝓞 K) OS
      (ordinaryRepresentative K S ζ hζ C J hC hJ N q.val),
    mul_ne_zero (Units.ne_zero _) (integerMap_ne_zero K S _
      (ordinaryRepresentative_spec K S ζ hζ C J hC hJ N q.val).1)⟩

theorem fiberRepresentative_clear (N M : ℕ)
    (a : 𝓞 K ⧸ clearedSModulus K S ζ hζ N)
    (q : chartFiber K S ζ hζ C J hC hJ hCS hJS N a) :
    algebraMap (𝓞 K) OS (D ^ M) *
      (fiberRepresentative K S ζ hζ C J hC hJ hCS hJS N M a q).val =
    algebraMap (𝓞 K) OS (ordinaryRepresentative K S ζ hζ C J hC hJ N q.val) := by
  rw [← commonDenominatorUnit_val K S M]
  exact (commonDenominatorUnit K S M).mul_inv_cancel_left _

/-- The coordinate bijection is exactly the actual reduction of the chosen S-integer. -/
theorem scaledChartFiberEquiv_eq_representative_reduction (N M : ℕ)
    (a : 𝓞 K ⧸ clearedSModulus K S ζ hζ N)
    (q : chartFiber K S ζ hζ C J hC hJ hCS hJS N a) :
    scaledChartFiberEquiv K S ζ hζ C J hC hJ hCS hJS N M a q =
      red (fiberRepresentative K S ζ hζ C J hC hJ hCS hJS N M a q).val := by
  have he := congrArg (chartCRT K S ζ hζ C J hC hJ hCS hJS N)
    (ordinaryRepresentative_spec K S ζ hζ C J hC hJ N q.val).2
  rw [chartCRT_mk] at he
  have hs := congrArg Prod.snd he
  change denominatorScale K S C J hC hJ hCS hJS M
    (chartCRT K S ζ hζ C J hC hJ hCS hJS N q.val).2 = _
  rw [← hs]
  exact denominatorScale_eq_jointReduction K S C J hC hJ hCS hJS M _ _
    (fiberRepresentative_clear K S ζ hζ C J hC hJ hCS hJS N M a q)

/-- Fixed residue congruence for the genuinely selected ordinary representatives. -/
theorem ordinaryRepresentative_sub_mem (N : ℕ) (z₀ : 𝓞 K)
    (q : chartFiber K S ζ hζ C J hC hJ hCS hJS N (Ideal.Quotient.mk _ z₀)) :
    ordinaryRepresentative K S ζ hζ C J hC hJ N q.val - z₀ ∈
      clearedSModulus K S ζ hζ N := by
  apply Ideal.Quotient.eq.mp
  have he := congrArg (chartCRT K S ζ hζ C J hC hJ hCS hJS N)
    (ordinaryRepresentative_spec K S ζ hζ C J hC hJ N q.val).2
  rw [chartCRT_mk] at he
  exact (congrArg Prod.fst he).trans q.property

/-- Clear the same divisor and moving column separately. The deeper actual
S modulus handles every denominator of d; d is never assumed integral. -/
theorem divisorColumn_chart_of_cleared_congruence (M L : ℕ)
    (d m m₀ : NZ) (a z z₀ : 𝓞 K)
    (hd : algebraMap (𝓞 K) OS (D ^ L) * d.val = algebraMap (𝓞 K) OS a)
    (hm : algebraMap (𝓞 K) OS (D ^ M) * m.val = algebraMap (𝓞 K) OS z)
    (h₀ : algebraMap (𝓞 K) OS (D ^ M) * m₀.val = algebraMap (𝓞 K) OS z₀)
    (hz : z - z₀ ∈ clearedSModulus K S ζ hζ (M + L)) :
    divisorColumn K S d m ∈ fixedSChart K S ζ hζ (divisorColumn K S d m₀) := by
  have clear (m : NZ) (z : 𝓞 K)
      (hm : algebraMap (𝓞 K) OS (D ^ M) * m.val = algebraMap (𝓞 K) OS z) :
      algebraMap (𝓞 K) OS (D ^ (M + L)) * (divisorColumn K S d m).val =
        algebraMap (𝓞 K) OS (a * z) := by
    change algebraMap (𝓞 K) OS (D ^ (M + L)) * (d.val * m.val) = _
    calc
      _ = (algebraMap (𝓞 K) OS (D ^ L) * d.val) *
          (algebraMap (𝓞 K) OS (D ^ M) * m.val) := by
        rw [pow_add, map_mul]; ring
      _ = _ := by rw [hd, hm, map_mul]
  apply mem_fixedSChart_of_cleared_congruence K S ζ hζ
    (D ^ (M + L)) (a * z) (a * z₀)
    (pow_ne_zero _ (finiteSIntegerDenominator_ne_zero K S))
    (divisorColumn K S d m) (divisorColumn K S d m₀) (clear m z hm) (clear m₀ z₀ h₀)
  rw [← mul_sub]
  exact (clearedSModulus K S ζ hζ (M + L)).mul_mem_left a hz

end ActualGramJointChartCoverDraft
end HeckeGeneral.Characters
