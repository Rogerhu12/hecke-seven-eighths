import ActualSIntegerDivisorColumn
import ActualSexticFixedSChart
import ActualSexticResidueJointMean

/-! UNCOMPILED / native 0. Representative-wise bridge from the literal
raw sextic times actual RCorrection, on genuine fixed S charts, to the
previous finite joint coefficient. The same divisor enters both columns;
the residual frequency remains k. No post-Mobius coprimality is imposed.
The residual factor is the separately defined zero-on-common-prime
extension, not the genuine affine sum on arbitrary columns. -/

noncomputable section
namespace HeckeGeneral.Characters
namespace ActualGramJointChartDraft
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Arithmetic.PeriodicFourier
open ActualGramJointMeanDraft
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
section GeneralIdeals
variable (C J : Ideal (𝓞 K)) (hC : C ≠ 0) (hJ : J ≠ 0)
variable (hCS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ C → p ∉ S)
variable (hJS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ J → p ∉ S)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "P" => jointPlaces K C J hC hJ
local notation "A" => jointResidues K C J hC hJ

local instance chartCRT_residueField (p : P) : Field (residue K C J hC hJ p) :=
  Ideal.Quotient.field _
local instance chartCRT_residueFintype (p : P) : Fintype (residue K C J hC hJ p) :=
  Fintype.ofFinite _

def jointExterior (p : P) : p.val ∉ S := by
  rcases Finset.mem_union.mp p.property with hp | hp
  · exact hCS p.val ((mem_sexticIdealPlaces_iff K C hC p.val).mp hp)
  · exact hJS p.val ((mem_sexticIdealPlaces_iff K J hJ p.val).mp hp)

/-- Actual reduction of every S-integer, including nonintegral and zero
representatives, in the joint radical's exterior coordinates. -/
def jointReduction (a : S.integer K) : A := fun p =>
  sIntegerSexticResidueMap K S p.val (jointExterior K S C J hC hJ hCS hJS p) a

local notation "red" => jointReduction K S C J hC hJ hCS hJS
local notation "h6" => jointAwaySix K S C J hC hJ hCS hJS hS6

def exteriorIdealAwaySix (p : HeightOneSpectrum (𝓞 K)) (hp : p.asIdeal ∣ J) :
    (6 : 𝓞 K) ∉ p.asIdeal := fun hp6 => hJS p hp (hS6 hp6)

local notation "EvalJ" => sIntegerSexticIdealEvaluation K S ζ hζ σ J hJ hJS
  (exteriorIdealAwaySix K S J hJS hS6)

/-- Product identification uses actual ideal evaluation on all S-integers.
The absent-prime branch and the positive-exponent zero extension are kept
separate; no unit or nonzero-value condition is required. -/
theorem prod_exteriorColumnFactor_eq_idealEvaluation
    (d m₁ m₂ : S.integer K) :
    (∏ p : P, exteriorColumnFactor K ζ hζ σ C J hC hJ h6 p
      (red d p) (red m₁ p) (red m₂ p)) =
      EvalJ (d * m₁) * conj (EvalJ (d * m₂)) := by
  let E (p : P) (a : S.integer K) := sIntegerSexticEvaluation K S p.val
    (jointExterior K S C J hC hJ hCS hJS p) ζ hζ σ (h6 p) a
  have hterm (p : P) :
      exteriorColumnFactor K ζ hζ σ C J hC hJ h6 p
        (red d p) (red m₁ p) (red m₂ p) =
      E p (d * m₁) ^ idealPrimeMultiplicity K p.val J *
        conj (E p (d * m₂) ^ idealPrimeMultiplicity K p.val J) := by
    by_cases he : idealPrimeMultiplicity K p.val J = 0
    · simp [exteriorColumnFactor, he]
    · simp only [exteriorColumnFactor, if_neg he,
        MulChar.pow_apply' (sexticResidueCharacter K ζ hζ σ p.val (h6 p)) he,
        E, sIntegerSexticEvaluation, jointReduction, map_mul]
  have hprod (a : S.integer K) :
      (∏ p : P, E p a ^ idealPrimeMultiplicity K p.val J) = EvalJ a := by
    exact sIntegerSexticIdealEvaluation_eq_prod_finite_support K S ζ hζ σ
      J hJ hJS (exteriorIdealAwaySix K S J hJS hS6) P
      (fun p hp => jointExterior K S C J hC hJ hCS hJS ⟨p, hp⟩)
      (fun p hp => h6 ⟨p, hp⟩)
      (fun p hp => Finset.mem_union_right _ ((mem_sexticIdealPlaces_iff K J hJ p).mpr hp)) a
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib, ← map_prod, hprod, hprod]

/-- Literal prime-power residual extension in the actual exterior residue
coordinates. The prime set may contain extra frequency primes; their
C-exponent zero branch contributes 1, not a principal-character zero mask. -/
def actualResidualExtension (d k m₁ m₂ : S.integer K) : ℂ :=
  ∏ p : P, residualColumnFactor K ζ hζ σ C J hC hJ h6 p
    (red d p) (red k p) (red m₁ p) (red m₂ p)

/-- Exact representative identification with the previously frozen finite
coefficient. No CRT-factorization identity is assumed. -/
theorem jointCoefficient_eq_actual_products (d k m₁ m₂ : S.integer K) :
    jointCoefficient K ζ hζ σ C J hC hJ h6 (red d) (red k) (red m₁, red m₂) =
      (EvalJ (d * m₁) * conj (EvalJ (d * m₂))) *
        actualResidualExtension K S ζ hζ σ C J hC hJ hCS hJS hS6 d k m₁ m₂ := by
  unfold jointCoefficient localJointCoefficient
  rw [Finset.prod_mul_distrib,
    prod_exteriorColumnFactor_eq_idealEvaluation K S ζ hζ σ C J hC hJ hCS hJS hS6]
  rfl

end GeneralIdeals
local notation "N" => NonzeroRingElements (S.integer K)

def actualFrequencyIdeal (k : N) : Ideal (𝓞 K) := sIntegerModulusContraction K S k.val

theorem actualFrequencyIdeal_ne_zero (k : N) : actualFrequencyIdeal K S k ≠ 0 :=
  sIntegerModulusContraction_ne_bot K S k.val k.property

def actualFrequencyIdeal_exterior (k : N)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p.asIdeal ∣ actualFrequencyIdeal K S k) : p ∉ S := by
  intro hpS
  have hc := sIntegerModulusContraction_coprime K S k.val k.property p hpS
  have hle : actualFrequencyIdeal K S k ≤ p.asIdeal := Ideal.dvd_iff_le.mp hp
  have htop : (⊤ : Ideal (𝓞 K)) ≤ p.asIdeal := by
    rw [← hc]
    exact sup_le hle le_rfl
  exact p.isPrime.ne_top (top_le_iff.mp htop)

variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
variable (c k : NonzeroRingElements (S.integer K))
local notation "C" => actualFrequencyIdeal K S c
local notation "J" => actualFrequencyIdeal K S k
local notation "hc" => actualFrequencyIdeal_ne_zero K S c
local notation "hk" => actualFrequencyIdeal_ne_zero K S k
local notation "hCS" => actualFrequencyIdeal_exterior K S c
local notation "hJS" => actualFrequencyIdeal_exterior K S k
local notation "h6" => jointAwaySix K S C J hc hk hCS hJS hS6
local notation "red" => jointReduction K S C J hc hk hCS hJS
local notation "active" => fun n : N => Prod.snd (sLocalNonzeroIntegerDiagonal K S n)

include c k in
/-- Complete chart-to-residue-coefficient bridge for the original raw
sextic and actual RCorrection. All ideals, reductions and corrections are
constructed from the actual nonzero S-integers c,k,d,m1,m2. There is no
coprimality premise on m1,m2 and no coefficient-equality premise. -/
theorem raw_mul_RCorrection_mul_residual_eq_chart_jointCoefficient
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (d m₁ b₁ m₂ b₂ : N)
    (h₁ : divisorColumn K S d m₁ ∈ fixedSChart K S ζ hζ b₁)
    (h₂ : divisorColumn K S d m₂ ∈ fixedSChart K S ζ hζ b₂)
    (hb₁ : active b₁ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ))
    (hb₂ : active b₂ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)) :
    (sIntegerSexticRawCoefficient K S ζ hζ σ hS6
      (divisorColumn K S d m₁) (divisorColumn K S d m₂) k *
      sIntegerSexticRCorrection K S ζ hζ σ
        (divisorColumn K S d m₁) (divisorColumn K S d m₂)) *
      actualResidualExtension K S ζ hζ σ C J hc hk hCS hJS hS6
        d.val k.val m₁.val m₂.val =
    actualChartPhase K S ζ hζ σ k b₁ b₂ *
      jointCoefficient K ζ hζ σ C J hc hk h6
        (red d.val) (red k.val) (red m₁.val, red m₂.val) := by
  rw [jointCoefficient_eq_actual_products K S ζ hζ σ C J hc hk hCS hJS hS6]
  have hleft := raw_mul_RCorrection_eq_chartPhase_mul_fixed_symbols K S ζ hζ σ hS6 Γ
    k (divisorColumn K S d m₁) b₁ (divisorColumn K S d m₂) b₂ h₁ h₂ hb₁ hb₂
  have he₁ : sIntegerSexticIdealEvaluation K S ζ hζ σ J hk hJS
      (exteriorIdealAwaySix K S J hJS hS6) (d.val * m₁.val) =
      sIntegerSexticSymbol K S ζ hζ σ hS6 (divisorColumn K S d m₁).val k := rfl
  have he₂ : sIntegerSexticIdealEvaluation K S ζ hζ σ J hk hJS
      (exteriorIdealAwaySix K S J hJS hS6) (d.val * m₂.val) =
      sIntegerSexticSymbol K S ζ hζ σ hS6 (divisorColumn K S d m₂).val k := rfl
  rw [he₁, he₂, hleft]
  ring

end ActualGramJointChartDraft
end HeckeGeneral.Characters
