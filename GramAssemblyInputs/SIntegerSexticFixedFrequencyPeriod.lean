import SIntegerSexticRIdentification
import HeckeGeneral.Arithmetic.SIntegerMovingPeriodClassScalar

/-! SOURCE ONLY, UNRUN. Actual fixed-frequency raw coefficient period.
There is one moving frequency ideal I_k, since I_(-k)=I_k. The sharper
arithmetic modulus is M_S * I_k. The existing lattice period includes the
fixed S-prime product as well, and is proved to refine that modulus.
No coprimality of either pair, full F identity, or CRT identity is used. -/
noncomputable section
namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical nonZeroDivisors
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "N" => NonzeroRingElements (S.integer K)
local notation "χ" => sIntegerSexticSymbol K S ζ hζ σ hS6
local notation "MS" => sIntegerSexticSPlaceModulus K S ζ hζ
local notation "active" => fun m : N => Prod.snd (sLocalNonzeroIntegerDiagonal K S m)

def sIntegerSexticNegativeFrequency (k : N) : N :=
  ⟨-k.val, neg_ne_zero.mpr k.property⟩

theorem sIntegerModulusContraction_negative_frequency (k : N) :
    sIntegerModulusContraction K S (sIntegerSexticNegativeFrequency K S k).val =
      sIntegerModulusContraction K S k.val := by
  unfold sIntegerModulusContraction sIntegerSexticNegativeFrequency
  rw [Ideal.span_singleton_neg]

/-- The S-place conductor is fixed before choosing the frequency. -/
def sIntegerSexticFixedFrequencyModulus (k : N) : Ideal (𝓞 K) :=
  MS * sIntegerModulusContraction K S k.val

theorem sIntegerSexticSymbol_fixed_frequency_periodic
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (k n m : N) (t : 𝓞 K)
    (ht : t ∈ sIntegerSexticFixedFrequencyModulus K S ζ hζ k)
    (he : n.val - m.val = algebraMap (𝓞 K) (S.integer K) t)
    (hm : active m ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)) :
    χ k.val n = χ k.val m := by
  have htS : t ∈ MS := Ideal.mul_le_left ht
  have htI : t ∈ sIntegerModulusContraction K S k.val := Ideal.mul_le_right ht
  have hnumerator : χ n.val k = χ m.val k := by
    apply sIntegerSexticSymbol_periodic K S ζ hζ σ hS6 n.val m.val k
    rw [he, ← map_sIntegerModulusContraction K S k.val]
    exact Ideal.mem_map_of_mem _ htI
  have hcorrection := (sIntegerSexticSPlaceCorrection_fixed_first_periodic
    K S ζ hζ Γ (nonzeroSIntegerFieldUnit K S k) n m t htS he hm).2
  rw [sIntegerSexticSymbol_reciprocity K S ζ hζ σ hS6 k n,
    sIntegerSexticSymbol_reciprocity K S ζ hζ σ hS6 k m,
    hcorrection, hnumerator]

/-- The literal minus sign uses the SAME ideal, never I_k * I_(-k). -/
theorem sIntegerSexticSymbol_negative_fixed_frequency_periodic
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (k n m : N) (t : 𝓞 K)
    (ht : t ∈ sIntegerSexticFixedFrequencyModulus K S ζ hζ k)
    (he : n.val - m.val = algebraMap (𝓞 K) (S.integer K) t)
    (hm : active m ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)) :
    χ (-k.val) n = χ (-k.val) m := by
  have htneg : t ∈ sIntegerSexticFixedFrequencyModulus K S ζ hζ
      (sIntegerSexticNegativeFrequency K S k) := by
    simpa only [sIntegerSexticFixedFrequencyModulus,
      sIntegerModulusContraction_negative_frequency] using ht
  exact sIntegerSexticSymbol_fixed_frequency_periodic K S ζ hζ σ hS6 Γ
    (sIntegerSexticNegativeFrequency K S k) n m t htneg he hm

theorem sIntegerSexticRawCoefficient_fixed_frequency_periodic
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (k n₁ m₁ n₂ m₂ : N) (t₁ t₂ : 𝓞 K)
    (ht₁ : t₁ ∈ sIntegerSexticFixedFrequencyModulus K S ζ hζ k)
    (ht₂ : t₂ ∈ sIntegerSexticFixedFrequencyModulus K S ζ hζ k)
    (he₁ : n₁.val - m₁.val = algebraMap (𝓞 K) (S.integer K) t₁)
    (he₂ : n₂.val - m₂.val = algebraMap (𝓞 K) (S.integer K) t₂)
    (hm₁ : active m₁ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ))
    (hm₂ : active m₂ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)) :
    sIntegerSexticRawCoefficient K S ζ hζ σ hS6 n₁ n₂ k =
      sIntegerSexticRawCoefficient K S ζ hζ σ hS6 m₁ m₂ k := by
  unfold sIntegerSexticRawCoefficient
  rw [sIntegerSexticSymbol_fixed_frequency_periodic K S ζ hζ σ hS6 Γ k n₁ m₁ t₁ ht₁ he₁ hm₁,
    sIntegerSexticSymbol_negative_fixed_frequency_periodic K S ζ hζ σ hS6 Γ k n₂ m₂ t₂ ht₂ he₂ hm₂]

theorem sIntegerSexticRaw_mul_RCorrection_fixed_frequency_periodic
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (k n₁ m₁ n₂ m₂ : N) (t₁ t₂ : 𝓞 K)
    (ht₁ : t₁ ∈ sIntegerSexticFixedFrequencyModulus K S ζ hζ k)
    (ht₂ : t₂ ∈ sIntegerSexticFixedFrequencyModulus K S ζ hζ k)
    (he₁ : n₁.val - m₁.val = algebraMap (𝓞 K) (S.integer K) t₁)
    (he₂ : n₂.val - m₂.val = algebraMap (𝓞 K) (S.integer K) t₂)
    (hm₁ : active m₁ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ))
    (hm₂ : active m₂ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)) :
    sIntegerSexticRawCoefficient K S ζ hζ σ hS6 n₁ n₂ k *
        sIntegerSexticRCorrection K S ζ hζ σ n₁ n₂ =
      sIntegerSexticRawCoefficient K S ζ hζ σ hS6 m₁ m₂ k *
        sIntegerSexticRCorrection K S ζ hζ σ m₁ m₂ := by
  rw [sIntegerSexticRawCoefficient_fixed_frequency_periodic K S ζ hζ σ hS6 Γ
    k n₁ m₁ n₂ m₂ t₁ t₂ ht₁ ht₂ he₁ he₂ hm₁ hm₂]
  rw [sIntegerSexticRCorrection_periodic K S ζ hζ σ Γ
    n₁ m₁ n₂ m₂ t₁ t₂ (Ideal.mul_le_left ht₁) (Ideal.mul_le_left ht₂)
    he₁ he₂ hm₁ hm₂]

/-- The exact supplied conductor for the existing moving-period lattice. -/
def sIntegerSexticMovingConductor : (Ideal (𝓞 K))⁰ :=
  ⟨MS, mem_nonZeroDivisors_of_ne_zero (sIntegerSexticSPlaceModulus_ne_bot K S ζ hζ)⟩

theorem sIntegerSexticMovingPeriod_le_fixedFrequencyModulus (k : N) :
    (sIntegerMovingPeriod K S (sIntegerSexticMovingConductor K S ζ hζ) k).val ≤
      sIntegerSexticFixedFrequencyModulus K S ζ hζ k := by
  change (sIntegerModulusContraction K S k.val * _) * MS ≤
    MS * sIntegerModulusContraction K S k.val
  rw [mul_comm MS]
  exact mul_le_mul_left Ideal.mul_le_left _

/-- Consumer in the exact period used by the existing lattice modules. -/
theorem sIntegerSexticRaw_mul_RCorrection_movingPeriod_periodic
    (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
    (k n₁ m₁ n₂ m₂ : N) (t₁ t₂ : 𝓞 K)
    (ht₁ : t₁ ∈ (sIntegerMovingPeriod K S
      (sIntegerSexticMovingConductor K S ζ hζ) k).val)
    (ht₂ : t₂ ∈ (sIntegerMovingPeriod K S
      (sIntegerSexticMovingConductor K S ζ hζ) k).val)
    (he₁ : n₁.val - m₁.val = algebraMap (𝓞 K) (S.integer K) t₁)
    (he₂ : n₂.val - m₂.val = algebraMap (𝓞 K) (S.integer K) t₂)
    (hm₁ : active m₁ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ))
    (hm₂ : active m₂ ∈ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)) :
    sIntegerSexticRawCoefficient K S ζ hζ σ hS6 n₁ n₂ k *
        sIntegerSexticRCorrection K S ζ hζ σ n₁ n₂ =
      sIntegerSexticRawCoefficient K S ζ hζ σ hS6 m₁ m₂ k *
        sIntegerSexticRCorrection K S ζ hζ σ m₁ m₂ := by
  exact sIntegerSexticRaw_mul_RCorrection_fixed_frequency_periodic
    K S ζ hζ σ hS6 Γ k n₁ m₁ n₂ m₂ t₁ t₂
    (sIntegerSexticMovingPeriod_le_fixedFrequencyModulus K S ζ hζ k ht₁)
    (sIntegerSexticMovingPeriod_le_fixedFrequencyModulus K S ζ hζ k ht₂)
    he₁ he₂ hm₁ hm₂
end HeckeGeneral.Characters
