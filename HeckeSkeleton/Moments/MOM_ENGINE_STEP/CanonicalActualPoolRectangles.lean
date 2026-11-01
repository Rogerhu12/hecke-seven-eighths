import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalActualSecondRectangles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CombinedSupportPoolAtlas

/-!
# Actual pool phases on the original combined occurrence branch

The valuation source is reindexed by the original combined support.
Its additional character is the actual pool generator with exponent
`2n`. Its scalar contains the original first norm/Fourier factor at
the extracted prime power and the original factor `Q(p)^n`.

The complete parent moving list, first active list and remaining
common-column mask are retained. No factorization of a transformed
rectangle is an input to the construction.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalActualPoolRectangles

open NumberField IsDedekindDomain DedekindZetaZeroFree UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open LocalFiniteSums CanonicalSecondFactorAssembly CanonicalOriginalPhaseCalibration
open CanonicalActualSecondRectangles

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- The original common part and the actual extracted pool power.
The displayed ideal retains the full power, even for exponent six. -/
def combinedCommon (D : A.Exterior) (p : ExteriorPrime A) (n : ℕ) : A.Exterior :=
  ExteriorIdealEuler.mul D (powerIdeal p n)

theorem combinedCommon_support (D : A.Exterior) (p : ExteriorPrime A)
    (n : ℕ) (hn : 0 < n) :
    primeSupport (combinedCommon D p n).val = primeSupport D.val ∪ {p.val.asIdeal} := by
  change (normalizedFactors (D.val * p.val.asIdeal ^ n)).toFinset = _
  rw [normalizedFactors_mul D.property.1 (pow_ne_zero n p.val.ne_bot),
    Multiset.toFinset_add, p.val.irreducible.normalizedFactors_pow, normalize_eq,
    Multiset.toFinset_replicate, if_neg (Nat.ne_of_gt hn)]
  rfl

theorem prime_dvd_combinedCommon (D : A.Exterior) (p : ExteriorPrime A)
    (n : ℕ) (hn : 0 < n) : p.val.asIdeal ∣ (combinedCommon D p n).val := by
  apply (prime_mem_support_iff_dvd p.val.asIdeal _ p.val.prime
    (combinedCommon D p n).property.1).mp
  rw [combinedCommon_support D p n hn]
  exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

section ResidualCoprimality

variable {k : ℕ} {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable (common : A.Exterior)
variable (b : SupportCartesianBranch S₁ S₂ S (primeSupport common.val))

/-- The whole residual ideal avoids the full original extraction,
because each residual is the actual support complement. -/
theorem residual_coprime_common (i : AllocationColumn K b.keep.card)
    (hi : i ∈ b.residualColumns) :
    IsCoprime (allocationColumnIdeal i) common.val := by
  have hr := b.residual_ideal (b.reconstruct i) (b.reconstruct_mem i hi)
  rw [b.residual_reconstruct i hi] at hr
  rw [← hr]
  exact CanonicalCommonColumnMask.residual_coprime common _

end ResidualCoprimality

section PoolTable

variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable (parent : MomentData K ω ψ) (correction : HeckeCharacter K)
variable (prefix : OriginalMovingFactors A P R) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (index : Fin k → Fin parent.geometry.slotCount)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
variable (hemb : P.arithmetic.embedding = σ)
variable (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (n : ℕ)
variable (side : SecondColumnSide) (χ : (PUnit × PUnit) →* Circle)
variable (S₁ S₂ : Finset (Ideal (𝓞 K)))
variable (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
variable (F : SecondCoefficientTermDictionary
  (movingSourceCharacters parent correction prefix remaining index)
  (side.phase PUnit χ) S₁ S₂ S)
variable (J : AllocationColumn K k → A.Exterior)
variable (hJ : ∀ i ∈ childCartesianColumns S₁ S₂ S, (J i).val = allocationColumnIdeal i)
variable (witness : AllocationColumn K k)
variable (hwitness : witness ∈ childCartesianColumns S₁ S₂ S)
variable (hcop : ∀ i ∈ childCartesianColumns S₁ S₂ S, IsCoprime (J i).val p.val.asIdeal)

local notation "E" => poolMovingFactors (P := P) (R := R) C p n

/-- Every single pool atom is constructed from the preceding original
atom and the actual reciprocal pool character. Its complete mask is
proved from the genuine residual prime coprimality. -/
def poolDictionary :
    SecondCoefficientTermDictionary
      (movingSourceCharacters parent correction (prefix.append E) remaining index)
      (side.phase PUnit χ) S₁ S₂ S := by
  have hc := occurrence_conditions S₁ S₂ S J hJ witness hwitness (LocalFiniteSums.primeIdeal p) hcop
  have hout₁ (I : Ideal (𝓞 K)) (hI : I ∈ S₁) :
      HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
        (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (sourceMomentIdeal I) := by
    apply (outside_iff_coprime _).mpr
    simpa only [sourceMomentIdeal_val_of_ne_zero I (hc.1 I hI).1] using (hc.1 I hI).2.1
  have hout₂ (I : Ideal (𝓞 K)) (hI : I ∈ S₂) :
      HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
        (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (sourceMomentIdeal I) := by
    apply (outside_iff_coprime _).mpr
    simpa only [sourceMomentIdeal_val_of_ne_zero I (hc.2.1 I hI).1] using (hc.2.1 I hI).2.1
  have hout (j : Fin k) (q : HeightOneSpectrum (𝓞 K)) (hq : q ∈ S j) :
      q ∉ (A.Sf : Set (HeightOneSpectrum (𝓞 K))) := by
    have he := (outside_iff_coprime (CanonicalOriginalPhaseCalibration.primeIdeal q)).mpr
      (hc.2.2 j q hq).1
    exact (he q (dvd_refl q.asIdeal)).1
  have hmask (I : Ideal (𝓞 K)) (hI : IsCoprime I p.val.asIdeal) :
      E.residueValue (σ := σ) I *
        (if IsCoprime I E.support.val then (1 : ℂ) else 0) =
          E.residueValue (σ := σ) I := by
    have hE : IsCoprime I E.support.val := by
      rw [E.coprime_support_iff_fullIdeal I, poolMovingFactors_fullIdeal]
      exact hI
    rw [if_pos hE, mul_one]
  refine
    { leftAtom := fun I => F.leftAtom I * E.residueHom (σ := σ) I
      rightAtom := fun I => F.rightAtom I * E.residueHom (σ := σ) I
      slotAtom := fun j q => F.slotAtom j q * E.residueHom (σ := σ) q.asIdeal
      leftRay := F.leftRay
      rightRay := F.rightRay
      slotRay := F.slotRay
      scale₁ := F.scale₁
      scale₂ := F.scale₂
      base := F.base
      length := F.length
      leftWeight := F.leftWeight
      rightWeight := F.rightWeight
      slotWeight := F.slotWeight
      plain₁ := ?_
      plain₂ := ?_
      prime := ?_ }
  · intro I hI
    have hv := sourceMomentIdeal_val_of_ne_zero I (hc.1 I hI).1
    have hphase := hmask (sourceMomentIdeal I).val (by rw [hv]; exact (hc.1 I hI).2.2)
    rw [moving_plain_append parent correction prefix E remaining index hroot hemb
      (sourceMomentIdeal I) (hout₁ I hI) hphase]
    have hold := F.plain₁ I hI
    simp only [CanonicalSecondRectangularFactors.punit_phase, mul_one] at hold ⊢
    rw [hold]
    change _ * E.residueValue (σ := σ) I = _
    rw [hv]
    ring
  · intro I hI
    have hv := sourceMomentIdeal_val_of_ne_zero I (hc.2.1 I hI).1
    have hphase := hmask (sourceMomentIdeal I).val (by rw [hv]; exact (hc.2.1 I hI).2.2)
    rw [moving_plain_append parent correction prefix E remaining index hroot hemb
      (sourceMomentIdeal I) (hout₂ I hI) hphase]
    have hold := F.plain₂ I hI
    simp only [CanonicalSecondRectangularFactors.punit_phase, mul_one] at hold ⊢
    rw [hold]
    change _ * E.residueValue (σ := σ) I = _
    rw [hv]
    ring
  · intro j q hq
    rw [moving_prime_append parent correction prefix E remaining index hroot hemb
      j q (hout j q hq) (hmask q.asIdeal (hc.2.2 j q hq).2)]
    have hold := F.prime j q hq
    simp only [CanonicalSecondRectangularFactors.punit_phase, mul_one] at hold ⊢
    rw [hold]
    change _ * E.residueValue (σ := σ) q.asIdeal = _
    ring

/-- The full reciprocal phase is the product of these actual atoms.
No phase has been replaced by its norm or by an arbitrary character. -/
theorem poolDictionary_coefficient (i : AllocationColumn K k) :
    (poolDictionary parent correction prefix remaining index hroot hemb C p n
      side χ S₁ S₂ S F J hJ witness hwitness hcop).coefficient i =
      F.coefficient i * E.residueHom (σ := σ) (allocationColumnIdeal i) := by
  exact (CanonicalSecondRectangularFactors.rectangle_mul_ideal_weight
    (E.residueHom (σ := σ)) F.leftAtom F.rightAtom F.slotAtom i).symm

end PoolTable

section ActualOriginalPool

variable {ω ψ : HeckeCharacter K} {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (x : X)
variable (W : NormProfileRecipe (fun _ : PUnit => data x))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ)
variable (S₁ S₂ : Finset (Ideal (𝓞 K)))
variable (S : Fin (data x).geometry.slotCount → Finset (HeightOneSpectrum (𝓞 K)))
variable (firstCommon : A.Exterior) (p : ExteriorPrime A) (v : ℕ) (hv : 0 < v)
variable (b : SupportCartesianBranch S₁ S₂ S (primeSupport (combinedCommon firstCommon p v).val))
variable {τ : Type*} [Fintype τ] [DecidableEq τ]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (primes : τ → ExteriorPrime A) (m n : τ → ℕ) (firstRight : Bool)
variable (δ : NonzeroRingElements A.R) (tilt ξ : ℝ)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2)
variable (hemb : P.arithmetic.embedding = σ)
variable (J : AllocationColumn K b.keep.card → A.Exterior)
variable (hJ : ∀ i ∈ b.residualColumns, (J i).val = allocationColumnIdeal i)
variable (hactive : ∀ i ∈ b.residualColumns,
  IsCoprime (J i).val (firstActiveIdeal primes m n).val)
variable (side : SecondColumnSide) (χ : (PUnit × PUnit) →* Circle)

local notation "common" => combinedCommon firstCommon p v
local notation "idx" => SlotRestriction.index b.keep
local notation "L₁" => SupportCartesian.plainResidual S₁ (primeSupport common.val) b.plainExtract₁
local notation "L₂" => SupportCartesian.plainResidual S₂ (primeSupport common.val) b.plainExtract₂
local notation "Slots" => fun j => SupportCartesian.primeLive (S (idx j)) (primeSupport common.val)
local notation "E₁" => CanonicalSecondRectangularFactors.firstMovingFactors P R C primes m n firstRight δ
local notation "Epool" => poolMovingFactors (P := P) (R := R) C p v
local notation "M₁" => E₁.residueHom (σ := σ) * normLogWeight (tilt - 1) ξ (if firstRight then 1 else -1)
local notation "firstTable" => firstResidualDictionary Q x W a Z t Y₁ Y₂ S₁ S₂ S common b
  C primes m n firstRight δ tilt ξ hroot hemb J hJ hactive side χ

/-- The real combined original branch constructs its pool dictionary.
Residual coprimality with the pool prime is derived from this branch,
including when the displayed pool character has exponent twelve. -/
def originalPoolDictionary (comparison : Bool) :
    SecondCoefficientTermDictionary
      (movingSourceCharacters (data x) Q.correction ((Q.moving.append E₁).append Epool)
        (Q.remaining * exteriorMomentIdeal common) idx)
      (side.phase PUnit χ) L₁ L₂ Slots :=
  poolDictionary (data x) Q.correction (Q.moving.append E₁)
    (Q.remaining * exteriorMomentIdeal common) idx hroot hemb C p v
    side χ L₁ L₂ Slots (firstTable comparison) J hJ
    (b.residual b.witness) (b.residual_mem b.witness b.witness_mem)
    (fun i hi => by
      rw [hJ i hi]
      exact (residual_coprime_common common b i hi).of_isCoprime_of_dvd_right
        (prime_dvd_combinedCommon firstCommon p v hv))

/-- The actual extracted prime power contributes a row-independent
complex scalar, still retaining its original Fourier phase. -/
def originalPoolScalar : ℂ :=
  Q.originalCommonScalar x Z t S₁ S₂ S b * M₁ (powerIdeal p v).val * (LocalFiniteSums.Q p : ℂ) ^ v

/-- This is exactly the shape of the genuine residualSource coefficient
after its proved prime-power reconstruction. -/
def originalPoolCoefficient (comparison : Bool) (i : AllocationColumn K b.keep.card) : ℂ :=
  (Q.originalTermDictionary x W a Z t Y₁ Y₂ .left 1 S₁ S₂ S comparison).
      coefficient (b.reconstruct i) *
    M₁ ((powerIdeal p v).val * (J i).val) * (LocalFiniteSums.Q p : ℂ) ^ v *
      Epool.residueHom (σ := σ) (J i).val

/-- The real pool coefficient is factored by the computed original
table. The full extracted scalar and the displayed prime remain exact. -/
theorem originalPoolCoefficient_eq (comparison : Bool)
    (i : AllocationColumn K b.keep.card) (hi : i ∈ b.residualColumns) :
    originalPoolCoefficient Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon p v b
        C primes m n firstRight δ tilt ξ J comparison i =
      originalPoolScalar Q x Z t S₁ S₂ S firstCommon p v b
          C primes m n firstRight δ tilt ξ *
        (originalPoolDictionary Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon p v hv b
          C primes m n firstRight δ tilt ξ hroot hemb J hJ hactive side χ comparison).
            coefficient i := by
  rw [originalPoolCoefficient, originalPoolScalar, originalPoolDictionary,
    poolDictionary_coefficient, map_mul, hJ i hi]
  have h := firstResidualTerm_eq Q x W a Z t Y₁ Y₂ S₁ S₂ S common b C primes m n
    firstRight δ tilt ξ hroot hemb J hJ hactive side χ comparison i hi
  change _ * M₁ (allocationColumnIdeal i) = _ at h
  calc
    _ = ((Q.originalTermDictionary x W a Z t Y₁ Y₂ .left 1 S₁ S₂ S comparison).
          coefficient (b.reconstruct i) * M₁ (allocationColumnIdeal i)) *
        M₁ (powerIdeal p v).val * (LocalFiniteSums.Q p : ℂ) ^ v *
          Epool.residueHom (σ := σ) (allocationColumnIdeal i) := by ring
    _ = _ := by rw [h]; ring

variable [IsPrincipalIdealRing A.R]
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (rows : ActualSecondCorrelationRows A σ H ι)
variable (secondCommon : A.Exterior)
variable (b₂ : SupportCartesianBranch L₁ L₂ Slots (primeSupport secondCommon.val))
variable (J₂ : AllocationColumn K b₂.keep.card → A.Exterior)
variable (hJ₂ : ∀ i ∈ b₂.residualColumns, (J₂ i).val = allocationColumnIdeal i)
variable (secondTilt : ℝ) (rowOffset : H → ℝ) (hZ : 1 < Z)

local notation "poolTable" => originalPoolDictionary Q x W a Z t Y₁ Y₂ S₁ S₂ S
  firstCommon p v hv b C primes m n firstRight δ tilt ξ hroot hemb J hJ hactive side χ
local notation "poolScalar" => originalPoolScalar Q x Z t S₁ S₂ S firstCommon p v b
  C primes m n firstRight δ tilt ξ
local notation "poolCoefficient" => originalPoolCoefficient Q x W a Z t Y₁ Y₂ S₁ S₂ S
  firstCommon p v b C primes m n firstRight δ tilt ξ J
local notation "prefix" => (Q.moving.append E₁).append Epool
local notation "idx₂" => SlotRestriction.index b₂.keep
local notation "ε" => sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) ∅
local notation "weight₂" => CanonicalSecondRectangularFactors.secondWeight (σ := σ) secondTilt ε.val
local notation "G₁" => Z ^ a.n₁ / idealNorm K b.plainDivisor₁ / idealNorm K b₂.plainDivisor₁
local notation "G₂" => Z ^ a.n₂ / idealNorm K b.plainDivisor₂ / idealNorm K b₂.plainDivisor₂
local notation "Gslots" => fun j => Z ^ ((data x).geometry.slots (idx (idx₂ j))).length
local notation "H₁" => fun comparison : Bool =>
  (if comparison then Y₁ else Z ^ a.n₁) / idealNorm K b.plainDivisor₁ /
    idealNorm K b₂.plainDivisor₁
local notation "H₂" => fun comparison : Bool =>
  (if comparison then Y₂ else Z ^ a.n₂) / idealNorm K b.plainDivisor₂ /
    idealNorm K b₂.plainDivisor₂

private theorem pool_plain_product (comparison : Bool)
    (hproduct : comparison = true → Y₁ * Y₂ = Z ^ a.n₁ * Z ^ a.n₂) :
    G₁ * G₂ = H₁ comparison * H₂ comparison := by
  cases comparison with
  | false => rfl
  | true =>
    change G₁ * G₂ =
      (Y₁ / idealNorm K b.plainDivisor₁ / idealNorm K b₂.plainDivisor₁) *
        (Y₂ / idealNorm K b.plainDivisor₂ / idealNorm K b₂.plainDivisor₂)
    simp only [div_eq_mul_inv]
    calc
      _ = (Z ^ a.n₁ * Z ^ a.n₂) *
          ((idealNorm K b.plainDivisor₁)⁻¹ * (idealNorm K b₂.plainDivisor₁)⁻¹ *
            (idealNorm K b.plainDivisor₂)⁻¹ * (idealNorm K b₂.plainDivisor₂)⁻¹) := by ring
      _ = _ := by rw [← hproduct rfl]; ring

/-- The actual pool source supplies a full second rectangle. The only
new scalar is the explicit original prime-power scalar proved above.
All characters and normalizers are computed from its original table. -/
def originalPoolSecondFactors (comparison : Bool)
    (hcomparison : comparison = true →
      0 < Y₁ ∧ 0 < Y₂ ∧ Y₁ * Y₂ = Z ^ a.n₁ * Z ^ a.n₂) :
    SecondRectangularFactors rows PUnit side
      (SupportCartesian.plainResidual L₁ (primeSupport secondCommon.val) b₂.plainExtract₁)
      (SupportCartesian.plainResidual L₂ (primeSupport secondCommon.val) b₂.plainExtract₂)
      (fun j => SupportCartesian.primeLive (Slots (idx₂ j)) (primeSupport secondCommon.val))
      J₂ (fun _ => PUnit.unit)
      (fun i => poolCoefficient comparison (b₂.reconstruct i) *
        weight₂ (secondCommon.val * (J₂ i).val))
      (fun h i => rowOffset h - Real.log (A.exteriorNorm secondCommon * A.exteriorNorm (J₂ i))) χ := by
  have hG₁ : 0 < G₁ := div_pos
    (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (idealNorm_pos K _))
    (idealNorm_pos K _)
  have hG₂ : 0 < G₂ := div_pos
    (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (idealNorm_pos K _))
    (idealNorm_pos K _)
  have hH₁ : 0 < H₁ comparison := by
    apply div_pos _ (idealNorm_pos K _)
    apply div_pos _ (idealNorm_pos K _)
    cases comparison
    · exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    · exact (hcomparison rfl).1
  have hH₂ : 0 < H₂ comparison := by
    apply div_pos _ (idealNorm_pos K _)
    apply div_pos _ (idealNorm_pos K _)
    cases comparison
    · exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    · exact (hcomparison rfl).2.1
  let f := secondRectangularFactors rows (data x) Q.correction prefix
    (Q.remaining * exteriorMomentIdeal common) idx hroot hemb side χ (poolTable comparison)
    b₂ secondCommon poolScalar secondTilt J₂ hJ₂ hZ
    (fun j => ((data x).geometry.slots (idx j)).length_pos)
    (H₁ comparison) (H₂ comparison) Gslots hH₁ hH₂
    (fun _ => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) rowOffset
  refine { f with gaussScale₁ := G₁, gaussScale₂ := G₂,
    gaussScale₁_pos := hG₁, gaussScale₂_pos := hG₂, coefficient_factor := ?_ }
  intro i hi
  rw [originalPoolCoefficient_eq Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon p v hv b
    C primes m n firstRight δ tilt ξ hroot hemb J hJ hactive side χ comparison
    (b₂.reconstruct i) (b₂.original_subset (b₂.reconstruct_mem i hi))]
  rw [normalizedCoefficient_plain_product f.dictionary G₁ G₂ Gslots
    (H₁ comparison) (H₂ comparison) hG₁.le hH₁.le
    (pool_plain_product x a Z Y₁ Y₂ S₁ S₂ S firstCommon p v b secondCommon b₂
      comparison (fun hc => (hcomparison hc).2.2)) i]
  exact f.coefficient_factor i hi

/-- The exact pool common scalar is shared by the two comparisons.
Its second common norm power remains explicit in the original weight. -/
def originalPoolSecondCommonScalar : ℂ :=
  poolScalar * b₂.bareCommonScalar
    (movingSourceCharacters (data x) Q.correction prefix
      (Q.remaining * exteriorMomentIdeal common) idx)
    Z (fun j => ((data x).geometry.slots (idx j)).length) (poolTable false).slotWeight *
      weight₂ secondCommon.val

theorem originalPoolSecondCommonScalar_eq (comparison : Bool) :
    originalPoolSecondCommonScalar Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon p v hv b
        C primes m n firstRight δ tilt ξ hroot hemb J hJ hactive side χ
        secondCommon b₂ secondTilt =
      poolScalar * b₂.bareCommonScalar
        (movingSourceCharacters (data x) Q.correction prefix
          (Q.remaining * exteriorMomentIdeal common) idx)
        (poolTable comparison).base (poolTable comparison).length
        (poolTable comparison).slotWeight * weight₂ secondCommon.val := by
  cases comparison <;> rfl

def originalPoolSecondCoreCoefficient (comparison : Bool)
    (i : AllocationColumn K b₂.keep.card) : ℂ :=
  b₂.bareResidualCoefficient
      (movingSourceCharacters (data x) Q.correction prefix
        (Q.remaining * exteriorMomentIdeal common) idx)
      (poolTable comparison).scale₁ (poolTable comparison).scale₂
      (poolTable comparison).base (poolTable comparison).length
      (poolTable comparison).leftWeight (poolTable comparison).rightWeight
      (poolTable comparison).slotWeight i * weight₂ (J₂ i).val

/-- This identity is on the actual original pool modulus. It moves
the proved common scalar before Cauchy; the residual profiles contain
none of the common atoms already paid in the original row mass. -/
theorem originalPoolSecondSource_to_core
    (hcommon : frozenSourceIdeal b₂.plainDivisor₁ b₂.plainDivisor₂ b₂.keep b₂.witness.2 =
      secondCommon.val)
    (comparison : Bool) (i : AllocationColumn K b₂.keep.card) (hi : i ∈ b₂.residualColumns) :
    poolCoefficient comparison (b₂.reconstruct i) * weight₂ (J (b₂.reconstruct i)).val =
      originalPoolSecondCommonScalar Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon p v hv b
          C primes m n firstRight δ tilt ξ hroot hemb J hJ hactive side χ
          secondCommon b₂ secondTilt *
        originalPoolSecondCoreCoefficient Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon p v hv b
          C primes m n firstRight δ tilt ξ hroot hemb J hJ hactive side χ
          secondCommon b₂ J₂ secondTilt comparison i := by
  rw [originalPoolCoefficient_eq Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon p v hv b
      C primes m n firstRight δ tilt ξ hroot hemb J hJ hactive side χ comparison
      (b₂.reconstruct i) (b₂.original_subset (b₂.reconstruct_mem i hi)),
    originalSourceModulus x S₁ S₂ S common b J hJ secondCommon b₂ J₂ hJ₂ hcommon i hi,
    originalPoolSecondCommonScalar_eq Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon p v hv b
      C primes m n firstRight δ tilt ξ hroot hemb J hJ hactive side χ
      secondCommon b₂ secondTilt comparison]
  have h := second_original_to_core (data x) Q.correction prefix
    (Q.remaining * exteriorMomentIdeal common) idx hroot hemb side χ (poolTable comparison)
    b₂ secondCommon poolScalar secondTilt J₂ hJ₂ i hi
  rw [secondResidualCoreDictionary_coefficient] at h
  · exact h
  · exact hi

/-- The source used after that exact reweighting has a constructed
rectangle with the same original total normalization scale. -/
def originalPoolSecondCoreFactors (comparison : Bool)
    (hcomparison : comparison = true →
      0 < Y₁ ∧ 0 < Y₂ ∧ Y₁ * Y₂ = Z ^ a.n₁ * Z ^ a.n₂) :
    SecondRectangularFactors rows PUnit side
      (SupportCartesian.plainResidual L₁ (primeSupport secondCommon.val) b₂.plainExtract₁)
      (SupportCartesian.plainResidual L₂ (primeSupport secondCommon.val) b₂.plainExtract₂)
      (fun j => SupportCartesian.primeLive (Slots (idx₂ j)) (primeSupport secondCommon.val))
      J₂ (fun _ => PUnit.unit)
      (originalPoolSecondCoreCoefficient Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon p v hv b
        C primes m n firstRight δ tilt ξ hroot hemb J hJ hactive side χ
        secondCommon b₂ J₂ secondTilt comparison)
      (fun h i => rowOffset h - Real.log (A.exteriorNorm secondCommon * A.exteriorNorm (J₂ i))) χ := by
  have hG₁ : 0 < G₁ := div_pos
    (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (idealNorm_pos K _))
    (idealNorm_pos K _)
  have hG₂ : 0 < G₂ := div_pos
    (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (idealNorm_pos K _))
    (idealNorm_pos K _)
  have hH₁ : 0 < H₁ comparison := by
    apply div_pos _ (idealNorm_pos K _)
    apply div_pos _ (idealNorm_pos K _)
    cases comparison
    · exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    · exact (hcomparison rfl).1
  have hH₂ : 0 < H₂ comparison := by
    apply div_pos _ (idealNorm_pos K _)
    apply div_pos _ (idealNorm_pos K _)
    cases comparison
    · exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    · exact (hcomparison rfl).2.1
  let f := secondResidualCoreRectangularFactors rows (data x) Q.correction prefix
    (Q.remaining * exteriorMomentIdeal common) idx hroot hemb side χ (poolTable comparison)
    b₂ secondCommon secondTilt J₂ hJ₂ hZ
    (fun j => ((data x).geometry.slots (idx j)).length_pos)
    (H₁ comparison) (H₂ comparison) Gslots hH₁ hH₂
    (fun _ => Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) rowOffset
  refine { f with gaussScale₁ := G₁, gaussScale₂ := G₂,
    gaussScale₁_pos := hG₁, gaussScale₂_pos := hG₂, coefficient_factor := ?_ }
  intro i hi
  rw [normalizedCoefficient_plain_product f.dictionary G₁ G₂ Gslots
    (H₁ comparison) (H₂ comparison) hG₁.le hH₁.le
    (pool_plain_product x a Z Y₁ Y₂ S₁ S₂ S firstCommon p v b secondCommon b₂
      comparison (fun hc => (hcomparison hc).2.2)) i]
  exact f.coefficient_factor i hi

local notation "coreFactor" => originalPoolSecondCoreFactors Q x W a Z t Y₁ Y₂
  S₁ S₂ S firstCommon p v hv b C primes m n firstRight δ tilt ξ hroot hemb
  J hJ hactive side χ rows secondCommon b₂ J₂ hJ₂ secondTilt rowOffset hZ

/-- The actual pool comparison changes the two original plain profiles
only. The original reciprocal pool character, common scalar, retained
slots, ray, and nominal Gauss normalizers remain the same fields. -/
def originalPoolSecondCoreComparison
    (hcomparison : 0 < Y₁ ∧ 0 < Y₂ ∧ Y₁ * Y₂ = Z ^ a.n₁ * Z ^ a.n₂) :
    SecondCoefficientComparison (coreFactor false (by simp)).dictionary where
  leftAtom := (coreFactor true (fun _ => hcomparison)).dictionary.leftAtom
  rightAtom := (coreFactor true (fun _ => hcomparison)).dictionary.rightAtom
  scale₁ := (coreFactor true (fun _ => hcomparison)).dictionary.scale₁
  scale₂ := (coreFactor true (fun _ => hcomparison)).dictionary.scale₂
  leftWeight := (coreFactor true (fun _ => hcomparison)).dictionary.leftWeight
  rightWeight := (coreFactor true (fun _ => hcomparison)).dictionary.rightWeight
  plain₁ := (coreFactor true (fun _ => hcomparison)).dictionary.plain₁
  plain₂ := (coreFactor true (fun _ => hcomparison)).dictionary.plain₂

local notation "coreComparison" => originalPoolSecondCoreComparison Q x W a Z t Y₁ Y₂
  S₁ S₂ S firstCommon p v hv b C primes m n firstRight δ tilt ξ hroot hemb
  J hJ hactive side χ rows secondCommon b₂ J₂ hJ₂ secondTilt rowOffset hZ

@[simp] theorem originalPoolSecondCoreComparison_dictionary
    (hcomparison : 0 < Y₁ ∧ 0 < Y₂ ∧ Y₁ * Y₂ = Z ^ a.n₁ * Z ^ a.n₂) :
    (coreComparison hcomparison).dictionary =
      (coreFactor true (fun _ => hcomparison)).dictionary := rfl

theorem originalPoolSecondCoreComparison_coefficient
    (hcomparison : 0 < Y₁ ∧ 0 < Y₂ ∧ Y₁ * Y₂ = Z ^ a.n₁ * Z ^ a.n₂)
    (i : AllocationColumn K b₂.keep.card) (hi : i ∈ b₂.residualColumns) :
    (coreComparison hcomparison).centeredCoefficient
        (Real.sqrt G₁ : ℂ)⁻¹ (Real.sqrt G₂ : ℂ)⁻¹
        (fun j => (Real.sqrt (Gslots j) : ℂ)⁻¹) i =
      originalPoolSecondCoreCoefficient Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon p v hv b
          C primes m n firstRight δ tilt ξ hroot hemb J hJ hactive side χ
          secondCommon b₂ J₂ secondTilt false i -
        originalPoolSecondCoreCoefficient Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon p v hv b
          C primes m n firstRight δ tilt ξ hroot hemb J hJ hactive side χ
          secondCommon b₂ J₂ secondTilt true i := by
  rw [SecondCoefficientComparison.centeredCoefficient,
    originalPoolSecondCoreComparison_dictionary]
  exact congrArg₂ (fun z w : ℂ => z - w)
    ((coreFactor false (by simp)).coefficient_factor i hi).symm
    ((coreFactor true (fun _ => hcomparison)).coefficient_factor i hi).symm

/-- Both complete original pool rectangles share the very same scalar
before Cauchy. Their full difference is retained in the core comparison. -/
theorem originalPoolSecondSource_centered_to_core
    (hcommon : frozenSourceIdeal b₂.plainDivisor₁ b₂.plainDivisor₂ b₂.keep b₂.witness.2 =
      secondCommon.val)
    (hcomparison : 0 < Y₁ ∧ 0 < Y₂ ∧ Y₁ * Y₂ = Z ^ a.n₁ * Z ^ a.n₂)
    (i : AllocationColumn K b₂.keep.card) (hi : i ∈ b₂.residualColumns) :
    poolCoefficient false (b₂.reconstruct i) * weight₂ (J (b₂.reconstruct i)).val -
        poolCoefficient true (b₂.reconstruct i) * weight₂ (J (b₂.reconstruct i)).val =
      originalPoolSecondCommonScalar Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon p v hv b
          C primes m n firstRight δ tilt ξ hroot hemb J hJ hactive side χ
          secondCommon b₂ secondTilt *
        (coreComparison hcomparison).centeredCoefficient
          (Real.sqrt G₁ : ℂ)⁻¹ (Real.sqrt G₂ : ℂ)⁻¹
          (fun j => (Real.sqrt (Gslots j) : ℂ)⁻¹) i := by
  rw [originalPoolSecondSource_to_core Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon p v hv b
      C primes m n firstRight δ tilt ξ hroot hemb J hJ hactive side χ
      secondCommon b₂ J₂ hJ₂ secondTilt hcommon false i hi,
    originalPoolSecondSource_to_core Q x W a Z t Y₁ Y₂ S₁ S₂ S firstCommon p v hv b
      C primes m n firstRight δ tilt ξ hroot hemb J hJ hactive side χ
      secondCommon b₂ J₂ hJ₂ secondTilt hcommon true i hi,
    originalPoolSecondCoreComparison_coefficient Q x W a Z t Y₁ Y₂
      S₁ S₂ S firstCommon p v hv b C primes m n firstRight δ tilt ξ hroot hemb
      J hJ hactive side χ rows secondCommon b₂ J₂ hJ₂ secondTilt rowOffset hZ hcomparison i hi,
    mul_sub]

end ActualOriginalPool

end HeckeSkeleton.Moments.EngineStep.CanonicalActualPoolRectangles

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualPoolRectangles.poolDictionary
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualPoolRectangles.originalPoolCoefficient_eq
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualPoolRectangles.originalPoolSecondFactors
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualPoolRectangles.originalPoolSecondSource_to_core
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalActualPoolRectangles.originalPoolSecondSource_centered_to_core
