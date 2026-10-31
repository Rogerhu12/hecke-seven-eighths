import ThetaGlobal.GlobalProjectReflectedLocalModel

/-!
# The four literal phase blocks of the reflected local product

Every phase is evaluated on the actual frequency representative. The
support proof determines which generators are units at each place. The
remaining cube phase in a column has sixth power one and disappears
after the quadratic character is taken.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section

namespace ThetaGlobal.GlobalProjectReflectedPhases

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.GlobalProjectLocalDigitTables ThetaGlobal.GlobalProjectLocalPhases
open ThetaGlobal.GlobalProjectReflectedLocalModel
open scoped NumberField Classical BigOperators nonZeroDivisors

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)

local notation "Sf" => (R.A.Sf : Set (HeightOneSpectrum (𝓞 F)))
local notation "P" => ThetaBranch.ExteriorPrime R.A

variable (Adata : ThetaArithmeticData F Sf)

theorem removePrime_eq (I : ExteriorIdeal F Sf) (p : P)
    (hp : primeExponents I.val p.val = 0) : removePrime F Sf I (skeletonPrime R p) = I := by
  apply GlobalIndexSupport.exterior_ext F Sf
  intro q
  change primeExponents (idealOfPrimeExponents ((primeExponents I.val).erase p.val)) q.val = _
  rw [primeExponents_idealOfPrimeExponents]
  by_cases h : q.val = p.val
  · simp [h, hp]
  · rw [Finsupp.erase_ne h]

theorem exponent_zero (I : ExteriorIdeal F Sf) (p : P)
    (hp : p ∉ exteriorSupport F Sf I) : primeExponents I.val p.val = 0 :=
  not_ne_iff.mp (fun h => hp ((GlobalIndexSupport.mem_exteriorSupport F Sf I p).mpr h))

variable (hA : AllowedGeneratorInput F Sf Adata)
  (hgen : ∀ I : ExteriorIdeal F Sf,
    GlobalActualFrequency.generatorUnit F Sf Adata I =
      R.probe.allowed.generator ((HeckeAxiom.exteriorEquiv R.A).symm I))

include hA hgen in
theorem phase_generator_unit (p : P) (I : ExteriorIdeal F Sf)
    (hp : primeExponents I.val p.val = 0) :
    phaseHom R Adata p (GlobalActualFrequency.generatorUnit F Sf Adata I) =
      primeEvaluation F Sf Adata (skeletonPrime R p) (Adata.generator I) := by
  rw [phaseHom_generator R Adata hA hgen, removePrime_eq R I p hp]

variable (d : MarkedDatum F Sf) (i : ReflectionIndex F Sf d)
  (hi : Admissible R d i)

def evaluation (p : P) (I : ExteriorIdeal F Sf) : ℂ :=
  primeEvaluation F Sf Adata (skeletonPrime R p) (Adata.generator I)

def unitEvaluation (p : P) : ℂ :=
  primeEvaluation F Sf Adata (skeletonPrime R p)
    (Sf.unitEquivUnitsInteger F (frequencyUnit F Sf d i)).val

def movingPhase (p : P) : ℂ :=
  unitEvaluation R Adata d i p * evaluation R Adata p i.numeratorFrozen *
    evaluation R Adata p (removePrime F Sf d.moving (skeletonPrime R p)) ^ (-2 : ℤ) *
    evaluation R Adata p (activeFrozenIdeal F Sf d i) ^ (-2 : ℤ)

def frozenPhase (p : P) : ℂ :=
  unitEvaluation R Adata d i p *
    evaluation R Adata p (removePrime F Sf i.numeratorFrozen (skeletonPrime R p)) *
    evaluation R Adata p i.n ^ 3 *
    evaluation R Adata p (removePrime F Sf (activeFrozenIdeal F Sf d i) (skeletonPrime R p)) ^ (-2 : ℤ)

def markedPhase (p : P) : ℂ :=
  unitEvaluation R Adata d i p * evaluation R Adata p i.numeratorFrozen *
    evaluation R Adata p (removePrime F Sf (activeMarkedIdeal F Sf d i) (skeletonPrime R p)) ^ (-2 : ℤ) *
    evaluation R Adata p (activeFrozenIdeal F Sf d i) ^ (-2 : ℤ)

def columnPhase (p : P) : ℂ :=
  unitEvaluation R Adata d i p * evaluation R Adata p i.numeratorFrozen *
    evaluation R Adata p (removePrime F Sf i.c (skeletonPrime R p)) *
    evaluation R Adata p (activeFrozenIdeal F Sf d i) ^ (-2 : ℤ)

theorem primeSet_exponent_zero (T : Finset P) (p : P) (hp : p ∉ T) :
    primeExponents (primeSetIdeal F Sf T).val p.val = 0 := by
  rw [GlobalIndexSupport.exponent_primeSetIdeal, if_neg hp]

include hA hgen hi in
theorem moving_phase (p : P) (hp : p ∈ exteriorSupport F Sf d.moving) :
    unitPhase R Adata p (x R Adata d i) =
      movingPhase R Adata d i p * evaluation R Adata p i.c *
        evaluation R Adata p i.n ^ 3 *
        evaluation R Adata p (activeMarkedIdeal F Sf d i) ^ (-2 : ℤ) := by
  have ha : p ∉ i.activeFrozen ∪ i.activeMarks :=
    fun h => (Finset.disjoint_left.mp (moving_active_disjoint R d i)) hp h
  have hf : p ∉ i.activeFrozen := fun h => ha (Finset.mem_union_left _ h)
  have hm : p ∉ i.activeMarks := fun h => ha (Finset.mem_union_right _ h)
  change phaseHom R Adata p (GlobalActualFrequency.representative F Sf Adata d i) = _
  simp only [GlobalActualFrequency.representative, map_mul, map_pow, map_zpow,
    phaseHom_sUnit,
    phase_generator_unit R Adata hA hgen p i.numeratorFrozen (outside_a R d i p hf),
    phase_generator_unit R Adata hA hgen p i.c (hi.moving_c p hp),
    phase_generator_unit R Adata hA hgen p i.n (hi.moving_n p hp),
    phase_generator_unit R Adata hA hgen p (activeFrozenIdeal F Sf d i)
      (primeSet_exponent_zero R i.activeFrozen p hf),
    phase_generator_unit R Adata hA hgen p (activeMarkedIdeal F Sf d i)
      (primeSet_exponent_zero R i.activeMarks p hm),
    phaseHom_generator R Adata hA hgen p d.moving]
  simp only [movingPhase, evaluation, unitEvaluation]
  ring

include hA hgen hi in
theorem frozen_phase (p : P) (hp : p ∈ i.activeFrozen) :
    unitPhase R Adata p (x R Adata d i) =
      frozenPhase R Adata d i p * evaluation R Adata p i.c *
        evaluation R Adata p d.moving ^ (-2 : ℤ) *
        evaluation R Adata p (activeMarkedIdeal F Sf d i) ^ (-2 : ℤ) := by
  have ha : p ∈ i.activeFrozen ∪ i.activeMarks := Finset.mem_union_left _ hp
  have hm : p ∉ exteriorSupport F Sf d.moving :=
    fun h => (Finset.disjoint_left.mp (moving_active_disjoint R d i)) h ha
  have hmark : p ∉ i.activeMarks :=
    fun h => (Finset.disjoint_left.mp (marks_frozen_disjoint R d i)) h hp
  change phaseHom R Adata p (GlobalActualFrequency.representative F Sf Adata d i) = _
  simp only [GlobalActualFrequency.representative, map_mul, map_pow, map_zpow,
    phaseHom_sUnit,
    phase_generator_unit R Adata hA hgen p i.c (active_c R d i hi p ha),
    phase_generator_unit R Adata hA hgen p i.n (active_n R d i hi p ha),
    phase_generator_unit R Adata hA hgen p d.moving (exponent_zero R d.moving p hm),
    phase_generator_unit R Adata hA hgen p (activeMarkedIdeal F Sf d i)
      (primeSet_exponent_zero R i.activeMarks p hmark),
    phaseHom_generator R Adata hA hgen p i.numeratorFrozen,
    phaseHom_generator R Adata hA hgen p (activeFrozenIdeal F Sf d i)]
  simp only [frozenPhase, evaluation, unitEvaluation]
  ring

include hA hgen hi in
theorem marked_phase (p : P) (hp : p ∈ i.activeMarks) :
    unitPhase R Adata p (x R Adata d i) =
      markedPhase R Adata d i p * evaluation R Adata p i.c *
        evaluation R Adata p i.n ^ 3 * evaluation R Adata p d.moving ^ (-2 : ℤ) := by
  have ha : p ∈ i.activeFrozen ∪ i.activeMarks := Finset.mem_union_right _ hp
  have hm : p ∉ exteriorSupport F Sf d.moving :=
    fun h => (Finset.disjoint_left.mp (moving_active_disjoint R d i)) h ha
  have hf : p ∉ i.activeFrozen :=
    fun h => (Finset.disjoint_left.mp (marks_frozen_disjoint R d i)) hp h
  change phaseHom R Adata p (GlobalActualFrequency.representative F Sf Adata d i) = _
  simp only [GlobalActualFrequency.representative, map_mul, map_pow, map_zpow,
    phaseHom_sUnit,
    phase_generator_unit R Adata hA hgen p i.numeratorFrozen (outside_a R d i p hf),
    phase_generator_unit R Adata hA hgen p i.c (active_c R d i hi p ha),
    phase_generator_unit R Adata hA hgen p i.n (active_n R d i hi p ha),
    phase_generator_unit R Adata hA hgen p d.moving (exponent_zero R d.moving p hm),
    phase_generator_unit R Adata hA hgen p (activeFrozenIdeal F Sf d i)
      (primeSet_exponent_zero R i.activeFrozen p hf),
    phaseHom_generator R Adata hA hgen p (activeMarkedIdeal F Sf d i)]
  simp only [markedPhase, evaluation, unitEvaluation]
  ring

include hA hgen hi in
theorem column_phase (p : P) (hp : p ∈ exteriorSupport F Sf i.c) :
    unitPhase R Adata p (x R Adata d i) =
      columnPhase R Adata d i p *
        phaseHom R Adata p (GlobalActualFrequency.generatorUnit F Sf Adata i.n) ^ 3 *
        evaluation R Adata p d.moving ^ (-2 : ℤ) *
        evaluation R Adata p (activeMarkedIdeal F Sf d i) ^ (-2 : ℤ) := by
  have hc : primeExponents i.c.val p.val ≠ 0 :=
    (GlobalIndexSupport.mem_exteriorSupport F Sf i.c p).mp hp
  have ha : p ∉ i.activeFrozen ∪ i.activeMarks := fun h => hc (active_c R d i hi p h)
  have hf : p ∉ i.activeFrozen := fun h => ha (Finset.mem_union_left _ h)
  have hmark : p ∉ i.activeMarks := fun h => ha (Finset.mem_union_right _ h)
  have hm : p ∉ exteriorSupport F Sf d.moving := fun h => hc (hi.moving_c p h)
  change phaseHom R Adata p (GlobalActualFrequency.representative F Sf Adata d i) = _
  simp only [GlobalActualFrequency.representative, map_mul, map_pow, map_zpow,
    phaseHom_sUnit,
    phase_generator_unit R Adata hA hgen p i.numeratorFrozen (outside_a R d i p hf),
    phase_generator_unit R Adata hA hgen p d.moving (exponent_zero R d.moving p hm),
    phase_generator_unit R Adata hA hgen p (activeFrozenIdeal F Sf d i)
      (primeSet_exponent_zero R i.activeFrozen p hf),
    phase_generator_unit R Adata hA hgen p (activeMarkedIdeal F Sf d i)
      (primeSet_exponent_zero R i.activeMarks p hmark),
    phaseHom_generator R Adata hA hgen p i.c]
  simp only [columnPhase, evaluation, unitEvaluation]
  ring

theorem zpow_neg_two_pow (z : ℂ) (e : ℕ) :
    (z ^ (-2 : ℤ)) ^ e = z ^ (-(2 * e : ℤ)) := by
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  push_cast
  ring

def movingCore (p : P) : ℂ :=
  localWeylScalar F Sf Adata (skeletonPrime R p) ⟨1, by decide⟩ 0 * movingPhase R Adata d i p

def frozenCore (p : P) : ℂ :=
  localWeylScalar F Sf Adata (skeletonPrime R p) (rowDigit F Sf d p)
    (primeExponents i.numeratorFrozen.val p.val) *
    frozenPhase R Adata d i p ^
      localWeylExponent (rowDigit F Sf d p) (primeExponents i.numeratorFrozen.val p.val)

def markedCore (p : P) : ℂ :=
  thetaGamma F Sf Adata (exteriorPrimeIdeal F Sf (skeletonPrime R p)) 2 * markedPhase R Adata d i p ^ 2

def columnCore (p : P) : ℂ :=
  thetaGamma F Sf Adata (exteriorPrimeIdeal F Sf (skeletonPrime R p)) 2 * columnPhase R Adata d i p ^ 2

include hA hgen hi in
theorem movingLocal_split (p : P) (hp : p ∈ exteriorSupport F Sf d.moving) :
    movingLocal R Adata d i p = movingCore R Adata d i p *
      evaluation R Adata p i.c * evaluation R Adata p i.n ^ 3 *
      evaluation R Adata p (activeMarkedIdeal F Sf d i) ^ (-2 : ℤ) := by
  rw [movingLocal, moving_phase R Adata hA hgen d i hi p hp]
  simp only [movingCore]
  ring

include hA hgen hi in
theorem frozenLocal_split (p : P) (hp : p ∈ i.activeFrozen) :
    frozenLocal R Adata d i p = frozenCore R Adata d i p *
      evaluation R Adata p i.c ^
        localWeylExponent (rowDigit F Sf d p) (primeExponents i.numeratorFrozen.val p.val) *
      evaluation R Adata p d.moving ^
        (-(2 * localWeylExponent (rowDigit F Sf d p) (primeExponents i.numeratorFrozen.val p.val) : ℤ)) *
      evaluation R Adata p (activeMarkedIdeal F Sf d i) ^
        (-(2 * localWeylExponent (rowDigit F Sf d p) (primeExponents i.numeratorFrozen.val p.val) : ℤ)) := by
  rw [frozenLocal, frozen_phase R Adata hA hgen d i hi p hp]
  simp only [mul_pow, zpow_neg_two_pow, frozenCore]
  ring

include hA hgen hi in
theorem markedLocal_split (p : P) (hp : p ∈ i.activeMarks) :
    quadraticLocal R Adata d i p =
      (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)⁻¹ * markedCore R Adata d i p *
      evaluation R Adata p i.c ^ 2 * evaluation R Adata p i.n ^ 6 *
      evaluation R Adata p d.moving ^ (-4 : ℤ) := by
  rw [quadraticLocal, marked_phase R Adata hA hgen d i hi p hp]
  simp only [markedCore, mul_pow, zpow_neg, zpow_ofNat, inv_pow, ← pow_mul]
  ring

include hA hgen hi in
theorem columnLocal_split (p : P) (hp : p ∈ exteriorSupport F Sf i.c) :
    quadraticLocal R Adata d i p =
      (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)⁻¹ * columnCore R Adata d i p *
      evaluation R Adata p d.moving ^ (-4 : ℤ) *
      evaluation R Adata p (activeMarkedIdeal F Sf d i) ^ (-4 : ℤ) := by
  rw [quadraticLocal, column_phase R Adata hA hgen d i hi p hp]
  simp only [columnCore, mul_pow, zpow_neg, zpow_ofNat, inv_pow, ← pow_mul,
    show (3 : ℕ) * 2 = 6 from rfl, phaseHom_sixth R Adata p, one_mul, mul_one]
  ring

end ThetaGlobal.GlobalProjectReflectedPhases
