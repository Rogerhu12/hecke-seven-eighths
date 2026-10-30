import HeckeSkeleton.LowEnergy.ActualFrozenIndependence
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Exact reflection-index reindexing by frozen state and full cube

The minimum-zero condition is retained in `canonical`: at a prime with
minimum exponent zero the supported cube exponent must also be zero.
The column condition is independent of the active marks.  The only additional
mark condition is `(P,b)=1`, later extended by zero as an explicit mask.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.ActualReflectionReindex

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowFrozenCube
open HeckeSkeleton.LowEnergy.IdealRows HeckeSkeleton.LowEnergy.FrozenIdealRows
open HeckeSkeleton.LowEnergy.ActualReflection HeckeSkeleton.LowEnergy.ActualFrozenCube
open HeckeSkeleton.LowEnergy.ActualFrozenIndependence
open HeckeSkeleton.LowEnergy.ActualFrozenMajorant HeckeSkeleton.LowEnergy.ActualLocalWeylTable
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem mem_image_prime_val (F : Finset (ExteriorPrime K S)) (p : ExteriorPrime K S) :
    p.val ∈ F.image Subtype.val ↔ p ∈ F := by
  constructor
  · intro hp
    obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hp
    exact (Subtype.ext he : q = p) ▸ hq
  · intro hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

def supportedExterior (F : Finset (ExteriorPrime K S)) (b : ExteriorIdeal K S) :
    ExteriorIdeal K S :=
  ⟨supportedIdeal (F.image Subtype.val) b.val,
    fun p hp => b.property p (dvd_trans hp (supportedIdeal_dvd _ _))⟩

def awayExterior (F : Finset (ExteriorPrime K S)) (b : ExteriorIdeal K S) :
    ExteriorIdeal K S :=
  ⟨awayIdeal (F.image Subtype.val) b.val,
    fun p hp => b.property p (dvd_trans hp (awayIdeal_dvd _ _))⟩

theorem supportedExterior_support (F : Finset (ExteriorPrime K S)) (b : ExteriorIdeal K S) :
    exteriorSupport K S (supportedExterior K S F b) ⊆ F := by
  intro p hp
  have he := (exponent_ne_zero_iff_dvd (supportedExterior K S F b).val p.val).mpr
    ((mem_exteriorSupport_iff K S _ p).mp hp)
  change primeExponents (supportedIdeal (F.image Subtype.val) b.val) p.val ≠ 0 at he
  rw [exponent_supportedIdeal] at he
  by_contra hnot
  rw [if_neg (fun h => hnot ((mem_image_prime_val K S F p).mp h))] at he
  exact he rfl

theorem supported_away_exterior (F : Finset (ExteriorPrime K S)) (b : ExteriorIdeal K S) :
    exteriorMul K S (supportedExterior K S F b) (awayExterior K S F b) = b := by
  apply Subtype.ext
  exact supported_away_decomposition _ _

theorem awayExterior_coprime (F : Finset (ExteriorPrime K S)) (b : ExteriorIdeal K S) :
    IsCoprime (awayExterior K S F b).val.val (primeSetIdeal K S F).val.val := by
  apply Ideal.coprime_of_no_prime_ge
  intro P hn hF hprime
  have hP0 : P ≠ ⊥ := by
    intro hz
    exact nonZeroDivisors.coe_ne_zero (awayExterior K S F b).val (le_bot_iff.mp (hz ▸ hn))
  let p : HeightOneSpectrum (𝓞 K) := ⟨P, hprime, hP0⟩
  let ep : ExteriorPrime K S := ⟨p, (awayExterior K S F b).property p
    (Ideal.dvd_iff_le.mpr hn)⟩
  have hp : ep ∈ F := (prime_dvd_primeSetIdeal_iff K S F ep).mp
    (Ideal.dvd_iff_le.mpr hF)
  have he := (exponent_ne_zero_iff_dvd (awayExterior K S F b).val p).mpr
    (Ideal.dvd_iff_le.mpr hn)
  change primeExponents (awayIdeal (F.image Subtype.val) b.val) p ≠ 0 at he
  rw [exponent_awayIdeal, if_neg (by simpa only [not_not] using
    (mem_image_prime_val K S F ep).mpr hp)] at he
  exact he rfl

/-- Frozen state contains no moving row and no active marked ideal. -/
structure FrozenState (frozen puncture : ExteriorIdeal K S) where
  active : Finset (ExteriorPrime K S)
  active_subset : active ⊆ exteriorSupport K S frozen ∪ exteriorSupport K S puncture
  nonzero_active : ∀ p ∈ exteriorSupport K S frozen ∪ exteriorSupport K S puncture,
    (frozenDigit K S frozen p).val ≠ 0 → p ∈ active
  minimum : ExteriorIdeal K S
  minimum_support : exteriorSupport K S minimum ⊆ active
  minimum_values : ∀ p : HeightOneSpectrum (𝓞 K),
    primeExponents minimum.val p = 0 ∨ primeExponents minimum.val p = 1 ∨
      primeExponents minimum.val p = 3
  unitSector : SixthUnitClasses K S

theorem FrozenState.ext {frozen puncture : ExteriorIdeal K S}
    {s t : FrozenState K S frozen puncture}
    (hF : s.active = t.active) (hm : s.minimum = t.minimum)
    (hu : s.unitSector = t.unitSector) : s = t := by
  cases s
  cases t
  cases hF
  cases hm
  cases hu
  rfl

def toFrozenState (d : MarkedDatum K S) (i : ReflectionIndex K S d) :
    FrozenState K S d.frozen d.puncture where
  active := i.activeFrozen
  active_subset := i.frozen_subset
  nonzero_active := by
    intro p hp hn
    apply i.nonzero_active hp
    rw [rowDigit_frozen_primes K S d p hp]
    exact hn
  minimum := numeratorMinimum K S d i
  minimum_support := by
    rw [numeratorMinimum_support]
    exact i.frozen_support
  minimum_values := by
    intro p
    change primeExponents (minimumPart i.numeratorFrozen.val) p = 0 ∨
      primeExponents (minimumPart i.numeratorFrozen.val) p = 1 ∨
      primeExponents (minimumPart i.numeratorFrozen.val) p = 3
    simp only [exponent_minimumPart]
    exact frozenMin_cases _
  unitSector := i.unitSector

/-- All constraints involving c and b before the moving active-mark mask. -/
def ColumnCondition {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) (c b : ExteriorIdeal K S) : Prop :=
  Squarefree c.val.val ∧ IsCoprime c.val.val (primeSetIdeal K S s.active).val.val ∧
  ∀ p : HeightOneSpectrum (𝓞 K),
    CanonicalFrozenPair (primeExponents s.minimum.val p)
      (primeExponents (supportedExterior K S s.active b).val p)

abbrev FrozenColumn {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) :=
  {cb : ExteriorIdeal K S × ExteriorIdeal K S // ColumnCondition K S s cb.1 cb.2}

/-- Nondependent data fields make the actual reindexing equality transparent. -/
structure ReflectionCoordinates (d : MarkedDatum K S) where
  state : FrozenState K S d.frozen d.puncture
  marks : Finset (ExteriorPrime K S)
  marks_subset : marks ⊆ d.marks
  c : ExteriorIdeal K S
  b : ExteriorIdeal K S
  column : ColumnCondition K S state c b
  marked_coprime : IsCoprime (primeSetIdeal K S marks).val.val b.val.val

theorem ReflectionCoordinates.ext {d : MarkedDatum K S} {r t : ReflectionCoordinates K S d}
    (hs : r.state = t.state) (hP : r.marks = t.marks) (hc : r.c = t.c) (hb : r.b = t.b) :
    r = t := by
  cases r
  cases t
  cases hs
  cases hP
  cases hc
  cases hb
  rfl

def toCoordinates (d : MarkedDatum K S) (i : ReflectionIndex K S d) :
    ReflectionCoordinates K S d where
  state := toFrozenState K S d i
  marks := i.activeMarks
  marks_subset := i.marks_subset
  c := i.c
  b := fullCubeIdeal K S d i
  column := by
    refine ⟨i.c_squarefree, i.c_coprime, ?_⟩
    intro p
    have hx := congrArg Prod.fst (fullCubeSplit_actual K S d i)
    change supportedIdeal (i.activeFrozen.image Subtype.val) (fullCubeIdeal K S d i).val =
      (numeratorCube K S d i).val at hx
    change CanonicalFrozenPair (primeExponents (minimumPart i.numeratorFrozen.val) p)
      (primeExponents (supportedIdeal (i.activeFrozen.image Subtype.val)
        (fullCubeIdeal K S d i).val) p)
    rw [hx]
    change CanonicalFrozenPair (primeExponents (minimumPart i.numeratorFrozen.val) p)
      (primeExponents (cubePart i.numeratorFrozen.val) p)
    rw [exponent_minimumPart, exponent_cubePart]
    exact frozenPair_canonical _
  marked_coprime := (fullCube_coprime_activeMarked K S d i).symm

def coordinatesNumerator (d : MarkedDatum K S) (r : ReflectionCoordinates K S d) :
    ExteriorIdeal K S :=
  exteriorMul K S r.state.minimum (exteriorPower K S (supportedExterior K S r.state.active r.b) 3)

def fromCoordinates (d : MarkedDatum K S) (r : ReflectionCoordinates K S d) :
    ReflectionIndex K S d where
  activeMarks := r.marks
  marks_subset := r.marks_subset
  activeFrozen := r.state.active
  frozen_subset := r.state.active_subset
  nonzero_active := by
    intro p hp hn
    apply r.state.nonzero_active p hp
    rwa [← rowDigit_frozen_primes K S d p hp]
  numeratorFrozen := coordinatesNumerator K S d r
  frozen_support := by
    intro p hp
    have hd := (mem_exteriorSupport_iff K S _ p).mp hp
    change p.val.asIdeal ∣ r.state.minimum.val.val *
      (supportedExterior K S r.state.active r.b).val.val ^ 3 at hd
    rcases p.val.prime.dvd_mul.mp hd with hm | hx
    · exact r.state.minimum_support ((mem_exteriorSupport_iff K S _ p).mpr hm)
    · exact supportedExterior_support K S _ _
        ((mem_exteriorSupport_iff K S _ p).mpr (p.val.prime.dvd_of_dvd_pow hx))
  frozen_digits := by
    intro p
    have hc := r.column.2.2 p.val
    have ha : AdmissibleExponent (primeExponents r.state.minimum.val p.val +
        3 * primeExponents (supportedExterior K S r.state.active r.b).val p.val) :=
      canonicalPair_admissible hc rfl
    change primeExponents (r.state.minimum.val *
      (supportedExterior K S r.state.active r.b).val ^ 3) p.val % 3 ≠ 2
    rw [primeExponents_mul, Finsupp.add_apply, exponent_pow]
    unfold AdmissibleExponent at ha
    omega
  n := awayExterior K S r.state.active r.b
  n_coprime := by
    apply IsCoprime.mul_right
    · exact awayExterior_coprime K S r.state.active r.b
    · exact (r.marked_coprime.of_isCoprime_of_dvd_right
        (awayIdeal_dvd (r.state.active.image Subtype.val) r.b.val)).symm
  c := r.c
  c_squarefree := r.column.1
  c_coprime := r.column.2.1
  unitSector := r.state.unitSector

theorem reflectionIndex_ext {d : MarkedDatum K S} {i j : ReflectionIndex K S d}
    (hP : i.activeMarks = j.activeMarks) (hF : i.activeFrozen = j.activeFrozen)
    (ha : i.numeratorFrozen = j.numeratorFrozen) (hn : i.n = j.n)
    (hc : i.c = j.c) (hu : i.unitSector = j.unitSector) : i = j := by
  cases i
  cases j
  cases hP
  cases hF
  cases ha
  cases hn
  cases hc
  cases hu
  rfl

theorem from_toCoordinates (d : MarkedDatum K S) (i : ReflectionIndex K S d) :
    fromCoordinates K S d (toCoordinates K S d i) = i := by
  apply reflectionIndex_ext K S rfl rfl _ _ rfl rfl
  · have hx : supportedExterior K S i.activeFrozen (fullCubeIdeal K S d i) =
        numeratorCube K S d i := by
      apply Subtype.ext
      exact congrArg Prod.fst (fullCubeSplit_actual K S d i)
    change exteriorMul K S (numeratorMinimum K S d i)
      (exteriorPower K S (supportedExterior K S i.activeFrozen (fullCubeIdeal K S d i)) 3) = _
    rw [hx]
    exact numerator_minimum_cube K S d i
  · apply Subtype.ext
    exact congrArg Prod.snd (fullCubeSplit_actual K S d i)

theorem minimum_fromCoordinates (d : MarkedDatum K S) (r : ReflectionCoordinates K S d) :
    numeratorMinimum K S d (fromCoordinates K S d r) = r.state.minimum := by
  apply Subtype.ext
  exact (minimum_cube_unique (coordinatesNumerator K S d r).val r.state.minimum.val
    (supportedExterior K S r.state.active r.b).val r.column.2.2 rfl).1.symm

theorem cube_fromCoordinates (d : MarkedDatum K S) (r : ReflectionCoordinates K S d) :
    numeratorCube K S d (fromCoordinates K S d r) = supportedExterior K S r.state.active r.b := by
  apply Subtype.ext
  exact (minimum_cube_unique (coordinatesNumerator K S d r).val r.state.minimum.val
    (supportedExterior K S r.state.active r.b).val r.column.2.2 rfl).2.symm

theorem to_fromCoordinates (d : MarkedDatum K S) (r : ReflectionCoordinates K S d) :
    toCoordinates K S d (fromCoordinates K S d r) = r := by
  apply ReflectionCoordinates.ext K S _ rfl rfl _
  · apply FrozenState.ext K S rfl _ rfl
    exact minimum_fromCoordinates K S d r
  · change exteriorMul K S (numeratorCube K S d (fromCoordinates K S d r))
      (awayExterior K S r.state.active r.b) = r.b
    rw [cube_fromCoordinates]
    exact supported_away_exterior K S r.state.active r.b

def reflectionCoordinatesEquiv (d : MarkedDatum K S) :
    ReflectionIndex K S d ≃ ReflectionCoordinates K S d where
  toFun := toCoordinates K S d
  invFun := fromCoordinates K S d
  left_inv := from_toCoordinates K S d
  right_inv := to_fromCoordinates K S d

abbrev MarkChoice (d : MarkedDatum K S) :=
  {A : Finset (ExteriorPrime K S) // A ⊆ d.marks}

abbrev MarkedColumn {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) (A : Finset (ExteriorPrime K S)) :=
  {cb : FrozenColumn K S s // IsCoprime (primeSetIdeal K S A).val.val cb.val.2.val.val}

abbrev ReflectionSigma (d : MarkedDatum K S) :=
  Σ s : FrozenState K S d.frozen d.puncture, Σ A : MarkChoice K S d, MarkedColumn K S s A.val

def coordinatesSigmaEquiv (d : MarkedDatum K S) :
    ReflectionCoordinates K S d ≃ ReflectionSigma K S d where
  toFun r := ⟨r.state, ⟨r.marks, r.marks_subset⟩,
    ⟨⟨(r.c, r.b), r.column⟩, r.marked_coprime⟩⟩
  invFun r := {
    state := r.1, marks := r.2.1.val, marks_subset := r.2.1.property,
    c := r.2.2.val.val.1, b := r.2.2.val.val.2,
    column := r.2.2.val.property, marked_coprime := r.2.2.property }
  left_inv r := by cases r; rfl
  right_inv r := by
    rcases r with ⟨s, ⟨A, hA⟩, ⟨⟨⟨c, b⟩, hcol⟩, hP⟩⟩
    rfl

def reflectionSigmaEquiv (d : MarkedDatum K S) :
    ReflectionIndex K S d ≃ ReflectionSigma K S d :=
  (reflectionCoordinatesEquiv K S d).trans (coordinatesSigmaEquiv K S d)

/-- A common column can be evaluated with no marked ideal at all. -/
def commonColumnCoordinates (d : MarkedDatum K S)
    (s : FrozenState K S d.frozen d.puncture) (cb : FrozenColumn K S s) :
    ReflectionCoordinates K S (frozenOnlyDatum K S d) where
  state := s
  marks := ∅
  marks_subset := Finset.empty_subset _
  c := cb.val.1
  b := cb.val.2
  column := cb.property
  marked_coprime := by rw [emptyPrimeIdeal_val]; exact isCoprime_one_left

def commonColumnIndex (d : MarkedDatum K S)
    (s : FrozenState K S d.frozen d.puncture) (cb : FrozenColumn K S s) :
    ReflectionIndex K S (frozenOnlyDatum K S d) :=
  fromCoordinates K S (frozenOnlyDatum K S d) (commonColumnCoordinates K S d s cb)

theorem frozenOnly_fromCoordinates (d : MarkedDatum K S) (r : ReflectionCoordinates K S d) :
    frozenOnlyIndex K S d (fromCoordinates K S d r) =
      commonColumnIndex K S d r.state ⟨(r.c, r.b), r.column⟩ := by
  apply reflectionIndex_ext K S <;> rfl

/-- The shared dual coefficient has no active-mark argument. -/
def commonDualCoefficient (D : ThetaArithmeticData K S) (θ : HeckeCharacter K)
    (d : MarkedDatum K S) (s : FrozenState K S d.frozen d.puncture)
    (cb : FrozenColumn K S s) : ℂ :=
  fullCubeCoefficient K S D (frozenOnlyDatum K S d) (commonColumnIndex K S d s cb) θ

theorem fullCubeCoefficient_fromCoordinates (D : ThetaArithmeticData K S)
    (θ : HeckeCharacter K) (d : MarkedDatum K S) (r : ReflectionCoordinates K S d) :
    fullCubeCoefficient K S D d (fromCoordinates K S d r) θ =
      commonDualCoefficient K S D θ d r.state ⟨(r.c, r.b), r.column⟩ := by
  rw [fullCubeCoefficient_frozenOnly K S D d (fromCoordinates K S d r) θ,
    frozenOnly_fromCoordinates]
  rfl

def stateMajorant {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) : ℝ :=
  ∏ p ∈ s.active, minimumMajorant K S p (frozenDigit K S frozen p)
    (primeExponents s.minimum.val p.val)

theorem stateMajorant_nonneg {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) : 0 ≤ stateMajorant K S s :=
  Finset.prod_nonneg (fun p _ => minimumMajorant_nonneg K S p _ _)

theorem frozenMajorant_eq_state (d : MarkedDatum K S) (i : ReflectionIndex K S d) :
    frozenMajorant K S d i = stateMajorant K S (toFrozenState K S d i) := by
  unfold frozenMajorant stateMajorant
  apply Finset.prod_congr rfl
  intro p hp
  rw [rowDigit_frozen_primes K S d p (i.frozen_subset hp)]
  change minimumMajorant K S p (frozenDigit K S d.frozen p)
      (frozenMin (primeExponents i.numeratorFrozen.val p.val)) =
    minimumMajorant K S p (frozenDigit K S d.frozen p)
      (primeExponents (minimumPart i.numeratorFrozen.val) p.val)
  rw [exponent_minimumPart]

theorem commonColumn_fullCube (d : MarkedDatum K S)
    (s : FrozenState K S d.frozen d.puncture) (cb : FrozenColumn K S s) :
    fullCubeIdeal K S (frozenOnlyDatum K S d) (commonColumnIndex K S d s cb) = cb.val.2 := by
  have h := congrArg ReflectionCoordinates.b
    (to_fromCoordinates K S (frozenOnlyDatum K S d) (commonColumnCoordinates K S d s cb))
  exact h

theorem commonColumn_state (d : MarkedDatum K S)
    (s : FrozenState K S d.frozen d.puncture) (cb : FrozenColumn K S s) :
    toFrozenState K S (frozenOnlyDatum K S d) (commonColumnIndex K S d s cb) = s := by
  exact congrArg ReflectionCoordinates.state
    (to_fromCoordinates K S (frozenOnlyDatum K S d) (commonColumnCoordinates K S d s cb))

/-- The same charged scalar bounds the coefficient on every common column. -/
theorem commonDualCoefficient_norm_le (D : ThetaArithmeticData K S) (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (d : MarkedDatum K S) (s : FrozenState K S d.frozen d.puncture)
    (cb : FrozenColumn K S s) :
    ‖commonDualCoefficient K S D θ d s cb‖ ≤ stateMajorant K S s /
      (Real.sqrt (exteriorNorm K S cb.val.1) * exteriorNorm K S cb.val.2) := by
  have h := fullCubeCoefficient_norm_le K S D (frozenOnlyDatum K S d)
    (commonColumnIndex K S d s cb) θ hθ
  rw [frozenMajorant_eq_state, commonColumn_state, commonColumn_fullCube] at h
  exact h

/-- An actual norm ball in exterior ideals is finite, using the actual ideal norm theorem. -/
theorem finite_exteriorNorm_le (X : ℝ) :
    Set.Finite {I : ExteriorIdeal K S | exteriorNorm K S I ≤ X} := by
  have hi : Set.InjOn (fun I : ExteriorIdeal K S => I.val.val)
      ((fun I : ExteriorIdeal K S => I.val.val) ⁻¹'
        {J : Ideal (𝓞 K) | J.absNorm ≤ Nat.ceil X}) := by
    intro I _ J _ h
    exact Subtype.ext (Subtype.ext h)
  apply (Set.Finite.preimage hi (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) (Nat.ceil X))).subset
  intro I hI
  change I.val.val.absNorm ≤ Nat.ceil X
  have h : (I.val.val.absNorm : ℝ) ≤ (Nat.ceil X : ℝ) := hI.trans (Nat.le_ceil X)
  exact_mod_cast h

def exteriorNormBall (X : ℝ) : Finset (ExteriorIdeal K S) :=
  (finite_exteriorNorm_le K S X).toFinset

@[simp] theorem mem_exteriorNormBall (X : ℝ) (I : ExteriorIdeal K S) :
    I ∈ exteriorNormBall K S X ↔ exteriorNorm K S I ≤ X :=
  Set.Finite.mem_toFinset _

def extendColumn {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) (f : FrozenColumn K S s → ℂ)
    (c b : ExteriorIdeal K S) : ℂ :=
  if h : ColumnCondition K S s c b then f ⟨(c, b), h⟩ else 0

theorem tsum_extendColumn {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) (f : FrozenColumn K S s → ℂ) :
    (∑' cb, f cb) = ∑' cb : ExteriorIdeal K S × ExteriorIdeal K S,
      extendColumn K S s f cb.1 cb.2 := by
  let g : ExteriorIdeal K S × ExteriorIdeal K S → ℂ :=
    fun cb => extendColumn K S s f cb.1 cb.2
  have hs : Function.support g ⊆ {cb | ColumnCondition K S s cb.1 cb.2} := by
    intro cb hcb
    by_contra h
    exact hcb (by simp [g, extendColumn, h])
  calc
    _ = ∑' cb : FrozenColumn K S s, g cb.val := by
      apply tsum_congr
      intro cb
      simp only [g, extendColumn, dif_pos cb.property]
    _ = _ := tsum_subtype_eq_of_support_subset hs

/-- A finite truncation is an exact common rectangle, with zero extension off
the inherited support.  Its supports depend only on N,B and the frozen state. -/
theorem truncated_columns_eq_rectangle {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) (f : FrozenColumn K S s → ℂ) (N B : ℝ) :
    (∑' cb : FrozenColumn K S s,
      if exteriorNorm K S cb.val.1 ≤ N ∧ exteriorNorm K S cb.val.2 ≤ B then f cb else 0) =
    ∑ c ∈ exteriorNormBall K S N, ∑ b ∈ exteriorNormBall K S B,
      extendColumn K S s f c b := by
  rw [tsum_extendColumn K S s]
  rw [tsum_eq_sum (s := exteriorNormBall K S N ×ˢ exteriorNormBall K S B) (by
    intro cb hcb
    have hcut : ¬(exteriorNorm K S cb.1 ≤ N ∧ exteriorNorm K S cb.2 ≤ B) := by
      simpa only [Finset.mem_product, mem_exteriorNormBall] using hcb
    unfold extendColumn
    split_ifs <;> simp_all)]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro b hb
  have hcut := And.intro ((mem_exteriorNormBall K S N c).mp hc)
    ((mem_exteriorNormBall K S B b).mp hb)
  unfold extendColumn
  split_ifs <;> simp_all

/-- Summability is used only for grouping the exact sigma-indexed series. -/
theorem tsum_reflectionSigma (d : MarkedDatum K S) (f : ReflectionIndex K S d → ℂ)
    (hf : Summable f) :
    (∑' i, f i) = ∑' s : FrozenState K S d.frozen d.puncture,
      ∑' A : MarkChoice K S d, ∑' cb : MarkedColumn K S s A.val,
        f ((reflectionSigmaEquiv K S d).symm ⟨s, A, cb⟩) := by
  let e := reflectionSigmaEquiv K S d
  have hs : Summable (fun z : ReflectionSigma K S d => f (e.symm z)) :=
    e.symm.summable_iff.mpr hf
  rw [← e.symm.tsum_eq, hs.tsum_sigma]
  apply tsum_congr
  intro s
  exact (hs.sigma_factor s).tsum_sigma

def extendMarkedColumn {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) (A : Finset (ExteriorPrime K S))
    (f : MarkedColumn K S s A → ℂ) (cb : FrozenColumn K S s) : ℂ :=
  if h : IsCoprime (primeSetIdeal K S A).val.val cb.val.2.val.val then f ⟨cb, h⟩ else 0

/-- The active mark restriction becomes an explicit zero mask on a common
column type; the full cube is never separated by an external Cauchy step. -/
theorem tsum_extendMarkedColumn {frozen puncture : ExteriorIdeal K S}
    (s : FrozenState K S frozen puncture) (A : Finset (ExteriorPrime K S))
    (f : MarkedColumn K S s A → ℂ) :
    (∑' cb, f cb) = ∑' cb : FrozenColumn K S s, extendMarkedColumn K S s A f cb := by
  let g := extendMarkedColumn K S s A f
  have hs : Function.support g ⊆
      {cb | IsCoprime (primeSetIdeal K S A).val.val cb.val.2.val.val} := by
    intro cb hcb
    by_contra h
    exact hcb (by simp [g, extendMarkedColumn, h])
  calc
    _ = ∑' cb : MarkedColumn K S s A, g cb.val := by
      apply tsum_congr
      intro cb
      simp only [g, extendMarkedColumn, dif_pos cb.property]
    _ = _ := tsum_subtype_eq_of_support_subset hs

/-- Exact marked reflection grouped by frozen states and common full-cube columns. -/
theorem completedThetaSum_reindexed (D : ThetaArithmeticData K S)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (d : MarkedDatum K S) (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X) :
    completedThetaSum K S D θ (rowElement K S D d) d.puncture d.marks V.toFun X =
      ∑' s : FrozenState K S d.frozen d.puncture, ∑' A : MarkChoice K S d,
        ∑' cb : FrozenColumn K S s, extendMarkedColumn K S s A.val
          (fun z => reflectedTerm K S D d
            ((reflectionSigmaEquiv K S d).symm ⟨s, A, z⟩) F θ V.toFun X) cb := by
  rw [hreflection.reflection d V X hX,
    tsum_reflectionSigma K S d _ (hreflection.reflected_absolute d V X hX)]
  apply tsum_congr
  intro s
  apply tsum_congr
  intro A
  exact tsum_extendMarkedColumn K S s A.val _

end HeckeSkeleton.LowEnergy.ActualReflectionReindex
