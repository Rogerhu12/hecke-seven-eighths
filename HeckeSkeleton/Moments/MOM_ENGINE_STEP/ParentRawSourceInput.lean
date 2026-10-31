import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ChildTermDictionary
import HeckeGeneral.Analysis.SUnitProfileFunctional

/-!
# A raw, individual-atom entrance to the original parent source

Both plain supports are the actual finite unions over the original
paired rows and both rectangles.  The slot supports are the original
prime-window supports.  All slots, including none, use the same finite
Cartesian expansion.  The entire centered difference is one coefficient.

The arithmetic/profile dictionary is required only for one plain ideal
or one slot prime.  The full polynomial identity is proved internally.
To obtain an orbital source, the analytic provider must additionally
construct the original Schwartz pair profiles with their pointwise
orbital Gram identity.  Single-variable smoothness or a rowwise seminorm
bound does not assert this mixed-profile construction.  That separate
primitive obligation is recorded literally, before any Poisson transform,
row sum, energy estimate or mass estimate.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- Both rectangles use the same computed finite ideal carrier. -/
def parentPlainCarrier (rows : Finset (HeckeGeneral.Analysis.NonzeroIdeal K))
    (W : IdealTest K) (t X Y : ℝ) : Finset (HeckeGeneral.Analysis.NonzeroIdeal K) :=
  rows.biUnion (fun u => W.support u t X ∪ W.support u t Y)

theorem parentPlainCarrier_contains
    (rows : Finset (HeckeGeneral.Analysis.NonzeroIdeal K))
    (W : IdealTest K) (t X Y : ℝ) (comparison : Bool)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (hu : u ∈ rows) :
    W.support u t (if comparison then Y else X) ⊆ parentPlainCarrier rows W t X Y := by
  intro I hI
  apply Finset.mem_biUnion.mpr
  refine ⟨u, hu, ?_⟩
  cases comparison with
  | false => exact Finset.mem_union_left _ hI
  | true => exact Finset.mem_union_right _ hI

def parentPlainAtom (d : MomentData K ω ψ) (W : IdealTest K)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (N t : ℝ)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) : ℂ :=
  (Real.sqrt N : ℂ)⁻¹ *
    (HeckeGeneral.Analysis.heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I *
      W.profile u t (HeckeGeneral.Analysis.idealNorm K I / N) * maskValue d u I.val)

def parentPrimeAtom (d : MomentData K ω ψ) (i : Fin d.geometry.slotCount)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (Z t : ℝ)
    (p : HeightOneSpectrum (𝓞 K)) : ℂ :=
  (Real.sqrt (Z ^ (d.geometry.slots i).length) : ℂ)⁻¹ *
    (primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p *
      (d.geometry.slots i).profile t
        ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length) *
          maskValue d u p.asIdeal)

/-- Primitive identities of individual actual summands.  The phase of
each plain is shared by its two scales, and every slot occurs once. -/
structure ParentRawAtoms (Q : Type*) (d : MomentData K ω ψ)
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) where
  rowMap : HeckeGeneral.Analysis.NonzeroIdeal K → Q
  leftCoefficient : Bool → Q → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ
  rightCoefficient : Bool → Q → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ
  primeCoefficient : Q → Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 K) → ℂ
  leftPhase : Q → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ
  rightPhase : Q → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ
  primePhase : Q → Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 K) → ℂ
  left : ∀ comparison u, u ∈ pairedRows d a Z →
    ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K,
      parentPlainAtom d d.plainTest₁ u (if comparison then Y₁ else Z ^ a.n₁) t I =
        leftCoefficient comparison (rowMap u) I * leftPhase (rowMap u) I
  right : ∀ comparison u, u ∈ pairedRows d a Z →
    ∀ I : HeckeGeneral.Analysis.NonzeroIdeal K,
      parentPlainAtom d d.plainTest₂ u (if comparison then Y₂ else Z ^ a.n₂) t I =
        rightCoefficient comparison (rowMap u) I * rightPhase (rowMap u) I
  prime : ∀ u, u ∈ pairedRows d a Z → ∀ i p,
    parentPrimeAtom d i u Z t p = primeCoefficient (rowMap u) i p * primePhase (rowMap u) i p

namespace ParentRawAtoms

variable {Q : Type*} {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable (raw : ParentRawAtoms Q d a Z t Y₁ Y₂)

abbrev Column (_raw : ParentRawAtoms Q d a Z t Y₁ Y₂) :=
  (HeckeGeneral.Analysis.NonzeroIdeal K × HeckeGeneral.Analysis.NonzeroIdeal K) ×
    (Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 K))

def leftColumns (_raw : ParentRawAtoms Q d a Z t Y₁ Y₂) :
    Finset (HeckeGeneral.Analysis.NonzeroIdeal K) :=
  parentPlainCarrier (pairedRows d a Z) d.plainTest₁ t (Z ^ a.n₁) Y₁

def rightColumns (_raw : ParentRawAtoms Q d a Z t Y₁ Y₂) :
    Finset (HeckeGeneral.Analysis.NonzeroIdeal K) :=
  parentPlainCarrier (pairedRows d a Z) d.plainTest₂ t (Z ^ a.n₂) Y₂

def slotColumns (_raw : ParentRawAtoms Q d a Z t Y₁ Y₂)
    (i : Fin d.geometry.slotCount) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length)

def columns : Finset raw.Column :=
  childCartesianColumns raw.leftColumns raw.rightColumns raw.slotColumns

def coefficient (centered : Bool) (q : Q) (v : raw.Column) : ℂ :=
  (raw.leftCoefficient false q v.1.1 * raw.rightCoefficient false q v.1.2 -
    if centered then
      raw.leftCoefficient true q v.1.1 * raw.rightCoefficient true q v.1.2 else 0) *
    ∏ i, raw.primeCoefficient q i (v.2 i)

def phase (q : Q) (v : raw.Column) : ℂ :=
  raw.leftPhase q v.1.1 * raw.rightPhase q v.1.2 *
    ∏ i, raw.primePhase q i (v.2 i)

def rectangleCoefficient (comparison : Bool) (q : Q) (v : raw.Column) : ℂ :=
  raw.leftCoefficient comparison q v.1.1 * raw.rightCoefficient comparison q v.1.2 *
    ∏ i, raw.primeCoefficient q i (v.2 i)

theorem coefficient_eq_rectangles (centered : Bool) (q : Q) (v : raw.Column) :
    raw.coefficient centered q v = raw.rectangleCoefficient false q v -
      if centered then raw.rectangleCoefficient true q v else 0 := by
  cases centered <;>
    simp only [coefficient, rectangleCoefficient, Bool.false_eq_true,
      ite_false, ite_true, sub_zero] <;> ring

private theorem cartesian_sum {X Y P : Type*} {k : ℕ}
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (a₁ : X → ℂ) (a₂ : Y → ℂ) (a₃ : Fin k → P → ℂ) :
    (∑ v ∈ childCartesianColumns S₁ S₂ S, childCartesianCoefficient a₁ a₂ a₃ v) =
      (∑ I ∈ S₁, a₁ I) * (∑ J ∈ S₂, a₂ J) * ∏ i, ∑ p ∈ S i, a₃ i p := by
  simpa [jointFourierColumn, childCartesianLocation, jointPhase] using
    (joint_cartesian_column_factorization (V := ℝ) S₁ S₂ S a₁ a₂ a₃
      (fun _ => 0) (fun _ => 0) (fun _ _ => 0) 0)

theorem coefficient_phase_sum (centered : Bool) (q : Q) :
    (∑ v ∈ raw.columns, raw.coefficient centered q v * raw.phase q v) =
      ((∑ I ∈ raw.leftColumns, raw.leftCoefficient false q I * raw.leftPhase q I) *
        (∑ J ∈ raw.rightColumns, raw.rightCoefficient false q J * raw.rightPhase q J) -
        if centered then
          (∑ I ∈ raw.leftColumns, raw.leftCoefficient true q I * raw.leftPhase q I) *
            (∑ J ∈ raw.rightColumns, raw.rightCoefficient true q J * raw.rightPhase q J)
        else 0) *
        ∏ i, ∑ p ∈ raw.slotColumns i, raw.primeCoefficient q i p * raw.primePhase q i p := by
  let rectangle (comparison : Bool) (v : raw.Column) : ℂ :=
    childCartesianCoefficient
      (fun I => raw.leftCoefficient comparison q I * raw.leftPhase q I)
      (fun J => raw.rightCoefficient comparison q J * raw.rightPhase q J)
      (fun i p => raw.primeCoefficient q i p * raw.primePhase q i p) v
  have hterm (v : raw.Column) : raw.coefficient centered q v * raw.phase q v =
      rectangle false v - if centered then rectangle true v else 0 := by
    cases centered <;>
      simp only [coefficient, phase, rectangle, childCartesianCoefficient,
        Bool.false_eq_true, ite_false, ite_true, sub_zero, Finset.prod_mul_distrib] <;> ring
  simp_rw [hterm]
  have hs (comparison : Bool) : (∑ v ∈ raw.columns, rectangle comparison v) =
      (∑ I ∈ raw.leftColumns, raw.leftCoefficient comparison q I * raw.leftPhase q I) *
        (∑ J ∈ raw.rightColumns, raw.rightCoefficient comparison q J * raw.rightPhase q J) *
          ∏ i, ∑ p ∈ raw.slotColumns i, raw.primeCoefficient q i p * raw.primePhase q i p :=
    cartesian_sum raw.leftColumns raw.rightColumns raw.slotColumns _ _ _
  cases centered with
  | false => simpa only [Bool.false_eq_true, ite_false, sub_zero] using hs false
  | true =>
    simp only [ite_true, Finset.sum_sub_distrib]
    rw [hs false, hs true]
    ring

theorem polynomial (centered : Bool) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hu : u ∈ pairedRows d a Z) :
    pairedStagePolynomial centered d u (Z ^ a.n₁) (Z ^ a.n₂) Y₁ Y₂ Z t =
      ∑ v ∈ raw.columns, raw.coefficient centered (raw.rowMap u) v * raw.phase (raw.rowMap u) v := by
  have hleft (comparison : Bool) :
      plainPolynomial d d.plainTest₁ u (if comparison then Y₁ else Z ^ a.n₁) t =
        ∑ I ∈ raw.leftColumns,
          raw.leftCoefficient comparison (raw.rowMap u) I * raw.leftPhase (raw.rowMap u) I := by
    rw [plainPolynomial_enlarge_support d d.plainTest₁ u _ t raw.leftColumns
      (parentPlainCarrier_contains (pairedRows d a Z) d.plainTest₁ t
        (Z ^ a.n₁) Y₁ comparison u hu)]
    apply Finset.sum_congr rfl
    intro I _
    simpa only [parentPlainAtom] using raw.left comparison u hu I
  have hright (comparison : Bool) :
      plainPolynomial d d.plainTest₂ u (if comparison then Y₂ else Z ^ a.n₂) t =
        ∑ I ∈ raw.rightColumns,
          raw.rightCoefficient comparison (raw.rowMap u) I * raw.rightPhase (raw.rowMap u) I := by
    rw [plainPolynomial_enlarge_support d d.plainTest₂ u _ t raw.rightColumns
      (parentPlainCarrier_contains (pairedRows d a Z) d.plainTest₂ t
        (Z ^ a.n₂) Y₂ comparison u hu)]
    apply Finset.sum_congr rfl
    intro I _
    simpa only [parentPlainAtom] using raw.right comparison u hu I
  have hslot : slotProduct d u Z t =
      ∏ i, ∑ p ∈ raw.slotColumns i,
        raw.primeCoefficient (raw.rowMap u) i p * raw.primePhase (raw.rowMap u) i p := by
    apply Finset.prod_congr rfl
    intro i _
    rw [primePolynomial_enlarge_support d i u Z t (raw.slotColumns i) (fun _ hp => hp)]
    exact Finset.sum_congr rfl (fun p _ => raw.prime u hu i p)
  have hleftMain := hleft false
  have hrightMain := hright false
  have hleftComparison := hleft true
  have hrightComparison := hright true
  simp only [Bool.false_eq_true, ite_false, ite_true] at hleftMain hrightMain hleftComparison hrightComparison
  rw [raw.coefficient_phase_sum, pairedStagePolynomial,
    hleftMain, hrightMain, hleftComparison, hrightComparison, hslot]

end ParentRawAtoms

section Orbital

open HeckeGeneral.Arithmetic HeckeGeneral.Analysis MeasureTheory

variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) [Γ.FiniteIndex]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

/-- The primitive analytic source obligation.  The Gram identity concerns
one original pair at one orbit.  It cannot be replaced by independent
rowwise profile bounds.  The finite source polynomial is not a field. -/
structure ParentRawOrbitalInput {d : MomentData K ω ψ} {a : RealParameters}
    {Z t Y₁ Y₂ : ℝ} (centered : Bool)
    (raw : ParentRawAtoms (SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ)
      d a Z t Y₁ Y₂)
    (pairs : raw.Column → raw.Column → ParentPeriodicPair K S Γ)
    (finiteTest : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (radius : {r : ℝ // 0 < r})
    (mask : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)))
    (fiberBound : ℕ) where
  weight : SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ → ℝ
  weight_nonneg : ∀ q, 0 ≤ weight q
  row_weight : ∀ u ∈ pairedRows d a Z, 1 ≤ weight (raw.rowMap u)
  row_mask : ∀ u ∈ pairedRows d a Z,
    sIntegerOrbitAvoidanceMask K _ Γ mask (raw.rowMap u) = 1
  fiber : ∀ q : SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ,
    ((pairedRows d a Z).filter (fun u => raw.rowMap u = q)).card ≤ fiberBound
  periodic : ∀ i ∈ raw.columns, ∀ j ∈ raw.columns, ∀ q,
    (pairs i j).orbitWeight q = raw.phase q i * star (raw.phase q j)
  gram : ∀ i ∈ raw.columns, ∀ j ∈ raw.columns, ∀ q,
    (pairs i j).orbitProfile finiteTest radius q =
      (weight q : ℂ) * (raw.coefficient centered q i * star (raw.coefficient centered q j))

variable {S Γ}

/-- The original parent calibration is constructed from genuine atom
and pair data.  No whole-polynomial equality or moment bound is an input. -/
def ParentRawOrbitalInput.toCalibration
    {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
    {centered : Bool}
    {raw : ParentRawAtoms (SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ)
      d a Z t Y₁ Y₂}
    {pairs : raw.Column → raw.Column → ParentPeriodicPair K S Γ}
    {finiteTest : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ}
    {radius : {r : ℝ // 0 < r}}
    {mask : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))}
    {fiberBound : ℕ}
    (source : ParentRawOrbitalInput S Γ centered raw pairs finiteTest radius mask fiberBound) :
    ParentSourceCalibration centered d a Z t Y₁ Y₂ raw.columns pairs
      finiteTest radius mask fiberBound where
  rowMap := raw.rowMap
  coefficient := raw.coefficient centered
  phase := raw.phase
  weight := source.weight
  weight_nonneg := source.weight_nonneg
  row_weight := source.row_weight
  row_mask := source.row_mask
  fiber := source.fiber
  polynomial := raw.polynomial centered
  periodic := source.periodic
  gram := source.gram

/-- Four original rectangle-pair profiles.  Their individual Gram
identities contain no centered coefficient, no sum over columns and no
transformed profile.  Centering will be performed by the actual linear
orbital integral. -/
structure ParentRectangleProfiles {d : MomentData K ω ψ} {a : RealParameters}
    {Z t Y₁ Y₂ : ℝ}
    (raw : ParentRawAtoms (SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ)
      d a Z t Y₁ Y₂)
    (finiteTest : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ)
    (radius : {r : ℝ // 0 < r})
    (weight : SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ → ℝ) where
  profile : Bool → Bool → raw.Column → raw.Column →
    SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ
  gram : ∀ comparison₁ comparison₂, ∀ i ∈ raw.columns, ∀ j ∈ raw.columns, ∀ q,
    sUnitOrbitalProfile K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K)))
        (profile comparison₁ comparison₂ i j) finiteTest)
      ⟨radius.val * (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val,
        mul_pos radius.property (sIntegerOrbitNorm K _ Γ q).property⟩ =
      (weight q : ℂ) *
        (raw.rectangleCoefficient comparison₁ q i * star (raw.rectangleCoefficient comparison₂ q j))

namespace ParentRectangleProfiles

variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable {raw : ParentRawAtoms (SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ)
  d a Z t Y₁ Y₂}
variable {finiteTest : ((v : (S : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ}
variable {radius : {r : ℝ // 0 < r}}
variable {weight : SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ → ℝ}

/-- The whole centered profile is formed before any absolute value.
The same four original rectangle profiles are used at the equal-product
quarter comparison scales, without changing a support or a slot. -/
def wholeProfile (profiles : ParentRectangleProfiles raw finiteTest radius weight)
    (centered : Bool) (i j : raw.Column) :
    SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ :=
  if centered then
    profiles.profile false false i j - profiles.profile false true i j -
      profiles.profile true false i j + profiles.profile true true i j
  else profiles.profile false false i j

theorem wholeProfile_gram (profiles : ParentRectangleProfiles raw finiteTest radius weight)
    (hTest : Continuous finiteTest)
    (hTestcs : HasCompactSupport finiteTest) (centered : Bool)
    (i : raw.Column) (hi : i ∈ raw.columns) (j : raw.Column) (hj : j ∈ raw.columns)
    (q : SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    sUnitOrbitalProfile K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sLocalTensorTestFunction K (S : Set (HeightOneSpectrum (𝓞 K)))
        (profiles.wholeProfile centered i j) finiteTest)
      ⟨radius.val * (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val,
        mul_pos radius.property (sIntegerOrbitNorm K _ Γ q).property⟩ =
      (weight q : ℂ) * (raw.coefficient centered q i * star (raw.coefficient centered q j)) := by
  let r : {r : ℝ // 0 < r} :=
    ⟨radius.val * (sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q).val,
      mul_pos radius.property (sIntegerOrbitNorm K _ Γ q).property⟩
  let L := sUnitProfileCLM K (S : Set (HeightOneSpectrum (𝓞 K))) Γ finiteTest hTest hTestcs r
  have hgram (b c : Bool) : L (profiles.profile b c i j) =
      (weight q : ℂ) * (raw.rectangleCoefficient b q i * star (raw.rectangleCoefficient c q j)) := by
    change sUnitProfileCLM K (S : Set (HeightOneSpectrum (𝓞 K))) Γ finiteTest hTest hTestcs r
      (profiles.profile b c i j) = _
    rw [sUnitProfileCLM_apply]
    exact profiles.gram b c i hi j hj q
  rw [← sUnitProfileCLM_apply K (S : Set (HeightOneSpectrum (𝓞 K))) Γ finiteTest hTest hTestcs r
    (profiles.wholeProfile centered i j)]
  change L (profiles.wholeProfile centered i j) = _
  cases centered with
  | false =>
    simpa only [wholeProfile, Bool.false_eq_true, ite_false,
      ParentRawAtoms.coefficient_eq_rectangles, sub_zero] using hgram false false
  | true =>
    simp only [wholeProfile, ite_true, map_add, map_sub,
      ParentRawAtoms.coefficient_eq_rectangles, star_sub]
    rw [hgram false false, hgram false true, hgram true false, hgram true true]
    ring

def pairs (profiles : ParentRectangleProfiles raw finiteTest radius weight) (centered : Bool)
    (template : raw.Column → raw.Column → ParentPeriodicPair K S Γ) :
    raw.Column → raw.Column → ParentPeriodicPair K S Γ :=
  fun i j => { template i j with profile := profiles.wholeProfile centered i j }

/-- Pointwise rectangle Gram data yield the complete centered source.
The periodic character, finite row map, mask and original fibers are
retained literally; there is no summed parent identity among the inputs. -/
def toRawOrbitalInput (profiles : ParentRectangleProfiles raw finiteTest radius weight)
    (hTest : Continuous finiteTest) (hTestcs : HasCompactSupport finiteTest)
    (centered : Bool) (template : raw.Column → raw.Column → ParentPeriodicPair K S Γ)
    (mask : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)))
    (fiberBound : ℕ)
    (weight_nonneg : ∀ q, 0 ≤ weight q)
    (row_weight : ∀ u ∈ pairedRows d a Z, 1 ≤ weight (raw.rowMap u))
    (row_mask : ∀ u ∈ pairedRows d a Z,
      sIntegerOrbitAvoidanceMask K _ Γ mask (raw.rowMap u) = 1)
    (fiber : ∀ q : SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ,
      ((pairedRows d a Z).filter (fun u => raw.rowMap u = q)).card ≤ fiberBound)
    (periodic : ∀ i ∈ raw.columns, ∀ j ∈ raw.columns, ∀ q,
      (template i j).orbitWeight q = raw.phase q i * star (raw.phase q j)) :
    ParentRawOrbitalInput S Γ centered raw (profiles.pairs centered template)
      finiteTest radius mask fiberBound where
  weight := weight
  weight_nonneg := weight_nonneg
  row_weight := row_weight
  row_mask := row_mask
  fiber := fiber
  periodic := periodic
  gram i hi j hj q := profiles.wholeProfile_gram hTest hTestcs centered i hi j hj q

end ParentRectangleProfiles

end Orbital
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.polynomial
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawOrbitalInput.toCalibration
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRectangleProfiles.wholeProfile_gram
