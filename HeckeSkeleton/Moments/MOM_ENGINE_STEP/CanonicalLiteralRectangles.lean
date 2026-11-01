import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralTerms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralLocations
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalGaussScaleProduction

/-!
# Actual ordinary rectangles from the original individual atoms

The two central-scale choices belong to the two original plain
rectangles. The slot characters, slot profiles and extra Gauss scales
are common to them. An uncentered source has the literal zero second
rectangle, represented by the zero first plain profile.

Each complete coefficient and each `SecondRectangularFactors` is
computed from these individual atoms. The original support extraction
then keeps one common scalar for the whole centered difference. There
is no assumed identity of a completed column or a polynomial sum.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralRectangles

/-- All fields are original single-occurrence inputs. The complete
coefficient and the actual frame are definitions below, not fields. -/
structure Atoms (k : ℕ) where
  characters : FixedChildCharacters K k
  plain₁ : Finset (Ideal (𝓞 K))
  plain₂ : Finset (Ideal (𝓞 K))
  slots : Fin k → Finset (HeightOneSpectrum (𝓞 K))
  plain₁_nonzero : ∀ I ∈ plain₁, I ≠ 0
  plain₂_nonzero : ∀ I ∈ plain₂, I ≠ 0
  centered : Bool
  scale₁ : Bool → ℝ
  scale₂ : Bool → ℝ
  scale₁_pos : ∀ r, 0 < scale₁ r
  scale₂_pos : ∀ r, 0 < scale₂ r
  base : ℝ
  base_gt_one : 1 < base
  length : Fin k → ℝ
  length_pos : ∀ i, 0 < length i
  leftWeight : Bool → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ
  rightWeight : Bool → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ
  slotWeight : Fin k → HeightOneSpectrum (𝓞 K) → ℂ
  gauss₁ : ℝ
  gauss₂ : ℝ
  gaussSlot : Fin k → ℝ
  gauss₁_pos : 0 < gauss₁
  gauss₂_pos : 0 < gauss₂
  gaussSlot_pos : ∀ i, 0 < gaussSlot i

namespace Atoms

variable {k : ℕ} (d : Atoms (K := K) k)

/-- Only the absent comparison rectangle is zeroed. Its positive
central scales and every original slot occurrence are retained. -/
def rectangleLeftWeight (r : Bool) : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ :=
  if r && !d.centered then fun _ => 0 else d.leftWeight r

def dictionary (phase : PUnit.{1} →* Circle) (r : Bool) :
    SecondCoefficientTermDictionary d.characters phase d.plain₁ d.plain₂ d.slots :=
  CanonicalLiteralTerms.dictionary d.characters phase d.plain₁ d.plain₂ d.slots
    (d.scale₁ r) (d.scale₂ r) d.base d.length
    (d.rectangleLeftWeight r) (d.rightWeight r) d.slotWeight

def normalizer : ℂ := extraGaussNormalizer d.gauss₁ d.gauss₂ d.gaussSlot

def term (r : Bool) (i : AllocationColumn K k) : ℂ :=
  d.normalizer * rawBareSourceCoefficient d.characters (d.scale₁ r) (d.scale₂ r)
    d.base d.length (d.rectangleLeftWeight r) (d.rightWeight r) d.slotWeight i

def whole (i : AllocationColumn K k) : ℂ := d.term false i - d.term true i

theorem term_false (i : AllocationColumn K k) :
    d.term false i = d.normalizer *
      rawBareSourceCoefficient d.characters (d.scale₁ false) (d.scale₂ false)
        d.base d.length (d.leftWeight false) (d.rightWeight false) d.slotWeight i := by
  simp only [term, rectangleLeftWeight, Bool.false_and, Bool.false_eq_true, if_false]

theorem term_true (i : AllocationColumn K k) :
    d.term true i = if d.centered then d.normalizer *
      rawBareSourceCoefficient d.characters (d.scale₁ true) (d.scale₂ true)
        d.base d.length (d.leftWeight true) (d.rightWeight true) d.slotWeight i else 0 := by
  cases hc : d.centered <;>
    simp [term, rectangleLeftWeight, hc, rawBareSourceCoefficient,
      FixedChildCharacters.bareCoefficient, childCartesianCoefficient]

theorem whole_eq (i : AllocationColumn K k) :
    d.whole i = d.normalizer *
      (rawBareSourceCoefficient d.characters (d.scale₁ false) (d.scale₂ false)
          d.base d.length (d.leftWeight false) (d.rightWeight false) d.slotWeight i -
        if d.centered then rawBareSourceCoefficient d.characters
          (d.scale₁ true) (d.scale₂ true) d.base d.length
          (d.leftWeight true) (d.rightWeight true) d.slotWeight i else 0) := by
  rw [whole, d.term_false, d.term_true]
  cases d.centered <;> simp only [Bool.false_eq_true, if_false, if_true, sub_zero, mul_zero,
    mul_sub]

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The atom identities are inserted directly into the actual factor
record. Its locations are the true residual log-norm occurrences. -/
def factors (R : ActualSecondCorrelationRows A σ H ι)
    (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
    (ideal : AllocationColumn K k → A.Exterior)
    (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
      (ideal i).val = allocationColumnIdeal i)
    (firstSign : ℝ) (r : Bool) :
    SecondRectangularFactors R PUnit.{1} side d.plain₁ d.plain₂ d.slots
      ideal (fun _ => PUnit.unit) (d.term r)
      (fun _ => rawSourceLocation (CanonicalLiteralLocations.plain firstSign)
        (CanonicalLiteralLocations.plain firstSign) (CanonicalLiteralLocations.prime firstSign)) χ where
  characters := d.characters
  dictionary := d.dictionary (side.phase PUnit.{1} χ) r
  base_gt_one := d.base_gt_one
  length_pos := d.length_pos
  plain₁_nonzero := d.plain₁_nonzero
  plain₂_nonzero := d.plain₂_nonzero
  ideal_product := hideal
  gaussScale₁ := d.gauss₁
  gaussScale₂ := d.gauss₂
  gaussSlotScale := d.gaussSlot
  gaussScale₁_pos := d.gauss₁_pos
  gaussScale₂_pos := d.gauss₂_pos
  gaussSlotScale_pos := d.gaussSlot_pos
  coefficient_factor i _ := by
    rw [SecondCoefficientTermDictionary.normalizedCoefficient_eq]
    rfl
  ray_factor _ _ := Subsingleton.elim _ _
  leftLocation _ := CanonicalLiteralLocations.plain firstSign
  rightLocation _ := CanonicalLiteralLocations.plain firstSign
  slotLocation _ := CanonicalLiteralLocations.prime firstSign
  point_factor _ _ _ _ := rfl

end Atoms

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {k l : ℕ}

/-- Both Boolean rectangles and their real atom frames are constructed
on the same actual allocation and the same complementary row set. -/
def rectangles (R : ActualSecondCorrelationRows A σ H ι)
    (left : Atoms (K := K) k) (right : Atoms (K := K) l)
    (IL : AllocationColumn K k → A.Exterior) (IR : AllocationColumn K l → A.Exterior)
    (hIL : ∀ i ∈ childCartesianColumns left.plain₁ left.plain₂ left.slots,
      (IL i).val = allocationColumnIdeal i)
    (hIR : ∀ j ∈ childCartesianColumns right.plain₁ right.plain₂ right.slots,
      (IR j).val = allocationColumnIdeal j)
    (b : liveSecondAllocationBranches (Ray := PUnit.{1})
      left.plain₁ left.plain₂ left.slots right.plain₁ right.plain₂ right.slots IR)
    (exceptional : H → Prop) (firstLeftSign firstRightSign : ℝ) :
    HybridOrdinaryRectangles R PUnit.{1}
      left.plain₁ left.plain₂ left.slots right.plain₁ right.plain₂ right.slots IL IR
      (fun _ => PUnit.unit) (fun _ => PUnit.unit) left.whole right.whole
      (fun _ => rawSourceLocation (CanonicalLiteralLocations.plain firstLeftSign)
        (CanonicalLiteralLocations.plain firstLeftSign)
        (CanonicalLiteralLocations.prime firstLeftSign))
      (fun _ => rawSourceLocation (CanonicalLiteralLocations.plain firstRightSign)
        (CanonicalLiteralLocations.plain firstRightSign)
        (CanonicalLiteralLocations.prime firstRightSign)) b exceptional where
  leftTerms := left.term
  rightTerms := right.term
  left_difference _ _ := rfl
  right_difference _ _ := rfl
  leftFactors r := left.factors (R.restrictRows fun h => ¬exceptional h)
    .left b.val.2.1 IL hIL firstLeftSign r
  rightFactors r := right.factors (R.restrictRows fun h => ¬exceptional h)
    .right b.val.2.1 IR hIR firstRightSign r

end CanonicalLiteralRectangles

namespace CompleteMovingRowRecipe

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*}
variable {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)

/-- The starting rectangle table is read from the actual original
moving-row source. Before the first transform there is no extra Gauss
denominator, so its three kinds of Gauss scale are all exactly one. -/
def literalOriginalAtoms (ξ : X)
    (W : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    CanonicalLiteralRectangles.Atoms (K := K) (data ξ).geometry.slotCount where
  characters := Q.literalSourceCharacters ξ
  plain₁ := (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalPlain₁
  plain₂ := (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalPlain₂
  slots := (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).exteriorSlots
  plain₁_nonzero := ParentRawAtoms.originalPlain₁_nonzero _
  plain₂_nonzero := ParentRawAtoms.originalPlain₂_nonzero _
  centered := centered
  scale₁ r := if r then Y₁ else Z ^ a.n₁
  scale₂ r := if r then Y₂ else Z ^ a.n₂
  scale₁_pos r := by
    cases r <;> simp only [Bool.false_eq_true, if_false, if_true]
    · exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    · exact hY₁
  scale₂_pos r := by
    cases r <;> simp only [Bool.false_eq_true, if_false, if_true]
    · exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
    · exact hY₂
  base := Z
  base_gt_one := hZ
  length i := ((data ξ).geometry.slots i).length
  length_pos i := ((data ξ).geometry.slots i).length_pos
  leftWeight r I := W.left PUnit.unit t
    (idealNorm K I / (if r then Y₁ else Z ^ a.n₁))
  rightWeight r I := W.right PUnit.unit t
    (idealNorm K I / (if r then Y₂ else Z ^ a.n₂))
  slotWeight i p := ((data ξ).geometry.slots i).profile t
    ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ ((data ξ).geometry.slots i).length)
  gauss₁ := 1
  gauss₂ := 1
  gaussSlot _ := 1
  gauss₁_pos := zero_lt_one
  gauss₂_pos := zero_lt_one
  gaussSlot_pos _ := zero_lt_one

@[simp] theorem literalOriginalAtoms_normalizer (ξ : X)
    (W : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).normalizer = 1 := by
  simp [literalOriginalAtoms, CanonicalLiteralRectangles.Atoms.normalizer,
    extraGaussNormalizer, SecondCoefficientTermDictionary.centralNormalizer]

/-- Each actual original rectangle is produced from the original
two plain profiles and all prime occurrences. There is no supplied
complete-coefficient equality. -/
theorem literalOriginalAtoms_term (ξ : X)
    (W : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered comparison : Bool)
    (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (i : AllocationColumn K (data ξ).geometry.slotCount) :
    let atoms := (Q.arithmeticAtoms ξ).constantAtoms W a Z t
    (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).term comparison i =
      if comparison && !centered then 0 else
        (atoms.values Y₁ Y₂).rectangle comparison ((atoms.raw Y₁ Y₂).originalIndex i) := by
  dsimp only
  rw [Q.literalOriginalDictionary_rectangle ξ W a Z t Y₁ Y₂ comparison
    (1 : PUnit.{1} →* Circle)]
  cases comparison <;> cases centered <;>
    simp [CanonicalLiteralRectangles.Atoms.term,
      CanonicalLiteralRectangles.Atoms.rectangleLeftWeight,
      literalOriginalAtoms, CanonicalLiteralRectangles.Atoms.normalizer,
      extraGaussNormalizer, SecondCoefficientTermDictionary.centralNormalizer,
      literalOriginalDictionary, CanonicalLiteralTerms.dictionary,
      CanonicalLiteralTerms.plainAtom, CanonicalLiteralTerms.primeAtom,
      SecondCoefficientTermDictionary.coefficient, rawBareSourceCoefficient,
      FixedChildCharacters.bareCoefficient, childCartesianCoefficient]

/-- The actual entire centered original coefficient, on its computed
Cartesian atlas, is the constructed whole rectangle. Empty slot sets
are covered by the same finite product. -/
theorem literalOriginalAtoms_whole (ξ : X)
    (W : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (i : AllocationColumn K (data ξ).geometry.slotCount) :
    let atoms := (Q.arithmeticAtoms ξ).constantAtoms W a Z t
    (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).whole i =
      (atoms.values Y₁ Y₂).coefficient centered ((atoms.raw Y₁ Y₂).originalIndex i) := by
  dsimp only
  unfold CanonicalLiteralRectangles.Atoms.whole
  rw [Q.literalOriginalAtoms_term ξ W a Z t Y₁ Y₂ centered false hZ hY₁ hY₂ i,
    Q.literalOriginalAtoms_term ξ W a Z t Y₁ Y₂ centered true hZ hY₁ hY₂ i]
  cases centered <;>
    simp [ParentRawAtoms.ConstantValues.coefficient]

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.whole_eq
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.factors
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.rectangles
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalAtoms_whole
