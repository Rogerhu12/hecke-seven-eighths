import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralTwoStages
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLogProfiles

/-!
# The original individual profiles of the literal two-stage source

The tests below are computed from the original norm profiles, frozen at
the original time and one original allowed row. Their finite supports
remain profile supports. Arithmetic masks belong to the coefficient
dictionary and are not inserted into these functions.

Constant factors, the actual Gauss square roots and the two norm tilts
are applied at individual occurrences. Common extraction retains the
same function and changes its central scale by the actual ideal norm.
The final Fourier multiplier has exponent zero and the pre-allocation
scale, so its phase is evaluated at the full allocated ideal.

This constructs literal tests and exact atom identities. Quantitative
Schwartz bounds are supplied by the original profile window and its
proved multiplication bounds, not asserted by the bare test structure.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralProfileData

/-- An individual multiplier can vanish. Its exact finite support is
therefore the corresponding filter of the original profile support. -/
def mulIdealTest (W : IdealTest K) (f : ℝ → ℂ) : IdealTest K where
  profile u t y := W.profile u t y * f y
  support u t N := (W.support u t N).filter (fun I => f (idealNorm K I / N) ≠ 0)
  support_spec u t N I := by
    simp only [Finset.mem_filter, W.support_spec, mul_ne_zero_iff]

def mulPrimeWindow (W : PrimeWindow K) (f : ℝ → ℂ) : PrimeWindow K where
  length := W.length
  length_pos := W.length_pos
  profile t y := W.profile t y * f y
  support t N := (W.support t N).filter
    (fun p => f ((Ideal.absNorm p.asIdeal : ℝ) / N) ≠ 0)
  support_spec t N p := by
    simp only [Finset.mem_filter, W.support_spec, mul_ne_zero_iff]

theorem mulIdealTest_positive (W : IdealTest K) (f : ℝ → ℂ)
    (hW : CanonicalLogProfiles.PositivePlainProfile W) :
    CanonicalLogProfiles.PositivePlainProfile (mulIdealTest W f) := by
  intro u t y hy
  exact hW u t y (left_ne_zero_of_mul hy)

theorem mulPrimeWindow_positive (W : PrimeWindow K) (f : ℝ → ℂ)
    (hW : CanonicalLogProfiles.PositivePrimeProfile W) :
    CanonicalLogProfiles.PositivePrimeProfile (mulPrimeWindow W f) := by
  intro t y hy
  exact hW t y (left_ne_zero_of_mul hy)

/-- The original time is fixed; the new row and time arguments do not
select another original profile. -/
def frozenNormTest (W : IdealTest K)
    (reference : HeckeGeneral.Analysis.NonzeroIdeal K) (time : ℝ) : IdealTest K where
  profile u _ := (normIdealTest W reference).profile u time
  support u _ := (normIdealTest W reference).support u time
  support_spec u _ := (normIdealTest W reference).support_spec u time

def frozenPrimeWindow (W : PrimeWindow K) (time : ℝ) : PrimeWindow K where
  length := W.length
  length_pos := W.length_pos
  profile _ := W.profile time
  support _ := W.support time
  support_spec _ := W.support_spec time

theorem idealNorm_mul (B I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    idealNorm K (B * I) = idealNorm K B * idealNorm K I := by
  change (Ideal.absNorm (B.val * I.val) : ℝ) =
    (Ideal.absNorm B.val : ℝ) * (Ideal.absNorm I.val : ℝ)
  rw [map_mul, Nat.cast_mul]

/-- The quotient scale represents the same original norm argument. -/
theorem quotient_argument (N : ℝ) (B I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    idealNorm K I / (N / idealNorm K B) = idealNorm K (B * I) / N := by
  rw [idealNorm_mul]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

end CanonicalLiteralProfileData

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)

theorem rectangleLeftWeight_ne_zero (r : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) (h : d.rectangleLeftWeight r I ≠ 0) :
    d.leftWeight r I ≠ 0 := by
  unfold rectangleLeftWeight at h
  split_ifs at h
  · exact (h rfl).elim
  · exact h

/-- Each field binds one original occurrence, before its finite sum.
Every new row and time sees the same already selected original test. -/
structure ProfileData where
  left : Bool → IdealTest K
  right : Bool → IdealTest K
  slot : Fin k → PrimeWindow K
  slot_length : ∀ j, (slot j).length = d.length j
  left_positive : ∀ r, CanonicalLogProfiles.PositivePlainProfile (left r)
  right_positive : ∀ r, CanonicalLogProfiles.PositivePlainProfile (right r)
  slot_positive : ∀ j, CanonicalLogProfiles.PositivePrimeProfile (slot j)
  left_frozen : ∀ r u t y, (left r).profile u t y = (left r).profile 1 0 y
  right_frozen : ∀ r u t y, (right r).profile u t y = (right r).profile 1 0 y
  slot_frozen : ∀ j t y, (slot j).profile t y = (slot j).profile 0 y
  left_eval : ∀ r u t I,
    (left r).profile u t (idealNorm K I / d.scale₁ r) = d.rectangleLeftWeight r I
  right_eval : ∀ r u t I,
    (right r).profile u t (idealNorm K I / d.scale₂ r) = d.rightWeight r I
  slot_eval : ∀ j t p,
    (slot j).profile t ((Ideal.absNorm p.asIdeal : ℝ) / d.base ^ d.length j) =
      d.slotWeight j p

namespace ProfileData

variable {d} (W : d.ProfileData)

/-- The actual frozen common scalar may be zero. It multiplies the
same first plain profile in both original rectangles. -/
def scale (c : ℂ) : (d.scale c).ProfileData where
  left r := CanonicalLiteralProfileData.mulIdealTest (W.left r) (fun _ => c)
  right := W.right
  slot := W.slot
  slot_length := W.slot_length
  left_positive r := CanonicalLiteralProfileData.mulIdealTest_positive _ _ (W.left_positive r)
  right_positive := W.right_positive
  slot_positive := W.slot_positive
  left_frozen r u t y := congrArg (fun z => z * c) (W.left_frozen r u t y)
  right_frozen := W.right_frozen
  slot_frozen := W.slot_frozen
  left_eval r u t I := by
    change (W.left r).profile u t (idealNorm K I / d.scale₁ r) * c = _
    rw [W.left_eval, d.scale_rectangleLeftWeight]
    exact mul_comm _ _
  right_eval := W.right_eval
  slot_eval := W.slot_eval

def addGauss (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ j, 0 < G j) :
    (d.addGauss G₁ G₂ G h₁ h₂ hG).ProfileData where
  left r := CanonicalLiteralProfileData.mulIdealTest (W.left r)
    (fun _ => (Real.sqrt G₁ : ℂ))
  right r := CanonicalLiteralProfileData.mulIdealTest (W.right r)
    (fun _ => (Real.sqrt G₂ : ℂ))
  slot j := CanonicalLiteralProfileData.mulPrimeWindow (W.slot j)
    (fun _ => (Real.sqrt (G j) : ℂ))
  slot_length := W.slot_length
  left_positive r := CanonicalLiteralProfileData.mulIdealTest_positive _ _ (W.left_positive r)
  right_positive r := CanonicalLiteralProfileData.mulIdealTest_positive _ _ (W.right_positive r)
  slot_positive j := CanonicalLiteralProfileData.mulPrimeWindow_positive _ _ (W.slot_positive j)
  left_frozen r u t y := congrArg (fun z => z * (Real.sqrt G₁ : ℂ)) (W.left_frozen r u t y)
  right_frozen r u t y := congrArg (fun z => z * (Real.sqrt G₂ : ℂ)) (W.right_frozen r u t y)
  slot_frozen j t y := congrArg (fun z => z * (Real.sqrt (G j) : ℂ)) (W.slot_frozen j t y)
  left_eval r u t I := by
    change (W.left r).profile u t (idealNorm K I / d.scale₁ r) * (Real.sqrt G₁ : ℂ) = _
    rw [W.left_eval, d.addGauss_rectangleLeftWeight]
  right_eval r u t I := by
    change (W.right r).profile u t (idealNorm K I / d.scale₂ r) * (Real.sqrt G₂ : ℂ) = _
    rw [W.right_eval] <;> rfl
  slot_eval j t p := by
    change (W.slot j).profile t ((Ideal.absNorm p.asIdeal : ℝ) / d.base ^ d.length j) *
      (Real.sqrt (G j) : ℂ) = _
    rw [W.slot_eval] <;> rfl

/-- The multiplier is evaluated at the full norm, using the current
original scale. This includes the inverse norm when δ is negative. -/
def normPower (δ : ℝ) : (d.normPower δ).ProfileData where
  left r := CanonicalLiteralProfileData.mulIdealTest (W.left r)
    (fun y => ((d.scale₁ r * y) ^ δ : ℝ))
  right r := CanonicalLiteralProfileData.mulIdealTest (W.right r)
    (fun y => ((d.scale₂ r * y) ^ δ : ℝ))
  slot j := CanonicalLiteralProfileData.mulPrimeWindow (W.slot j)
    (fun y => ((d.base ^ d.length j * y) ^ δ : ℝ))
  slot_length := W.slot_length
  left_positive r := CanonicalLiteralProfileData.mulIdealTest_positive _ _ (W.left_positive r)
  right_positive r := CanonicalLiteralProfileData.mulIdealTest_positive _ _ (W.right_positive r)
  slot_positive j := CanonicalLiteralProfileData.mulPrimeWindow_positive _ _ (W.slot_positive j)
  left_frozen r u t y := congrArg (fun z => z * ((d.scale₁ r * y) ^ δ : ℝ))
    (W.left_frozen r u t y)
  right_frozen r u t y := congrArg (fun z => z * ((d.scale₂ r * y) ^ δ : ℝ))
    (W.right_frozen r u t y)
  slot_frozen j t y := congrArg (fun z => z * ((d.base ^ d.length j * y) ^ δ : ℝ))
    (W.slot_frozen j t y)
  left_eval r u t I := by
    change (W.left r).profile u t (idealNorm K I / d.scale₁ r) *
      ((d.scale₁ r * (idealNorm K I / d.scale₁ r)) ^ δ : ℝ) = _
    have hs : d.scale₁ r * (idealNorm K I / d.scale₁ r) = idealNorm K I := by
      rw [mul_comm, div_mul_cancel₀ _ (d.scale₁_pos r).ne']
    rw [W.left_eval, hs, d.normPower_rectangleLeftWeight]
  right_eval r u t I := by
    change (W.right r).profile u t (idealNorm K I / d.scale₂ r) *
      ((d.scale₂ r * (idealNorm K I / d.scale₂ r)) ^ δ : ℝ) = _
    have hs : d.scale₂ r * (idealNorm K I / d.scale₂ r) = idealNorm K I := by
      rw [mul_comm, div_mul_cancel₀ _ (d.scale₂_pos r).ne']
    rw [W.right_eval, hs] <;> rfl
  slot_eval j t p := by
    change (W.slot j).profile t ((Ideal.absNorm p.asIdeal : ℝ) / d.base ^ d.length j) *
      ((d.base ^ d.length j * ((Ideal.absNorm p.asIdeal : ℝ) / d.base ^ d.length j)) ^ δ : ℝ) = _
    have hs : d.base ^ d.length j *
        ((Ideal.absNorm p.asIdeal : ℝ) / d.base ^ d.length j) =
        (Ideal.absNorm p.asIdeal : ℝ) := by
      rw [mul_comm, div_mul_cancel₀ _
        (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _).ne']
    rw [W.slot_eval, hs] <;> rfl

def twoStageNorms (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ j, 0 < G j)
    (δ₁ δ₂ : ℝ) : (d.twoStageNorms G₁ G₂ G h₁ h₂ hG δ₁ δ₂).ProfileData :=
  (((W.addGauss G₁ G₂ G h₁ h₂ hG).normPower (-1)).normPower δ₁).normPower δ₂

variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)

/-- Extraction does not modify a plain profile function. Its new
scale is exactly the old scale divided by the extracted ideal norm. -/
def extract : (d.extract b).ProfileData where
  left := W.left
  right := W.right
  slot j := W.slot (SlotRestriction.index b.keep j)
  slot_length j := W.slot_length (SlotRestriction.index b.keep j)
  left_positive := W.left_positive
  right_positive := W.right_positive
  slot_positive j := W.slot_positive (SlotRestriction.index b.keep j)
  left_frozen := W.left_frozen
  right_frozen := W.right_frozen
  slot_frozen j := W.slot_frozen (SlotRestriction.index b.keep j)
  left_eval r u t I := by
    change (W.left r).profile u t (idealNorm K I / (d.scale₁ r / idealNorm K b.plainDivisor₁)) = _
    rw [CanonicalLiteralProfileData.quotient_argument, W.left_eval,
      d.extract_rectangleLeftWeight]
  right_eval r u t I := by
    change (W.right r).profile u t (idealNorm K I / (d.scale₂ r / idealNorm K b.plainDivisor₂)) = _
    rw [CanonicalLiteralProfileData.quotient_argument, W.right_eval] <;> rfl
  slot_eval j t p := W.slot_eval (SlotRestriction.index b.keep j) t p

@[simp] theorem extract_left (r : Bool) : (W.extract b).left r = W.left r := rfl
@[simp] theorem extract_right (r : Bool) : (W.extract b).right r = W.right r := rfl
@[simp] theorem extract_slot (j : Fin b.keep.card) :
    (W.extract b).slot j = W.slot (SlotRestriction.index b.keep j) := rfl

def firstExtracted : (d.firstExtracted b).ProfileData :=
  (W.extract b).scale (d.commonScalar b)

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

/-- All fixed residue phases remain in the arithmetic dictionary. -/
def movingSingleton (I : A.Exterior) (a : A.R) (ha : A.Generates I a) :
    (d.movingSingleton P R I a ha).ProfileData where
  left := W.left
  right := W.right
  slot := W.slot
  slot_length := W.slot_length
  left_positive := W.left_positive
  right_positive := W.right_positive
  slot_positive := W.slot_positive
  left_frozen := W.left_frozen
  right_frozen := W.right_frozen
  slot_frozen := W.slot_frozen
  left_eval := W.left_eval
  right_eval := W.right_eval
  slot_eval := W.slot_eval

/-- The actual first extraction, three fixed phases and two transforms
all act on the same original single-atom tests. -/
def secondInput (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ) :
    (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).ProfileData :=
  let e := d.firstExtracted b
  let n := (W.firstExtracted b).twoStageNorms (e.scale₁ false) (e.scale₂ false)
    (fun j => e.base ^ e.length j) (e.scale₁_pos false) (e.scale₂_pos false)
    (fun _ => Real.rpow_pos_of_pos (zero_lt_one.trans e.base_gt_one) _) δ₁ δ₂
  let f := ((n.movingSingleton P R firstFixed firstElement hfirst).movingSingleton
    P R poolFixed poolElement hpool).movingSingleton P R unitFixed unitElement hunit
  f.scale (((A.exteriorNorm power ^ δ₁ : ℝ) : ℂ) *
    actualIdealResidue (A := A) (σ := σ) power.val firstElement)

end ProfileData
end CanonicalLiteralRectangles.Atoms

namespace CompleteMovingRowRecipe

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*}
variable {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)

/-- The initial tests are the actual original parent tests at one
original allowed row. The original norm identity makes that choice
agree with every original row in the source. -/
def literalOriginalProfileData (ξ : X)
    (W : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
    (href : (data ξ).allowedRow reference)
    (hleft : ∀ y, (data ξ).plainTest₁.profile reference t y ≠ 0 → 0 < y)
    (hright : ∀ y, (data ξ).plainTest₂.profile reference t y ≠ 0 → 0 < y)
    (hprime : ∀ j y, ((data ξ).geometry.slots j).profile t y ≠ 0 → 0 < y) :
    (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).ProfileData where
  left r := CanonicalLiteralProfileData.mulIdealTest
    (CanonicalLiteralProfileData.frozenNormTest (data ξ).plainTest₁ reference t)
    (fun _ => if r && !centered then 0 else 1)
  right _ := CanonicalLiteralProfileData.frozenNormTest (data ξ).plainTest₂ reference t
  slot j := CanonicalLiteralProfileData.frozenPrimeWindow ((data ξ).geometry.slots j) t
  slot_length _ := rfl
  left_positive _ _ _ y hy := hleft y (left_ne_zero_of_mul hy)
  right_positive _ _ _ y hy := hright y hy
  slot_positive j _ y hy := hprime j y hy
  left_frozen _ _ _ _ := rfl
  right_frozen _ _ _ _ := rfl
  slot_frozen _ _ _ := rfl
  left_eval r u time I := by
    change (data ξ).plainTest₁.profile reference t
        (idealNorm K I / (if r then Y₁ else Z ^ a.n₁)) *
      (if r && !centered then 0 else 1) = _
    rw [W.left_eq PUnit.unit reference href]
    change _ = (if r && !centered then
      (fun _ : HeckeGeneral.Analysis.NonzeroIdeal K => (0 : ℂ))
      else (fun J => W.left PUnit.unit t
        (idealNorm K J / (if r then Y₁ else Z ^ a.n₁)))) I
    split_ifs <;> simp only [mul_zero, mul_one]
  right_eval r u time I := W.right_eq PUnit.unit reference href t _
  slot_eval _ _ _ := rfl

/-- A positive original support window supplies every positivity fact
used above. No new final-child profile or support condition is needed. -/
def literalOriginalProfileDataOfWindow (ξ : X)
    (W : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
    (href : (data ξ).allowedRow reference)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)} {bound : ℝ}
    (original : RawProfileWindow rowDomain heightDomain window seminorms (data ξ) bound)
    (hreference : reference ∈ rowDomain) (ht : t ∈ heightDomain)
    (hwindow : window ⊆ Set.Ioi 0) :
    (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).ProfileData :=
  Q.literalOriginalProfileData ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂ reference href
    (fun y hy => hwindow (original.left_support reference hreference t ht (by
      simpa only [Function.mem_support, ← original.left_eq] using hy)))
    (fun y hy => hwindow (original.right_support reference hreference t ht (by
      simpa only [Function.mem_support, ← original.right_eq] using hy)))
    (fun j y hy => hwindow (original.prime_support j t ht (by
      simpa only [Function.mem_support, ← original.prime_eq] using hy)))

/-- The original support union contains each nonzero plain profile
at any actual original paired row. The exterior filter is discharged
by the original arithmetic mask, separately from the smooth profile. -/
theorem literalOriginalAtoms_left_weight_mem (ξ : X)
    (W : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
    (href : reference ∈ pairedRows (data ξ) a Z) (r : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) (hI : IsCoprime I.val A.cS)
    (hweight : (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).leftWeight r I ≠ 0) :
    I.val ∈ (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₁ := by
  have hrefa : (data ξ).allowedRow reference :=
    (((data ξ).rows_spec _ reference).1 (Finset.mem_filter.mp href).1).1
  refine Finset.mem_image.mpr ⟨I, Finset.mem_filter.mpr ⟨?_, hI⟩, rfl⟩
  apply parentPlainCarrier_contains (pairedRows (data ξ) a Z) (data ξ).plainTest₁
    t (Z ^ a.n₁) Y₁ r reference href
  apply ((data ξ).plainTest₁.support_spec reference t _ I).mpr
  rw [W.left_eq PUnit.unit reference hrefa]
  exact hweight

theorem literalOriginalAtoms_right_weight_mem (ξ : X)
    (W : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
    (href : reference ∈ pairedRows (data ξ) a Z) (r : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) (hI : IsCoprime I.val A.cS)
    (hweight : (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).rightWeight r I ≠ 0) :
    I.val ∈ (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₂ := by
  have hrefa : (data ξ).allowedRow reference :=
    (((data ξ).rows_spec _ reference).1 (Finset.mem_filter.mp href).1).1
  refine Finset.mem_image.mpr ⟨I, Finset.mem_filter.mpr ⟨?_, hI⟩, rfl⟩
  apply parentPlainCarrier_contains (pairedRows (data ξ) a Z) (data ξ).plainTest₂
    t (Z ^ a.n₂) Y₂ r reference href
  apply ((data ξ).plainTest₂.support_spec reference t _ I).mpr
  rw [W.right_eq PUnit.unit reference hrefa]
  exact hweight

/-- Prime profiles have no row parameter. Only the original exterior
prime condition is needed in addition to their actual nonzero value. -/
theorem literalOriginalAtoms_slot_weight_mem (ξ : X)
    (W : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (j : Fin (data ξ).geometry.slotCount) (p : HeightOneSpectrum (𝓞 K))
    (hp : IsCoprime p.asIdeal A.cS)
    (hweight : (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).slotWeight j p ≠ 0) :
    p ∈ (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).slots j := by
  refine Finset.mem_filter.mpr ⟨?_, hp⟩
  exact (((data ξ).geometry.slots j).support_spec t _ p).mpr hweight

end CompleteMovingRowRecipe

namespace CanonicalLiteralProfileData

/-- This is precisely the original left location, or its actual
negative-side location. No Fourier variable is replaced. -/
def orientedLocation (negative : Bool) (x : WithLp 2 (ℝ × ℝ)) : WithLp 2 (ℝ × ℝ) :=
  if negative then -x else x

def fourierAtom (scale : ℝ) (hscale : 0 < scale) (firstSign : ℝ) (negative : Bool) :
    CanonicalLogProfiles.Atom (WithLp 2 (ℝ × ℝ)) where
  scale := scale
  scale_pos := hscale
  exponent := 0
  offset := 0
  direction := if negative then CanonicalLiteralLocations.direction firstSign
    else -CanonicalLiteralLocations.direction firstSign

theorem fourierAtom_multiplier_ratio (scale : ℝ) (hscale : 0 < scale)
    (firstSign : ℝ) (negative : Bool) (ξ : WithLp 2 (ℝ × ℝ)) (N : ℝ) :
    (fourierAtom scale hscale firstSign negative).multiplier ξ (N / scale) =
      jointPhase ξ (orientedLocation negative
        (-Real.log N • CanonicalLiteralLocations.direction firstSign)) := by
  rw [CanonicalLogProfiles.Atom.multiplier_ratio]
  cases negative <;>
    simp only [fourierAtom, orientedLocation, Bool.false_eq_true, if_false, if_true,
      Real.rpow_zero, Complex.ofReal_one, one_mul, zero_add, smul_neg, neg_smul, neg_neg]

end CanonicalLiteralProfileData

namespace CanonicalLiteralRectangles.Atoms.ProfileData

variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData)

def fourierLeft (r : Bool) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) : IdealTest K :=
  (CanonicalLiteralProfileData.fourierAtom (d.scale₁ r) (d.scale₁_pos r)
    firstSign negative).idealTest (W.left r) (W.left_positive r) ξ

def fourierRight (r : Bool) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) : IdealTest K :=
  (CanonicalLiteralProfileData.fourierAtom (d.scale₂ r) (d.scale₂_pos r)
    firstSign negative).idealTest (W.right r) (W.right_positive r) ξ

def fourierSlot (j : Fin k) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) : PrimeWindow K :=
  (CanonicalLiteralProfileData.fourierAtom (d.base ^ d.length j)
    (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _)
    firstSign negative).primeWindow (W.slot j) (W.slot_positive j) ξ

@[simp] theorem fourierLeft_support (r : Bool) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    (W.fourierLeft r firstSign negative ξ).support = (W.left r).support := rfl

@[simp] theorem fourierRight_support (r : Bool) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    (W.fourierRight r firstSign negative ξ).support = (W.right r).support := rfl

@[simp] theorem fourierSlot_support (j : Fin k) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    (W.fourierSlot j firstSign negative ξ).support = (W.slot j).support := rfl

@[simp] theorem fourierSlot_length (j : Fin k) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    (W.fourierSlot j firstSign negative ξ).length = d.length j := W.slot_length j

theorem fourierLeft_frozen (r : Bool) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (time y : ℝ) :
    (W.fourierLeft r firstSign negative ξ).profile u time y =
      (W.fourierLeft r firstSign negative ξ).profile 1 0 y :=
  congrArg (fun z => z *
    (CanonicalLiteralProfileData.fourierAtom (d.scale₁ r) (d.scale₁_pos r)
      firstSign negative).multiplier ξ y) (W.left_frozen r u time y)

theorem fourierRight_frozen (r : Bool) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (time y : ℝ) :
    (W.fourierRight r firstSign negative ξ).profile u time y =
      (W.fourierRight r firstSign negative ξ).profile 1 0 y :=
  congrArg (fun z => z *
    (CanonicalLiteralProfileData.fourierAtom (d.scale₂ r) (d.scale₂_pos r)
      firstSign negative).multiplier ξ y) (W.right_frozen r u time y)

theorem fourierSlot_frozen (j : Fin k) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) (time y : ℝ) :
    (W.fourierSlot j firstSign negative ξ).profile time y =
      (W.fourierSlot j firstSign negative ξ).profile 0 y :=
  congrArg (fun z => z *
    (CanonicalLiteralProfileData.fourierAtom (d.base ^ d.length j)
      (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _)
      firstSign negative).multiplier ξ y) (W.slot_frozen j time y)

theorem fourierLeft_eval (r : Bool) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (time : ℝ)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (W.fourierLeft r firstSign negative ξ).profile u time (idealNorm K I / d.scale₁ r) =
      d.rectangleLeftWeight r I * jointPhase ξ
        (CanonicalLiteralProfileData.orientedLocation negative
          (CanonicalLiteralLocations.plain firstSign I)) := by
  change (W.left r).profile u time (idealNorm K I / d.scale₁ r) *
    (CanonicalLiteralProfileData.fourierAtom (d.scale₁ r) (d.scale₁_pos r)
      firstSign negative).multiplier ξ (idealNorm K I / d.scale₁ r) = _
  rw [W.left_eval, CanonicalLiteralProfileData.fourierAtom_multiplier_ratio] <;> rfl

theorem fourierRight_eval (r : Bool) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (time : ℝ)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (W.fourierRight r firstSign negative ξ).profile u time (idealNorm K I / d.scale₂ r) =
      d.rightWeight r I * jointPhase ξ
        (CanonicalLiteralProfileData.orientedLocation negative
          (CanonicalLiteralLocations.plain firstSign I)) := by
  change (W.right r).profile u time (idealNorm K I / d.scale₂ r) *
    (CanonicalLiteralProfileData.fourierAtom (d.scale₂ r) (d.scale₂_pos r)
      firstSign negative).multiplier ξ (idealNorm K I / d.scale₂ r) = _
  rw [W.right_eval, CanonicalLiteralProfileData.fourierAtom_multiplier_ratio] <;> rfl

/-- The multiplier uses the pre-allocation scale. Consequently its
phase is the original location of `B * I`, as required by the actual
allocated source dictionary. -/
theorem fourierLeft_allocated (r : Bool) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (time : ℝ)
    (B I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (W.fourierLeft r firstSign negative ξ).profile u time
        (idealNorm K I / (d.scale₁ r / idealNorm K B)) =
      d.rectangleLeftWeight r (B * I) * jointPhase ξ
        (CanonicalLiteralProfileData.orientedLocation negative
          (CanonicalLiteralLocations.plain firstSign (B * I))) := by
  rw [CanonicalLiteralProfileData.quotient_argument]
  exact W.fourierLeft_eval r firstSign negative ξ u time (B * I)

theorem fourierRight_allocated (r : Bool) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (time : ℝ)
    (B I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (W.fourierRight r firstSign negative ξ).profile u time
        (idealNorm K I / (d.scale₂ r / idealNorm K B)) =
      d.rightWeight r (B * I) * jointPhase ξ
        (CanonicalLiteralProfileData.orientedLocation negative
          (CanonicalLiteralLocations.plain firstSign (B * I))) := by
  rw [CanonicalLiteralProfileData.quotient_argument]
  exact W.fourierRight_eval r firstSign negative ξ u time (B * I)

theorem fourierSlot_eval (j : Fin k) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) (time : ℝ) (p : HeightOneSpectrum (𝓞 K)) :
    (W.fourierSlot j firstSign negative ξ).profile time
        ((Ideal.absNorm p.asIdeal : ℝ) / d.base ^ d.length j) =
      d.slotWeight j p * jointPhase ξ
        (CanonicalLiteralProfileData.orientedLocation negative
          (CanonicalLiteralLocations.prime firstSign j p)) := by
  change (W.slot j).profile time ((Ideal.absNorm p.asIdeal : ℝ) / d.base ^ d.length j) *
    (CanonicalLiteralProfileData.fourierAtom (d.base ^ d.length j)
      (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _)
      firstSign negative).multiplier ξ
        ((Ideal.absNorm p.asIdeal : ℝ) / d.base ^ d.length j) = _
  rw [W.slot_eval, CanonicalLiteralProfileData.fourierAtom_multiplier_ratio] <;> rfl

end CanonicalLiteralRectangles.Atoms.ProfileData

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalProfileData
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalProfileDataOfWindow
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalAtoms_left_weight_mem
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalAtoms_slot_weight_mem
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.secondInput
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.fourierLeft_allocated
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.fourierSlot_eval
