import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualExceptionalColumnOrientation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualSecondRowMassSwap
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualExceptionalBudget

/-!
# The original exceptional atom charts in either column orientation

On the old right source the residue sees `(-g) * h'`; after the column
exchange it sees `g * (-h')`. On the old left source it sees `g * h'`;
after the exchange and its right-side convention it sees `(-g) * (-h')`.
These products agree exactly. The source locations also agree at the
same Fourier parameter, because the right-side convention supplies the
second location negation.

Consequently every individual plain chart, retained prime atom control,
formal scale, support, time, and profile is transported without a new
source identity or bound. The two original volume-control records only
exchange roles. Both orientations of a fixed profile can be included in
the finite catalogue before any moving source is chosen.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray] {k : ℕ}

namespace ActualSecondCorrelationRows

/-- The same original live row, as an equivalence of the two actual
finite carriers. No row or extracted element is chosen again. -/
def swapLiveEquiv (R : ActualSecondCorrelationRows A σ H ι) : R.live ≃ R.swapColumns.live where
  toFun := R.swapLive
  invFun h := ⟨h.val, by simpa only [R.swapColumns_live] using h.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

@[simp] theorem swapLiveEquiv_apply (h : R.live) :
    R.swapLiveEquiv h = R.swapLive h := rfl

@[simp] theorem swapLiveEquiv_symm_val (h : R.swapColumns.live) :
    (R.swapLiveEquiv.symm h).val = h.val := rfl

/-- The exceptional predicate is preserved on the same original row,
while its two actual character coordinates exchange places. -/
def swapExceptionalRowsEquiv (R : ActualSecondCorrelationRows A σ H ι)
    {theta : Finset (HeckeCharacter K)} (Q : PairedFiniteCharacters theta H) :
    R.exceptionalRows Q ≃ R.swapColumns.exceptionalRows Q.swapColumns where
  toFun h := ⟨R.swapLive h.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    simpa only [PairedFiniteCharacters.swapColumns_exceptional, swapLive_val] using
      (Finset.mem_filter.mp h.property).2⟩⟩
  invFun h := ⟨R.swapLiveEquiv.symm h.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    simpa only [PairedFiniteCharacters.swapColumns_exceptional, swapLiveEquiv_symm_val] using
      (Finset.mem_filter.mp h.property).2⟩⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext (Subtype.ext rfl)

@[simp] theorem swapExceptionalRowsEquiv_apply_val
    {theta : Finset (HeckeCharacter K)} (Q : PairedFiniteCharacters theta H)
    (h : R.exceptionalRows Q) :
    (R.swapExceptionalRowsEquiv Q h).val = R.swapLive h.val := rfl

end ActualSecondCorrelationRows

namespace ExceptionalPlainChart

variable {χ θ : HeckeCharacter K} {M Ψ : Ideal (𝓞 K) →* ℂ}
variable {g h' a b : A.R} {mask : Ideal (𝓞 K)} {W : ℝ → ℂ} {t N : ℝ}
variable {S : Finset (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {w : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ}
variable {x : HeckeGeneral.Analysis.NonzeroIdeal K → V} {ξ : V}

/-- The primitive residue entry depends on the actual product of the
two extracted factors. The original profile and support are unchanged. -/
theorem of_factor_product
    (T : ExceptionalPlainChart (σ := σ) χ θ M g h' Ψ mask W t N S w x ξ)
    (he : a * b = g * h') :
    ExceptionalPlainChart (σ := σ) χ θ M a b Ψ mask W t N S w x ξ where
  coefficient I hI := by simpa only [he] using T.coefficient I hI
  profile := T.profile
  support := T.support

end ExceptionalPlainChart

namespace SecondSideFrame

@[simp] theorem toLeft_source_factor_product
    (f : SecondSideFrame (V := V) C R Ray .right k) (h : R.live) :
    f.toLeft.source.extractedFactor (R.swapLive h) *
        (f.toLeft.source.row (R.swapLive h)).element =
      f.source.extractedFactor h * (f.source.row h).element := by
  change R.swapColumns.factor C h.val *
      (R.swapColumns.extractedRow C (R.swapLive h)).element =
    (-R.factor C h.val) * (R.extractedRow C h).element
  rw [R.swapColumns_factor C h.val, R.swapColumns_extractedRow_element C h,
    mul_neg, neg_mul]

@[simp] theorem toRight_source_factor_product
    (f : SecondSideFrame (V := V) C R Ray .left k) (h : R.live) :
    f.toRight.source.extractedFactor (R.swapLive h) *
        (f.toRight.source.row (R.swapLive h)).element =
      f.source.extractedFactor h * (f.source.row h).element := by
  change (-R.swapColumns.factor C h.val) *
      (R.swapColumns.extractedRow C (R.swapLive h)).element =
    R.factor C h.val * (R.extractedRow C h).element
  rw [R.swapColumns_factor C h.val, R.swapColumns_extractedRow_element C h, neg_mul_neg]

@[simp] theorem toLeft_source_leftLocation
    (f : SecondSideFrame (V := V) C R Ray .right k) (h : R.live) :
    f.toLeft.source.leftLocation (R.swapLive h) = f.source.leftLocation h := rfl

@[simp] theorem toLeft_source_rightLocation
    (f : SecondSideFrame (V := V) C R Ray .right k) (h : R.live) :
    f.toLeft.source.rightLocation (R.swapLive h) = f.source.rightLocation h := rfl

@[simp] theorem toLeft_source_slotLocation
    (f : SecondSideFrame (V := V) C R Ray .right k) (h : R.live) :
    f.toLeft.source.slotLocation (R.swapLive h) = f.source.slotLocation h := rfl

@[simp] theorem toRight_source_leftLocation
    (f : SecondSideFrame (V := V) C R Ray .left k) (h : R.live) :
    f.toRight.source.leftLocation (R.swapLive h) = f.source.leftLocation h := by
  funext I
  exact neg_neg _

@[simp] theorem toRight_source_rightLocation
    (f : SecondSideFrame (V := V) C R Ray .left k) (h : R.live) :
    f.toRight.source.rightLocation (R.swapLive h) = f.source.rightLocation h := by
  funext I
  exact neg_neg _

@[simp] theorem toRight_source_slotLocation
    (f : SecondSideFrame (V := V) C R Ray .left k) (h : R.live) :
    f.toRight.source.slotLocation (R.swapLive h) = f.source.slotLocation h := by
  funext j p
  exact neg_neg _

variable {Ψ : Ideal (𝓞 K) →* ℂ} {W₁ W₂ : ℝ → ℂ} {ξ : V} {h : R.live}

/-- The original ordinary charts of the right frame, on its identical
two plain supports, now supply the actual left terminal. -/
def ordinaryExceptionalAtToLeft
    (f : SecondSideFrame (V := V) C R Ray .right k)
    (T : f.source.OrdinaryExceptionalAt (σ := σ) Ψ W₁ W₂ ξ h) :
    f.toLeft.source.OrdinaryExceptionalAt (σ := σ) Ψ W₁ W₂ ξ (R.swapLive h) where
  mask := T.mask
  time := T.time
  product := T.product
  lower := T.lower
  lower_pos := T.lower_pos
  X₁_lower := T.X₁_lower
  X₂_lower := T.X₂_lower
  productX := T.productX
  chartX₁ := T.chartX₁.of_factor_product (f.toLeft_source_factor_product h)
  chartX₂ := T.chartX₂.of_factor_product (f.toLeft_source_factor_product h)

def ordinaryExceptionalAtToRight
    (f : SecondSideFrame (V := V) C R Ray .left k)
    (T : f.source.OrdinaryExceptionalAt (σ := σ) Ψ W₁ W₂ ξ h) :
    f.toRight.source.OrdinaryExceptionalAt (σ := σ) Ψ W₁ W₂ ξ (R.swapLive h) where
  mask := T.mask
  time := T.time
  product := T.product
  lower := T.lower
  lower_pos := T.lower_pos
  X₁_lower := T.X₁_lower
  X₂_lower := T.X₂_lower
  productX := T.productX
  chartX₁ := by
    simpa only [toRight_source_leftLocation] using
      T.chartX₁.of_factor_product (f.toRight_source_factor_product h)
  chartX₂ := by
    simpa only [toRight_source_rightLocation] using
      T.chartX₂.of_factor_product (f.toRight_source_factor_product h)

/-- The comparison rectangle uses the same two scales and profile
values. Only the phase-map proof follows the actual frame swap. -/
def exceptionalAtToLeft
    (f : SecondSideFrame (V := V) C R Ray .right k)
    (E : SecondCoefficientComparison f.dictionary)
    (T : f.source.ExceptionalAt (σ := σ) E.scale₁ E.scale₂
      (fun _ => E.leftWeight) (fun _ => E.rightWeight) Ψ W₁ W₂ ξ h) :
    f.toLeft.source.ExceptionalAt (σ := σ)
      (f.toLeftComparison E).scale₁ (f.toLeftComparison E).scale₂
      (fun _ => (f.toLeftComparison E).leftWeight)
      (fun _ => (f.toLeftComparison E).rightWeight) Ψ W₁ W₂ ξ (R.swapLive h) where
  mask := T.mask
  time := T.time
  product := T.product
  lower := T.lower
  lower_pos := T.lower_pos
  X₁_lower := T.X₁_lower
  X₂_lower := T.X₂_lower
  Y₁_lower := T.Y₁_lower
  Y₂_lower := T.Y₂_lower
  productX := T.productX
  productY := T.productY
  chartX₁ := T.chartX₁.of_factor_product (f.toLeft_source_factor_product h)
  chartX₂ := T.chartX₂.of_factor_product (f.toLeft_source_factor_product h)
  chartY₁ := T.chartY₁.of_factor_product (f.toLeft_source_factor_product h)
  chartY₂ := T.chartY₂.of_factor_product (f.toLeft_source_factor_product h)

def exceptionalAtToRight
    (f : SecondSideFrame (V := V) C R Ray .left k)
    (E : SecondCoefficientComparison f.dictionary)
    (T : f.source.ExceptionalAt (σ := σ) E.scale₁ E.scale₂
      (fun _ => E.leftWeight) (fun _ => E.rightWeight) Ψ W₁ W₂ ξ h) :
    f.toRight.source.ExceptionalAt (σ := σ)
      (f.toRightComparison E).scale₁ (f.toRightComparison E).scale₂
      (fun _ => (f.toRightComparison E).leftWeight)
      (fun _ => (f.toRightComparison E).rightWeight) Ψ W₁ W₂ ξ (R.swapLive h) where
  mask := T.mask
  time := T.time
  product := T.product
  lower := T.lower
  lower_pos := T.lower_pos
  X₁_lower := T.X₁_lower
  X₂_lower := T.X₂_lower
  Y₁_lower := T.Y₁_lower
  Y₂_lower := T.Y₂_lower
  productX := T.productX
  productY := T.productY
  chartX₁ := by
    simpa only [toRight_source_leftLocation] using
      T.chartX₁.of_factor_product (f.toRight_source_factor_product h)
  chartX₂ := by
    simpa only [toRight_source_rightLocation] using
      T.chartX₂.of_factor_product (f.toRight_source_factor_product h)
  chartY₁ := by
    simpa only [toRight_source_leftLocation] using
      T.chartY₁.of_factor_product (f.toRight_source_factor_product h)
  chartY₂ := by
    simpa only [toRight_source_rightLocation] using
      T.chartY₂.of_factor_product (f.toRight_source_factor_product h)

/-- Each retained prime atom has the same literal residue argument;
all other atomic windows are definitionally the original ones. -/
theorem ordinaryExceptionalAtToLeft_atomicControl
    (f : SecondSideFrame (V := V) C R Ray .right k)
    (T : f.source.OrdinaryExceptionalAt (σ := σ) Ψ W₁ W₂ ξ h)
    (Z : ℝ) (U : ExceptionalAtomicScales f.allocation)
    (H : T.source.AtomicControl Z U) :
    (f.ordinaryExceptionalAtToLeft T).source.AtomicControl Z U where
  base_pos := H.base_pos
  plain₁ := H.plain₁
  plain₂ := H.plain₂
  frozen_prime := H.frozen_prime
  frozen_annulus := H.frozen_annulus
  frozen_profile := H.frozen_profile
  frozen_norm := H.frozen_norm
  rectangle_product := H.rectangle_product
  prime_norm := H.prime_norm
  prime_atom j p hp := by
    simpa only [sourcePrimeTerm, toLeft_source_factor_product] using H.prime_atom j p hp

theorem ordinaryExceptionalAtToRight_atomicControl
    (f : SecondSideFrame (V := V) C R Ray .left k)
    (T : f.source.OrdinaryExceptionalAt (σ := σ) Ψ W₁ W₂ ξ h)
    (Z : ℝ) (U : ExceptionalAtomicScales f.allocation)
    (H : T.source.AtomicControl Z U) :
    (f.ordinaryExceptionalAtToRight T).source.AtomicControl Z U where
  base_pos := H.base_pos
  plain₁ := H.plain₁
  plain₂ := H.plain₂
  frozen_prime := H.frozen_prime
  frozen_annulus := H.frozen_annulus
  frozen_profile := H.frozen_profile
  frozen_norm := H.frozen_norm
  rectangle_product := H.rectangle_product
  prime_norm := H.prime_norm
  prime_atom j p hp := by
    simpa only [sourcePrimeTerm, toRight_source_factor_product] using H.prime_atom j p hp

theorem exceptionalAtToLeft_atomicControl
    (f : SecondSideFrame (V := V) C R Ray .right k)
    (E : SecondCoefficientComparison f.dictionary)
    (T : f.source.ExceptionalAt (σ := σ) E.scale₁ E.scale₂
      (fun _ => E.leftWeight) (fun _ => E.rightWeight) Ψ W₁ W₂ ξ h)
    (Z : ℝ) (U : ExceptionalAtomicScales f.allocation)
    (H : T.source.AtomicControl Z U) :
    (f.exceptionalAtToLeft E T).source.AtomicControl Z U where
  base_pos := H.base_pos
  plain₁ := H.plain₁
  plain₂ := H.plain₂
  frozen_prime := H.frozen_prime
  frozen_annulus := H.frozen_annulus
  frozen_profile := H.frozen_profile
  frozen_norm := H.frozen_norm
  rectangle_product := H.rectangle_product
  prime_norm := H.prime_norm
  prime_atom j p hp := by
    simpa only [sourcePrimeTerm, toLeft_source_factor_product] using H.prime_atom j p hp

theorem exceptionalAtToRight_atomicControl
    (f : SecondSideFrame (V := V) C R Ray .left k)
    (E : SecondCoefficientComparison f.dictionary)
    (T : f.source.ExceptionalAt (σ := σ) E.scale₁ E.scale₂
      (fun _ => E.leftWeight) (fun _ => E.rightWeight) Ψ W₁ W₂ ξ h)
    (Z : ℝ) (U : ExceptionalAtomicScales f.allocation)
    (H : T.source.AtomicControl Z U) :
    (f.exceptionalAtToRight E T).source.AtomicControl Z U where
  base_pos := H.base_pos
  plain₁ := H.plain₁
  plain₂ := H.plain₂
  frozen_prime := H.frozen_prime
  frozen_annulus := H.frozen_annulus
  frozen_profile := H.frozen_profile
  frozen_norm := H.frozen_norm
  rectangle_product := H.rectangle_product
  prime_norm := H.prime_norm
  prime_atom j p hp := by
    simpa only [sourcePrimeTerm, toRight_source_factor_product] using H.prime_atom j p hp

end SecondSideFrame

namespace ExceptionalOriginalProfilePair

/-- Exchange the two original profile pairs and their existing volume
proofs. Neither of the two plain profiles within a pair is exchanged. -/
def swap (p : ExceptionalOriginalProfilePair K) : ExceptionalOriginalProfilePair K where
  leftCharacter := p.rightCharacter
  rightCharacter := p.leftCharacter
  leftPlain₁ := p.rightPlain₁
  leftPlain₂ := p.rightPlain₂
  rightPlain₁ := p.leftPlain₁
  rightPlain₂ := p.leftPlain₂
  leftVolume := p.rightVolume
  rightVolume := p.leftVolume

@[simp] theorem swap_swap (p : ExceptionalOriginalProfilePair K) : p.swap.swap = p := rfl

/-- This two-element orientation family is fixed with the original
profile. Uniform orders and constants can be chosen over it before the
scale, source, selected row or chosen smaller second ideal. -/
def orientation (p : ExceptionalOriginalProfilePair K) (flipped : Bool) :
    ExceptionalOriginalProfilePair K := if flipped then p.swap else p

@[simp] theorem orientation_false (p : ExceptionalOriginalProfilePair K) :
    p.orientation false = p := rfl

@[simp] theorem orientation_true (p : ExceptionalOriginalProfilePair K) :
    p.orientation true = p.swap := rfl

/-- A canonical pair table formed from one earlier single-character
profile family. The two actual volume certificates follow their labels. -/
def ofFamily {Θ : Type*} (character : Θ → Ideal (𝓞 K) →* ℂ)
    (plain₁ plain₂ : Θ → ℝ → ℂ)
    (volume : ∀ χ, ExceptionalVolumeControl (character χ) (plain₁ χ) (plain₂ χ))
    (χ : Θ × Θ) : ExceptionalOriginalProfilePair K where
  leftCharacter := character χ.1
  rightCharacter := character χ.2
  leftPlain₁ := plain₁ χ.1
  leftPlain₂ := plain₂ χ.1
  rightPlain₁ := plain₁ χ.2
  rightPlain₂ := plain₂ χ.2
  leftVolume := volume χ.1
  rightVolume := volume χ.2

/-- Coordinate exchange is proved for this actual table; it is not
asserted for an arbitrary pair-profile function. -/
@[simp] theorem ofFamily_swap {Θ : Type*}
    (character : Θ → Ideal (𝓞 K) →* ℂ) (plain₁ plain₂ : Θ → ℝ → ℂ)
    (volume : ∀ χ, ExceptionalVolumeControl (character χ) (plain₁ χ) (plain₂ χ))
    (χ : Θ × Θ) :
    (ofFamily character plain₁ plain₂ volume χ).swap =
      ofFamily character plain₁ plain₂ volume (χ.2, χ.1) := rfl

/-- For arbitrary original left/right families the orientation is an
additional fixed finite coordinate. The true branch is indexed by the
swapped theta class and reads the old pair in its original order. -/
def orientedTable {Θ : Type*} (profiles : Θ × Θ → ExceptionalOriginalProfilePair K)
    (i : Bool × (Θ × Θ)) : ExceptionalOriginalProfilePair K :=
  if i.1 then (profiles (i.2.2, i.2.1)).swap else profiles i.2

@[simp] theorem orientedTable_false {Θ : Type*}
    (profiles : Θ × Θ → ExceptionalOriginalProfilePair K) (χ : Θ × Θ) :
    orientedTable profiles (false, χ) = profiles χ := rfl

@[simp] theorem orientedTable_true_swap {Θ : Type*}
    (profiles : Θ × Θ → ExceptionalOriginalProfilePair K) (χ : Θ × Θ) :
    orientedTable profiles (true, (χ.2, χ.1)) = (profiles χ).swap := rfl

/-- A table genuinely built from one family needs no additional
orientation-dependent profile choice after swapping the theta labels. -/
@[simp] theorem orientedTable_ofFamily {Θ : Type*}
    (character : Θ → Ideal (𝓞 K) →* ℂ) (plain₁ plain₂ : Θ → ℝ → ℂ)
    (volume : ∀ χ, ExceptionalVolumeControl (character χ) (plain₁ χ) (plain₂ χ))
    (flipped : Bool) (χ : Θ × Θ) :
    orientedTable (ofFamily character plain₁ plain₂ volume) (flipped, χ) =
      ofFamily character plain₁ plain₂ volume χ := by
  cases flipped <;> rfl

section UniformCatalogue

variable [IsPrincipalIdealRing A.R]
variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Θ : Type*} [Fintype Θ]

/-- The fixed Bool-times-theta-square catalogue supplies the order
before either column orientation or any moving label is selected. -/
def orientedCatalogueOrder (profiles : Θ × Θ → ExceptionalOriginalProfilePair K)
    (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent) : ℕ :=
  finiteExceptionalOrder (fun i : Bool × (Θ × Θ) =>
    (orientedTable profiles i).order (U := U) (E := E) (σ := σ) (η := η) (hS := hS)
      ε maskExponent hε hmask)

def orientedCatalogueConstant (profiles : Θ × Θ → ExceptionalOriginalProfilePair K)
    (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent) : ℝ :=
  finiteExceptionalConstant (fun i : Bool × (Θ × Θ) =>
    (orientedTable profiles i).constant (U := U) (E := E) (σ := σ) (η := η) (hS := hS)
      ε maskExponent hε hmask)

theorem orientedCatalogueConstant_pos (profiles : Θ × Θ → ExceptionalOriginalProfilePair K)
    (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent) :
    0 < orientedCatalogueConstant (U := U) (E := E) (σ := σ) (η := η) (hS := hS)
      profiles ε maskExponent hε hmask :=
  finiteExceptionalConstant_pos _ (fun i =>
    ((orientedTable profiles i).constant_pos (U := U) (E := E) (σ := σ) (η := η) (hS := hS)
      ε maskExponent hε hmask).le)

theorem orientedCatalogue_order_le (profiles : Θ × Θ → ExceptionalOriginalProfilePair K)
    (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent) (i : Bool × (Θ × Θ)) :
    (orientedTable profiles i).order (U := U) (E := E) (σ := σ) (η := η) (hS := hS)
      ε maskExponent hε hmask ≤
      orientedCatalogueOrder (U := U) (E := E) (σ := σ) (η := η) (hS := hS)
        profiles ε maskExponent hε hmask :=
  Finset.le_sup (Finset.mem_univ i)

theorem orientedCatalogue_constant_le (profiles : Θ × Θ → ExceptionalOriginalProfilePair K)
    (ε maskExponent : ℝ) (hε : 0 < ε) (hmask : 0 ≤ maskExponent) (i : Bool × (Θ × Θ)) :
    (orientedTable profiles i).constant (U := U) (E := E) (σ := σ) (η := η) (hS := hS)
      ε maskExponent hε hmask ≤
      orientedCatalogueConstant (U := U) (E := E) (σ := σ) (η := η) (hS := hS)
        profiles ε maskExponent hε hmask := by
  have hs := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Bool × (Θ × Θ)))) =>
      ((orientedTable profiles j).constant_pos (U := U) (E := E) (σ := σ) (η := η) (hS := hS)
        ε maskExponent hε hmask).le) (Finset.mem_univ i)
  unfold orientedCatalogueConstant finiteExceptionalConstant
  linarith

end UniformCatalogue

end ExceptionalOriginalProfilePair

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondCorrelationRows.swapExceptionalRowsEquiv
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.toLeft_source_factor_product
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.toRight_source_factor_product
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.ordinaryExceptionalAtToLeft
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.exceptionalAtToRight
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.ordinaryExceptionalAtToLeft_atomicControl
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.exceptionalAtToRight_atomicControl
#print axioms HeckeSkeleton.Moments.EngineStep.ExceptionalOriginalProfilePair.ofFamily_swap
#print axioms HeckeSkeleton.Moments.EngineStep.ExceptionalOriginalProfilePair.orientedTable_ofFamily
#print axioms HeckeSkeleton.Moments.EngineStep.ExceptionalOriginalProfilePair.orientedCatalogueConstant_pos
#print axioms HeckeSkeleton.Moments.EngineStep.ExceptionalOriginalProfilePair.orientedCatalogue_order_le
