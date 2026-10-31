import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalThetaPartition
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalRelativeBudget

/-!
# Original atoms and generators on each actual theta class

The finite inducing-character partition restricts the original rows.
It preserves both complete source columns, all their frozen atoms,
the actual common ideals and their orbital scalar, and the original
ideal-fibre bound.  In particular the right column still uses the
negative extracted factor and the same residual generator as the left.

The pointwise binding below applies the exceptional volume estimate to
one actual character pair at a time.  Together with the exact finite
partition this avoids assuming that membership in a finite theta set
already makes the inducing character constant across all rows.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

namespace FrozenSourceAtoms

variable {H : Type*} {rows : Finset H} {k : ℕ}

/-- Only row-dependent proof fields are restricted.  The original
individual coefficients, frozen ideals and profile windows are literal. -/
def onRows (W : FrozenSourceAtoms A σ H rows k) (rows' : Finset H)
    (hrows : rows' ⊆ rows) : FrozenSourceAtoms A σ H rows' k where
  plain₁ := W.plain₁
  plain₂ := W.plain₂
  keep := W.keep
  primes := W.primes
  characters := W.characters
  factor := W.factor
  residual := W.residual
  base := W.base
  base_pos := W.base_pos
  length := W.length
  slotWeight := W.slotWeight
  annulus := W.annulus
  profile := W.profile
  annulus_nonneg := W.annulus_nonneg
  profile_nonneg := W.profile_nonneg
  plain₁_bound := fun h hh => W.plain₁_bound h (hrows hh)
  plain₂_bound := fun h hh => W.plain₂_bound h (hrows hh)
  prime_bound := fun h hh => W.prime_bound h (hrows hh)
  prime_annulus := W.prime_annulus
  slot_bound := fun h hh => W.slot_bound h (hrows hh)

@[simp] theorem onRows_value (W : FrozenSourceAtoms A σ H rows k)
    (rows' : Finset H) (hrows : rows' ⊆ rows) (h : H) :
    (W.onRows rows' hrows).value h = W.value h := rfl

@[simp] theorem onRows_ideal (W : FrozenSourceAtoms A σ H rows k)
    (rows' : Finset H) (hrows : rows' ⊆ rows) :
    (W.onRows rows' hrows).ideal = W.ideal := rfl

@[simp] theorem onRows_envelope (W : FrozenSourceAtoms A σ H rows k)
    (rows' : Finset H) (hrows : rows' ⊆ rows) :
    (W.onRows rows' hrows).envelope = W.envelope := rfl

end FrozenSourceAtoms

variable [IsPrincipalIdealRing A.R]
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {C : A.GeneralArithmeticContext σ η hS}
variable {R : ActualSecondCorrelationRows A σ H ι}

namespace ActualSecondRowMass

variable {kLeft kRight : ℕ} (W : ActualSecondRowMass R C kLeft kRight)

/-- The actual row calibration after restriction.  No new row bound
or fibre estimate is supplied: they come from the original atoms and
the original ideal fibres on the larger row set. -/
def restrictRows (p : H → Prop) :
    ActualSecondRowMass (R.restrictRows p) C kLeft kRight where
  leftAtoms := W.leftAtoms.onRows (R.rows.filter p) (Finset.filter_subset p R.rows)
  rightAtoms := W.rightAtoms.onRows (R.rows.filter p) (Finset.filter_subset p R.rows)
  left_ideal := W.left_ideal
  right_ideal := W.right_ideal
  radius := W.radius
  mask := W.mask
  rowProfile := W.rowProfile
  profileBound := W.profileBound
  profileBound_nonneg := W.profileBound_nonneg
  profile_bound := fun h hh => W.profile_bound h (Finset.mem_filter.mp hh).1
  weight_eq := fun h hh => W.weight_eq h (Finset.mem_filter.mp hh).1
  unitIdeal := W.unitIdeal
  unit_ideal := fun h hh => W.unit_ideal h (Finset.mem_filter.mp hh).1
  nonunitIdeal := W.nonunitIdeal
  nonunit_ideal := fun h hh => W.nonunit_ideal h (Finset.mem_filter.mp hh).1
  left_positive := W.left_positive
  originalFiber := W.originalFiber
  original_fibers := by
    intro I
    apply le_trans (Finset.card_le_card ?_) (W.original_fibers I)
    intro h hh
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).1,
        (Finset.mem_filter.mp hh).2⟩

@[simp] theorem restrictRows_leftIdeal (p : H → Prop) :
    (W.restrictRows p).leftIdeal = W.leftIdeal := rfl

@[simp] theorem restrictRows_rightIdeal (p : H → Prop) :
    (W.restrictRows p).rightIdeal = W.rightIdeal := rfl

@[simp] theorem restrictRows_commonEnvelope (p : H → Prop) :
    (W.restrictRows p).commonEnvelope = W.commonEnvelope := rfl

@[simp] theorem restrictRows_rowBound (p : H → Prop) :
    (W.restrictRows p).rowBound = W.rowBound := rfl

@[simp] theorem restrictRows_originalFiber (p : H → Prop) :
    (W.restrictRows p).originalFiber = W.originalFiber := rfl

end ActualSecondRowMass

namespace SecondSideFrame

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {side : SecondColumnSide} {k : ℕ}
variable (f : SecondSideFrame (V := V) C R Ray side k)

/-- A literal original exceptional chart is transported to the
restricted row with the same residual element; no chart is reselected. -/
def restrictExceptionalAt (p : H → Prop)
    (E : SecondCoefficientComparison f.dictionary)
    {Ψ : Ideal (𝓞 F) →* ℂ} {W₁ W₂ : ℝ → ℂ} {ξ : V}
    (h : (R.restrictRows p).live)
    (T : f.source.ExceptionalAt (σ := σ) E.scale₁ E.scale₂
      (fun _ => E.leftWeight) (fun _ => E.rightWeight) Ψ W₁ W₂ ξ (R.restrictLive p h)) :
    (f.restrictRows p).source.ExceptionalAt (σ := σ) E.scale₁ E.scale₂
      (fun _ => E.leftWeight) (fun _ => E.rightWeight) Ψ W₁ W₂ ξ h := by
  cases side <;> exact T

end SecondSideFrame

namespace ActualHybridLeaf

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable (B : ActualHybridLeaf F H U E)

/-- This is the exceptional integrand of the canonical leaf on one
actual theta class.  It is bound to the same original whole centered
coefficients by the original single-atom identities. -/
theorem thetaClassLeaf_exceptionalIntegrand_eq_centered_frames
    (left : SecondSideFrame (V := WithLp 2 (U × E)) C R Ray .left B.leftSlots)
    (right : SecondSideFrame (V := WithLp 2 (U × E)) C R Ray .right B.rightSlots)
    (EL : SecondCoefficientComparison left.dictionary)
    (ER : SecondCoefficientComparison right.dictionary)
    {theta : Finset (HeckeCharacter F)} (Q : PairedFiniteCharacters theta H)
    (hrows : B.rows = R.rows) (hleft : B.left = left.allocation.columns)
    (hright : B.right = right.allocation.columns) (hpredicate : B.exceptional = Q.exceptional)
    (hweight : ∀ h ∈ B.rows, B.rowWeight h = R.weight h * R.correlation h)
    (hleftAtom : ∀ h ∈ B.rows, ∀ i ∈ B.left,
      B.leftCoefficient h i = left.centeredCoefficient EL h i)
    (hrightAtom : ∀ h ∈ B.rows, ∀ i ∈ B.right,
      star (B.rightCoefficient h i) = right.centeredCoefficient ER h i)
    (hleftPoint : ∀ h ∈ B.rows, ∀ i ∈ B.left,
      WithLp.toLp 2 (B.leftFirst h i, B.leftSecond h i) =
        rawSourceLocation (left.leftLocation h) (left.rightLocation h) (left.slotLocation h) i)
    (hrightPoint : ∀ h ∈ B.rows, ∀ i ∈ B.right,
      WithLp.toLp 2 (-B.rightFirst h i, B.rightSecond h i) =
        rawSourceLocation (right.leftLocation h) (right.rightLocation h) (right.slotLocation h) i)
    (χ : theta × theta) (z : U × E) :
    (B.thetaClassLeaf Q χ).exceptionalIntegrand z =
      jointColumnPairMagnitude ((R.restrictRows (Q.thetaClass χ)).exceptionalRows Q)
        left.allocation.columns right.allocation.columns
        (fun h : (R.restrictRows (Q.thetaClass χ)).live =>
          R.weight h.val * R.correlation h.val)
        (fun h => left.centeredCoefficient EL h.val)
        (fun h => right.centeredCoefficient ER h.val)
        (fun h => rawSourceLocation (left.leftLocation h.val) (left.rightLocation h.val)
          (left.slotLocation h.val))
        (fun h => rawSourceLocation (right.leftLocation h.val) (right.rightLocation h.val)
          (right.slotLocation h.val)) (WithLp.toLp 2 z) := by
  exact (B.thetaClassLeaf Q χ).exceptionalIntegrand_eq_centered_frames C
    (left.restrictRows (Q.thetaClass χ)) (right.restrictRows (Q.thetaClass χ))
    EL ER Q (congrArg (fun rows => rows.filter (Q.thetaClass χ)) hrows)
    hleft hright hpredicate
    (fun h hh => hweight h (Finset.mem_filter.mp hh).1)
    (fun h hh => hleftAtom h (Finset.mem_filter.mp hh).1)
    (fun h hh => hrightAtom h (Finset.mem_filter.mp hh).1)
    (fun h hh => hleftPoint h (Finset.mem_filter.mp hh).1)
    (fun h hh => hrightPoint h (Finset.mem_filter.mp hh).1) z

end ActualHybridLeaf
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualSecondRowMass.restrictRows
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.restrictExceptionalAt
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.thetaClassLeaf_exceptionalIntegrand_eq_centered_frames
