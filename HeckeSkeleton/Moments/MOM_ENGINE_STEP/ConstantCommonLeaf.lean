import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCommonAtomBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedHybridLeaves

/-!
# Move the actual constant common atoms inside the same hybrid leaf

The bare common-extraction atoms are independent of the physical row.
Their two constants can therefore be moved from the complete left and
right columns into the common row weight even after paired Cauchy.
The exceptional row products and the ordinary paired energies are
exactly unchanged. No corresponding assertion is made for arbitrary
row-dependent scalars.

The original finite label, both kernels, both continuous locations, the
exceptional predicate, and the outer scalar remain fixed. All inputs
identifying the residual columns are individual coefficient identities.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {H U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

private theorem constant_atom_column {E I : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Finset I) (c d : I → ℂ) (a : ℂ) (x : I → E) (ξ : E)
    (hc : ∀ i ∈ S, c i = a * d i) :
    jointFourierColumn S c x ξ = a * jointFourierColumn S d x ξ := by
  calc
    _ = jointFourierColumn S (fun i => a * d i) x ξ :=
      Finset.sum_congr rfl (fun i hi => by rw [hc i hi])
    _ = _ := by simp only [jointFourierColumn, Finset.mul_sum, mul_assoc]

private theorem constant_atom_energy {E I J : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rows : Finset J) (cols : Finset I) (q : J → ℂ)
    (c d : J → I → ℂ) (a : ℂ) (x : J → I → E) (ξ : E)
    (hc : ∀ h ∈ rows, ∀ i ∈ cols, c h i = a * d h i) :
    jointColumnEnergy rows cols q c x ξ =
      ‖a‖ ^ 2 * jointColumnEnergy rows cols q d x ξ := by
  unfold jointColumnEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [constant_atom_column cols (c h) (d h) a (x h) ξ (hc h hh), norm_mul, mul_pow]
  ring

private theorem constant_atom_row_weight {E I J : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rows : Finset J) (cols : Finset I) (q : J → ℂ)
    (c : J → I → ℂ) (a b : ℂ) (x : J → I → E) (ξ : E) :
    jointColumnEnergy rows cols (fun h => q h * a * star b) c x ξ =
      (‖a‖ * ‖b‖) * jointColumnEnergy rows cols q c x ξ := by
  unfold jointColumnEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  simp only [norm_mul, norm_star]
  ring

private theorem sqrt_pair_constant_atoms (a b x y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a ^ 2 * x) * Real.sqrt (b ^ 2 * y) =
      Real.sqrt ((a * b) * x) * Real.sqrt ((a * b) * y) := by
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_mul (sq_nonneg b),
    Real.sqrt_sq ha, Real.sqrt_sq hb,
    Real.sqrt_mul (mul_nonneg ha hb), Real.sqrt_mul (mul_nonneg ha hb)]
  calc
    _ = (a * b) * (Real.sqrt x * Real.sqrt y) := by ring
    _ = Real.sqrt (a * b) ^ 2 * (Real.sqrt x * Real.sqrt y) := by
      rw [Real.sq_sqrt (mul_nonneg ha hb)]
    _ = _ := by ring

namespace ActualHybridLeaf

variable (B : ActualHybridLeaf K H U V)

/-- Only the three arithmetic coefficient fields change.  In particular
the finite carrier and its exceptional partition are identical. -/
def withConstantAtoms (a b : ℂ)
    (c : H → AllocationColumn K B.leftSlots → ℂ)
    (d : H → AllocationColumn K B.rightSlots → ℂ) : ActualHybridLeaf K H U V :=
  { B with
    rowWeight := fun h => B.rowWeight h * a * star b
    leftCoefficient := c
    rightCoefficient := d }

variable (a b : ℂ)
variable (c : H → AllocationColumn K B.leftSlots → ℂ)
variable (d : H → AllocationColumn K B.rightSlots → ℂ)
variable (hc : ∀ h ∈ B.rows, ∀ i ∈ B.left, B.leftCoefficient h i = a * c h i)
variable (hd : ∀ h ∈ B.rows, ∀ i ∈ B.right, B.rightCoefficient h i = b * d h i)

theorem exceptionalIntegrand_eq_withConstantAtoms (z : U × V) :
    B.exceptionalIntegrand z = (B.withConstantAtoms a b c d).exceptionalIntegrand z := by
  unfold exceptionalIntegrand jointColumnPairMagnitude
  dsimp only [withConstantAtoms]
  apply Finset.sum_congr rfl
  intro h hh
  have hrow := (Finset.mem_filter.mp hh).1
  rw [constant_atom_column B.left (B.leftCoefficient h) (c h) a _ _ (hc h hrow)]
  rw [constant_atom_column B.right (fun i => star (B.rightCoefficient h i))
    (fun i => star (d h i)) (star b) _ _ (fun i hi => by rw [hd h hrow i hi, star_mul'])]
  simp only [norm_mul, norm_star]
  ring

theorem ordinaryIntegrand_eq_withConstantAtoms (z : U × V) :
    B.ordinaryIntegrand z = (B.withConstantAtoms a b c d).ordinaryIntegrand z := by
  have hl := constant_atom_energy (B.rows.filter fun h => ¬B.exceptional h) B.left
    B.rowWeight B.leftCoefficient c a
    (fun h i => WithLp.toLp 2 (B.leftFirst h i, B.leftSecond h i))
    (WithLp.toLp 2 z) (fun h hh => hc h (Finset.mem_filter.mp hh).1)
  have hr := constant_atom_energy (B.rows.filter fun h => ¬B.exceptional h) B.right
    B.rowWeight (fun h i => star (B.rightCoefficient h i)) (fun h i => star (d h i))
    (star b) (fun h i => WithLp.toLp 2 (-B.rightFirst h i, B.rightSecond h i))
    (WithLp.toLp 2 z) (fun h hh i hi => by
      rw [hd h (Finset.mem_filter.mp hh).1 i hi, star_mul'])
  simp only [norm_star] at hr
  unfold ordinaryIntegrand
  dsimp only [withConstantAtoms]
  rw [hl, hr, constant_atom_row_weight, constant_atom_row_weight]
  exact sqrt_pair_constant_atoms ‖a‖ ‖b‖ _ _ (norm_nonneg _) (norm_nonneg _)

theorem exceptionalCost_eq_withConstantAtoms :
    B.exceptionalCost = (B.withConstantAtoms a b c d).exceptionalCost := by
  change B.weight * (∫ z, B.exceptionalIntegrand z ∂B.measure) =
    B.weight * (∫ z, (B.withConstantAtoms a b c d).exceptionalIntegrand z ∂B.measure)
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall
    (B.exceptionalIntegrand_eq_withConstantAtoms a b c d hc hd))

theorem ordinaryCost_eq_withConstantAtoms :
    B.ordinaryCost = (B.withConstantAtoms a b c d).ordinaryCost := by
  change B.weight * (∫ z, B.ordinaryIntegrand z ∂B.measure) =
    B.weight * (∫ z, (B.withConstantAtoms a b c d).ordinaryIntegrand z ∂B.measure)
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall
    (B.ordinaryIntegrand_eq_withConstantAtoms a b c d hc hd))

theorem cost_eq_withConstantAtoms :
    B.cost = (B.withConstantAtoms a b c d).cost := by
  rw [cost, cost, B.exceptionalCost_eq_withConstantAtoms a b c d hc hd,
    B.ordinaryCost_eq_withConstantAtoms a b c d hc hd]

/-- The arithmetic extraction records only the two original single
coefficient identities; all energy and cost identities are proved. -/
structure ConstantAtomExtraction where
  leftScalar : ℂ
  rightScalar : ℂ
  leftResidual : H → AllocationColumn K B.leftSlots → ℂ
  rightResidual : H → AllocationColumn K B.rightSlots → ℂ
  left : ∀ h ∈ B.rows, ∀ i ∈ B.left,
    B.leftCoefficient h i = leftScalar * leftResidual h i
  right : ∀ h ∈ B.rows, ∀ i ∈ B.right,
    B.rightCoefficient h i = rightScalar * rightResidual h i

namespace ConstantAtomExtraction

variable {B} (X : B.ConstantAtomExtraction)

def leaf : ActualHybridLeaf K H U V :=
  B.withConstantAtoms X.leftScalar X.rightScalar X.leftResidual X.rightResidual

theorem exceptionalCost_eq : B.exceptionalCost = X.leaf.exceptionalCost :=
  B.exceptionalCost_eq_withConstantAtoms _ _ _ _ X.left X.right

theorem ordinaryCost_eq : B.ordinaryCost = X.leaf.ordinaryCost :=
  B.ordinaryCost_eq_withConstantAtoms _ _ _ _ X.left X.right

theorem cost_eq : B.cost = X.leaf.cost :=
  B.cost_eq_withConstantAtoms _ _ _ _ X.left X.right

theorem ordinaryIntegrand_eq (z : U × V) :
    B.ordinaryIntegrand z = X.leaf.ordinaryIntegrand z :=
  B.ordinaryIntegrand_eq_withConstantAtoms _ _ _ _ X.left X.right z

/-- Bind the actual residual leaf to its source rectangles by individual
row weights, columns and locations. The two common constants occur only
in the row-weight equality; neither column is divided by a possibly
zero constant. -/
def ordinaryBinding
    {A : SArithmeticData K} {σ : K →+* ℂ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ActualSecondCorrelationRows A σ H ι}
    {Ray : Type*} [CommGroup Ray] [Fintype Ray]
    {S₁ S₂ : Finset (Ideal (𝓞 K))}
    {S : Fin B.leftSlots → Finset (HeightOneSpectrum (𝓞 K))}
    {T₁ T₂ : Finset (Ideal (𝓞 K))}
    {T : Fin B.rightSlots → Finset (HeightOneSpectrum (𝓞 K))}
    {IA : AllocationColumn K B.leftSlots → A.Exterior}
    {IB : AllocationColumn K B.rightSlots → A.Exterior}
    {rayLeft : AllocationColumn K B.leftSlots → Ray}
    {rayRight : AllocationColumn K B.rightSlots → Ray}
    {wholeLeft : AllocationColumn K B.leftSlots → ℂ}
    {wholeRight : AllocationColumn K B.rightSlots → ℂ}
    {x : H → AllocationColumn K B.leftSlots → WithLp 2 (U × V)}
    {y : H → AllocationColumn K B.rightSlots → WithLp 2 (U × V)}
    {b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB}
    {exceptional : H → Prop}
    (rectangles : HybridOrdinaryRectangles R Ray S₁ S₂ S T₁ T₂ T IA IB
      rayLeft rayRight wholeLeft wholeRight x y b exceptional)
    (hrows : B.rows = R.rows)
    (hleft : B.left = b.val.leftColumns S₁ S₂ S)
    (hright : B.right = b.val.rightColumns)
    (hexceptional : ∀ h ∈ B.rows, B.exceptional h ↔ exceptional h)
    (hweight : ∀ h ∈ B.rows,
      B.rowWeight h * X.leftScalar * star X.rightScalar = R.weight h * R.correlation h)
    (hleftCoefficient : ∀ h ∈ B.rows, ∀ i ∈ B.left,
      X.leftResidual h i =
        secondAllocatedLeftCoefficient (σ := σ) Ray IA R.frequency rayLeft b.val.2.1 wholeLeft h i)
    (hrightCoefficient : ∀ h ∈ B.rows, ∀ i ∈ B.right,
      star (X.rightResidual h i) =
        secondAllocatedRightCoefficient (σ := σ) Ray IB R.frequency rayRight b.val.2.1 wholeRight h i)
    (hleftPoint : ∀ h ∈ B.rows, ∀ i ∈ B.left,
      WithLp.toLp 2 (B.leftFirst h i, B.leftSecond h i) = x h i)
    (hrightPoint : ∀ h ∈ B.rows, ∀ i ∈ B.right,
      WithLp.toLp 2 (-B.rightFirst h i, B.rightSecond h i) = y h i) :
    X.leaf.OrdinaryBinding rectangles where
  rows := by
    intro h hh
    exact hrows.symm ▸ hh
  rows_zero h hh hn := (hn (hrows ▸ hh)).elim
  left := hleft
  right := hright
  exceptional := hexceptional
  rowWeight := hweight
  leftCoefficient := hleftCoefficient
  rightCoefficient := hrightCoefficient
  leftPoint := hleftPoint
  rightPoint := hrightPoint

/-- The arithmetic source uses precisely the original nonzero complete
correlations. Omitted rows have zero actual weight, proved from the same
single-row common-atom identity. The original leaf, its two kernels,
the outer labels and both stored complete columns remain unchanged. -/
def ordinaryBindingOnCorrelationSupport
    {A : SArithmeticData K} {σ : K →+* ℂ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ActualSecondCorrelationRows A σ H ι}
    {Ray : Type*} [CommGroup Ray] [Fintype Ray]
    {S₁ S₂ : Finset (Ideal (𝓞 K))}
    {S : Fin B.leftSlots → Finset (HeightOneSpectrum (𝓞 K))}
    {T₁ T₂ : Finset (Ideal (𝓞 K))}
    {T : Fin B.rightSlots → Finset (HeightOneSpectrum (𝓞 K))}
    {IA : AllocationColumn K B.leftSlots → A.Exterior}
    {IB : AllocationColumn K B.rightSlots → A.Exterior}
    {rayLeft : AllocationColumn K B.leftSlots → Ray}
    {rayRight : AllocationColumn K B.rightSlots → Ray}
    {wholeLeft : AllocationColumn K B.leftSlots → ℂ}
    {wholeRight : AllocationColumn K B.rightSlots → ℂ}
    {x : H → AllocationColumn K B.leftSlots → WithLp 2 (U × V)}
    {y : H → AllocationColumn K B.rightSlots → WithLp 2 (U × V)}
    {b : liveSecondAllocationBranches (Ray := Ray) S₁ S₂ S T₁ T₂ T IB}
    {exceptional : H → Prop}
    (rectangles : HybridOrdinaryRectangles
      (R.restrictRows (fun h => R.correlation h ≠ 0))
      Ray S₁ S₂ S T₁ T₂ T IA IB rayLeft rayRight wholeLeft wholeRight x y b exceptional)
    (hrows : B.rows = R.rows)
    (hleft : B.left = b.val.leftColumns S₁ S₂ S)
    (hright : B.right = b.val.rightColumns)
    (hexceptional : ∀ h ∈ B.rows, B.exceptional h ↔ exceptional h)
    (hweight : ∀ h ∈ B.rows,
      B.rowWeight h * X.leftScalar * star X.rightScalar = R.weight h * R.correlation h)
    (hleftCoefficient : ∀ h ∈ B.rows, ∀ i ∈ B.left,
      X.leftResidual h i =
        secondAllocatedLeftCoefficient (σ := σ) Ray IA R.frequency rayLeft b.val.2.1 wholeLeft h i)
    (hrightCoefficient : ∀ h ∈ B.rows, ∀ i ∈ B.right,
      star (X.rightResidual h i) =
        secondAllocatedRightCoefficient (σ := σ) Ray IB R.frequency rayRight b.val.2.1 wholeRight h i)
    (hleftPoint : ∀ h ∈ B.rows, ∀ i ∈ B.left,
      WithLp.toLp 2 (B.leftFirst h i, B.leftSecond h i) = x h i)
    (hrightPoint : ∀ h ∈ B.rows, ∀ i ∈ B.right,
      WithLp.toLp 2 (-B.rightFirst h i, B.rightSecond h i) = y h i) :
    X.leaf.OrdinaryBinding rectangles where
  rows := by
    intro h hh
    exact hrows.symm ▸ (Finset.mem_filter.mp hh).1
  rows_zero h hh hn := by
    have hc : R.correlation h = 0 := by
      by_contra hc
      exact hn (Finset.mem_filter.mpr ⟨hrows ▸ hh, hc⟩)
    change B.rowWeight h * X.leftScalar * star X.rightScalar = 0
    rw [hweight h hh, hc, mul_zero]
  left := hleft
  right := hright
  exceptional := hexceptional
  rowWeight := hweight
  leftCoefficient := hleftCoefficient
  rightCoefficient := hrightCoefficient
  leftPoint := hleftPoint
  rightPoint := hrightPoint

/-- A normalization for the actual residual leaf bounds the original
ordinary term. No source-polynomial or source-energy identity is input. -/
theorem ordinaryCost_le_sourcePairs
    {A : SArithmeticData K} {σ : K →+* ℂ}
    {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
    {C : A.GeneralArithmeticContext σ η hS}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ray : Type*} [CommGroup Ray] [Fintype Ray] {ω ψ : HeckeCharacter K}
    {Z : ℝ} {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)}
    (N : X.leaf.NormalizationData (ι := ι) C Ray ω ψ Z
      rowDomain heightDomain window seminorms)
    (parentWidth : ℝ) (hZ : 0 < Z) :
    B.ordinaryCost / Z ^ parentWidth ≤
      ∑ rs : Bool × Bool, B.weight *
        ∫ z : U × V, N.family.sourcePair parentWidth rs (WithLp.toLp 2 z) ∂B.measure := by
  rw [X.ordinaryCost_eq]
  exact N.ordinaryCost_le_sourcePairs parentWidth hZ

end ConstantAtomExtraction
end ActualHybridLeaf

namespace SupportCartesianBranch.CommonAtomBounds

variable {A : SArithmeticData K} {σ : K →+* ℂ} {k : ℕ}
variable {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {P : Finset (Ideal (𝓞 K))}
variable {b : SupportCartesianBranch S₁ S₂ S P}
variable {T : FixedChildCharacters K k} {Z : ℝ} {length : Fin k → ℝ}
variable {w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ}
variable (bounds : b.CommonAtomBounds T Z length w)

/-- The actual atom construction has factor=residual=1 and all
characters and slot weights fixed before the physical row. -/
def constantValue : ℂ :=
  (bounds.atoms (A := A) (σ := σ) (Finset.univ : Finset PUnit)).value PUnit.unit

theorem atoms_value_eq_constant {J : Type*} (rows : Finset J) (h : J) :
    (bounds.atoms (A := A) (σ := σ) rows).value h =
      bounds.constantValue (A := A) (σ := σ) := rfl

theorem constantValue_eq_bare (I : A.Exterior)
    (hI : b.plainExtract₁ * b.plainExtract₂ * (∏ i, b.slotExtract i) = I.val) :
    bounds.constantValue (A := A) (σ := σ) = b.bareCommonScalar T Z length w :=
  bounds.atoms_value (Finset.univ : Finset PUnit) I hI PUnit.unit

end SupportCartesianBranch.CommonAtomBounds

namespace ActualHybridLeaf.ConstantAtomExtraction

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {k l : ℕ}
variable {S₁ S₂ T₁ T₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {T : Fin l → Finset (HeightOneSpectrum (𝓞 K))}
variable {P : Finset (Ideal (𝓞 K))}
variable {left : SupportCartesianBranch S₁ S₂ S P}
variable {right : SupportCartesianBranch T₁ T₂ T P}
variable {charsL : FixedChildCharacters K k} {charsR : FixedChildCharacters K l}
variable {Z : ℝ} {lengthL : Fin k → ℝ} {lengthR : Fin l → ℝ}
variable {wL : Fin k → HeightOneSpectrum (𝓞 K) → ℂ}
variable {wR : Fin l → HeightOneSpectrum (𝓞 K) → ℂ}
variable (B : ActualHybridLeaf K H U V)
variable (BL : left.CommonAtomBounds charsL Z lengthL wL)
variable (BR : right.CommonAtomBounds charsR Z lengthR wR)

/-- The scalar is the actual common atom evaluated at one, exactly as
in the complete-correlation row-mass theorem. The required coefficient
identities are supplied by the proved individual-factor extraction. -/
def ofCommonAtoms
    (IL IR : A.Exterior)
    (hIL : left.plainExtract₁ * left.plainExtract₂ * (∏ i, left.slotExtract i) = IL.val)
    (hIR : right.plainExtract₁ * right.plainExtract₂ * (∏ i, right.slotExtract i) = IR.val)
    (c : H → AllocationColumn K B.leftSlots → ℂ)
    (d : H → AllocationColumn K B.rightSlots → ℂ)
    (hc : ∀ h ∈ B.rows, ∀ i ∈ B.left,
      B.leftCoefficient h i = left.bareCommonScalar charsL Z lengthL wL * c h i)
    (hd : ∀ h ∈ B.rows, ∀ i ∈ B.right,
      B.rightCoefficient h i = right.bareCommonScalar charsR Z lengthR wR * d h i) :
    B.ConstantAtomExtraction where
  leftScalar := BL.constantValue (A := A) (σ := σ)
  rightScalar := BR.constantValue (A := A) (σ := σ)
  leftResidual := c
  rightResidual := d
  left h hh i hi := by rw [BL.constantValue_eq_bare IL hIL]; exact hc h hh i hi
  right h hh i hi := by rw [BR.constantValue_eq_bare IR hIR]; exact hd h hh i hi

/-- The reweighted stored row is precisely the arithmetic context with
the same complete correlation and the actual two common atom tables.
No equality of summed kernels is assumed. -/
theorem commonAtoms_rowWeight
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ActualSecondCorrelationRows A σ H ι)
    (hweight : ∀ h ∈ B.rows, B.rowWeight h = R.weight h * R.correlation h)
    (c : H → AllocationColumn K B.leftSlots → ℂ)
    (d : H → AllocationColumn K B.rightSlots → ℂ)
    (h : H) (hh : h ∈ B.rows) :
    (B.withConstantAtoms (BL.constantValue (A := A) (σ := σ))
      (BR.constantValue (A := A) (σ := σ)) c d).rowWeight h =
      (R.withCommonAtoms (BL.atoms R.rows) (BR.atoms R.rows)).weight h *
        R.correlation h := by
  change (B.rowWeight h * BL.constantValue (A := A) (σ := σ) *
    star (BR.constantValue (A := A) (σ := σ))) =
    (R.weight h * (BL.atoms (A := A) (σ := σ) R.rows).value h *
      star ((BR.atoms (A := A) (σ := σ) R.rows).value h)) *
      R.correlation h
  rw [hweight h hh, BL.atoms_value_eq_constant, BR.atoms_value_eq_constant]
  ring

end ActualHybridLeaf.ConstantAtomExtraction

namespace ActualHybridFamily

variable {J : Type*} [Fintype J]
variable (leaves : J → ActualHybridLeaf K H U V)
variable (X : ∀ j, (leaves j).ConstantAtomExtraction)

/-- The same actual finite labels are retained when the common atoms
are moved into the row weight. -/
def withConstantAtoms : J → ActualHybridLeaf K H U V := fun j => (X j).leaf

theorem sum_cost_eq_withConstantAtoms :
    (∑ j, (leaves j).cost) = ∑ j, (withConstantAtoms leaves X j).cost :=
  Finset.sum_congr rfl (fun j _ => (X j).cost_eq)

theorem sum_exceptionalCost_eq_withConstantAtoms :
    (∑ j, (leaves j).exceptionalCost) =
      ∑ j, (withConstantAtoms leaves X j).exceptionalCost :=
  Finset.sum_congr rfl (fun j _ => (X j).exceptionalCost_eq)

theorem sum_ordinaryCost_eq_withConstantAtoms :
    (∑ j, (leaves j).ordinaryCost) =
      ∑ j, (withConstantAtoms leaves X j).ordinaryCost :=
  Finset.sum_congr rfl (fun j _ => (X j).ordinaryCost_eq)

end ActualHybridFamily
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.exceptionalIntegrand_eq_withConstantAtoms
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.ordinaryIntegrand_eq_withConstantAtoms
#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.CommonAtomBounds.atoms_value_eq_constant

