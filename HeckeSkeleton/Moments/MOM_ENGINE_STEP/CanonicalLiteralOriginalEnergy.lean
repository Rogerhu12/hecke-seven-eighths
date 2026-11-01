import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveEnergy

/-!
# The original complete columns on their actual frequency rows

The whole centered coefficient is evaluated at the original frequency
before any norm or passive allocation is introduced. The primitive
single-occurrence residue identity gives its literal frequency form,
including the complete extra Gauss normalizer exactly once.

The original correlation-zero rows are removed by their exact energy
identity. On the right, conjugation of the entire Fourier column keeps
the negative frequency and negates both continuous locations. Neither
the column carrier nor the Fourier variable is changed.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralOriginalEnergy

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments
open CanonicalLiteralPassiveEnergy

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {k : ℕ}
variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)

/-- The actual ideal product determines every residue factor. No
completed coefficient identity is supplied. -/
theorem term_residue (rectangle : Bool) (i : AllocationColumn K k)
    (I : A.Exterior) (hI : I.val = allocationColumnIdeal i)
    (frequency g h : A.R) (hfrequency : frequency = g * h) :
    d.term rectangle i * σ (A.sexticResidue I frequency) =
      d.frequencyTerm (σ := σ) g h rectangle i := by
  unfold CanonicalLiteralRectangles.Atoms.term
    CanonicalLiteralRectangles.Atoms.frequencyTerm
  rw [raw_source_coefficient_eq_bare_mul_residue d.characters g h
    (d.scale₁ rectangle) (d.scale₂ rectangle) d.base d.length
    (d.rectangleLeftWeight rectangle) (d.rightWeight rectangle) d.slotWeight i I hI,
    hfrequency]
  ring

/-- The subtraction remains inside the complete original column. -/
theorem whole_residue (i : AllocationColumn K k)
    (I : A.Exterior) (hI : I.val = allocationColumnIdeal i)
    (frequency g h : A.R) (hfrequency : frequency = g * h) :
    d.whole i * σ (A.sexticResidue I frequency) =
      d.frequencyWhole (σ := σ) g h i := by
  unfold CanonicalLiteralRectangles.Atoms.whole
    CanonicalLiteralRectangles.Atoms.frequencyWhole
  rw [sub_mul, term_residue d false i I hI frequency g h hfrequency,
    term_residue d true i I hI frequency g h hfrequency]

private theorem energy_congr {H J V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (rows : Finset H) (columns : Finset J) (weight : H → ℂ)
    (c f : H → J → ℂ) (point : H → J → V) (ξ : V)
    (hcoefficient : ∀ h ∈ rows, ∀ i ∈ columns, c h i = f h i) :
    jointColumnEnergy rows columns weight c point ξ =
      jointColumnEnergy rows columns weight f point ξ := by
  unfold jointColumnEnergy
  apply Finset.sum_congr rfl
  intro h hh
  have he : jointFourierColumn columns (c h) (point h) ξ =
      jointFourierColumn columns (f h) (point h) ξ := by
    unfold jointFourierColumn
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcoefficient h hh i hi]
  rw [he]

variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (R : ActualSecondCorrelationRows A σ H ι)
variable (C : A.GeneralArithmeticContext σ η hS)
variable (B : ActualColumnAllocation K k)
variable (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
variable (ideal : AllocationColumn K k → A.Exterior)
variable (hideal : ∀ i ∈ B.columns, (ideal i).val = allocationColumnIdeal i)

/-- The original left allocated energy is the literal frequency
energy on the same actual allocation and live rows. Only the actual
ideal product is needed; no support or whole-energy identity is input. -/
theorem left_energy (firstSign : ℝ) (ξ : WithLp 2 (ℝ × ℝ)) :
    jointColumnEnergy R.rows B.columns (fun h => R.weight h * R.correlation h)
      (secondAllocatedLeftCoefficient (σ := σ) PUnit.{1} ideal R.frequency
        (fun _ => PUnit.unit) χ d.whole)
      (fun _ => rawSourceLocation (CanonicalLiteralLocations.plain firstSign)
        (CanonicalLiteralLocations.plain firstSign)
        (CanonicalLiteralLocations.prime firstSign)) ξ =
      jointColumnEnergy Finset.univ B.columns
        (fun h : R.live => R.weight h.val * R.correlation h.val)
        (fun h : R.live =>
          d.frequencyWhole (σ := σ) (R.factor C h.val) (R.extractedRow C h).element)
        (fun _ => canonicalPoint firstSign false) ξ := by
  rw [R.energy_live]
  apply energy_congr
  intro h _ i hi
  simpa only [secondAllocatedLeftCoefficient, CanonicalLiteralTerms.phase_unit, mul_one] using
    whole_residue d i (ideal i) (hideal i hi) (R.frequency h.val)
      (R.factor C h.val) (R.extractedRow C h).element (R.extractedRow C h).frequency

/-- The right residue is evaluated at the negative actual frequency.
Its full star is removed only after taking the complete column norm,
which negates the original logarithmic locations. -/
theorem right_energy (firstSign : ℝ) (ξ : WithLp 2 (ℝ × ℝ)) :
    jointColumnEnergy R.rows B.columns (fun h => R.weight h * R.correlation h)
      (secondAllocatedRightCoefficient (σ := σ) PUnit.{1} ideal R.frequency
        (fun _ => PUnit.unit) χ d.whole)
      (fun _ => rawSourceLocation (CanonicalLiteralLocations.plain firstSign)
        (CanonicalLiteralLocations.plain firstSign)
        (CanonicalLiteralLocations.prime firstSign)) ξ =
      jointColumnEnergy Finset.univ B.columns
        (fun h : R.live => R.weight h.val * R.correlation h.val)
        (fun h : R.live =>
          d.frequencyWhole (σ := σ) (-R.factor C h.val) (R.extractedRow C h).element)
        (fun _ => canonicalPoint firstSign true) ξ := by
  rw [R.energy_live]
  let c := fun h : R.live =>
    d.frequencyWhole (σ := σ) (-R.factor C h.val) (R.extractedRow C h).element
  have hc (h : R.live) (i : AllocationColumn K k) (hi : i ∈ B.columns) :
      secondAllocatedRightCoefficient (σ := σ) PUnit.{1} ideal R.frequency
        (fun _ => PUnit.unit) χ d.whole h.val i = star (c h i) := by
    unfold secondAllocatedRightCoefficient
    apply congrArg star
    simpa only [CanonicalLiteralTerms.phase_unit, mul_one, c] using
      whole_residue d i (ideal i) (hideal i hi) (-R.frequency h.val)
        (-R.factor C h.val) (R.extractedRow C h).element
        ((congrArg Neg.neg (R.extractedRow C h).frequency).trans (neg_mul _ _).symm)
  calc
    _ = jointColumnEnergy Finset.univ B.columns
        (fun h : R.live => R.weight h.val * R.correlation h.val)
        (fun h i => star (c h i))
        (fun _ => rawSourceLocation (CanonicalLiteralLocations.plain firstSign)
          (CanonicalLiteralLocations.plain firstSign)
          (CanonicalLiteralLocations.prime firstSign)) ξ :=
      energy_congr _ _ _ _ _ _ _ (fun h _ i hi => hc h i hi)
    _ = _ := by
      rw [joint_energy_star_neg_locations]
      apply congrArg (fun locations : R.live → AllocationColumn K k → WithLp 2 (ℝ × ℝ) =>
        jointColumnEnergy Finset.univ B.columns
          (fun h : R.live => R.weight h.val * R.correlation h.val) c locations ξ)
      funext h i
      exact (rawSourceLocation_neg (CanonicalLiteralLocations.plain firstSign)
        (CanonicalLiteralLocations.plain firstSign)
        (CanonicalLiteralLocations.prime firstSign) i).symm

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralOriginalEnergy

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralOriginalEnergy.term_residue
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralOriginalEnergy.whole_residue
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralOriginalEnergy.left_energy
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralOriginalEnergy.right_energy
