import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentConstantSource

/-!
# The actual original column phase from its individual atoms

The two original plain ideals and every original prime occurrence are
kept in one Cartesian tuple.  Their complete residue values multiply to
the character of its complete ideal, including all nonunit zeros.  No
coprimality between the occurrences and no whole-column phase identity
is an input.

The source constructor at the end uses the same row map, constant
coefficients and positive orbital chart as `ParentConstantSource`.  Its
only phase dictionaries concern a single original ideal or prime.  The
finite product proof also covers zero slots.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {Γ : Subgroup A.U}
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)

local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- The genuine original character is the complete residue value at
the supplied nonzero representative, with no unit restriction. -/
theorem generatedOriginalColumn_originalOrbit_mk
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (x : NonzeroRingElements A.R) :
    (generatedOriginalColumn (σ := σ) hΓ I a ha).originalOrbit
        (Quotient.mk _ x) =
      actualIdealResidue (A := A) (σ := σ) I.val x.val := by
  change (generatedOriginalColumn (σ := σ) hΓ I a ha).character
    (Ideal.Quotient.mk _ x.val) = _
  rw [generatedOriginalColumn_character_mk, actualIdealResidue_exterior]

/-- The original orbit representative is used literally; no new
generator or representative is selected for the column. -/
theorem generatedOriginalColumn_originalOrbit_out
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a) (q : Q) :
    (generatedOriginalColumn (σ := σ) hΓ I a ha).originalOrbit q =
      actualIdealResidue (A := A) (σ := σ) I.val q.out.val := by
  have h := generatedOriginalColumn_originalOrbit_mk (σ := σ) hΓ I a ha q.out
  simpa only [Quotient.out_eq] using h

/-- Multiplication of complete original columns has no coprimality
condition.  The displayed whole generator may be any generator of the
same product ideal; `generatedIdealCharacter_mul` retains every zero. -/
theorem generatedOriginalColumn_originalOrbit_mul
    (I J IJ : A.Exterior) (hIJ : IJ.val = I.val * J.val)
    (a b c : A.R) (ha : A.Generates I a) (hb : A.Generates J b)
    (hc : A.Generates IJ c) (q : Q) :
    (generatedOriginalColumn (σ := σ) hΓ IJ c hc).originalOrbit q =
      (generatedOriginalColumn (σ := σ) hΓ I a ha).originalOrbit q *
        (generatedOriginalColumn (σ := σ) hΓ J b hb).originalOrbit q := by
  refine Quotient.inductionOn q ?_
  intro x
  change (generatedOriginalColumn (σ := σ) hΓ IJ c hc).character
    (Ideal.Quotient.mk _ x.val) =
      (generatedOriginalColumn (σ := σ) hΓ I a ha).character
        (Ideal.Quotient.mk _ x.val) *
      (generatedOriginalColumn (σ := σ) hΓ J b hb).character
        (Ideal.Quotient.mk _ x.val)
  simp only [generatedOriginalColumn_character_mk]
  have h := generatedIdealCharacter_mul (σ := σ) I J IJ hIJ a b ha hb
    (generated_product I J IJ hIJ a b ha hb) x.val
  simpa only [generatedIdealCharacter_mk] using h

/-- The original ideal-product identity alone turns a finite list of
individual residue factors into the actual generated whole column. -/
theorem generatedOriginalColumn_originalOrbit_ideal_prod
    {ι : Type*} (s : Finset ι) (I : ι → Ideal (𝓞 K))
    (J : A.Exterior) (a : A.R) (ha : A.Generates J a)
    (hJ : J.val = ∏ i ∈ s, I i) (q : Q) :
    (generatedOriginalColumn (σ := σ) hΓ J a ha).originalOrbit q =
      ∏ i ∈ s, actualIdealResidue (A := A) (σ := σ) (I i) q.out.val := by
  rw [generatedOriginalColumn_originalOrbit_out (σ := σ) hΓ J a ha,
    hJ, actualIdealResidue_prod]

namespace ParentRawAtoms

section Ideal

variable {Q₀ : Type*} {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}

/-- The literal two plain ideals times every original prime occurrence.
Repeated occurrences retain their multiplicity. -/
def columnIdeal (raw : ParentRawAtoms Q₀ d a Z t Y₁ Y₂)
    (v : raw.Column) : Ideal (𝓞 K) :=
  v.1.1.val * v.1.2.val * ∏ i, (v.2 i).asIdeal

end Ideal

variable {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable (raw : ParentRawAtoms (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t Y₁ Y₂)

/-- Only complete columns in the original exterior support are kept.
All other columns will be proved to have zero complete phase. -/
def exteriorColumns : Finset raw.Column :=
  raw.columns.filter
    (fun v => raw.columnIdeal v ≠ 0 ∧ IsCoprime (raw.columnIdeal v) A.cS)

/-- The actual whole ideal on the retained carrier.  The unit value
outside that carrier merely makes the original column map total. -/
def columnExterior (v : raw.Column) : A.Exterior :=
  if h : raw.columnIdeal v ≠ 0 ∧ IsCoprime (raw.columnIdeal v) A.cS then
    ⟨raw.columnIdeal v, h.1, Ideal.isCoprime_iff_sup_eq.mp h.2⟩
  else unitExterior A

theorem columnExterior_val_of_mem (v : raw.Column) (hv : v ∈ raw.exteriorColumns) :
    (raw.columnExterior v).val = raw.columnIdeal v := by
  have h := (Finset.mem_filter.mp hv).2
  simp only [columnExterior, dif_pos h]

variable (left : ∀ I ∈ raw.leftColumns, ∀ q : (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ),
  raw.leftPhase q I = actualIdealResidue (A := A) (σ := σ) I.val q.out.val)
variable (right : ∀ I ∈ raw.rightColumns, ∀ q : (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ),
  raw.rightPhase q I = actualIdealResidue (A := A) (σ := σ) I.val q.out.val)
variable (prime : ∀ i, ∀ p ∈ raw.slotColumns i, ∀ q : (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ),
  raw.primePhase q i p = actualIdealResidue (A := A) (σ := σ) p.asIdeal q.out.val)

include left right prime

/-- One actual tuple is identified from its individual atom identities.
No equality for the tuple or for its finite polynomial is assumed. -/
theorem phase_eq_actualIdealResidue (v : raw.Column) (hv : v ∈ raw.columns) (q : Q) :
    raw.phase q v = actualIdealResidue (A := A) (σ := σ) (raw.columnIdeal v) q.out.val := by
  have hm : v.1 ∈ raw.leftColumns.product raw.rightColumns ∧
      v.2 ∈ Fintype.piFinset raw.slotColumns :=
    Finset.mem_product.mp hv
  have hp := Finset.mem_product.mp hm.1
  have hprime : (∏ i, raw.primePhase q i (v.2 i)) =
      ∏ i, actualIdealResidue (A := A) (σ := σ) (v.2 i).asIdeal q.out.val := by
    apply Finset.prod_congr rfl
    intro i _
    exact prime i (v.2 i) (Fintype.mem_piFinset.mp hm.2 i) q
  calc
    raw.phase q v =
        actualIdealResidue (A := A) (σ := σ) v.1.1.val q.out.val *
          actualIdealResidue (A := A) (σ := σ) v.1.2.val q.out.val *
            ∏ i, actualIdealResidue (A := A) (σ := σ) (v.2 i).asIdeal q.out.val := by
      dsimp only [phase]
      rw [left v.1.1 hp.1 q, right v.1.2 hp.2 q, hprime]
    _ = _ := by
      simp only [columnIdeal, actualIdealResidue_ideal_mul, actualIdealResidue_prod]

/-- Tuples outside the original exterior support have zero phase.
This fact is proved before discarding any source column. -/
theorem phase_eq_zero_of_not_exterior
    (v : raw.Column) (hv : v ∈ raw.columns)
    (hnot : ¬(raw.columnIdeal v ≠ 0 ∧ IsCoprime (raw.columnIdeal v) A.cS)) (q : Q) :
    raw.phase q v = 0 := by
  rw [raw.phase_eq_actualIdealResidue left right prime v hv q,
    actualIdealResidue, dif_neg hnot]

/-- The finite source may discard precisely the nonexterior tuples,
whose complete phase is already zero.  The whole centered coefficient
remains unchanged. -/
theorem coefficient_phase_sum_filter_exterior (centered : Bool) (q : Q) :
    (∑ v ∈ raw.columns, raw.coefficient centered q v * raw.phase q v) =
      ∑ v ∈ raw.exteriorColumns,
        raw.coefficient centered q v * raw.phase q v := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro v hv hn
  have hnot : ¬(raw.columnIdeal v ≠ 0 ∧ IsCoprime (raw.columnIdeal v) A.cS) := by
    intro hext
    exact hn (Finset.mem_filter.mpr ⟨hv, hext⟩)
  rw [raw.phase_eq_zero_of_not_exterior left right prime v hv hnot q, mul_zero]

/-- The original per-tuple ideal product, together with the per-atom
phase dictionaries, supplies the exact generated-column identity. -/
theorem phase_eq_generatedOriginalColumn
    (ideal : raw.Column → A.Exterior) (generator : raw.Column → A.R)
    (generates : ∀ v, A.Generates (ideal v) (generator v))
    (product : ∀ v ∈ raw.columns, (ideal v).val = raw.columnIdeal v)
    (v : raw.Column) (hv : v ∈ raw.columns) (q : Q) :
    raw.phase q v =
      (generatedOriginalColumn (σ := σ) hΓ (ideal v) (generator v) (generates v)).originalOrbit q := by
  rw [raw.phase_eq_actualIdealResidue left right prime v hv q,
    generatedOriginalColumn_originalOrbit_out (σ := σ) hΓ,
    product v hv]

/-- On the computed exterior carrier the original ideal-product
identity is definitional, so no support or product premise is needed. -/
theorem phase_eq_columnExteriorOrbit
    (generator : raw.Column → A.R)
    (generates : ∀ v, A.Generates (raw.columnExterior v) (generator v))
    (v : raw.Column) (hv : v ∈ raw.exteriorColumns) (q : Q) :
    raw.phase q v =
      (generatedOriginalColumn (σ := σ) hΓ (raw.columnExterior v)
        (generator v) (generates v)).originalOrbit q := by
  rw [raw.phase_eq_actualIdealResidue left right prime v (Finset.mem_filter.mp hv).1 q,
    generatedOriginalColumn_originalOrbit_out (σ := σ) hΓ,
    raw.columnExterior_val_of_mem v hv]

section Calibration

variable [Γ.FiniteIndex]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable {φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ((v : (A.Sf : Set (HeightOneSpectrum (𝓞 K)))) → v.val.adicCompletion K) → ℂ}
variable {radius : {r : ℝ // 0 < r}} {mask : Finset (HeightOneSpectrum A.R)}
variable {fiberBound : ℕ}

/-- Construct the same actual parent source from only single-atom
phase identities and the original ideal product.  The original positive
chart constructs the Gram profiles, and the Cartesian expansion proves
the whole parent polynomial internally. -/
def ConstantValues.actualCalibrationOfAtomPhases (values : raw.ConstantValues)
    (chart : GaussEnergyChart (pairedRows d a Z) raw.rowMap (fun _ => 1)
      φ finiteTest radius mask fiberBound)
    (hTest : Continuous finiteTest) (hTestcs : HasCompactSupport finiteTest)
    (centered : Bool) (ideal : raw.Column → A.Exterior) (generator : raw.Column → A.R)
    (generates : ∀ v, A.Generates (ideal v) (generator v))
    (product : ∀ v ∈ raw.columns, (ideal v).val = raw.columnIdeal v) :
    ParentSourceCalibration centered d a Z t Y₁ Y₂ raw.columns
      (fun i j =>
        (generatedOriginalColumn (σ := σ) hΓ (ideal i) (generator i) (generates i)).originalPair
          (generatedOriginalColumn (σ := σ) hΓ (ideal j) (generator j) (generates j))
          ((values.coefficient centered i * star (values.coefficient centered j)) • φ))
      finiteTest radius mask fiberBound :=
  values.actualCalibration chart hTest hTestcs centered
    (fun i => generatedOriginalColumn (σ := σ) hΓ (ideal i) (generator i) (generates i))
    (raw.phase_eq_generatedOriginalColumn (σ := σ) hΓ left right prime ideal generator generates product)

/-- The full original parent source on its computed exterior columns.
Its polynomial identity follows from the original atom expansion and
the proved zero-phase filter; it is not supplied as an input.  The
coefficient, row map, centered profiles and orbital majorant are the
same original ones. -/
def ConstantValues.actualExteriorCalibrationOfAtomPhases (values : raw.ConstantValues)
    (chart : GaussEnergyChart (pairedRows d a Z) raw.rowMap (fun _ => 1)
      φ finiteTest radius mask fiberBound)
    (hTest : Continuous finiteTest) (hTestcs : HasCompactSupport finiteTest)
    (centered : Bool) (generator : raw.Column → A.R)
    (generates : ∀ v, A.Generates (raw.columnExterior v) (generator v)) :
    ParentSourceCalibration centered d a Z t Y₁ Y₂ raw.exteriorColumns
      (fun i j =>
        (generatedOriginalColumn (σ := σ) hΓ (raw.columnExterior i)
          (generator i) (generates i)).originalPair
          (generatedOriginalColumn (σ := σ) hΓ (raw.columnExterior j)
            (generator j) (generates j))
          ((values.coefficient centered i * star (values.coefficient centered j)) • φ))
      finiteTest radius mask fiberBound where
  rowMap := raw.rowMap
  coefficient := raw.coefficient centered
  phase := raw.phase
  weight q := (gaussSourceProfile φ finiteTest radius q).re
  weight_nonneg := chart.profile_nonneg
  row_weight := chart.row_weight
  row_mask := chart.row_mask
  fiber := chart.fiber
  polynomial u hu :=
    (raw.polynomial centered u hu).trans
      (raw.coefficient_phase_sum_filter_exterior left right prime centered (raw.rowMap u))
  periodic i hi j hj q := by
    rw [OrbitalGaussColumn.originalPair_orbitWeight,
      ← raw.phase_eq_columnExteriorOrbit (σ := σ) hΓ left right prime generator generates i hi q,
      ← raw.phase_eq_columnExteriorOrbit (σ := σ) hΓ left right prime generator generates j hj q]
  gram i hi j hj q := by
    have h := (values.rectangleProfiles chart).wholeProfile_gram hTest hTestcs centered
      i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 q
    rw [values.wholeProfile_eq chart centered i j] at h
    exact h

end Calibration
end ParentRawAtoms

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.generatedOriginalColumn_originalOrbit_mul
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.phase_eq_actualIdealResidue
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.coefficient_phase_sum_filter_exterior
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.ConstantValues.actualCalibrationOfAtomPhases
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.ConstantValues.actualExteriorCalibrationOfAtomPhases
