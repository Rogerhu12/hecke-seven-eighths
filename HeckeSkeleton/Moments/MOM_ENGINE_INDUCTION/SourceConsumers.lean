import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.SourceAdapter
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RootNormalization

/-!
# Returning the paired moment estimates to the actual physical source

The source index, finite sectors and no-slot projection are those of one
fixed expansion.  The physical energy below is the literal witness sum.
The only reindexing input compares that finite sum with the complete
paired model sum; it supplies no scale or height estimate.

The two proved model bounds have their constants joined before producing
`PSource`.  An explicit equality identifies the expansion with the one in
the actual `TargetData`, including its excluded places.  The row-width
transfer uses the exact dyadic factor two and only needs the row geometry
above its own threshold on retained bins.  This module does not import
the admitted global choices in `Moments.lean`.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField IsDedekindDomain
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {S : MomentSourceData K c}

/-- The actual selected-slot fourth moment on the witness rows, before
the finite-sector reindexing. -/
def physicalPlainEnergy {Z T : ℝ} (i : SourceMomentIndexFor K c S Z T) : ℝ :=
  ∑ u ∈ (momentWitness i).rows,
    ‖(momentWitness i).plainValue u ^ 2 *
      ∏ j ∈ i.selected, (momentAmplitude i).slotValue j u‖ ^ 2

/-- Transport only the expansion's row type along the equality of the
actual excluded-place sets.  The complete expansion itself is unchanged. -/
def expansionAtPlaces (D : TargetData K c.geometry)
    (hplaces : D.S = excludedPlaces K c) :
    ℝ → ℝ → HighExpansion (FrequencyRow K (places K c)) c.geometry.slots :=
  Eq.ndrec (motive := fun P : Finset (HeightOneSpectrum (𝓞 K)) =>
    ℝ → ℝ → HighExpansion
      (FrequencyRow K (P : Set (HeightOneSpectrum (𝓞 K)))) c.geometry.slots)
    D.expansion hplaces

/-- Common constants for two fixed actual energy families.  The height
degree and ceiling still precede the moving exponent `τ`. -/
theorem uniformMomentBound_join
    (E F p q : ∀ Z T, SourceMomentIndexFor K c S Z T → ℝ)
    (P Q : ∀ Z T, SourceMomentIndexFor K c S Z T → Prop)
    (hE : UniformMomentBound E p P) (hF : UniformMomentBound F q Q) :
    ∃ A ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ ceiling → ∃ Z₀ k : ℝ, 1 ≤ Z₀ ∧ 0 ≤ k ∧
        ∀ Z : ℝ, Z₀ ≤ Z → ∀ i : SourceMomentIndexFor K c S Z (Z ^ τ),
          51 / 100 < (momentBlock i).bin →
          (P Z (Z ^ τ) i → E Z (Z ^ τ) i ≤
            k * momentBase i ^ (p Z (Z ^ τ) i + c.family.lamA) * (1 + Z ^ τ) ^ A) ∧
          (Q Z (Z ^ τ) i → F Z (Z ^ τ) i ≤
            k * momentBase i ^ (q Z (Z ^ τ) i + c.family.lamA) * (1 + Z ^ τ) ^ A) := by
  obtain ⟨A₁, H₁, hA₁, hH₁, hb₁⟩ := hE
  obtain ⟨A₂, H₂, hA₂, hH₂, hb₂⟩ := hF
  refine ⟨max A₁ A₂, min H₁ H₂, hA₁.trans (le_max_left _ _), lt_min hH₁ hH₂, ?_⟩
  intro τ hτ hτH
  obtain ⟨Z₁, k₁, hZ₁, hk₁, he⟩ := hb₁ τ hτ (hτH.trans (min_le_left _ _))
  obtain ⟨Z₂, k₂, hZ₂, hk₂, hf⟩ := hb₂ τ hτ (hτH.trans (min_le_right _ _))
  refine ⟨max Z₁ Z₂, max k₁ k₂, hZ₁.trans (le_max_left _ _),
    hk₁.trans (le_max_left _ _), ?_⟩
  intro Z hZ i hbin
  have hZ₁' : Z₁ ≤ Z := (le_max_left _ _).trans hZ
  have hZ₂' : Z₂ ≤ Z := (le_max_right _ _).trans hZ
  have hZn : 0 ≤ Z := zero_le_one.trans (hZ₁.trans hZ₁')
  have hT : 1 ≤ 1 + Z ^ τ := by linarith [Real.rpow_nonneg hZn τ]
  have hU : 0 ≤ momentBase i := Real.rpow_nonneg hZn _
  have raise (k A r x : ℝ) (hk : 0 ≤ k) (hkk : k ≤ max k₁ k₂)
      (hAA : A ≤ max A₁ A₂)
      (hx : x ≤ k * momentBase i ^ r * (1 + Z ^ τ) ^ A) :
      x ≤ max k₁ k₂ * momentBase i ^ r * (1 + Z ^ τ) ^ max A₁ A₂ := by
    apply hx.trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hkk (Real.rpow_nonneg hU _)
    · exact Real.rpow_le_rpow_of_exponent_le hT hAA
    · exact Real.rpow_nonneg (zero_le_one.trans hT) _
    · exact mul_nonneg (hk₁.trans (le_max_left _ _)) (Real.rpow_nonneg hU _)
  constructor
  · intro hi
    exact raise k₁ A₁ _ _ hk₁ (le_max_left _ _) (le_max_left _ _) (he Z hZ₁' i hbin hi)
  · intro hi
    exact raise k₂ A₂ _ _ hk₂ (le_max_right _ _) (le_max_right _ _) (hf Z hZ₂' i hbin hi)

/-- The exact physical `PSource`, from the proved positive- and zero-slot
model bounds and the finite-sector comparison for the same expansion.
The unrestricted zero-slot model is evaluated at `i.noSlots`; no equality
between models at distinct selected-slot indices is assumed. -/
theorem plainSource_of_model_bounds
    (M : SourceMomentModelsFor K c S) (D : TargetData K c.geometry)
    (hplaces : D.S = excludedPlaces K c)
    (hexpansion : expansionAtPlaces D hplaces = S.expansion)
    (hpositive : UniformMomentBound
      (fun _ _ i => pairedModelEnergy M i) (fun _ _ _ => 1)
      (fun _ _ i => pairedCapacity i ∧ i.selected.Nonempty))
    (hzero : UniformMomentBound
      (fun _ _ i => pairedModelEnergy M i.noSlots) (fun _ _ _ => 1)
      (fun _ _ _ => True))
    (hreindex : ∀ Z T (i : SourceMomentIndexFor K c S Z T),
      physicalPlainEnergy i ≤ pairedModelEnergy M i) :
    PSource c.geometry D c.family.B c.family.lamA
      (momentMesh K c.family).val := by
  rcases D with ⟨targetPlaces, targetProbe, targetMeasures, targetRay,
    targetExpansion, targetRows⟩
  change targetPlaces = excludedPlaces K c at hplaces
  subst targetPlaces
  change targetExpansion = S.expansion at hexpansion
  subst targetExpansion
  obtain ⟨A, H, hA, hH, hb⟩ := uniformMomentBound_join
    (fun _ _ i => pairedModelEnergy M i)
    (fun _ _ i => pairedModelEnergy M i.noSlots)
    (fun _ _ _ => 1) (fun _ _ _ => 1)
    (fun _ _ i => pairedCapacity i ∧ i.selected.Nonempty)
    (fun _ _ _ => True) hpositive hzero
  refine ⟨A, H, hA, hH, ?_⟩
  intro τ hτ hτH
  obtain ⟨Z₀, k, hZ₀, hk, hbound⟩ := hb τ hτ hτH
  refine ⟨Z₀, k, hZ₀, hk, ?_⟩
  intro Z hZ b hbin ℓ t ht ht' j
  constructor
  · intro I hmesh hcap
    let i : SourceMomentIndexFor K c S Z (Z ^ τ) := ⟨b, ℓ, t, ht, ht', j, I⟩
    by_cases hI : I.Nonempty
    · exact (hreindex Z (Z ^ τ) i).trans
        ((hbound Z hZ i hbin).1 ⟨⟨hmesh, hcap⟩, hI⟩)
    · have hIempty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
      subst I
      exact (hreindex Z (Z ^ τ) i).trans
        ((hbound Z hZ i hbin).2 trivial)
  · let i : SourceMomentIndexFor K c S Z (Z ^ τ) := ⟨b, ℓ, t, ht, ht', j, ∅⟩
    have hh := (hreindex Z (Z ^ τ) i).trans ((hbound Z hZ i hbin).2 trivial)
    simpa only [i, physicalPlainEnergy, SourceMomentIndexFor.noSlots,
      momentWitness, momentAmplitude, momentBlock, momentBase,
      Finset.prod_empty, mul_one] using hh

/-- A fixed enlargement of the actual row cutoff returns the raw paired
moment estimates to the physical source power.  Only the scalar and the
threshold change; the index, model, capacity and finite sectors do not. -/
theorem plainSource_of_row_bounds
    (M : SourceMomentModelsFor K c S) (D : TargetData K c.geometry)
    (hplaces : D.S = excludedPlaces K c)
    (hexpansion : expansionAtPlaces D hplaces = S.expansion)
    {rowFactor : ℝ} (hrowFactor : 0 ≤ rowFactor) (Zrow : ℝ)
    (hscale : ∀ Z T (i : SourceMomentIndexFor K c S Z T), Zrow ≤ Z →
      51 / 100 < (momentBlock i).bin →
      0 < momentBase i ∧ momentBase i ^ rowWidth i ≤ rowFactor * momentBase i)
    (hpositive : UniformMomentBound
      (fun _ _ i => pairedModelEnergy M i) (fun _ _ i => rowWidth i)
      (fun _ _ i => pairedCapacity i ∧ i.selected.Nonempty))
    (hzero : UniformMomentBound
      (fun _ _ i => pairedModelEnergy M i.noSlots) (fun _ _ i => rowWidth i)
      (fun _ _ _ => True))
    (hreindex : ∀ Z T (i : SourceMomentIndexFor K c S Z T),
      physicalPlainEnergy i ≤ pairedModelEnergy M i) :
    PSource c.geometry D c.family.B c.family.lamA
      (momentMesh K c.family).val := by
  have normalize (E : ∀ Z T, SourceMomentIndexFor K c S Z T → ℝ)
      (eligible : ∀ Z T, SourceMomentIndexFor K c S Z T → Prop)
      (h : UniformMomentBound E (fun _ _ i => rowWidth i) eligible) :
      UniformMomentBound E (fun _ _ _ => 1) eligible := by
    exact (sourceFamily K c S M).uniformBound_of_rowWidth_le_from
      E eligible hrowFactor Zrow hscale h
  exact plainSource_of_model_bounds M D hplaces hexpansion
    (normalize _ _ hpositive) (normalize _ _ hzero) hreindex

/-- The actual dyadic envelope `2 * U` costs precisely the fixed scalar
factor two.  Its logarithmic row exponent is used only at the large-base,
retained-bin indices where the source geometry supplies `U > 1`. -/
theorem plainSource_of_dyadic_model_bounds
    (M : SourceMomentModelsFor K c S) (D : TargetData K c.geometry)
    (hplaces : D.S = excludedPlaces K c)
    (hexpansion : expansionAtPlaces D hplaces = S.expansion)
    (Zrow : ℝ)
    (hbase : ∀ Z T (i : SourceMomentIndexFor K c S Z T), Zrow ≤ Z →
      51 / 100 < (momentBlock i).bin → 1 < momentBase i)
    (hwidth : ∀ U : ℝ, 1 < U → S.rowExponent U = 1 + Real.log 2 / Real.log U)
    (hpositive : UniformMomentBound
      (fun _ _ i => pairedModelEnergy M i) (fun _ _ i => rowWidth i)
      (fun _ _ i => pairedCapacity i ∧ i.selected.Nonempty))
    (hzero : UniformMomentBound
      (fun _ _ i => pairedModelEnergy M i.noSlots) (fun _ _ i => rowWidth i)
      (fun _ _ _ => True))
    (hreindex : ∀ Z T (i : SourceMomentIndexFor K c S Z T),
      physicalPlainEnergy i ≤ pairedModelEnergy M i) :
    PSource c.geometry D c.family.B c.family.lamA
      (momentMesh K c.family).val := by
  apply plainSource_of_row_bounds M D hplaces hexpansion
    (rowFactor := 2) (by norm_num) Zrow ?_ hpositive hzero hreindex
  intro Z T i hZ hbin
  have hU := hbase Z T i hZ hbin
  refine ⟨zero_lt_one.trans hU, ?_⟩
  rw [rowWidth, hwidth _ hU]
  exact (rpow_log_row_width hU (by norm_num : (0 : ℝ) < 2)).le

end HeckeSkeleton.Moments.EngineInduction.Source
