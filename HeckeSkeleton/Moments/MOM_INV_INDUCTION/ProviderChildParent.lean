import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderRows
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCappedProduction

/-!
# An actual canonical child is a new actual orbital parent

The new parent is constructed from the child's arithmetic fields and
the fixed positive row majorant. Its cube pool is the singleton unit,
its original slots are exactly the surviving slots, and its puncture
is the actual reconstructed puncture. The child's complete column pool
is reduced to the genuine dyadic pool using its proved [1,2] test
support. No polynomial-identification premise is used.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderChildParent

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckeSkeleton.Moments.MOMInvStep
open HeckeSkeleton.Moments.MOM_INV_STEP
open FixedTripleFibers FixedTripleEnergy CanonicalChildren CanonicalNormPools
open HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderRows
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
variable {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

def columns (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K) :
    CanonicalBlock.ColumnData K S σ where
  lambda := C.lambda
  background := C.background γ
  puncture := childPuncture C.originalPuncture γ
  slots := C.survivors γ
  primeLists := C.primeLists
  primeWeights := C.primeWeights
  labelWeight := fun _ _ => 1
  cutoff := C.cutoff γ
  base := C.base
  length := C.columnLength γ

def parentData (C : ColumnFamily K Sset σ Θ ψ) (γ : OuterTriple K)
    (hbase : 0 < C.base) (H : {r : ℝ // 0 < r}) : FirstParentEnergy.Data K S (σ := σ) where
  columns := columns K S C γ
  label := FirstInversePoisson.unitIdeal K S
  cubes := {FirstInversePoisson.unitIdeal K S}
  scale := ⟨C.base ^ C.columnLength γ, Real.rpow_pos_of_pos hbase _⟩
  archTest := rowBallArchTest K S 1
  localTest := rowBallFiniteFamily K S 1
  locallyConstant := rowBallFiniteFamily_locallyConstant K S 1
  compactSupport := rowBallFiniteFamily_compactSupport K S 1
  mask := ∅
  radius := InverseRowMajorant.rowRadius H
  frequencyBound := 1

theorem parentData_background (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (hbase : 0 < C.base) (H : {r : ℝ // 0 < r}) :
    BackgroundCycle.Admissible K Θ ψ (parentData K S C γ hbase H).columns.background :=
  C.background_admissible γ

theorem parentData_slots_subset (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (hbase : 0 < C.base) (H : {r : ℝ // 0 < r}) :
    (parentData K S C γ hbase H).columns.slots ⊆ C.originalSlots :=
  C.survivors_subset γ

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Orbit" => SIntegerOrbits K Sset Γ
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

/-- The complete child pool loses no term when restricted to its
actual annular support. -/
theorem amplitude_eq_dyadic (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (f : Ideal (𝓞 K)) (hbase : 0 < C.base)
    (hpool : C.columns γ = squarefreePool K Sset (2 * C.base ^ C.columnLength γ))
    (hW : tsupport (C.cutoff γ) ⊆ Set.Icc (1 : ℝ) 2) (q : Orbit) :
    amplitude K S Γ D (C.columns γ) (coefficient K S D C γ f) q =
      ∑ n ∈ dyadicPool K Sset (C.base ^ C.columnLength γ),
        coefficient K S D C γ f n * idealSymbol K Sset D n q.out.val := by
  have hX : 0 < C.base ^ C.columnLength γ := Real.rpow_pos_of_pos hbase _
  unfold amplitude
  rw [hpool]
  symm
  apply Finset.sum_subset
  · intro n hn
    obtain ⟨hsf, hlo, hhi⟩ := (mem_dyadicPool K Sset _ n).mp hn
    exact (mem_squarefreePool K Sset _ n).mpr ⟨hsf, by linarith⟩
  · intro n hn hnot
    have hz : C.cutoff γ ((n.val.val.absNorm : ℝ) / C.base ^ C.columnLength γ) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      have hb := hW hs
      apply hnot
      apply (mem_dyadicPool K Sset _ n).mpr
      refine ⟨((mem_squarefreePool K Sset _ n).mp hn).1, ?_, ?_⟩
      · simpa only [one_mul, height] using (le_div_iff₀ hX).mp hb.1
      · simpa only [height] using (div_le_iff₀ hX).mp hb.2
    simp only [coefficient, hz, mul_zero, zero_mul]

variable [IsPrincipalIdealRing (Set.integer Sset K)]

/-- Equality with the provider's literal original parent, proved by
expanding its singleton cube pool and the actual child coefficient. -/
theorem parent_eq_orbitalEnergy (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (hbase : 0 < C.base) (H : {r : ℝ // 0 < r})
    (hpool : C.columns γ = squarefreePool K Sset (2 * C.base ^ C.columnLength γ))
    (hW : tsupport (C.cutoff γ) ⊆ Set.Icc (1 : ℝ) 2) (f : Ext) :
    FirstCappedProduction.parent K S D Γ (parentData K S C γ hbase H) f =
      orbitalEnergy K S Γ D (C.columns γ) (coefficient K S D C γ f.val.val) H := by
  unfold FirstCappedProduction.parent CanonicalBlock.canonicalCubeEnergy
    CanonicalPoissonSource.squaredRowOrbitalSeries orbitalEnergy
  apply congrArg (sIntegerWeightedOrbitalSeries K S Γ (rowBallArchTest K S 1)
    (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S 1))
    (InverseRowMajorant.rowRadius H))
  funext q
  simp only [parentData, sIntegerOrbitAvoidanceMask, Finset.notMem_empty,
    false_implies, implies_true, if_true, one_mul]
  apply congrArg (fun z : ℂ => ((‖z‖ ^ 2 : ℝ) : ℂ))
  rw [amplitude_eq_dyadic K S Γ D C γ f.val.val hbase hpool hW q]
  simp only [Finset.sum_product, Finset.sum_singleton, FirstParentEnergy.columnPool,
    parentData, FirstInversePoisson.idealSymbol_unit, one_pow, one_mul]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [CanonicalBlock.canonicalColumn, columns, coefficient,
    FirstInversePoisson.unitIdeal_val, one_pow, mul_one, one_mul, labelRow_exterior]
  ring

variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)

include hΓ in
/-- A genuine child row sum is bounded by a constructed parent. The
comparison preserves its actual coefficient, test, puncture and marks. -/
theorem canonical_rows_le_parent (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (hbase : 0 < C.base) (H : {r : ℝ // 0 < r})
    (hpool : C.columns γ = squarefreePool K Sset (2 * C.base ^ C.columnLength γ))
    (hW : tsupport (C.cutoff γ) ⊆ Set.Icc (1 : ℝ) 2)
    (f : Ext) (T : Finset (Ideal (𝓞 K) × Sector))
    (hT : ∀ x ∈ T, (x.1.absNorm : ℝ) ≤ H.val) :
    (∑ x ∈ T,
      ‖column K Sset D C (CanonicalSectors.sectorUnit K Sset Γ) γ f.val.val x‖ ^ 2) ≤
      (InverseRowMajorant.rowCovolume K S)⁻¹ *
        ‖FirstCappedProduction.parent K S D Γ (parentData K S C γ hbase H) f‖ := by
  rw [parent_eq_orbitalEnergy K S Γ D C γ hbase H hpool hW f]
  exact canonical_rows_le_orbital_norm K S Γ D hΓ C γ f.val.val H T hT

def labelEmbedding : Ext ↪ Ideal (𝓞 K) where
  toFun f := f.val.val
  inj' := by
    intro x y h
    exact Subtype.ext (Subtype.ext h)

def exteriorLabels (L : Finset (Ideal (𝓞 K))) : Finset Ext :=
  L.preimage (labelEmbedding K S) (labelEmbedding K S).injective.injOn

theorem exteriorLabels_image (L : Finset (Ideal (𝓞 K))) :
    (exteriorLabels K S L).image (labelEmbedding K S) =
      L.filter (IsExterior K Sset) := by
  ext f
  constructor
  · intro hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_preimage.mp hg, exterior_isExterior K Sset g⟩
  · intro hf
    obtain ⟨hf, hext⟩ := Finset.mem_filter.mp hf
    refine Finset.mem_image.mpr ⟨exteriorOf K Sset f hext, ?_, rfl⟩
    exact Finset.mem_preimage.mpr hf

theorem column_zero_of_label_not_exterior (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (f : Ideal (𝓞 K)) (k : Ideal (𝓞 K) × Sector)
    (hf : ¬ IsExterior K Sset f) :
    column K Sset D C (CanonicalSectors.sectorUnit K Sset Γ) γ f k = 0 := by
  simp [column, labelRow, hf]

/-- Enlarged packet labels outside the exterior class vanish before
the divisor-weighted label sum is estimated. -/
theorem childEnergy_eq_exterior_labels (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (slotCap : ℕ) (L : Finset (Ideal (𝓞 K)))
    (T : Finset (Ideal (𝓞 K) × Sector)) :
    childEnergy slotCap L T
      (childValue K Sset D C (CanonicalSectors.sectorUnit K Sset Γ)) γ =
      ∑ f ∈ exteriorLabels K S L, labelDivisorWeight slotCap f.val.val *
        ∑ x ∈ T,
          ‖column K Sset D C (CanonicalSectors.sectorUnit K Sset Γ) γ f.val.val x‖ ^ 2 := by
  unfold childEnergy childValue
  have hf : (∑ f ∈ L.filter (IsExterior K Sset),
      labelDivisorWeight slotCap f * ∑ x ∈ T,
        ‖column K Sset D C (CanonicalSectors.sectorUnit K Sset Γ) γ f x‖ ^ 2) =
      ∑ f ∈ L, labelDivisorWeight slotCap f * ∑ x ∈ T,
        ‖column K Sset D C (CanonicalSectors.sectorUnit K Sset Γ) γ f x‖ ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro f hf hn
    have hbad : ¬ IsExterior K Sset f := by
      intro hext
      exact hn (Finset.mem_filter.mpr ⟨hf, hext⟩)
    have hz (x : Ideal (𝓞 K) × Sector) :
        column K Sset D C (CanonicalSectors.sectorUnit K Sset Γ) γ f x = 0 :=
      column_zero_of_label_not_exterior K S Γ D C γ f x hbad
    simp only [hz,
      norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero, mul_zero]
  rw [← hf, ← exteriorLabels_image K S L,
    Finset.sum_image (fun _ _ _ _ h => (labelEmbedding K S).injective h)]
  rfl

include hΓ in
/-- The complete packet child, including both exact normalizations,
is dominated by its constructed orbital parent. The original divisor
label weights remain inside the same label sum. -/
theorem normalized_childEnergy_le_parent (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (hbase : 0 < C.base) (H : {r : ℝ // 0 < r})
    (hpool : C.columns γ = squarefreePool K Sset (2 * C.base ^ C.columnLength γ))
    (hW : tsupport (C.cutoff γ) ⊆ Set.Icc (1 : ℝ) 2)
    (slotCap : ℕ) (V : ℝ) (L : Finset (Ideal (𝓞 K)))
    (T : Finset (Ideal (𝓞 K) × Sector))
    (hT : ∀ x ∈ T, (x.1.absNorm : ℝ) ≤ H.val) :
    normalizedChildEnergy C.base (C.columnLength γ) V slotCap L T
      (childValue K Sset D C (CanonicalSectors.sectorUnit K Sset Γ)) γ ≤
      (InverseRowMajorant.rowCovolume K S)⁻¹ *
        (C.base ^ (-(C.columnLength γ) - V) *
          ∑ f ∈ exteriorLabels K S L, labelDivisorWeight slotCap f.val.val *
            ‖FirstCappedProduction.parent K S D Γ (parentData K S C γ hbase H) f‖) := by
  rw [normalizedChildEnergy_eq _ _ _ hbase, childEnergy_eq_exterior_labels]
  have hsum : (∑ f ∈ exteriorLabels K S L, labelDivisorWeight slotCap f.val.val *
        ∑ x ∈ T,
          ‖column K Sset D C (CanonicalSectors.sectorUnit K Sset Γ) γ f.val.val x‖ ^ 2) ≤
      (InverseRowMajorant.rowCovolume K S)⁻¹ *
        ∑ f ∈ exteriorLabels K S L, labelDivisorWeight slotCap f.val.val *
          ‖FirstCappedProduction.parent K S D Γ (parentData K S C γ hbase H) f‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro f hf
    have hb := mul_le_mul_of_nonneg_left
      (canonical_rows_le_parent K S Γ D hΓ C γ hbase H hpool hW f T hT)
      (labelDivisorWeight_nonneg slotCap f.val.val)
    exact hb.trans_eq (by ring)
  apply (mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hbase.le _)).trans_eq
  rw [show -(C.columnLength γ + V) = -(C.columnLength γ) - V by ring]
  ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderChildParent

end
