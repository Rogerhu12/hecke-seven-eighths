import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualLeafNormWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalAmplifiedCarrier
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCoveredFibreMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstBlockMaskCardinality

set_option linter.unusedSectionVars false

/-!
# Fibres of the actual parent arithmetic map

The independent arithmetic coordinates are retained by the map.  The
finite count below charges only the original masks, source classes and
two side choices.  In particular a fixed prime/valuation tag costs no
prime-pool cardinality.  The real counting lemmas are shared with the
direct entrance, whose tag coordinate is absent.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

namespace OriginalFiniteFibre

variable {α β : Type*} [Fintype α] [Fintype β]

def realCount (P : α → Prop) : ℝ := ((Finset.univ.filter P).card : ℝ)

theorem realCount_nonneg (P : α → Prop) : 0 ≤ realCount P := by
  sorry

theorem realCount_eq_sum (P : α → Prop) :
    realCount P = ∑ a : α, if P a then (1 : ℝ) else 0 := by
  sorry

theorem realCount_eq_zero (P : α → Prop) (hP : ∀ a, ¬ P a) : realCount P = 0 := by
  sorry

theorem realCount_mono {P Q : α → Prop} (h : ∀ a, P a → Q a) :
    realCount P ≤ realCount Q := by
  sorry

theorem realCount_injective {P : α → Prop} {Q : β → Prop}
    (f : α → β) (hf : Function.Injective f) (h : ∀ a, P a → Q (f a)) :
    realCount P ≤ realCount Q := by
  sorry

theorem realCount_equiv (e : α ≃ β) (P : α → Prop) :
    realCount P = realCount (fun b => P (e.symm b)) := by
  sorry

theorem realCount_sum (P : α ⊕ β → Prop) :
    realCount P = realCount (fun a => P (.inl a)) +
      realCount (fun b => P (.inr b)) := by
  sorry

theorem realCount_sigma {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (P : (Σ i, X i) → Prop) :
    realCount P = ∑ i : ι, realCount (fun x => P ⟨i, x⟩) := by
  sorry

theorem realCount_sigma_le {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (P : (Σ i, X i) → Prop)
    (C : ℝ) (hC : ∀ i, realCount (fun x => P ⟨i, x⟩) ≤ C) :
    realCount P ≤ (Fintype.card ι : ℝ) * C := by
  sorry

/-- An arithmetic coordinate fixed by an injective original projection
has one possible value, even if its declared ambient carrier is large. -/
theorem realCount_sigma_fixed_le {ι J : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (P : (Σ i, X i) → Prop)
    (f : ι → J) (hf : Function.Injective f) (j : J)
    (hfix : ∀ x, P x → f x.1 = j)
    (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ i, realCount (fun x => P ⟨i, x⟩) ≤ C) :
    realCount P ≤ C := by
  sorry

theorem realCount_sigma_subsingleton_le {ι : Type*} [Fintype ι] [Subsingleton ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (P : (Σ i, X i) → Prop)
    (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ i, realCount (fun x => P ⟨i, x⟩) ≤ C) :
    realCount P ≤ C := by
  sorry

theorem realCount_prod_left (P : α → Prop) :
    realCount (fun x : α × β => P x.1) = (Fintype.card β : ℝ) * realCount P := by
  sorry

abbrev FourTag (ι : Type*) := Unit ⊕ (ι ⊕ (ι ⊕ ι))

def fourTagCode {ι J : Type*} (f : ι → J) : FourTag ι → Option (ℕ × J)
  | .inl _ => none
  | .inr (.inl p) => some (1, f p)
  | .inr (.inr (.inl p)) => some (6, f p)
  | .inr (.inr (.inr p)) => some (7, f p)

theorem fourTagCode_injective {ι J : Type*} (f : ι → J) (hf : Function.Injective f) :
    Function.Injective (fourTagCode f) := by
  sorry

section Tagged

universe u v
variable {ι : Type u} [Fintype ι]
variable (X₀ : Type v) (X₁ X₆ X₇ : ι → Type v)
variable [Fintype X₀] [∀ i, Fintype (X₁ i)]
  [∀ i, Fintype (X₆ i)] [∀ i, Fintype (X₇ i)]

abbrev FourSource := X₀ ⊕ ((Σ i, X₁ i) ⊕ ((Σ i, X₆ i) ⊕ (Σ i, X₇ i)))

def FourSourceAt : FourTag ι → Type _
  | .inl _ => X₀
  | .inr (.inl i) => X₁ i
  | .inr (.inr (.inl i)) => X₆ i
  | .inr (.inr (.inr i)) => X₇ i

instance fourSourceAtFintype (i : FourTag ι) :
    Fintype (FourSourceAt X₀ X₁ X₆ X₇ i) := by
  rcases i with i | (i | (i | i)) <;>
    dsimp only [FourSourceAt] <;> infer_instance

def fourSourceEquiv : FourSource X₀ X₁ X₆ X₇ ≃
    (Σ i : FourTag ι, FourSourceAt X₀ X₁ X₆ X₇ i) where
  toFun
    | .inl x => ⟨.inl (), x⟩
    | .inr (.inl ⟨i, x⟩) => ⟨.inr (.inl i), x⟩
    | .inr (.inr (.inl ⟨i, x⟩)) => ⟨.inr (.inr (.inl i)), x⟩
    | .inr (.inr (.inr ⟨i, x⟩)) => ⟨.inr (.inr (.inr i)), x⟩
  invFun
    | ⟨.inl _, x⟩ => .inl x
    | ⟨.inr (.inl i), x⟩ => .inr (.inl ⟨i, x⟩)
    | ⟨.inr (.inr (.inl i)), x⟩ => .inr (.inr (.inl ⟨i, x⟩))
    | ⟨.inr (.inr (.inr i)), x⟩ => .inr (.inr (.inr ⟨i, x⟩))
  left_inv x := by
    rcases x with x | (⟨i, x⟩ | (⟨i, x⟩ | ⟨i, x⟩)) <;> rfl
  right_inv x := by
    rcases x with ⟨i | (i | (i | i)), x⟩
    · cases i
      rfl
    all_goals rfl

/-- Exactly one of main/1/6/7 and exactly one prime survives a fixed
original tag. This is why the pool cardinality never enters the fibre. -/
theorem realCount_fourSource_fixed_le {J : Type*}
    (P : FourSource X₀ X₁ X₆ X₇ → Prop)
    (f : ι → J) (hf : Function.Injective f) (j : Option (ℕ × J))
    (hfix : ∀ x, P x →
      fourTagCode f ((fourSourceEquiv X₀ X₁ X₆ X₇) x).1 = j)
    (C : ℝ) (hC : 0 ≤ C)
    (h₀ : realCount (fun x => P (.inl x)) ≤ C)
    (h₁ : ∀ i, realCount (fun x => P (.inr (.inl ⟨i, x⟩))) ≤ C)
    (h₆ : ∀ i, realCount (fun x => P (.inr (.inr (.inl ⟨i, x⟩)))) ≤ C)
    (h₇ : ∀ i, realCount (fun x => P (.inr (.inr (.inr ⟨i, x⟩)))) ≤ C) :
    realCount P ≤ C := by
  sorry

end Tagged
end OriginalFiniteFibre

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckePort.IdealMobiusDivisorSum
open DedekindZetaZeroFree.LocalFiniteSums (ExteriorPrime)
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup HeckePort.Moments.Support
open CommonSupportMass UniqueFactorizationMonoid OriginalFiniteFibre

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local instance actualParentFibreCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Θ : Type*} [Fintype Θ] {cap dimension width : ℕ} {B Z : ℝ}

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
variable (LC RC : SourceCartesianCover G.columns G.ideal)

def rowPresent (j : s.CoveredLeafKey LC RC) : Prop :=
  j.1.rowLabel ∈ s.actualRowLabels j.1.1 j.1.2.1

theorem rowPresent_of_fiberLeaf_live
    (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (j : s.CoveredLeafKey LC RC)
    (hj : (s.fiberCoveredLeaf LC RC exceptional F x j).Live) :
    s.rowPresent LC RC j := by
  sorry

/-- Primitive original row coordinates.  The forward classifier
identity forbids arbitrary refinement of the declared row-label set.
The mask remains fixed for the stage, while each common block uses
its own original prime support and original support-ideal window. -/
structure OriginalFibreRows (Θ : Type*) (dimension width : ℕ) (B Z : ℝ) where
  support : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val) →
    Finset (HeightOneSpectrum (𝓞 K))
  maskIdeal : Ideal (𝓞 K)
  rowIdeal : commonSupportPool G.columns G.columns
    (fun i => (G.ideal i).val) (fun j => (G.ideal j).val) → Ideal (𝓞 K)
  mask_nonzero : maskIdeal ≠ 0
  row_nonzero : ∀ DE, rowIdeal DE ≠ 0
  maskPrimes : OriginalMaskPrimeData s.mask maskIdeal
  row_divides : ∀ DE, ∀ p ∈ support DE, p.asIdeal ∣ rowIdeal DE
  mask_norm : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ B
  row_norm : ∀ DE, (Ideal.absNorm (rowIdeal DE) : ℝ) ≤ Z ^ B
  code : ∀ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
    s.mask.powerset → Q → RowCode (support DE) Θ dimension width
  encode : ∀ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
    ∀ D : s.mask.powerset, RowCode (support DE) Θ dimension width →
      Fin ((s.charts DE D).rowLabelCount + 1)
  row_label : ∀ DE D, ∀ h ∈ (s.sources DE).rows,
    (s.charts DE D).rowLabel h = encode DE D (code DE D h)

/-- A genuinely uniform original support remains a special case of
the block-dependent certificate.  Existing uniform constructors keep
their original scalar windows and classifier identities. -/
def OriginalFibreRows.ofUniform
    (support : Finset (HeightOneSpectrum (𝓞 K))) (maskIdeal rowIdeal : Ideal (𝓞 K))
    (mask_nonzero : maskIdeal ≠ 0) (row_nonzero : rowIdeal ≠ 0)
    (maskPrimes : OriginalMaskPrimeData s.mask maskIdeal)
    (row_divides : ∀ p ∈ support, p.asIdeal ∣ rowIdeal)
    (mask_norm : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ B)
    (row_norm : (Ideal.absNorm rowIdeal : ℝ) ≤ Z ^ B)
    (code : ∀ DE : commonSupportPool G.columns G.columns
        (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
      s.mask.powerset → Q → RowCode support Θ dimension width)
    (encode : ∀ DE : commonSupportPool G.columns G.columns
        (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
      ∀ D : s.mask.powerset, RowCode support Θ dimension width →
        Fin ((s.charts DE D).rowLabelCount + 1))
    (row_label : ∀ DE D, ∀ h ∈ (s.sources DE).rows,
      (s.charts DE D).rowLabel h = encode DE D (code DE D h)) :
    s.OriginalFibreRows Θ dimension width B Z where
  support _ := support
  maskIdeal := maskIdeal
  rowIdeal _ := rowIdeal
  mask_nonzero := mask_nonzero
  row_nonzero _ := row_nonzero
  maskPrimes := maskPrimes
  row_divides _ := row_divides
  mask_norm := mask_norm
  row_norm _ := row_norm
  code := code
  encode := encode
  row_label := row_label

def OriginalFibreRows.rowPrimes (rows : s.OriginalFibreRows Θ dimension width B Z)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val)) :
    OriginalMaskPrimeData (rows.support DE) (rows.rowIdeal DE) where
  prime := id
  injective := fun _ _ _ _ h => h
  divides := rows.row_divides DE

end ActualGaussStage

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps} {ι : Type*}
variable {originalColumns : Finset ι} {originalIdeal : ι → A.Exterior}

namespace FirstGaussPoolData

variable (d : FirstGaussPoolData C P ι)
variable (T : SourceCartesianAtlas originalColumns originalIdeal)
variable (support : Finset (Ideal (𝓞 K))) (D₀ : Ideal (𝓞 K))
variable (hcolumns : d.columns = originalColumns.filter
  (fun i => supportExtract (originalIdeal i).val support = D₀))
variable (hideal : ∀ i, (d.ideal i).val = supportResidual (originalIdeal i).val support)
variable (c : ι → ℂ)

section Main

variable (s : ActualGaussStage (E := E) hΓ μv hDiff (d.mainSource c) finiteTest)
local notation "CV" => d.mainSourceCartesianCover T support D₀ hcolumns hideal c

/-- A predicate on the actual source carrier is counted from its
original rows and the arithmetic coordinates that it retains. -/
theorem main_original_predicate_subpower
    (hcap : T.slotCount ≤ cap) (ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (hZ : 1 ≤ Z)
    (rows : s.OriginalFibreRows Θ dimension width B Z)
    (hD₀ : D₀ ≠ 0) (hND₀ : (Ideal.absNorm D₀ : ℝ) ≤ Z ^ B)
    (hN : ∀ i ∈ d.columns, (Ideal.absNorm (d.ideal i).val : ℝ) ≤ Z ^ B)
    (pred : s.CoveredLeafKey CV CV → Prop)
    (hrow : ∀ j, pred j → s.rowPresent CV CV j)
    (pair : Ideal (𝓞 K) × Ideal (𝓞 K)) (a : OriginalAllocationFingerprint K cap)
    (hcommon : ∀ j, pred j → j.1.1.val = pair)
    (hallocation : ∀ j, pred j →
      s.cappedAllocationFingerprint CV CV
        (fun q => (d.mainSourceCartesianCover_slotCount_le T support D₀ hcolumns hideal c q).trans hcap)
        (fun q => (d.mainSourceCartesianCover_slotCount_le T support D₀ hcolumns hideal c q).trans hcap)
        j = a) :
    realCount pred ≤ coordinateConstant (K := K) cap (Fintype.card Θ)
      dimension width B ε hB hε * Z ^ ε := by
  sorry

end Main

section Residual

variable (p : ExteriorPrime A) (n : ℕ)
variable (s : ActualGaussStage (E := E) hΓ μv hDiff (d.residualSource p n c) finiteTest)
local notation "CV" => d.residualSourceCartesianCover T support D₀ hcolumns hideal p n c

theorem residual_original_predicate_subpower
    (hcap : T.slotCount ≤ cap) (ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (hZ : 1 ≤ Z)
    (rows : s.OriginalFibreRows Θ dimension width B Z)
    (hD₀ : D₀ ≠ 0)
    (hNcombined : (Ideal.absNorm (D₀ * p.val.asIdeal ^ n) : ℝ) ≤ Z ^ B)
    (hN : ∀ i ∈ d.columns, (Ideal.absNorm (d.ideal i).val : ℝ) ≤ Z ^ B)
    (pred : s.CoveredLeafKey CV CV → Prop)
    (hrow : ∀ j, pred j → s.rowPresent CV CV j)
    (pair : Ideal (𝓞 K) × Ideal (𝓞 K)) (a : OriginalAllocationFingerprint K cap)
    (hcommon : ∀ j, pred j → j.1.1.val = pair)
    (hallocation : ∀ j, pred j →
      s.cappedAllocationFingerprint CV CV
        (fun q => (d.residualSourceCartesianCover_slotCount_le T support D₀ hcolumns hideal p n c q).trans hcap)
        (fun q => (d.residualSourceCartesianCover_slotCount_le T support D₀ hcolumns hideal p n c q).trans hcap)
        j = a) :
    realCount pred ≤ coordinateConstant (K := K) cap (Fintype.card Θ)
      dimension width B ε hB hε * Z ^ ε := by
  sorry

end Residual
end FirstGaussPoolData

namespace ActualPoolStages

variable {d : FirstGaussPoolData C P ι} {c : ι → ℂ}
variable (s : ActualPoolStages (E := E) hΓ μv hDiff d c finiteTest)
variable (covers : d.SourceCovers c)

def rowPresent : s.CoveredLeafKey covers → Prop
  | .inl j => s.main.rowPresent covers.main covers.main j
  | .inr (.inl ⟨p, j⟩) =>
      (s.one p).rowPresent (covers.residual p 1) (covers.residual p 1) j
  | .inr (.inr (.inl ⟨p, j⟩)) =>
      (s.six p).rowPresent (covers.residual p 6) (covers.residual p 6) j
  | .inr (.inr (.inr ⟨p, j⟩)) =>
      (s.seven p).rowPresent (covers.residual p 7) (covers.residual p 7) j

theorem rowPresent_of_leaf_live (exceptional : s.CoverHybridPredicates covers)
    (F : SchwartzMap W ℂ) (x : ι → W) (j : s.CoveredLeafKey covers)
    (hj : (s.coveredLeaf covers exceptional F x j).Live) : s.rowPresent covers j := by
  sorry

structure OriginalFibreRows (Θ : Type*) (dimension width : ℕ) (B Z : ℝ) where
  main : s.main.OriginalFibreRows Θ dimension width B Z
  one : ∀ p : P.primes, (s.one p).OriginalFibreRows Θ dimension width B Z
  six : ∀ p : P.primes, (s.six p).OriginalFibreRows Θ dimension width B Z
  seven : ∀ p : P.primes, (s.seven p).OriginalFibreRows Θ dimension width B Z

variable (T : SourceCartesianAtlas originalColumns originalIdeal)
variable (support : Finset (Ideal (𝓞 K))) (D₀ : Ideal (𝓞 K))
variable (hcolumns : d.columns = originalColumns.filter
  (fun i => supportExtract (originalIdeal i).val support = D₀))
variable (hideal : ∀ i, (d.ideal i).val = supportResidual (originalIdeal i).val support)
local notation "CV" => d.sourceCoversOfOriginal c T support D₀ hcolumns hideal

/-- The real four-tag family has the one-source fibre bound: its
arithmetic index already fixes the valuation and the actual prime. -/
theorem original_predicate_subpower
    (hcap : T.slotCount ≤ cap) (ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (hZ : 1 ≤ Z)
    (rows : s.OriginalFibreRows Θ dimension width B Z)
    (hD₀ : D₀ ≠ 0) (hND₀ : (Ideal.absNorm D₀ : ℝ) ≤ Z ^ B)
    (hNcombined : ∀ p : P.primes, ∀ n ∈ ({1, 6, 7} : Finset ℕ),
      (Ideal.absNorm (D₀ * p.val.val.asIdeal ^ n) : ℝ) ≤ Z ^ B)
    (hN : ∀ i ∈ d.columns, (Ideal.absNorm (d.ideal i).val : ℝ) ≤ Z ^ B)
    (pred : s.CoveredLeafKey CV → Prop)
    (hrow : ∀ j, pred j → s.rowPresent CV j)
    (pair : Ideal (𝓞 K) × Ideal (𝓞 K)) (a : OriginalAllocationFingerprint K cap)
    (tag : Option (ℕ × ExteriorPrime A))
    (hcommon : ∀ j, pred j → s.commonLabel CV j = pair)
    (hallocation : ∀ j, pred j → s.allocationFingerprint CV
      (d.sourceCoversOfOriginal_slotCap c T support D₀ hcolumns hideal hcap) j = a)
    (htag : ∀ j, pred j → s.amplifierTag CV j = tag) :
    realCount pred ≤ coordinateConstant (K := K) cap (Fintype.card Θ)
      dimension width B ε hB hε * Z ^ ε := by
  sorry

end ActualPoolStages

namespace FirstBlockPoolData

variable {κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {radius : {r : ℝ // 0 < r}} {D : Finset (HeightOneSpectrum A.R)}
variable {chart : FirstBlockProfileChart (E := W) hΓ μv b C left right profiles finiteTest radius D}
variable {M : Finset (HeightOneSpectrum A.R)} {X : ℝ} {hX : 1 ≤ X}
variable {p : FirstBlockPoolData chart P M X hX}

namespace SecondStages

variable (R : p.SecondStages (E := E) (hDiff := hDiff))
variable (LA : SourceCartesianAtlas left fullI) (RA : SourceCartesianAtlas right fullJ)

def rowPresent (j : R.CoveredLeafKey LA RA) : Prop :=
  match j.2.2 with
  | .inl k => (R.left j.1 j.2.1).rowPresent (p.leftSourceCovers LA j.1 j.2.1) k
  | .inr k => (R.right j.1 j.2.1).rowPresent (p.rightSourceCovers RA j.1 j.2.1) k

structure OriginalFibreRows (Θ : Type*) (dimension width : ℕ) (B Z : ℝ) where
  left : ∀ S χ, (R.left S χ).OriginalFibreRows Θ dimension width B Z
  right : ∀ S χ, (R.right S χ).OriginalFibreRows Θ dimension width B Z

theorem rowPresent_of_leaf_live
    (NL NR : (divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val)) →
      ((PUnit × PUnit) →* Circle) → ℝ)
    (hNL : ∀ S χ, 0 < NL S χ) (hNR : ∀ S χ, 0 < NR S χ)
    (exceptional : R.CoverHybridPredicates LA RA)
    (j : R.CoveredLeafKey LA RA)
    (hj : (R.coveredLeaf LA RA NL NR hNL hNR exceptional j).Live) :
    R.rowPresent LA RA j := by
  sorry

/-- Once the original first divisor and pool tag are fixed, only the
two genuine side choices contribute a fixed multiplicity. The phase
carrier is subsingleton and is not counted as a moving parameter. -/
theorem original_predicate_subpower
    (hLA : LA.slotCount ≤ cap) (hRA : RA.slotCount ≤ cap)
    (ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (hZ : 1 ≤ Z)
    (rows : R.OriginalFibreRows Θ dimension width B Z)
    (hDE : DE.1 ≠ 0 ∧ DE.2 ≠ 0)
    (hNDE : (Ideal.absNorm DE.1 : ℝ) ≤ Z ^ B ∧ (Ideal.absNorm DE.2 : ℝ) ≤ Z ^ B)
    (hcombined : ∀ q : P.primes, ∀ n ∈ ({1, 6, 7} : Finset ℕ),
      (Ideal.absNorm (DE.1 * q.val.val.asIdeal ^ n) : ℝ) ≤ Z ^ B ∧
      (Ideal.absNorm (DE.2 * q.val.val.asIdeal ^ n) : ℝ) ≤ Z ^ B)
    (hL : ∀ i ∈ left, (Ideal.absNorm (fullI i).val : ℝ) ≤ Z ^ B)
    (hR : ∀ i ∈ right, (Ideal.absNorm (fullJ i).val : ℝ) ≤ Z ^ B)
    (pred : R.CoveredLeafKey LA RA → Prop)
    (hrow : ∀ j, pred j → R.rowPresent LA RA j)
    (S₀ : Ideal (𝓞 K)) (pair : Ideal (𝓞 K) × Ideal (𝓞 K))
    (a : OriginalAllocationFingerprint K cap) (tag : Option (ℕ × ExteriorPrime A))
    (hS₀ : ∀ j, pred j → j.1.val = S₀)
    (hcommon : ∀ j, pred j → R.commonLabel LA RA j = pair)
    (hallocation : ∀ j, pred j → R.allocationFingerprint LA RA hLA hRA j = a)
    (htag : ∀ j, pred j → R.amplifierTag LA RA j = tag) :
    realCount pred ≤ 2 * (coordinateConstant (K := K) cap (Fintype.card Θ)
      dimension width B ε hB hε * Z ^ ε) := by
  sorry

end SecondStages
end FirstBlockPoolData

namespace OriginalFiniteFibre

def firstMaskConstant (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) : ℝ :=
  let C : ℝ := Classical.choose
    (support_tuple_multiplicity_subpower (K := K) 1 B (ε / 2) hB (by positivity))
  C * C

theorem firstMaskConstant_pos (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    0 < firstMaskConstant (K := K) B ε hB hε := by
  sorry

theorem firstMaskCount_le (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε)
    (hZ : 1 ≤ Z) {ι κ : Type*} {I : ι → A.Exterior} {J : κ → A.Exterior}
    {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} (b : FirstCommonCharacterBlock I J DE)
    (M : Finset (HeightOneSpectrum A.R)) (R : Ideal (𝓞 K)) (hR : R ≠ 0)
    (hNR : (Ideal.absNorm R : ℝ) ≤ Z ^ B) (hND : (Ideal.absNorm DE.1 : ℝ) ≤ Z ^ B)
    (mask : OriginalMaskPrimeData M R) :
    ((b.mask M).powerset.card : ℝ) ≤ firstMaskConstant (K := K) B ε hB hε * Z ^ ε := by
  sorry

/-- The actual residual cover ideal costs only the original column
window and at most seven copies of the pool's original norm window. -/
theorem combined_original_norm_le (P : PowerScaleExteriorPool A bad Z ell eps)
    {B₀ B : ℝ} (hbox : B₀ + 7 * ell ≤ B)
    (I : Ideal (𝓞 K)) (hI : (Ideal.absNorm I : ℝ) ≤ Z ^ B₀)
    (p : P.primes) (n : ℕ) (hn : n ∈ ({1, 6, 7} : Finset ℕ)) :
    (Ideal.absNorm (I * p.val.val.asIdeal ^ n) : ℝ) ≤ Z ^ B := by
  sorry

end OriginalFiniteFibre

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualFirstSource.SecondStages

variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)

def rowPresent (j : R.CoveredLeafKey L) : Prop :=
  (R j.1 j.2.1).rowPresent L L j.2.2

structure OriginalFibreRows (Θ : Type*) (dimension width : ℕ) (B Z : ℝ) where
  source : ∀ v D, (R v D).OriginalFibreRows Θ dimension width B Z

theorem rowPresent_of_live (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.liveLeaves L exceptional N) : R.rowPresent L j.val := by
  sorry

/-- The whole actual parent fibre follows from original column and
row data. Fixed first/second common labels, divisors and tagged full
allocations are never charged again as auxiliary coordinates. -/
theorem original_predicate_subpower
    (hcap : L.slotCount ≤ cap) (δ₁ δ₂ B₀ : ℝ)
    (hB : 0 ≤ B) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hbox : B₀ + 7 * ell ≤ B)
    (rows : R.OriginalFibreRows Θ dimension width B Z)
    (maskIdeal : Ideal (𝓞 K)) (hmask0 : maskIdeal ≠ 0)
    (mask : OriginalMaskPrimeData s.mask maskIdeal)
    (hmaskN : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ B)
    (hN : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B₀)
    (pred : R.CoveredLeafKey L → Prop) (hrow : ∀ j, pred j → R.rowPresent L j)
    (firstPair : Ideal (𝓞 K) × Ideal (𝓞 K)) (S₀ : Ideal (𝓞 K))
    (secondPair : Ideal (𝓞 K) × Ideal (𝓞 K))
    (allocation : OriginalAllocationFingerprint K cap) (tag : Option (ℕ × ExteriorPrime A))
    (hfirst : ∀ j, pred j → j.1.val = firstPair)
    (hS₀ : ∀ j, pred j → j.2.2.1.val = S₀)
    (hsecond : ∀ j, pred j → R.commonLabel L j = secondPair)
    (halloc : ∀ j, pred j →
      (R j.1 j.2.1).allocationFingerprint L L hcap hcap j.2.2 = allocation)
    (htag : ∀ j, pred j → (R j.1 j.2.1).amplifierTag L L j.2.2 = tag) :
    realCount pred ≤
      2 * firstMaskConstant (K := K) B δ₁ hB hδ₁ *
        coordinateConstant (K := K) cap (Fintype.card Θ) dimension width B δ₂ hB hδ₂ *
          Z ^ (δ₁ + δ₂) := by
  sorry

abbrev AmplifiedArithmeticIndex (hcap : L.slotCount ≤ cap)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization) :=
  AmplifiedCommonIndex P
    ((R.arithmeticLabels L hcap exceptional N).mainCarrier (R.arithmeticTag L exceptional N))
    ((R.arithmeticLabels L hcap exceptional N).errorCarrier (R.arithmeticTag L exceptional N))

/-- This map uses the same actual live source labels and both literal
original allocation functions. Its target supports are computed by
finite images, with the genuine prime/valuation retained. -/
def originalAmplifiedIndex (hcap : L.slotCount ≤ cap)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.liveLeaves L exceptional N) :
    R.AmplifiedArithmeticIndex L hcap exceptional N :=
  (R.arithmeticLabels L hcap exceptional N).amplifiedIndex
    (R.arithmeticTag L exceptional N) P (R.arithmeticTag_mem L exceptional N) j

/-- Uniform fibre cardinality of the engine's concrete map on its
actual live leaves. No aggregate cardinality premise occurs. -/
theorem originalAmplifiedIndex_fibre_subpower
    (hcap : L.slotCount ≤ cap) (δ₁ δ₂ B₀ : ℝ)
    (hB : 0 ≤ B) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hbox : B₀ + 7 * ell ≤ B)
    (rows : R.OriginalFibreRows Θ dimension width B Z)
    (maskIdeal : Ideal (𝓞 K)) (hmask0 : maskIdeal ≠ 0)
    (mask : OriginalMaskPrimeData s.mask maskIdeal)
    (hmaskN : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ B)
    (hN : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B₀)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.AmplifiedArithmeticIndex L hcap exceptional N) :
    ((Finset.univ.filter (fun i : R.liveLeaves L exceptional N =>
        R.originalAmplifiedIndex L hcap exceptional N i = j)).card : ℝ) ≤
      2 * firstMaskConstant (K := K) B δ₁ hB hδ₁ *
        coordinateConstant (K := K) cap (Fintype.card Θ) dimension width B δ₂ hB hδ₂ *
          Z ^ (δ₁ + δ₂) := by
  sorry

/-- Restricting to the actual active leaves can only reduce a fibre.
The four ordinary rectangles are retained and contribute exactly four;
together with the two side choices the fixed factor is eight. -/
theorem originalAmplifiedIndex_active_rectangles_fibre_subpower
    (hcap : L.slotCount ≤ cap) (δ₁ δ₂ B₀ : ℝ)
    (hB : 0 ≤ B) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hbox : B₀ + 7 * ell ≤ B)
    (rows : R.OriginalFibreRows Θ dimension width B Z)
    (maskIdeal : Ideal (𝓞 K)) (hmask0 : maskIdeal ≠ 0)
    (mask : OriginalMaskPrimeData s.mask maskIdeal)
    (hmaskN : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ B)
    (hN : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B₀)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (active : Finset (R.liveLeaves L exceptional N))
    (j : R.AmplifiedArithmeticIndex L hcap exceptional N) :
    ((Finset.univ.filter (fun i : active × (Bool × Bool) =>
        R.originalAmplifiedIndex L hcap exceptional N i.1.val = j)).card : ℝ) ≤
      8 * firstMaskConstant (K := K) B δ₁ hB hδ₁ *
        coordinateConstant (K := K) cap (Fintype.card Θ) dimension width B δ₂ hB hδ₂ *
          Z ^ (δ₁ + δ₂) := by
  sorry

/-- This is the form used by the normalized family: its active labels
are a literal subset of live-leaf/rectangle pairs, and different leaves
may retain different rectangles. The actual selection costs nothing. -/
theorem originalAmplifiedIndex_retained_rectangles_fibre_subpower
    (hcap : L.slotCount ≤ cap) (δ₁ δ₂ B₀ : ℝ)
    (hB : 0 ≤ B) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hbox : B₀ + 7 * ell ≤ B)
    (rows : R.OriginalFibreRows Θ dimension width B Z)
    (maskIdeal : Ideal (𝓞 K)) (hmask0 : maskIdeal ≠ 0)
    (mask : OriginalMaskPrimeData s.mask maskIdeal)
    (hmaskN : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ B)
    (hN : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B₀)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (active : Finset ((R.liveLeaves L exceptional N) × (Bool × Bool)))
    (j : R.AmplifiedArithmeticIndex L hcap exceptional N) :
    ((Finset.univ.filter (fun i : active =>
        R.originalAmplifiedIndex L hcap exceptional N i.val.1 = j)).card : ℝ) ≤
      8 * firstMaskConstant (K := K) B δ₁ hB hδ₁ *
        coordinateConstant (K := K) cap (Fintype.card Θ) dimension width B δ₂ hB hδ₂ *
          Z ^ (δ₁ + δ₂) := by
  sorry

end ActualFirstSource.SecondStages

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalFiniteFibre.realCount_sigma_fixed_le
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalFiniteFibre.realCount_fourSource_fixed_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.originalAmplifiedIndex_fibre_subpower
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.originalAmplifiedIndex_active_rectangles_fibre_subpower
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.originalAmplifiedIndex_retained_rectangles_fibre_subpower
