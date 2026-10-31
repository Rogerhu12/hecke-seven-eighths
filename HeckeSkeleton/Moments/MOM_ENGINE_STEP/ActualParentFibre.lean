import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualLeafNormWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalAmplifiedCarrier
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCoveredFibreMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstBlockMaskCardinality

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

theorem realCount_nonneg (P : α → Prop) : 0 ≤ realCount P := Nat.cast_nonneg _

theorem realCount_eq_sum (P : α → Prop) :
    realCount P = ∑ a : α, if P a then (1 : ℝ) else 0 := by
  simp [realCount, Finset.card_eq_sum_ones, Finset.sum_filter]

theorem realCount_eq_zero (P : α → Prop) (hP : ∀ a, ¬ P a) : realCount P = 0 := by
  rw [realCount_eq_sum]
  simp only [hP, if_false, Finset.sum_const_zero]

theorem realCount_mono {P Q : α → Prop} (h : ∀ a, P a → Q a) :
    realCount P ≤ realCount Q := by
  unfold realCount
  exact_mod_cast Finset.card_le_card
    (show Finset.univ.filter P ⊆ Finset.univ.filter Q from
      fun a ha => Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, h a (Finset.mem_filter.mp ha).2⟩)

theorem realCount_injective {P : α → Prop} {Q : β → Prop}
    (f : α → β) (hf : Function.Injective f) (h : ∀ a, P a → Q (f a)) :
    realCount P ≤ realCount Q := by
  have hsub : (Finset.univ.filter P).image f ⊆ Finset.univ.filter Q := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, h a (Finset.mem_filter.mp ha).2⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hf] at hc
  exact_mod_cast hc

theorem realCount_equiv (e : α ≃ β) (P : α → Prop) :
    realCount P = realCount (fun b => P (e.symm b)) := by
  simp only [realCount_eq_sum]
  exact Fintype.sum_equiv e _ _ (fun a => by rw [e.symm_apply_apply])

theorem realCount_sum (P : α ⊕ β → Prop) :
    realCount P = realCount (fun a => P (.inl a)) +
      realCount (fun b => P (.inr b)) := by
  simp only [realCount_eq_sum, Fintype.sum_sum_type]

theorem realCount_sigma {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (P : (Σ i, X i) → Prop) :
    realCount P = ∑ i : ι, realCount (fun x => P ⟨i, x⟩) := by
  simp only [realCount_eq_sum, Fintype.sum_sigma]

theorem realCount_sigma_le {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (P : (Σ i, X i) → Prop)
    (C : ℝ) (hC : ∀ i, realCount (fun x => P ⟨i, x⟩) ≤ C) :
    realCount P ≤ (Fintype.card ι : ℝ) * C := by
  rw [realCount_sigma]
  calc
    _ ≤ ∑ _i : ι, C := Finset.sum_le_sum (fun i _ => hC i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- An arithmetic coordinate fixed by an injective original projection
has one possible value, even if its declared ambient carrier is large. -/
theorem realCount_sigma_fixed_le {ι J : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (P : (Σ i, X i) → Prop)
    (f : ι → J) (hf : Function.Injective f) (j : J)
    (hfix : ∀ x, P x → f x.1 = j)
    (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ i, realCount (fun x => P ⟨i, x⟩) ≤ C) :
    realCount P ≤ C := by
  by_cases hex : ∃ x, P x
  · obtain ⟨⟨i₀, x₀⟩, hx₀⟩ := hex
    calc
      _ = realCount (fun x => P ⟨i₀, x⟩) := by
        rw [realCount_sigma]
        apply Finset.sum_eq_single i₀
        · intro i _ hne
          apply realCount_eq_zero
          intro x hx
          exact hne (hf ((hfix ⟨i, x⟩ hx).trans (hfix ⟨i₀, x₀⟩ hx₀).symm))
        · intro hnot
          exact (hnot (Finset.mem_univ _)).elim
      _ ≤ C := hlocal i₀
  · rw [realCount_eq_zero P (fun x hx => hex ⟨x, hx⟩)]
    exact hC

theorem realCount_sigma_subsingleton_le {ι : Type*} [Fintype ι] [Subsingleton ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (P : (Σ i, X i) → Prop)
    (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ i, realCount (fun x => P ⟨i, x⟩) ≤ C) :
    realCount P ≤ C := by
  have hc : (Fintype.card ι : ℝ) ≤ 1 := by
    exact_mod_cast (Fintype.card_le_one_iff_subsingleton.mpr
      (inferInstance : Subsingleton ι))
  exact (realCount_sigma_le P C hlocal).trans
    ((mul_le_mul_of_nonneg_right hc hC).trans_eq (one_mul C))

theorem realCount_prod_left (P : α → Prop) :
    realCount (fun x : α × β => P x.1) = (Fintype.card β : ℝ) * realCount P := by
  simp only [realCount_eq_sum, Fintype.sum_prod_type, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]

abbrev FourTag (ι : Type*) := Unit ⊕ (ι ⊕ (ι ⊕ ι))

def fourTagCode {ι J : Type*} (f : ι → J) : FourTag ι → Option (ℕ × J)
  | .inl _ => none
  | .inr (.inl p) => some (1, f p)
  | .inr (.inr (.inl p)) => some (6, f p)
  | .inr (.inr (.inr p)) => some (7, f p)

theorem fourTagCode_injective {ι J : Type*} (f : ι → J) (hf : Function.Injective f) :
    Function.Injective (fourTagCode f) := by
  intro a b h
  rcases a with a | (a | (a | a)) <;>
    rcases b with b | (b | (b | b)) <;>
    simp_all [fourTagCode, hf.eq_iff]

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
  rw [realCount_equiv (fourSourceEquiv X₀ X₁ X₆ X₇)]
  apply realCount_sigma_fixed_le _ (fourTagCode f) (fourTagCode_injective f hf) j
  · intro x hx
    simpa only [Equiv.apply_symm_apply] using
      hfix ((fourSourceEquiv X₀ X₁ X₆ X₇).symm x) hx
  · exact hC
  · rintro (i | (i | (i | i)))
    · exact h₀
    · exact h₁ i
    · exact h₆ i
    · exact h₇ i

end Tagged
end OriginalFiniteFibre

open NumberField IsDedekindDomain DedekindZetaZeroFree
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
local instance : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

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
    s.rowPresent LC RC j :=
  j.1.rowLabel_mem_of_live exceptional F x j.2
    ((s.coveredLeaf LC RC exceptional F x j).live_of_scale_live _ _ hj)

/-- Primitive original row coordinates.  The forward classifier
identity forbids arbitrary refinement of the declared row-label set.
The two ideal windows concern the original mask and row support only. -/
structure OriginalFibreRows (Θ : Type*) (dimension width : ℕ) (B Z : ℝ) where
  support : Finset (HeightOneSpectrum (𝓞 K))
  maskIdeal : Ideal (𝓞 K)
  rowIdeal : Ideal (𝓞 K)
  mask_nonzero : maskIdeal ≠ 0
  row_nonzero : rowIdeal ≠ 0
  maskPrimes : OriginalMaskPrimeData s.mask maskIdeal
  row_divides : ∀ p ∈ support, p.asIdeal ∣ rowIdeal
  mask_norm : (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ B
  row_norm : (Ideal.absNorm rowIdeal : ℝ) ≤ Z ^ B
  code : ∀ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
    s.mask.powerset → Q → RowCode support Θ dimension width
  encode : ∀ DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val),
    ∀ D : s.mask.powerset, RowCode support Θ dimension width →
      Fin ((s.charts DE D).rowLabelCount + 1)
  row_label : ∀ DE D, ∀ h ∈ (s.sources DE).rows,
    (s.charts DE D).rowLabel h = encode DE D (code DE D h)

def OriginalFibreRows.rowPrimes (rows : s.OriginalFibreRows Θ dimension width B Z) :
    OriginalMaskPrimeData rows.support rows.rowIdeal where
  prime := id
  injective := fun _ _ _ _ h => h
  divides := rows.row_divides

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
  have hbound : 0 ≤ coordinateConstant (K := K) cap (Fintype.card Θ)
      dimension width B ε hB hε * Z ^ ε :=
    mul_nonneg (coordinateConstant_pos (K := K)
      cap (Fintype.card Θ) dimension width B ε hB hε).le
      (Real.rpow_nonneg (zero_le_one.trans hZ) ε)
  by_cases hex : ∃ j, pred j
  · obtain ⟨j₀, hj₀⟩ := hex
    let DE := j₀.1.1
    let leaves := Finset.univ.filter pred
    let hs : ∀ q, (CV.branch q).slotCount ≤ cap := fun q =>
      (d.mainSourceCartesianCover_slotCount_le T support D₀ hcolumns hideal c q).trans hcap
    let hl := fun v : s.CoveredClassKey CV CV => v.leftSlots_le hs
    let hr := fun v : s.CoveredClassKey CV CV => v.rightSupportSlots_le hs
    let index := s.cappedAllocationFingerprint CV CV hs hs
    have hn := actual_common_pair_norm _ _ _ _ (Z ^ B)
      (fun i _ => (d.ideal i).property.1) (fun i _ => (d.ideal i).property.1) hN hN DE
    have hc := d.main_covered_index_fibre_subpower T support D₀ hcolumns hideal c s
      cap dimension width hcap B ε hB hε hZ hl hr index id (fun _ => rfl) leaves a DE
      (fun j hj _ => Subtype.ext ((hcommon j (Finset.mem_filter.mp hj).2).trans
        (hcommon j₀ hj₀).symm))
      (fun j hj => hrow j (Finset.mem_filter.mp hj).2)
      rows.support (rows.code DE) (rows.encode DE) (rows.row_label DE)
      ⟨(actual_common_pair_properties _ _ _ _ DE).1,
        (actual_common_pair_properties _ _ _ _ DE).2.1⟩ hD₀
      rows.maskIdeal rows.rowIdeal rows.mask_nonzero rows.row_nonzero
      rows.maskPrimes rows.rowPrimes rows.mask_norm rows.row_norm hND₀ hn.1 hn.2
    have he : leaves.filter (fun j => index j = a) = leaves :=
      Finset.filter_eq_self.mpr (fun j hj => hallocation j (Finset.mem_filter.mp hj).2)
    rw [he] at hc
    exact hc
  · rw [realCount_eq_zero pred (fun j hj => hex ⟨j, hj⟩)]
    exact hbound

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
  have hbound : 0 ≤ coordinateConstant (K := K) cap (Fintype.card Θ)
      dimension width B ε hB hε * Z ^ ε :=
    mul_nonneg (coordinateConstant_pos (K := K)
      cap (Fintype.card Θ) dimension width B ε hB hε).le
      (Real.rpow_nonneg (zero_le_one.trans hZ) ε)
  by_cases hex : ∃ j, pred j
  · obtain ⟨j₀, hj₀⟩ := hex
    let DE := j₀.1.1
    let leaves := Finset.univ.filter pred
    let hs : ∀ q, (CV.branch q).slotCount ≤ cap := fun q =>
      (d.residualSourceCartesianCover_slotCount_le T support D₀ hcolumns hideal p n c q).trans hcap
    let hl := fun v : s.CoveredClassKey CV CV => v.leftSlots_le hs
    let hr := fun v : s.CoveredClassKey CV CV => v.rightSupportSlots_le hs
    let index := s.cappedAllocationFingerprint CV CV hs hs
    have hres (i : d.valuationColumns p n) :
        (Ideal.absNorm ((d.residualSource p n c).ideal i).val : ℝ) ≤ Z ^ B :=
      (d.residualSource_ideal_norm_le p n c i).trans
        (hN i.val (Finset.mem_filter.mp i.property).1)
    have hn := actual_common_pair_norm _ _ _ _ (Z ^ B)
      (fun i _ => ((d.residualSource p n c).ideal i).property.1)
      (fun i _ => ((d.residualSource p n c).ideal i).property.1)
      (fun i _ => hres i) (fun i _ => hres i) DE
    have hc := d.residual_covered_index_fibre_subpower T support D₀ hcolumns hideal c p n s
      cap dimension width hcap B ε hB hε hZ hl hr index id (fun _ => rfl) leaves a DE
      (fun j hj _ => Subtype.ext ((hcommon j (Finset.mem_filter.mp hj).2).trans
        (hcommon j₀ hj₀).symm))
      (fun j hj => hrow j (Finset.mem_filter.mp hj).2)
      rows.support (rows.code DE) (rows.encode DE) (rows.row_label DE)
      ⟨(actual_common_pair_properties _ _ _ _ DE).1,
        (actual_common_pair_properties _ _ _ _ DE).2.1⟩ hD₀
      rows.maskIdeal rows.rowIdeal rows.mask_nonzero rows.row_nonzero
      rows.maskPrimes rows.rowPrimes rows.mask_norm rows.row_norm hNcombined hn.1 hn.2
    have he : leaves.filter (fun j => index j = a) = leaves :=
      Finset.filter_eq_self.mpr (fun j hj => hallocation j (Finset.mem_filter.mp hj).2)
    rw [he] at hc
    exact hc
  · rw [realCount_eq_zero pred (fun j hj => hex ⟨j, hj⟩)]
    exact hbound

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
  rcases j with j | (⟨p, j⟩ | (⟨p, j⟩ | ⟨p, j⟩))
  · exact s.main.rowPresent_of_fiberLeaf_live covers.main covers.main exceptional.main F x j
      ((s.main.fiberCoveredLeaf covers.main covers.main exceptional.main F x j).live_of_scale_live _ _ hj)
  · exact (s.one p).rowPresent_of_fiberLeaf_live
      (covers.residual p 1) (covers.residual p 1) (exceptional.one p) F (fun i => x i.val) j
      (((s.one p).fiberCoveredLeaf (covers.residual p 1) (covers.residual p 1)
        (exceptional.one p) F (fun i => x i.val) j).live_of_scale_live _ _ hj)
  · exact (s.six p).rowPresent_of_fiberLeaf_live
      (covers.residual p 6) (covers.residual p 6) (exceptional.six p) F (fun i => x i.val) j
      (((s.six p).fiberCoveredLeaf (covers.residual p 6) (covers.residual p 6)
        (exceptional.six p) F (fun i => x i.val) j).live_of_scale_live _ _ hj)
  · exact (s.seven p).rowPresent_of_fiberLeaf_live
      (covers.residual p 7) (covers.residual p 7) (exceptional.seven p) F (fun i => x i.val) j
      (((s.seven p).fiberCoveredLeaf (covers.residual p 7) (covers.residual p 7)
        (exceptional.seven p) F (fun i => x i.val) j).live_of_scale_live _ _ hj)

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
  apply realCount_fourSource_fixed_le _ _ _ _ pred
    (fun p : P.primes => p.val) Subtype.coe_injective tag
  · intro j hj
    rcases j with j | (⟨p, j⟩ | (⟨p, j⟩ | ⟨p, j⟩)) <;> exact htag _ hj
  · exact mul_nonneg (coordinateConstant_pos (K := K)
      cap (Fintype.card Θ) dimension width B ε hB hε).le
      (Real.rpow_nonneg (zero_le_one.trans hZ) ε)
  · exact d.main_original_predicate_subpower T support D₀ hcolumns hideal c s.main
      hcap ε hB hε hZ rows.main hD₀ hND₀ hN
      (fun j => pred (.inl j)) (fun j hj => hrow (.inl j) hj) pair a
      (fun j hj => hcommon (.inl j) hj) (fun j hj => hallocation (.inl j) hj)
  · intro p
    exact d.residual_original_predicate_subpower T support D₀ hcolumns hideal c p.val 1 (s.one p)
      hcap ε hB hε hZ (rows.one p) hD₀ (hNcombined p 1 (by simp)) hN
      (fun j => pred (.inr (.inl ⟨p, j⟩)))
      (fun j hj => hrow (.inr (.inl ⟨p, j⟩)) hj) pair a
      (fun j hj => hcommon (.inr (.inl ⟨p, j⟩)) hj)
      (fun j hj => hallocation (.inr (.inl ⟨p, j⟩)) hj)
  · intro p
    exact d.residual_original_predicate_subpower T support D₀ hcolumns hideal c p.val 6 (s.six p)
      hcap ε hB hε hZ (rows.six p) hD₀ (hNcombined p 6 (by simp)) hN
      (fun j => pred (.inr (.inr (.inl ⟨p, j⟩))))
      (fun j hj => hrow (.inr (.inr (.inl ⟨p, j⟩))) hj) pair a
      (fun j hj => hcommon (.inr (.inr (.inl ⟨p, j⟩))) hj)
      (fun j hj => hallocation (.inr (.inr (.inl ⟨p, j⟩))) hj)
  · intro p
    exact d.residual_original_predicate_subpower T support D₀ hcolumns hideal c p.val 7 (s.seven p)
      hcap ε hB hε hZ (rows.seven p) hD₀ (hNcombined p 7 (by simp)) hN
      (fun j => pred (.inr (.inr (.inr ⟨p, j⟩))))
      (fun j hj => hrow (.inr (.inr (.inr ⟨p, j⟩))) hj) pair a
      (fun j hj => hcommon (.inr (.inr (.inr ⟨p, j⟩))) hj)
      (fun j hj => hallocation (.inr (.inr (.inr ⟨p, j⟩))) hj)

end ActualPoolStages

namespace FirstBlockPoolData

variable {κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {left : Finset ι} {right : Finset κ} {profiles : ι → κ → SchwartzMap V ℂ}
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
  rcases j with ⟨S, χ, j | j⟩
  · exact (R.left S χ).rowPresent_of_leaf_live (p.leftSourceCovers LA S χ)
      (exceptional.left S χ) chart.kernel chart.leftPoint j
      (((R.left S χ).coveredLeaf (p.leftSourceCovers LA S χ)
        (exceptional.left S χ) chart.kernel chart.leftPoint j).live_of_scale_live _ _ hj)
  · exact (R.right S χ).rowPresent_of_leaf_live (p.rightSourceCovers RA S χ)
      (exceptional.right S χ) chart.kernel (fun i => -chart.rightPoint i) j
      (((R.right S χ).coveredLeaf (p.rightSourceCovers RA S χ)
        (exceptional.right S χ) chart.kernel (fun i => -chart.rightPoint i) j).live_of_scale_live _ _ hj)

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
  let bound := coordinateConstant (K := K) cap (Fintype.card Θ)
    dimension width B ε hB hε * Z ^ ε
  have hb : 0 ≤ bound :=
    mul_nonneg (coordinateConstant_pos (K := K)
      cap (Fintype.card Θ) dimension width B ε hB hε).le
      (Real.rpow_nonneg (zero_le_one.trans hZ) ε)
  apply realCount_sigma_fixed_le pred Subtype.val Subtype.coe_injective S₀ hS₀
    (2 * bound) (mul_nonneg (by norm_num) hb)
  intro S
  apply realCount_sigma_subsingleton_le _ (2 * bound) (mul_nonneg (by norm_num) hb)
  intro χ
  rw [realCount_sum]
  have hl := (R.left S χ).original_predicate_subpower LA (primeSupport DE.1) DE.1
    ((p.divisorPools.left_columns S).trans p.left_columns)
    (by intro i; rw [p.divisorPools.left_ideal S, p.left_ideal]; exact b.left_residual i)
    hLA ε hB hε hZ (rows.left S χ) hDE.1 hNDE.1
    (fun q n hn => (hcombined q n hn).1)
    (by simpa only [p.divisorPools.left_columns S, p.divisorPools.left_ideal S] using
      p.left_ideal_norm_le (Z ^ B) hL)
    (fun j => pred ⟨S, χ, .inl j⟩)
    (fun j hj => hrow ⟨S, χ, .inl j⟩ hj) pair a tag
    (fun j hj => hcommon ⟨S, χ, .inl j⟩ hj)
    (fun j hj => hallocation ⟨S, χ, .inl j⟩ hj)
    (fun j hj => htag ⟨S, χ, .inl j⟩ hj)
  have hr := (R.right S χ).original_predicate_subpower RA (primeSupport DE.1) DE.2
    ((p.divisorPools.right_columns S).trans p.right_columns)
    (by intro i; rw [p.divisorPools.right_ideal S, p.right_ideal]; exact b.right_residual i)
    hRA ε hB hε hZ (rows.right S χ) hDE.2 hNDE.2
    (fun q n hn => (hcombined q n hn).2)
    (by simpa only [p.divisorPools.right_columns S, p.divisorPools.right_ideal S] using
      p.right_ideal_norm_le (Z ^ B) hR)
    (fun j => pred ⟨S, χ, .inr j⟩)
    (fun j hj => hrow ⟨S, χ, .inr j⟩ hj) pair a tag
    (fun j hj => hcommon ⟨S, χ, .inr j⟩ hj)
    (fun j hj => hallocation ⟨S, χ, .inr j⟩ hj)
    (fun j hj => htag ⟨S, χ, .inr j⟩ hj)
  exact (add_le_add hl hr).trans_eq (by dsimp only [bound]; ring)

end SecondStages
end FirstBlockPoolData

namespace OriginalFiniteFibre

def firstMaskConstant (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) : ℝ :=
  Classical.choose (first_block_mask_labels_subpower (K := K) B ε hB hε)

theorem firstMaskConstant_pos (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    0 < firstMaskConstant (K := K) B ε hB hε :=
  (Classical.choose_spec (first_block_mask_labels_subpower (K := K) B ε hB hε)).1

theorem firstMaskCount_le (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε)
    (hZ : 1 ≤ Z) {ι κ : Type*} {I : ι → A.Exterior} {J : κ → A.Exterior}
    {DE : Ideal (𝓞 K) × Ideal (𝓞 K)} (b : FirstCommonCharacterBlock I J DE)
    (M : Finset (HeightOneSpectrum A.R)) (R : Ideal (𝓞 K)) (hR : R ≠ 0)
    (hNR : (Ideal.absNorm R : ℝ) ≤ Z ^ B) (hND : (Ideal.absNorm DE.1 : ℝ) ≤ Z ^ B)
    (mask : OriginalMaskPrimeData M R) :
    ((b.mask M).powerset.card : ℝ) ≤ firstMaskConstant (K := K) B ε hB hε * Z ^ ε :=
  (Classical.choose_spec (first_block_mask_labels_subpower (K := K) B ε hB hε)).2
    Z hZ b M R hR hNR hND mask

/-- The actual residual cover ideal costs only the original column
window and at most seven copies of the pool's original norm window. -/
theorem combined_original_norm_le (P : PowerScaleExteriorPool A bad Z ell eps)
    {B₀ B : ℝ} (hbox : B₀ + 7 * ell ≤ B)
    (I : Ideal (𝓞 K)) (hI : (Ideal.absNorm I : ℝ) ≤ Z ^ B₀)
    (p : P.primes) (n : ℕ) (hn : n ∈ ({1, 6, 7} : Finset ℕ)) :
    (Ideal.absNorm (I * p.val.val.asIdeal ^ n) : ℝ) ≤ Z ^ B := by
  have hz : 0 < Z := zero_lt_one.trans P.base_gt_one
  have hn7 : n ≤ 7 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl <;> norm_num
  have hn7r : (n : ℝ) ≤ 7 := by exact_mod_cast hn7
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Ideal.absNorm p.val.val.asIdeal)
    (P.norm_upper p.val p.property) n
  calc
    _ = (Ideal.absNorm I : ℝ) * (Ideal.absNorm p.val.val.asIdeal : ℝ) ^ n := by
      rw [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
    _ ≤ Z ^ B₀ * (Z ^ ell) ^ n :=
      mul_le_mul hI hp (by positivity) (Real.rpow_nonneg hz.le B₀)
    _ = Z ^ (B₀ + ell * n) := by
      rw [← Real.rpow_mul_natCast hz.le, ← Real.rpow_add hz]
    _ ≤ Z ^ B := Real.rpow_le_rpow_of_exponent_le P.base_gt_one.le
      (le_trans (by nlinarith [P.exponent_pos]) hbox)

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
    (j : R.liveLeaves L exceptional N) : R.rowPresent L j.val :=
  (R j.val.1 j.val.2.1).rowPresent_of_leaf_live L L
    (N.left j.val.1 j.val.2.1) (N.right j.val.1 j.val.2.1)
    (N.left_pos j.val.1 j.val.2.1) (N.right_pos j.val.1 j.val.2.1)
    (exceptional j.val.1 j.val.2.1) j.val.2.2
    ((R.coveredLeaf L exceptional N j.val).live_of_scale_live _ _
      (R.liveLeaves_spec L exceptional N j))

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
  let Cm := firstMaskConstant (K := K) B δ₁ hB hδ₁
  let Cc := coordinateConstant (K := K) cap (Fintype.card Θ) dimension width B δ₂ hB hδ₂
  have hCm : 0 < Cm := firstMaskConstant_pos _ _ _ _
  have hCc : 0 < Cc := coordinateConstant_pos _ _ _ _ _ _ _ _
  have hz : 0 < Z := zero_lt_one.trans P.base_gt_one
  have hB₀ : B₀ ≤ B := le_trans
    (le_add_of_nonneg_right (mul_nonneg (by norm_num) P.exponent_pos.le)) hbox
  have hNB : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B :=
    fun i hi => (hN i hi).trans (Real.rpow_le_rpow_of_exponent_le P.base_gt_one.le hB₀)
  apply realCount_sigma_fixed_le pred Subtype.val Subtype.coe_injective firstPair hfirst
    (2 * Cm * Cc * Z ^ (δ₁ + δ₂)) (by positivity)
  intro v
  have hn := actual_common_pair_norm _ _ _ _ (Z ^ B₀)
    (fun i _ => (s.ideal i).property.1) (fun i _ => (s.ideal i).property.1) hN hN v
  have hnb : (Ideal.absNorm v.val.1 : ℝ) ≤ Z ^ B ∧
      (Ideal.absNorm v.val.2 : ℝ) ≤ Z ^ B :=
    ⟨hn.1.trans (Real.rpow_le_rpow_of_exponent_le P.base_gt_one.le hB₀),
      hn.2.trans (Real.rpow_le_rpow_of_exponent_le P.base_gt_one.le hB₀)⟩
  have hcommon := actual_common_pair_properties _ _ _ _ v
  have hm := firstMaskCount_le B δ₁ hB hδ₁ P.base_gt_one.le (s.block v)
    s.mask maskIdeal hmask0 hmaskN hnb.1 mask
  have hl (D : ((s.block v).mask s.mask).powerset) :
      realCount (fun j => pred ⟨v, D, j⟩) ≤ 2 * (Cc * Z ^ δ₂) :=
    (R v D).original_predicate_subpower L L hcap hcap δ₂ hB hδ₂ P.base_gt_one.le
      (rows.source v D) ⟨hcommon.1, hcommon.2.1⟩ hnb
      (fun q n hn' =>
        ⟨combined_original_norm_le P hbox v.val.1 hn.1 q n hn',
          combined_original_norm_le P hbox v.val.2 hn.2 q n hn'⟩)
      hNB hNB (fun j => pred ⟨v, D, j⟩)
      (fun j hj => hrow ⟨v, D, j⟩ hj) S₀ secondPair allocation tag
      (fun j hj => hS₀ ⟨v, D, j⟩ hj)
      (fun j hj => hsecond ⟨v, D, j⟩ hj)
      (fun j hj => halloc ⟨v, D, j⟩ hj)
      (fun j hj => htag ⟨v, D, j⟩ hj)
  calc
    _ ≤ (Fintype.card (((s.block v).mask s.mask).powerset) : ℝ) * (2 * (Cc * Z ^ δ₂)) :=
      realCount_sigma_le _ _ hl
    _ = (((s.block v).mask s.mask).powerset.card : ℝ) * (2 * (Cc * Z ^ δ₂)) := by
      rw [Fintype.card_coe]
    _ ≤ (Cm * Z ^ δ₁) * (2 * (Cc * Z ^ δ₂)) :=
      mul_le_mul_of_nonneg_right hm (by positivity)
    _ = _ := by rw [Real.rpow_add hz]; ring

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
  let labels := R.arithmeticLabels L hcap exceptional N
  let tags := R.arithmeticTag L exceptional N
  let firstPair := (labels.amplifiedFirst tags P j).1
  let S₀ := labels.amplifiedFirstDivisor tags P j
  let secondPair := (labels.amplifiedSecond tags P j).1
  let allocation := labels.amplifiedAllocation tags P j
  let tag := labels.amplifiedTag tags P j
  let pred : R.CoveredLeafKey L → Prop := fun i =>
    R.rowPresent L i ∧ i.1.val = firstPair ∧ i.2.2.1.val = S₀ ∧
      R.commonLabel L i = secondPair ∧
      (R i.1 i.2.1).allocationFingerprint L L hcap hcap i.2.2 = allocation ∧
      (R i.1 i.2.1).amplifierTag L L i.2.2 = tag
  have hc := R.original_predicate_subpower L hcap δ₁ δ₂ B₀ hB hδ₁ hδ₂ hbox rows
    maskIdeal hmask0 mask hmaskN hN pred (fun _ h => h.1)
    firstPair S₀ secondPair allocation tag
    (fun _ h => h.2.1) (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.1)
    (fun _ h => h.2.2.2.2.1) (fun _ h => h.2.2.2.2.2)
  apply le_trans (realCount_injective
    (P := fun i : R.liveLeaves L exceptional N =>
      R.originalAmplifiedIndex L hcap exceptional N i = j)
    (Q := pred) Subtype.val Subtype.coe_injective ?_) hc
  intro i hi
  have hfirst := congrArg (labels.amplifiedFirst tags P) hi
  have hS₀ := congrArg (labels.amplifiedFirstDivisor tags P) hi
  have hsecond := congrArg (labels.amplifiedSecond tags P) hi
  have halloc := congrArg (labels.amplifiedAllocation tags P) hi
  have htag := congrArg (labels.amplifiedTag tags P) hi
  change labels.amplifiedFirst tags P
    (labels.amplifiedIndex tags P (R.arithmeticTag_mem L exceptional N) i) = _ at hfirst
  change labels.amplifiedFirstDivisor tags P
    (labels.amplifiedIndex tags P (R.arithmeticTag_mem L exceptional N) i) = _ at hS₀
  change labels.amplifiedSecond tags P
    (labels.amplifiedIndex tags P (R.arithmeticTag_mem L exceptional N) i) = _ at hsecond
  change labels.amplifiedAllocation tags P
    (labels.amplifiedIndex tags P (R.arithmeticTag_mem L exceptional N) i) = _ at halloc
  change labels.amplifiedTag tags P
    (labels.amplifiedIndex tags P (R.arithmeticTag_mem L exceptional N) i) = _ at htag
  rw [OriginalArithmeticLabels.amplifiedIndex_first] at hfirst
  rw [OriginalArithmeticLabels.amplifiedIndex_firstDivisor] at hS₀
  rw [OriginalArithmeticLabels.amplifiedIndex_second] at hsecond
  rw [OriginalArithmeticLabels.amplifiedIndex_allocation] at halloc
  rw [OriginalArithmeticLabels.amplifiedIndex_tag] at htag
  exact ⟨R.rowPresent_of_live L exceptional N i,
    congrArg (fun v : Label K => v.1) hfirst, hS₀,
    congrArg (fun v : Label K => v.1) hsecond, halloc, htag⟩

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
  have ha : realCount (fun i : active => R.originalAmplifiedIndex L hcap exceptional N i.val = j) ≤
      realCount (fun i : R.liveLeaves L exceptional N =>
        R.originalAmplifiedIndex L hcap exceptional N i = j) :=
    realCount_injective Subtype.val Subtype.coe_injective (fun _ h => h)
  have hf := R.originalAmplifiedIndex_fibre_subpower L hcap δ₁ δ₂ B₀ hB hδ₁ hδ₂ hbox
    rows maskIdeal hmask0 mask hmaskN hN exceptional N j
  change realCount (fun i : active × (Bool × Bool) =>
    R.originalAmplifiedIndex L hcap exceptional N i.1.val = j) ≤ _
  rw [realCount_prod_left]
  have hcard : (Fintype.card (Bool × Bool) : ℝ) = 4 := by norm_num
  rw [hcard]
  calc
    _ ≤ 4 * realCount (fun i : R.liveLeaves L exceptional N =>
        R.originalAmplifiedIndex L hcap exceptional N i = j) :=
      mul_le_mul_of_nonneg_left ha (by norm_num)
    _ ≤ 4 * (2 * firstMaskConstant (K := K) B δ₁ hB hδ₁ *
        coordinateConstant (K := K) cap (Fintype.card Θ) dimension width B δ₂ hB hδ₂ *
          Z ^ (δ₁ + δ₂)) := mul_le_mul_of_nonneg_left hf (by norm_num)
    _ = _ := by ring

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
  have ha : realCount (fun i : active => R.originalAmplifiedIndex L hcap exceptional N i.val.1 = j) ≤
      realCount (fun i : (R.liveLeaves L exceptional N) × (Bool × Bool) =>
        R.originalAmplifiedIndex L hcap exceptional N i.1 = j) :=
    realCount_injective Subtype.val Subtype.coe_injective (fun _ h => h)
  have hf := R.originalAmplifiedIndex_fibre_subpower L hcap δ₁ δ₂ B₀ hB hδ₁ hδ₂ hbox
    rows maskIdeal hmask0 mask hmaskN hN exceptional N j
  refine ha.trans ?_
  rw [realCount_prod_left]
  have hcard : (Fintype.card (Bool × Bool) : ℝ) = 4 := by norm_num
  rw [hcard]
  exact (mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by ring)

end ActualFirstSource.SecondStages

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalFiniteFibre.realCount_sigma_fixed_le
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalFiniteFibre.realCount_fourSource_fixed_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.originalAmplifiedIndex_fibre_subpower
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.originalAmplifiedIndex_active_rectangles_fibre_subpower
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.originalAmplifiedIndex_retained_rectangles_fibre_subpower
