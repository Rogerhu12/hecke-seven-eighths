import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualSourceImageKernelMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalProfileAtomBounds

/-!
# Original support windows and the two distinct mask roles

The original profile support bounds each plain ideal in both rectangles
and every selected prime occurrence. Multiplicativity then bounds the
same complete column ideal used by the canonical parent atlas, including
repeated slots. A fixed annulus threshold absorbs its constant before
the source, characters, labels or coefficients are selected.

The physical avoidance mask remains in the actual source and in its
finite-fibre count. It need not divide every original column. The final
harmonic estimate does not retain an inverse old-mask factor, so that
independent arithmetic parameter is chosen to be the unit ideal. No
physical mask, Poisson source, live leaf or normalized child is changed.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

namespace RawProfileWindow

variable {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window orders d amplitude)

include profiles

theorem original_left_norm_le_annulus (annulus scale t : ℝ)
    (hscale : 0 < scale) (ht : t ∈ heightDomain)
    (hwindow : window ⊆ Set.Iic annulus)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (hu : u ∈ rowDomain) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : I ∈ d.plainTest₁.support u t scale) :
    idealNorm K I ≤ annulus * scale := by
  have hrep : profiles.leftRep u t (idealNorm K I / scale) ≠ 0 := by
    simpa only [profiles.left_eq] using (d.plainTest₁.support_spec u t scale I).mp hI
  exact (div_le_iff₀ hscale).mp
    (hwindow (profiles.left_support u hu t ht hrep))

theorem original_right_norm_le_annulus (annulus scale t : ℝ)
    (hscale : 0 < scale) (ht : t ∈ heightDomain)
    (hwindow : window ⊆ Set.Iic annulus)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (hu : u ∈ rowDomain) (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : I ∈ d.plainTest₂.support u t scale) :
    idealNorm K I ≤ annulus * scale := by
  have hrep : profiles.rightRep u t (idealNorm K I / scale) ≠ 0 := by
    simpa only [profiles.right_eq] using (d.plainTest₂.support_spec u t scale I).mp hI
  exact (div_le_iff₀ hscale).mp
    (hwindow (profiles.right_support u hu t ht hrep))

end RawProfileWindow

/-- This threshold depends only on the fixed annulus, slot cap and
positive exponent loss. It precedes the actual source. -/
theorem original_annulus_power_threshold (cap : ℕ) (annulus loss : ℝ)
    (hloss : 0 < loss) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z → annulus ^ (cap + 2) ≤ Z ^ loss := by
  have hevent := (_root_.tendsto_rpow_atTop hloss).eventually
    (Filter.eventually_ge_atTop (annulus ^ (cap + 2)))
  obtain ⟨Z₁, hZ₁⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨max Z₁ 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro Z hZ
  exact hZ₁ Z ((le_max_left _ _).trans hZ)

namespace ParentRawAtoms

variable {A : SArithmeticData K} {Γ : Subgroup A.U}
variable {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ} {a : RealParameters}
variable {Z t Y₁ Y₂ : ℝ}
variable (raw : ParentRawAtoms
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) d a Z t Y₁ Y₂)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)} {amplitude : ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window orders d amplitude)

include profiles

/-- Both rectangles are bounded on the original union of their plain
supports. There is no assumption about the complete column product. -/
theorem original_leftColumns_norm_le (annulus : ℝ) (hannulus : 0 ≤ annulus)
    (hZ : 0 < Z) (hY₁ : 0 < Y₁) (hY₁le : Y₁ ≤ Z ^ a.n₁)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) (hI : I ∈ raw.leftColumns) :
    idealNorm K I ≤ annulus * Z ^ a.n₁ := by
  obtain ⟨u, hu, hI⟩ := Finset.mem_biUnion.mp hI
  rcases Finset.mem_union.mp hI with hI | hI
  · exact profiles.original_left_norm_le_annulus annulus (Z ^ a.n₁) t
      (Real.rpow_pos_of_pos hZ _) ht hwindow u (hrows u hu) I hI
  · exact (profiles.original_left_norm_le_annulus annulus Y₁ t hY₁ ht hwindow
      u (hrows u hu) I hI).trans (mul_le_mul_of_nonneg_left hY₁le hannulus)

theorem original_rightColumns_norm_le (annulus : ℝ) (hannulus : 0 ≤ annulus)
    (hZ : 0 < Z) (hY₂ : 0 < Y₂) (hY₂le : Y₂ ≤ Z ^ a.n₂)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) (hI : I ∈ raw.rightColumns) :
    idealNorm K I ≤ annulus * Z ^ a.n₂ := by
  obtain ⟨u, hu, hI⟩ := Finset.mem_biUnion.mp hI
  rcases Finset.mem_union.mp hI with hI | hI
  · exact profiles.original_right_norm_le_annulus annulus (Z ^ a.n₂) t
      (Real.rpow_pos_of_pos hZ _) ht hwindow u (hrows u hu) I hI
  · exact (profiles.original_right_norm_le_annulus annulus Y₂ t hY₂ ht hwindow
      u (hrows u hu) I hI).trans (mul_le_mul_of_nonneg_left hY₂le hannulus)

/-- The literal whole-ideal norm follows from the original individual
profile supports. Every original prime occurrence remains in the product. -/
theorem original_column_norm_le_annulus (annulus : ℝ) (hannulus : 0 ≤ annulus)
    (hZ : 0 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hY₁le : Y₁ ≤ Z ^ a.n₁) (hY₂le : Y₂ ≤ Z ^ a.n₂)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (v : raw.Column) (hv : v ∈ raw.exteriorColumns) :
    (Ideal.absNorm (raw.columnExterior v).val : ℝ) ≤
      annulus ^ (d.geometry.slotCount + 2) *
        Z ^ (a.n₁ + a.n₂ + d.geometry.totalLength) := by
  have hm := Finset.mem_product.mp (Finset.mem_filter.mp hv).1
  have hp := Finset.mem_product.mp hm.1
  have hleft := raw.original_leftColumns_norm_le profiles annulus hannulus hZ hY₁ hY₁le
    hrows ht hwindow v.1.1 hp.1
  have hright := raw.original_rightColumns_norm_le profiles annulus hannulus hZ hY₂ hY₂le
    hrows ht hwindow v.1.2 hp.2
  have hprime (i : Fin d.geometry.slotCount) :
      (Ideal.absNorm (v.2 i).asIdeal : ℝ) ≤
        annulus * Z ^ (d.geometry.slots i).length := by
    have hi := Fintype.mem_piFinset.mp hm.2 i
    have hrep : profiles.primeRep i t
        ((Ideal.absNorm (v.2 i).asIdeal : ℝ) / Z ^ (d.geometry.slots i).length) ≠ 0 := by
      simpa only [profiles.prime_eq] using
        ((d.geometry.slots i).support_spec t (Z ^ (d.geometry.slots i).length) (v.2 i)).mp hi
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp
      (hwindow (profiles.prime_support i t ht hrep))
  have hprod : (∏ i, (Ideal.absNorm (v.2 i).asIdeal : ℝ)) ≤
      ∏ i, annulus * Z ^ (d.geometry.slots i).length :=
    Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hprime i)
  calc
    _ = (idealNorm K v.1.1 * idealNorm K v.1.2) *
        ∏ i, (Ideal.absNorm (v.2 i).asIdeal : ℝ) := by
      rw [raw.columnExterior_val_of_mem v hv]
      simp only [columnIdeal, idealNorm, map_mul, map_prod, Nat.cast_mul, Nat.cast_prod]
    _ ≤ ((annulus * Z ^ a.n₁) * (annulus * Z ^ a.n₂)) *
        ∏ i, annulus * Z ^ (d.geometry.slots i).length :=
      mul_le_mul (mul_le_mul hleft hright (idealNorm_pos K _).le
        (mul_nonneg hannulus (Real.rpow_nonneg hZ.le _))) hprod
        (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _))
        (mul_nonneg (mul_nonneg hannulus (Real.rpow_nonneg hZ.le _))
          (mul_nonneg hannulus (Real.rpow_nonneg hZ.le _)))
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Real.rpow_sum_of_pos hZ]
      simp only [SlotGeometry.totalLength, Real.rpow_add hZ, pow_add]
      ring

/-- The fixed annulus threshold and original formal lengths give the
pure power window used by the actual arithmetic and fibre theorems. -/
theorem original_column_norm_le_power (cap : ℕ) (annulus loss : ℝ)
    (hannulus : 1 ≤ annulus) (hcap : d.geometry.slotCount ≤ cap)
    (hannulusZ : annulus ^ (cap + 2) ≤ Z ^ loss)
    (hZ : 0 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hY₁le : Y₁ ≤ Z ^ a.n₁) (hY₂le : Y₂ ≤ Z ^ a.n₂)
    (hrows : ∀ u ∈ pairedRows d a Z, u ∈ rowDomain)
    (ht : t ∈ heightDomain) (hwindow : window ⊆ Set.Iic annulus)
    (v : raw.Column) (hv : v ∈ raw.exteriorColumns) :
    (Ideal.absNorm (raw.columnExterior v).val : ℝ) ≤
      Z ^ (a.n₁ + a.n₂ + d.geometry.totalLength + loss) := by
  have hraw := raw.original_column_norm_le_annulus profiles annulus
    (zero_le_one.trans hannulus) hZ hY₁ hY₂ hY₁le hY₂le hrows ht hwindow v hv
  have hpower := (pow_le_pow_right₀ hannulus (Nat.add_le_add_right hcap 2)).trans hannulusZ
  exact (hraw.trans (mul_le_mul_of_nonneg_right hpower (Real.rpow_nonneg hZ.le _))).trans_eq
    (by rw [Real.rpow_add hZ]; ring)

end ParentRawAtoms
end HeckeSkeleton.Moments.EngineStep

namespace HeckeSkeleton.Moments.EngineStep.InternalMassAssembly

open NumberField IsDedekindDomain DedekindZetaZeroFree CommonSupportMass
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments ActualNormalizedPairFamily

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
  [MeasurableSpace (WithLp 2 (W × E))] [BorelSpace (WithLp 2 (W × E))]
variable {Θ : Type*} [Fintype Θ]
variable {ω ψ : HeckeCharacter K}

/-- The original physical mask controls only the actual finite fibres.
The independent harmonic parameter is the unit ideal, whose divisibility
is automatic. The complete source and its avoidance mask are unchanged. -/
theorem actual_direct_source_image_kernel_mass_physical_mask
    (cap dimension width J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ dWeight : ℕ)
    (B ε Cweight : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (hCweight : 0 < Cweight) :
    ∃ seminorms₁ seminorms₂ : Finset (ℕ × ℕ), ∃ Cmass : ℝ, 0 < Cmass ∧
    ∀ (Z : ℝ), 1 < Z → ∀ profile : ℝ, 1 ≤ profile →
    ∀ (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
      (centered : Bool) (d : MomentData K ω ψ) (a : RealParameters)
      (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X)
      (s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX)
      (R : s.SecondStages (E := E) (hDiff := hDiff))
      (L : SourceCartesianAtlas s.columns s.ideal) (hcap : L.slotCount ≤ cap)
      (exceptional : R.prepared.CoverHybridPredicates L) (N : s.Normalization),
    ∀ (families : (R.prepared.liveLeaves L exceptional N) →
        ActualNormalizedPairFamily A σ (WithLp 2 (W × E)) (Bool × Bool) ω ψ Z)
      (F₁ : (R.prepared.liveLeaves L exceptional N) × (Bool × Bool) → 𝓢(W, ℂ))
      (F₂ : (R.prepared.liveLeaves L exceptional N) × (Bool × Bool) → 𝓢(E, ℂ))
      (outer B₁ B₂ : (R.prepared.liveLeaves L exceptional N) × (Bool × Bool) → ℝ)
      (parentWidth : ℝ),
    ProfileWindows (combine families) Finset.univ F₁ F₂ outer B₁ B₂ profile
      cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ seminorms₁ seminorms₂ →
    ∀ (rows : R.prepared.OriginalFibreRows Θ dimension width B Z)
      (physicalMask : Ideal (𝓞 K)), physicalMask ≠ 0 →
      OriginalMaskPrimeData s.mask physicalMask →
      (Ideal.absNorm physicalMask : ℝ) ≤ Z ^ B →
      (∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B) →
      (∀ b : (combine families).active Finset.univ,
        outer b.val * (combine families).weight Finset.univ parentWidth b ≤
          (Cweight * profile ^ dWeight * Z ^ (ε / 4)) *
            (R.prepared.arithmeticLabels L hcap exceptional N).carrier.indexWeight
              ((R.prepared.arithmeticLabels L hcap exceptional N).rectangleIndex families b)) →
      (∀ b : (combine families).active Finset.univ,
        IsFiniteMeasure ((combine families).kernel Finset.univ
          (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b)) ∧
      (∑ b : (combine families).active Finset.univ,
        ((combine families).kernel Finset.univ
          (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b).real Set.univ) ≤
        Cmass * profile ^ totalProfileDegree cap dBL dBR dF₁ dF₂ dWeight 0 * Z ^ ε := by
  let Cf := kernelSourceFibreConstant K cap (Fintype.card Θ) dimension width B ε hB hε
  have hCf : 0 < Cf :=
    kernelSourceFibreConstant_pos K cap (Fintype.card Θ) dimension width B ε hB hε
  obtain ⟨s₁, s₂, Cmass, hCmass, hm⟩ :=
    direct_kernel_mass_of_pointwise_index (A := A) (σ := σ) (ω := ω) (ψ := ψ)
      (U := W) (E := E) cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ dWeight 0
      (cap + 2) B ε Cweight (4 * Cf) hB hε hCweight (by positivity)
  refine ⟨s₁, s₂, Cmass, hCmass, ?_⟩
  intro Z hZ profile hprofile finiteTest centered d a t Y₁ Y₂ X hX s R L hcap
    exceptional N families F₁ F₂ outer B₁ B₂ parentWidth windows
    rows physicalMask hmask0 mask hmaskN hN hweight
  have hadmissible := R.arithmeticLabels_admissible L hcap exceptional N
    B 1 squarefree_one (fun _ _ => one_dvd _) hN
  apply hm Z hZ profile hprofile (combine families) Finset.univ
    F₁ F₂ outer B₁ B₂ parentWidth windows 1 squarefree_one one_ne_zero
    (R.prepared.arithmeticLabels L hcap exceptional N).carrier hadmissible
    ((R.prepared.arithmeticLabels L hcap exceptional N).rectangleIndex families) hweight
  intro j
  have hf := R.prepared.normalized_image_kernel_fibre L hcap ε hB hε hZ.le
    rows physicalMask hmask0 mask hmaskN hN exceptional N families j
  simpa only [Cf, pow_zero, mul_one] using hf

/-- The same mask separation preserves the original pool and each
actual prime/valuation tag. Physical mask norms and source row codes
still enter the finite-fibre estimate; neither is replaced by a unit mask. -/
theorem actual_amplified_source_image_kernel_mass_physical_mask
    (cap dimension width J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ dWeight : ℕ)
    (B ε Cweight ell eps Mmax Bmax : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε) (hCweight : 0 < Cweight)
    (hell : 0 < ell) (heps : 0 < eps) (hepsell : eps < ell) (hepsε : eps ≤ ε / 4)
    (hMmax : 0 ≤ Mmax) (hBmax : 0 ≤ Bmax) :
    ∃ seminorms₁ seminorms₂ : Finset (ℕ × ℕ), ∃ Cmass Z₀ : ℝ, 0 < Cmass ∧ 1 < Z₀ ∧
    ∀ (Z : ℝ), Z₀ ≤ Z → ∀ profile : ℝ, 1 ≤ profile →
    ∀ (bad : Finset (HeightOneSpectrum (𝓞 K)))
      (pool : PowerScaleExteriorPool A bad Z ell eps)
      (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
      (centered : Bool) (d : MomentData K ω ψ) (a : RealParameters)
      (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X)
      (s : ActualFirstSource (E := W) hΓ μv C pool finiteTest centered d a t Y₁ Y₂ X hX)
      (R : s.SecondStages (E := E) (hDiff := hDiff))
      (L : SourceCartesianAtlas s.columns s.ideal) (hcap : L.slotCount ≤ cap)
      (exceptional : R.supported.gated.CoverHybridPredicates L) (N : s.Normalization),
    ∀ (families : (R.supported.gated.liveLeaves L exceptional N) →
        ActualNormalizedPairFamily A σ (WithLp 2 (W × E)) (Bool × Bool) ω ψ Z)
      (F₁ : (R.supported.gated.liveLeaves L exceptional N) × (Bool × Bool) → 𝓢(W, ℂ))
      (F₂ : (R.supported.gated.liveLeaves L exceptional N) × (Bool × Bool) → 𝓢(E, ℂ))
      (outer B₁ B₂ : (R.supported.gated.liveLeaves L exceptional N) × (Bool × Bool) → ℝ)
      (parentWidth : ℝ),
    ProfileWindows (combine families) Finset.univ F₁ F₂ outer B₁ B₂ profile
      cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ seminorms₁ seminorms₂ →
    ∀ (B₀ : ℝ), B₀ + 7 * ell ≤ B →
    ∀ (rows : R.supported.gated.OriginalFibreRows Θ dimension width B Z)
      (physicalMask : Ideal (𝓞 K)), physicalMask ≠ 0 →
      OriginalMaskPrimeData s.mask physicalMask →
      (Ideal.absNorm physicalMask : ℝ) ≤ Z ^ B →
      (∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B₀) →
      (∀ b : (combine families).active Finset.univ,
        outer b.val * (combine families).weight Finset.univ parentWidth b ≤
          (Cweight * profile ^ dWeight * Z ^ (ε / 4)) *
            amplifiedIndexWeight pool Mmax Bmax
              ((R.supported.gated.arithmeticLabels L hcap exceptional N).mainCarrier
                (R.supported.gated.arithmeticTag L exceptional N))
              ((R.supported.gated.arithmeticLabels L hcap exceptional N).errorCarrier
                (R.supported.gated.arithmeticTag L exceptional N))
              ((R.supported.gated.arithmeticLabels L hcap exceptional N).rectangleAmplifiedIndex
                families pool (R.supported.gated.arithmeticTag L exceptional N)
                (R.supported.gated.arithmeticTag_mem L exceptional N) b)) →
      (∀ b : (combine families).active Finset.univ,
        IsFiniteMeasure ((combine families).kernel Finset.univ
          (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b)) ∧
      (∑ b : (combine families).active Finset.univ,
        ((combine families).kernel Finset.univ
          (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b).real Set.univ) ≤
        Cmass * profile ^ totalProfileDegree cap dBL dBR dF₁ dF₂ dWeight 0 * Z ^ ε := by
  let Cf := kernelSourceFibreConstant K cap (Fintype.card Θ) dimension width B ε hB hε
  have hCf : 0 < Cf :=
    kernelSourceFibreConstant_pos K cap (Fintype.card Θ) dimension width B ε hB hε
  obtain ⟨s₁, s₂, Cmass, Z₀, hCmass, hZ₀, hm⟩ :=
    amplified_kernel_mass_of_pointwise_index (A := A) (σ := σ) (ω := ω) (ψ := ψ)
      (U := W) (E := E) cap J₁₁ J₁₂ J₂₁ J₂₂ dBL dBR dF₁ dF₂ dWeight 0
      (cap + 2) B ε Cweight (4 * Cf) ell eps Mmax Bmax hB hε hCweight
      (by positivity) hell heps hepsell hepsε hMmax hBmax
  refine ⟨s₁, s₂, Cmass, Z₀, hCmass, hZ₀, ?_⟩
  intro Z hZ profile hprofile bad pool finiteTest centered d a t Y₁ Y₂ X hX s R L hcap
    exceptional N families F₁ F₂ outer B₁ B₂ parentWidth windows
    B₀ hbox rows physicalMask hmask0 mask hmaskN hN hweight
  have hZ1 : 1 < Z := hZ₀.trans_le hZ
  have hB₀ : B₀ ≤ B := by linarith
  have hN' : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B := by
    intro i hi
    exact (hN i hi).trans (Real.rpow_le_rpow_of_exponent_le hZ1.le hB₀)
  have hadmissible := R.arithmeticCarriers_admissible L hcap N exceptional
    B 1 squarefree_one (fun _ _ => one_dvd _) hN'
  apply hm Z hZ profile hprofile (combine families) Finset.univ
    F₁ F₂ outer B₁ B₂ parentWidth windows bad pool Mmax Bmax hMmax le_rfl le_rfl
    1 squarefree_one one_ne_zero
    ((R.supported.gated.arithmeticLabels L hcap exceptional N).mainCarrier
      (R.supported.gated.arithmeticTag L exceptional N)) hadmissible.1
    ((R.supported.gated.arithmeticLabels L hcap exceptional N).errorCarrier
      (R.supported.gated.arithmeticTag L exceptional N))
    (fun n _ p _ => hadmissible.2 n p)
    ((R.supported.gated.arithmeticLabels L hcap exceptional N).rectangleAmplifiedIndex
      families pool (R.supported.gated.arithmeticTag L exceptional N)
      (R.supported.gated.arithmeticTag_mem L exceptional N)) hweight
  intro j
  have hf := R.supported.gated.normalized_image_kernel_fibre L hcap ε B₀ hB hε
    hbox rows physicalMask hmask0 mask hmaskN hN exceptional N families j
  simpa only [Cf, pow_zero, mul_one] using hf

end HeckeSkeleton.Moments.EngineStep.InternalMassAssembly

#print axioms HeckeSkeleton.Moments.EngineStep.InternalMassAssembly.actual_direct_source_image_kernel_mass_physical_mask
#print axioms HeckeSkeleton.Moments.EngineStep.InternalMassAssembly.actual_amplified_source_image_kernel_mass_physical_mask

#print axioms HeckeSkeleton.Moments.EngineStep.original_annulus_power_threshold
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.original_column_norm_le_annulus
#print axioms HeckeSkeleton.Moments.EngineStep.ParentRawAtoms.original_column_norm_le_power
