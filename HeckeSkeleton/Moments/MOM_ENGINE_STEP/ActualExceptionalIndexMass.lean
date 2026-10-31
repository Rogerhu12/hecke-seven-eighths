import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualParentFibre
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectParentFibre
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualArithmeticIndex
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AmplifiedExceptionalMass

/-!
# Exceptional dyad mass on the actual parent leaves

The original source computes the arithmetic carrier, its map and every
extra finite fibre. Original column and row data prove admissibility and
the fibre bound internally. The remaining input is the original upper
dyad window of the literal second divisor on each actual live leaf.

The arithmetic constant and, in the amplified case, the scale threshold
are selected before the scale, pool, source, children and divisor dyads.
Neither a total fibre bound nor a per-leaf mass estimate is assumed.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.MobiusRegroup HeckePort.Moments.Support
open CommonSupportMass UniqueFactorizationMonoid OriginalFiniteFibre

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K}

namespace OriginalArithmeticLabels

theorem amplifiedInnerDivisor_eq_allocation
    {I : Type*} [Fintype I] {cap : ℕ} (L : OriginalArithmeticLabels K I cap)
    (tag : I → Option (ℕ × ExteriorPrime A))
    {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
    (P : PowerScaleExteriorPool A bad Z ell eps)
    (j : AmplifiedCommonIndex P (L.mainCarrier tag) (L.errorCarrier tag)) :
    amplifiedInnerDivisor j = (L.amplifiedAllocation tag P j).1 := by
  cases j <;> rfl

end OriginalArithmeticLabels

variable {σ : K →+* ℂ}
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
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {Θ : Type*} [Fintype Θ]

section AmplifiedIdentity

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}

theorem ActualFirstSource.SecondStages.arithmeticIndex_innerDivisor
    (R : s.SecondStages (E := E) (hDiff := hDiff))
    (L : SourceCartesianAtlas s.columns s.ideal) {cap : ℕ} (hcap : L.slotCount ≤ cap)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.liveLeaves L exceptional N) :
    amplifiedInnerDivisor (R.arithmeticIndex L hcap exceptional N j) =
      R.innerDivisor L j.val := by
  calc
    _ = ((R.arithmeticLabels L hcap exceptional N).amplifiedAllocation
        (R.arithmeticTag L exceptional N) P (R.arithmeticIndex L hcap exceptional N j)).1 :=
      (R.arithmeticLabels L hcap exceptional N).amplifiedInnerDivisor_eq_allocation
        (R.arithmeticTag L exceptional N) P _
    _ = ((R.arithmeticLabels L hcap exceptional N).allocation j).1 :=
      congrArg (fun a : OriginalAllocationFingerprint K cap => a.1)
        (R.arithmeticIndex_allocation L hcap exceptional N j)
    _ = _ := R.arithmeticLabels_secondDivisor L hcap exceptional N j

end AmplifiedIdentity

section DirectIdentity

variable {Z : ℝ} {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}

theorem ActualDirectFirstSource.SecondStages.originalIndex_innerDivisor
    (R : s.SecondStages (E := E) (hDiff := hDiff))
    (L : SourceCartesianAtlas s.columns s.ideal) {cap : ℕ} (hcap : L.slotCount ≤ cap)
    (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
    (j : R.liveLeaves L exceptional N) :
    (R.originalIndex L hcap exceptional N j).2.2.2.1.val = R.innerDivisor L j.val :=
  R.arithmeticLabels_secondDivisor L hcap exceptional N j

end DirectIdentity

/-- The complete exceptional dyad sum on the actual amplified live
family. The index, branch admissibility and source fibre are all
constructed from the original data inside this theorem. -/
theorem actual_amplified_exceptional_index_mass
    (cap dimension width : ℕ) (normBox δ₁ δ₂ δ₃ ell eps Mmax Bmax : ℝ)
    (hbox : 0 ≤ normBox) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃)
    (hell : 0 < ell) (heps : 0 < eps) (hepsell : eps < ell)
    (hMmax : 0 ≤ Mmax) (hBmax : 0 ≤ Bmax) :
    ∃ Cex Z₀ : ℝ, 0 < Cex ∧ 1 < Z₀ ∧
    ∀ Z : ℝ, Z₀ ≤ Z → ∀ bad : Finset (HeightOneSpectrum (𝓞 K)),
    ∀ pool : PowerScaleExteriorPool A bad Z ell eps,
    ∀ M B : ℝ, 0 ≤ M → M ≤ Mmax → B ≤ Bmax →
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ) (a : RealParameters)
      (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X)
      (s : ActualFirstSource (E := W) hΓ μv C pool finiteTest centered d a t Y₁ Y₂ X hX)
      (R : s.SecondStages (E := E) (hDiff := hDiff))
      (L : SourceCartesianAtlas s.columns s.ideal) (hcap : L.slotCount ≤ cap)
      (exceptional : R.supported.gated.CoverHybridPredicates L) (N : s.Normalization)
      (B₀ : ℝ), B₀ + 7 * ell ≤ normBox →
    ∀ rows : R.supported.gated.OriginalFibreRows Θ dimension width normBox Z,
    ∀ oldMask : Ideal (𝓞 K), Squarefree oldMask → oldMask ≠ 0 →
      (∀ i ∈ s.columns, oldMask ∣ (s.ideal i).val) →
    ∀ maskIdeal : Ideal (𝓞 K), maskIdeal ≠ 0 →
      OriginalMaskPrimeData s.mask maskIdeal →
      (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ normBox →
      (∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ B₀) →
    ∀ (lower : R.supported.gated.liveLeaves L exceptional N → ℝ) (mesh : ℝ),
      (∀ i, (Ideal.absNorm (R.supported.gated.innerDivisor L i.val) : ℝ) ≤
        Z ^ (lower i + mesh)) →
      (∑ i : R.supported.gated.liveLeaves L exceptional N,
        amplifiedExceptionalDyadWeight pool M B
          ((R.supported.gated.arithmeticLabels L hcap exceptional N).mainCarrier
            (R.supported.gated.arithmeticTag L exceptional N))
          ((R.supported.gated.arithmeticLabels L hcap exceptional N).errorCarrier
            (R.supported.gated.arithmeticTag L exceptional N))
          (lower i) (R.supported.gated.arithmeticIndex L hcap exceptional N i)) ≤
        Cex * Z ^ (δ₁ + δ₂ + δ₃ + eps + mesh) / (Ideal.absNorm oldMask : ℝ) := by
  obtain ⟨Ca, Z₀, hCa, hZ₀, hm⟩ := uniform_amplified_exceptional_dyad_mass
    (A := A) (cap + 2) normBox δ₃ ell eps Mmax Bmax
    hbox hδ₃ hell heps hepsell hMmax hBmax
  let Cm := firstMaskConstant (K := K) normBox δ₁ hbox hδ₁
  let Cc := coordinateConstant (K := K) cap (Fintype.card Θ)
    dimension width normBox δ₂ hbox hδ₂
  have hCm : 0 < Cm := firstMaskConstant_pos _ _ _ _
  have hCc : 0 < Cc := coordinateConstant_pos _ _ _ _ _ _ _ _
  refine ⟨2 * Cm * Cc * Ca, Z₀, by positivity, hZ₀, ?_⟩
  intro Z hZ bad pool M B hM hMM hBB ω ψ centered d a t Y₁ Y₂ X hX s R L hcap
    exceptional N B₀ hB₀ rows oldMask hs hs0 hmask maskIdeal hmask0 mask hmaskN hN lower mesh hwindow
  have hz : 0 < Z := zero_lt_one.trans (hZ₀.trans_le hZ)
  have hNB₀ : B₀ ≤ normBox :=
    le_trans (le_add_of_nonneg_right (mul_nonneg (by norm_num) hell.le)) hB₀
  have hNB : ∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ normBox :=
    fun i hi => (hN i hi).trans
      (Real.rpow_le_rpow_of_exponent_le pool.base_gt_one.le hNB₀)
  have ha := R.arithmeticCarriers_admissible (L := L) (hcap := hcap) (N := N)
    exceptional normBox oldMask hs hmask hNB
  let multiplicity := 2 * Cm * Cc * Z ^ (δ₁ + δ₂)
  have hmult : 0 ≤ multiplicity := by dsimp only [multiplicity]; positivity
  have hcard (j : R.supported.gated.ArithmeticIndex L hcap exceptional N) :
      ((Finset.univ.filter (fun i : R.supported.gated.liveLeaves L exceptional N =>
        R.supported.gated.arithmeticIndex L hcap exceptional N i = j)).card : ℝ) ≤ multiplicity :=
    R.supported.gated.originalAmplifiedIndex_fibre_subpower L hcap δ₁ δ₂ B₀ hbox hδ₁ hδ₂ hB₀
      rows maskIdeal hmask0 mask hmaskN hN exceptional N j
  have hwin (i : R.supported.gated.liveLeaves L exceptional N) :
      (Ideal.absNorm (amplifiedInnerDivisor
        (R.supported.gated.arithmeticIndex L hcap exceptional N i)) : ℝ) ≤ Z ^ (lower i + mesh) := by
    rw [R.supported.gated.arithmeticIndex_innerDivisor L hcap exceptional N i]
    exact hwindow i
  have hsum := hm Z hZ bad pool M B hM hMM hBB oldMask hs hs0
    ((R.supported.gated.arithmeticLabels L hcap exceptional N).mainCarrier
      (R.supported.gated.arithmeticTag L exceptional N)) ha.1
    ((R.supported.gated.arithmeticLabels L hcap exceptional N).errorCarrier
      (R.supported.gated.arithmeticTag L exceptional N)) (fun n _ p _ => ha.2 n p)
    (R.supported.gated.arithmeticIndex L hcap exceptional N) multiplicity mesh hmult hcard lower hwin
  refine hsum.trans_eq ?_
  rw [show δ₁ + δ₂ + δ₃ + eps + mesh = (δ₁ + δ₂) + (δ₃ + eps + mesh) by ring,
    Real.rpow_add hz (δ₁ + δ₂) (δ₃ + eps + mesh)]
  dsimp only [multiplicity]
  ring

/-- The same actual-source assembly for the direct entrance. There is
no pool, tag count, density or amplification loss in the statement. -/
theorem actual_direct_exceptional_index_mass
    (cap dimension width : ℕ) (normBox δ₁ δ₂ δ₃ : ℝ)
    (hbox : 0 ≤ normBox) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) :
    ∃ Cex : ℝ, 0 < Cex ∧ ∀ Z : ℝ, 1 ≤ Z →
    ∀ {ω ψ : HeckeCharacter K} (centered : Bool) (d : MomentData K ω ψ) (a : RealParameters)
      (t Y₁ Y₂ X : ℝ) (hX : 1 ≤ X)
      (s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX)
      (R : s.SecondStages (E := E) (hDiff := hDiff))
      (L : SourceCartesianAtlas s.columns s.ideal) (hcap : L.slotCount ≤ cap)
      (exceptional : R.prepared.CoverHybridPredicates L) (N : s.Normalization),
    ∀ rows : R.prepared.OriginalFibreRows Θ dimension width normBox Z,
    ∀ oldMask : Ideal (𝓞 K), Squarefree oldMask → oldMask ≠ 0 →
      (∀ i ∈ s.columns, oldMask ∣ (s.ideal i).val) →
    ∀ maskIdeal : Ideal (𝓞 K), maskIdeal ≠ 0 →
      OriginalMaskPrimeData s.mask maskIdeal →
      (Ideal.absNorm maskIdeal : ℝ) ≤ Z ^ normBox →
      (∀ i ∈ s.columns, (Ideal.absNorm (s.ideal i).val : ℝ) ≤ Z ^ normBox) →
    ∀ (lower : R.prepared.liveLeaves L exceptional N → ℝ) (mesh : ℝ),
      (∀ i, (Ideal.absNorm (R.prepared.innerDivisor L i.val) : ℝ) ≤ Z ^ (lower i + mesh)) →
      (∑ i : R.prepared.liveLeaves L exceptional N,
        (R.prepared.arithmeticLabels L hcap exceptional N).carrier.exceptionalDyadWeight
          Z (lower i) (R.prepared.originalIndex L hcap exceptional N i)) ≤
        Cex * Z ^ (δ₁ + δ₂ + δ₃ + mesh) / (Ideal.absNorm oldMask : ℝ) := by
  obtain ⟨Ca, hCa, hm⟩ := TwoDivisorCommonBranch.uniform_exceptional_dyad_mass
    (K := K) (cap + 2) normBox δ₃ hbox hδ₃
  let Cm := firstMaskConstant (K := K) normBox δ₁ hbox hδ₁
  let Cc := coordinateConstant (K := K) cap (Fintype.card Θ)
    dimension width normBox δ₂ hbox hδ₂
  have hCm : 0 < Cm := firstMaskConstant_pos _ _ _ _
  have hCc : 0 < Cc := coordinateConstant_pos _ _ _ _ _ _ _ _
  refine ⟨2 * Cm * Cc * Ca, by positivity, ?_⟩
  intro Z hZ ω ψ centered d a t Y₁ Y₂ X hX s R L hcap exceptional N rows
    oldMask hs hs0 hmask maskIdeal hmask0 mask hmaskN hN lower mesh hwindow
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have ha := R.arithmeticLabels_admissible L hcap exceptional N normBox oldMask hs hmask hN
  let multiplicity := 2 * Cm * Cc * Z ^ (δ₁ + δ₂)
  have hmult : 0 ≤ multiplicity := by dsimp only [multiplicity]; positivity
  have hcard (j : R.prepared.ArithmeticIndex L hcap exceptional N) :
      ((Finset.univ.filter (fun i : R.prepared.liveLeaves L exceptional N =>
        R.prepared.originalIndex L hcap exceptional N i = j)).card : ℝ) ≤ multiplicity :=
    R.prepared.originalIndex_fibre_subpower L hcap δ₁ δ₂ hbox hδ₁ hδ₂ hZ
      rows maskIdeal hmask0 mask hmaskN hN exceptional N j
  have hwin (i : R.prepared.liveLeaves L exceptional N) :
      (Ideal.absNorm (R.prepared.originalIndex L hcap exceptional N i).2.2.2.1.val : ℝ) ≤
        Z ^ (lower i + mesh) := by
    rw [R.prepared.originalIndex_innerDivisor L hcap exceptional N i]
    exact hwindow i
  have hsum := hm Z hZ oldMask hs hs0 (R.prepared.arithmeticLabels L hcap exceptional N).carrier ha
    (R.prepared.originalIndex L hcap exceptional N) multiplicity mesh hmult hcard lower hwin
  refine hsum.trans_eq ?_
  rw [show δ₁ + δ₂ + δ₃ + mesh = (δ₁ + δ₂) + (δ₃ + mesh) by ring,
    Real.rpow_add hz (δ₁ + δ₂) (δ₃ + mesh)]
  dsimp only [multiplicity]
  ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.arithmeticIndex_innerDivisor
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.originalIndex_innerDivisor
#print axioms HeckeSkeleton.Moments.EngineStep.actual_amplified_exceptional_index_mass
#print axioms HeckeSkeleton.Moments.EngineStep.actual_direct_exceptional_index_mass
