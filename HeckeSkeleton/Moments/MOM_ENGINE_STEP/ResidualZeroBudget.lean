import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondZeroDiagonal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ResidualTupleCount
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PoolSecondStage

/-!
# The genuine second zero diagonal after prime-power removal

The first theorem pays a finite tuple fibre once.  The actual residual
specialization then derives that fibre from the original whole factors
and their canonical prime-power quotients.  All scalar/profile hypotheses
remain pointwise, and the common-label sum is performed internally.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis MeasureTheory
open HeckePort.IdealMobiusDivisorSum HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable {ι κ : Type*} {fullI : ι → A.Exterior} {fullJ : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

/-- The full second source zero bound, allowing a finite tuple fibre. -/
theorem second_zero_diagonal_normalized_of_fibers
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Cbound : ℝ, 0 < Cbound ∧
    ∀ (C : A.GeneralArithmeticContext σ η hS) {ι κ : Type*}
      (left : Finset ι) (right : Finset κ)
      (fullI : ι → A.Exterior) (fullJ : κ → A.Exterior),
    ∀ blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val,
    ∀ (profiles : ι → κ → SchwartzMap V ℂ)
      (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf → HeckeGeneral.Characters.localDifferentExponent K v = 0)
      (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
      (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
      (factors : ι × κ → Fin k → Ideal (𝓞 K)) (multiplicity : ℕ),
    (∀ v, ((left ×ˢ right).filter (fun ij => factors ij = v)).card ≤ multiplicity) →
    (∀ ij ∈ left ×ˢ right, PowerfulDiagonal.tupleIdeal (factors ij) =
      (fullI ij.1).val * (fullJ ij.2).val) →
    ∀ N Amp : ℝ, 1 ≤ N → 0 ≤ Amp →
    (∀ ij ∈ left ×ˢ right,
      (Ideal.absNorm ((fullI ij.1).val * (fullJ ij.2).val) : ℝ) ≤ N) →
    (∀ i ∈ left, ∀ j ∈ right, profiles i j 0 = 0) →
    (∀ DE, ∀ i ∈ (blocks DE).leftColumns left, ∀ D ∈ M.powerset,
      IsCoprime (engineAllowedGenerator C (blocks DE).commonLeftIdeal * (blocks DE).leftGenerator i)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) →
    (∀ DE, ∀ j ∈ (blocks DE).rightColumns right, ∀ D ∈ M.powerset,
      IsCoprime (engineAllowedGenerator C (blocks DE).commonRightIdeal * (blocks DE).rightGenerator j)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) →
    (∀ v ∈ firstZeroPairs left right fullI fullJ,
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        A.exteriorNorm (fullI v.2.1) *
        (∑ D ∈ M.powerset, firstZeroDivisorWeight radius D) ≤ Amp / Real.sqrt N) →
    (∑ DE, ‖((blocks DE).secondFiniteSource hΓ hDiff C left right profiles M radius cutoff hcutoff).zeroTerm
      μv hDiff finiteTest‖) ≤ Cbound * multiplicity * Amp * N ^ ε := by
  obtain ⟨seminorms, C₀, hC₀, hzero⟩ :=
    second_zero_amplitude_uniform (σ := σ) hΓ μv finiteTest
  obtain ⟨Cdiag, hCdiag, hdiag⟩ :=
    common_label_powerful_normalized_sum_of_fibers (A := A) k ε hε
  refine ⟨seminorms, Cdiag * (1 + C₀), mul_pos hCdiag (by linarith), ?_⟩
  intro C ι κ left right fullI fullJ blocks profiles hDiff radius M cutoff hcutoff
    factors multiplicity hfiber hfactor N Amp hN hAmp hnorm hannular hleftmask hrightmask hprofile
  let pairs := firstZeroPairs left right fullI fullJ
  let amp := secondZeroPairAmplitude hΓ μv C left right fullI fullJ
    blocks profiles hDiff finiteTest radius M
  have hampnonneg (v : FirstZeroLabel left right fullI fullJ × (ι × κ)) : 0 ≤ amp v := norm_nonneg _
  have hmem (v) (hv : v ∈ pairs) := (mem_firstZeroPairs left right fullI fullJ v).mp hv
  have hblock (v) (hv : v ∈ pairs) :
      v.2.1 ∈ (blocks v.1).leftColumns left ∧
      v.2.2 ∈ (blocks v.1).rightColumns right ∧
      IsCoprime ((blocks v.1).leftResidual v.2.1).val ((blocks v.1).rightResidual v.2.2).val :=
    ((blocks v.1).mem_iff_label left right
      (commonSupportPool_support_eq left right (fun i => (fullI i).val)
        (fun j => (fullJ j).val) v.1.val v.1.property) _ _).mpr (hmem v hv)
  have hcoef (v) (hv : v ∈ pairs) : amp v ≤ (C₀ * Amp) / Real.sqrt N := by
    have hs : 0 ≤ seminorms.sup (schwartzSeminormFamily ℂ V ℂ)
        (profiles v.2.1 v.2.2) := apply_nonneg _ _
    have hb (D) (hD : D ∈ M.powerset) :
        ‖((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).transformedZero
          μv hDiff finiteTest radius D‖ ≤
        C₀ * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
          firstZeroDivisorWeight radius D * A.exteriorNorm (fullI v.2.1) := by
      unfold FirstCommonCharacterBlock.secondPair
      rw [ParentPeriodicPair.gated_transformedZero (A := A), if_pos (hblock v hv).2.2]
      have he := hzero ((blocks v.1).secondLeftIdeal v.2.1) ((blocks v.1).secondRightIdeal v.2.2)
        _ _ ((blocks v.1).secondLeft_generates C _) ((blocks v.1).secondRight_generates C _)
        (profiles v.2.1 v.2.2) (hannular _ (hmem v hv).1 _ (hmem v hv).2.1) hDiff radius D
        (hleftmask v.1 _ (hblock v hv).1 D hD) (hrightmask v.1 _ (hblock v hv).2.1 D hD)
      apply he.trans
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (mul_nonneg hC₀ hs) (firstZeroDivisorWeight_nonneg radius D))
      rw [(blocks v.1).secondLeftIdeal_eq left _ (hblock v hv).1,
        (blocks v.1).secondRightIdeal_eq right _ (hblock v hv).2.1]
      split_ifs
      · exact le_rfl
      · exact (A.exteriorNorm_pos _).le
    change ‖∑ D ∈ M.powerset,
      ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).transformedZero
        μv hDiff finiteTest radius D‖ ≤ _
    calc
      _ ≤ ∑ D ∈ M.powerset,
          ‖((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).transformedZero
            μv hDiff finiteTest radius D‖ := norm_sum_le _ _
      _ ≤ ∑ D ∈ M.powerset,
          C₀ * seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
            firstZeroDivisorWeight radius D * A.exteriorNorm (fullI v.2.1) :=
        Finset.sum_le_sum (fun D hD => hb D hD)
      _ = C₀ * (seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
          A.exteriorNorm (fullI v.2.1) * ∑ D ∈ M.powerset, firstZeroDivisorWeight radius D) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro D hD
        ring
      _ ≤ C₀ * (Amp / Real.sqrt N) := mul_le_mul_of_nonneg_left (hprofile v hv) hC₀
      _ = _ := by ring
  have hc := hdiag left right fullI fullJ factors multiplicity hfiber hfactor N (C₀ * Amp)
    hN (mul_nonneg hC₀ hAmp) hnorm (fun v => (amp v : ℂ))
    (by
      intro v hv hbad
      have hz : amp v = 0 := by
        change ‖∑ D ∈ M.powerset,
          ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).transformedZero
            μv hDiff finiteTest radius D‖ = 0
        have he : (∑ D ∈ M.powerset,
          ((blocks v.1).secondPair hΓ hDiff C profiles v.2.1 v.2.2).transformedZero
            μv hDiff finiteTest radius D) = 0 :=
          Finset.sum_eq_zero (fun D hD =>
            (blocks v.1).secondZero_of_not_powerful hΓ μv C hDiff finiteTest left right profiles
              v.2.1 (hblock v hv).1 v.2.2 (hblock v hv).2.1 hbad
              (hannular _ (hmem v hv).1 _ (hmem v hv).2.1) radius D
              (hleftmask v.1 _ (hblock v hv).1 D hD)
              (hrightmask v.1 _ (hblock v hv).2.1 D hD))
        rw [he, norm_zero]
      rw [hz, Complex.ofReal_zero])
    (by
      intro v hv
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hampnonneg v)] using hcoef v hv)
  have hreal : ‖∑ v ∈ pairs, (amp v : ℂ)‖ = ∑ v ∈ pairs, amp v := by
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (Finset.sum_nonneg (fun v _ => hampnonneg v))
  rw [hreal] at hc
  calc
    _ ≤ ∑ v ∈ pairs, amp v :=
      second_zero_blocks_le_pair_sum hΓ μv C left right fullI fullJ blocks profiles
        hDiff finiteTest radius M cutoff hcutoff
    _ ≤ Cdiag * multiplicity * (C₀ * Amp) * N ^ ε := hc
    _ = (Cdiag * C₀) * ((multiplicity : ℝ) * Amp * N ^ ε) := by ring
    _ ≤ (Cdiag * (1 + C₀)) * ((multiplicity : ℝ) * Amp * N ^ ε) := by
      apply mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith : C₀ ≤ 1 + C₀) hCdiag.le)
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hAmp)
        (Real.rpow_nonneg (zero_le_one.trans hN) _)
    _ = (Cdiag * (1 + C₀)) * multiplicity * Amp * N ^ ε := by ring


/-- Actual prime-power residual columns.  The only injection is that of
the original whole tuple; the residual tuple and its finite multiplicity
are constructed in the proof.  The constant and original seminorms are
chosen before the prime, the valuation, all columns and all profiles. -/
theorem actual_residual_second_zero_bound
    (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ seminorms : Finset (ℕ × ℕ), ∃ Cbound : ℝ, 0 < Cbound ∧
    ∀ (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
      (nLeft nRight : ℕ) {ι κ : Type*} (left : Finset ι) (right : Finset κ)
      (originalI : ι → A.Exterior) (originalJ : κ → A.Exterior)
      (RI : ∀ i, AmplifierResidualPresentation C p nLeft (originalI i))
      (RJ : ∀ j, AmplifierResidualPresentation C p nRight (originalJ j)),
    let fullI := fun i => (RI i).residual
    let fullJ := fun j => (RJ j).residual
    ∀ blocks : ∀ DE : FirstZeroLabel left right fullI fullJ,
      FirstCommonCharacterBlock fullI fullJ DE.val,
    ∀ (profiles : ι → κ → SchwartzMap V ℂ)
      (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
        HeckeGeneral.Characters.localDifferentExponent K v = 0)
      (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum A.R))
      (cutoff : ℝ) (hcutoff : 1 ≤ cutoff)
      (originalFactors : ι × κ → Fin k → A.Exterior),
    Set.InjOn (fun ij t => (originalFactors ij t).val) (left ×ˢ right : Set (ι × κ)) →
    (∀ ij ∈ left ×ˢ right,
      PowerfulDiagonal.tupleIdeal (fun t => (originalFactors ij t).val) =
        (originalI ij.1).val * (originalJ ij.2).val) →
    ∀ N Amp : ℝ, 1 ≤ N → 0 ≤ Amp →
    (∀ ij ∈ left ×ˢ right,
      (Ideal.absNorm ((fullI ij.1).val * (fullJ ij.2).val) : ℝ) ≤ N) →
    (∀ i ∈ left, ∀ j ∈ right, profiles i j 0 = 0) →
    (∀ DE, ∀ i ∈ (blocks DE).leftColumns left, ∀ D ∈ M.powerset,
      IsCoprime (engineAllowedGenerator C (blocks DE).commonLeftIdeal * (blocks DE).leftGenerator i)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) →
    (∀ DE, ∀ j ∈ (blocks DE).rightColumns right, ∀ D ∈ M.powerset,
      IsCoprime (engineAllowedGenerator C (blocks DE).commonRightIdeal * (blocks DE).rightGenerator j)
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) →
    (∀ v ∈ firstZeroPairs left right fullI fullJ,
      seminorms.sup (schwartzSeminormFamily ℂ V ℂ) (profiles v.2.1 v.2.2) *
        A.exteriorNorm (fullI v.2.1) *
        (∑ D ∈ M.powerset, firstZeroDivisorWeight radius D) ≤ Amp / Real.sqrt N) →
    (∑ DE, ‖((blocks DE).secondFiniteSource hΓ hDiff C left right profiles M radius cutoff hcutoff).zeroTerm
      μv hDiff finiteTest‖) ≤ Cbound * ((nLeft + nRight + 1) ^ k : ℕ) * Amp * N ^ ε := by
  obtain ⟨seminorms, Cbound, hCbound, hz⟩ :=
    second_zero_diagonal_normalized_of_fibers (σ := σ) (η := η) (hS := hS)
      (hΓ := hΓ) (μv := μv) finiteTest k ε hε
  refine ⟨seminorms, Cbound, hCbound, ?_⟩
  intro C p nLeft nRight ι κ left right originalI originalJ RI RJ
  dsimp only
  intro blocks profiles hDiff radius M cutoff hcutoff originalFactors hinj hproduct
    N Amp hN hAmp hnorm hannular hleftmask hrightmask hprofile
  let factors := fun ij => actualResidualFactorTuple C p (originalFactors ij)
  have hfiber (v) : ((left ×ˢ right).filter (fun ij => factors ij = v)).card ≤
      (nLeft + nRight + 1) ^ k := by
    apply actual_residual_tuple_fiber_card C p (left ×ˢ right) originalFactors
      (fun ij hij uv huv he => hinj (Finset.mem_product.mp hij)
        (Finset.mem_product.mp huv) he)
    intro ij hij
    have hs := actual_factor_valuation_sum p (originalFactors ij)
      (ExteriorIdealEuler.mul (originalI ij.1) (originalJ ij.2)) (hproduct ij hij)
    rw [primeExponent_exterior_mul, (RI ij.1).original_valuation,
      (RJ ij.2).original_valuation] at hs
    exact hs
  exact hz C left right (fun i => (RI i).residual) (fun j => (RJ j).residual)
    blocks profiles hDiff radius M cutoff hcutoff factors ((nLeft + nRight + 1) ^ k)
    hfiber (fun ij hij => actual_residual_pair_tuple_product C p (originalFactors ij)
      (originalI ij.1) (originalJ ij.2) (hproduct ij hij) (RI ij.1) (RJ ij.2))
    N Amp hN hAmp hnorm hannular hleftmask hrightmask hprofile

namespace FirstGaussPoolData

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {P : PowerScaleExteriorPool A bad Z ell eps}

/-- The factor data of the literal source used by `energy_eq_sources`.
This supplies the finite-fibre premise of the zero estimate directly
from the original whole-index encoding, for each of the errors 1/6/7. -/
theorem residual_source_pair_factors {ι : Type*} (d : FirstGaussPoolData C P ι)
    (p : ExteriorPrime A) (n k : ℕ) (c : ι → ℂ)
    (originalFactors : ι × ι → Fin k → A.Exterior)
    (hinj : Set.InjOn (fun ij t => (originalFactors ij t).val)
      (d.columns ×ˢ d.columns : Set (ι × ι)))
    (hproduct : ∀ ij ∈ d.columns ×ˢ d.columns,
      PowerfulDiagonal.tupleIdeal (fun t => (originalFactors ij t).val) =
        (d.ideal ij.1).val * (d.ideal ij.2).val) :
    let G := d.residualSource p n c
    let factors := fun ij : d.valuationColumns p n × d.valuationColumns p n =>
      actualResidualFactorTuple C p (originalFactors (ij.1.val, ij.2.val))
    (∀ ij ∈ G.columns ×ˢ G.columns, PowerfulDiagonal.tupleIdeal (factors ij) =
      (G.ideal ij.1).val * (G.ideal ij.2).val) ∧
    (∀ v, ((G.columns ×ˢ G.columns).filter (fun ij => factors ij = v)).card ≤
      (n + n + 1) ^ k) := by
  dsimp only
  have hmem (ij : d.valuationColumns p n × d.valuationColumns p n) :
      (ij.1.val, ij.2.val) ∈ d.columns ×ˢ d.columns :=
    Finset.mem_product.mpr ⟨(Finset.mem_filter.mp ij.1.property).1,
      (Finset.mem_filter.mp ij.2.property).1⟩
  constructor
  · intro ij hij
    exact actual_residual_pair_tuple_product C p (originalFactors (ij.1.val, ij.2.val))
      (d.ideal ij.1.val) (d.ideal ij.2.val) (hproduct _ (hmem ij))
      (d.residualPresentation p n ij.1) (d.residualPresentation p n ij.2)
  · intro v
    apply actual_residual_tuple_fiber_card C p
      ((d.residualSource p n c).columns ×ˢ (d.residualSource p n c).columns)
      (fun ij => originalFactors (ij.1.val, ij.2.val))
    · intro ij hij uv huv he
      have hp := hinj (Finset.mem_product.mp (hmem ij))
        (Finset.mem_product.mp (hmem uv)) he
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst hp)
      · exact Subtype.ext (congrArg Prod.snd hp)
    · intro ij hij
      have hs := actual_factor_valuation_sum p (originalFactors (ij.1.val, ij.2.val))
        (ExteriorIdealEuler.mul (d.ideal ij.1.val) (d.ideal ij.2.val)) (hproduct _ (hmem ij))
      rw [primeExponent_exterior_mul,
        (d.residualPresentation p n ij.1).original_valuation,
        (d.residualPresentation p n ij.2).original_valuation] at hs
      exact hs

end FirstGaussPoolData

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.second_zero_diagonal_normalized_of_fibers
#print axioms HeckeSkeleton.Moments.EngineStep.actual_residual_second_zero_bound
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.residual_source_pair_factors
