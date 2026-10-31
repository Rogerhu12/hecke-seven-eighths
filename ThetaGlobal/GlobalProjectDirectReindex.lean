import ThetaGlobal.GlobalProjectFrequencySeed
import ThetaGlobal.GlobalGeneratorPeriod
import DedekindZetaZeroFree.Theta.Unfolding.PrimeGeneratorFrequencyIndex

/-!
# The actual direct frequency series is indexed by squarefree/cube ideals

The exterior reference vector forces nonnegative valuations congruent to
zero or one modulo three.  The allowed local-class mask then leaves the
unique prescribed generator class for each squarefree/cube pair.  This
reindexes the actual high K-type series; no coefficient dictionary or
global frequency-bijection hypothesis is inserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section

namespace ThetaGlobal.GlobalProjectDirectReindex

open NumberField MeasureTheory DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.OrbitExpansion DedekindZetaZeroFree.ThetaProfileHaarSheets
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)
  {Q : AdmissibleFlatSources R} {T : Realization R Q}
  (D : SourceFactorization R Q T) (E : ExteriorCoefficients R Q T D)

local notation "P" => ThetaBranch.ExteriorPrime R.A
local notation "Sf" => (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))

def exteriorProduct (a : Fˣ) : ℂ := ∏ᶠ p : P, D.exteriorValue R p a

include E in
theorem exteriorProduct_eq_of_frequency_eq (a b : Fˣ)
    (h : (QuotientGroup.mk a : ThetaReflectionData.Frequency R.A) = QuotientGroup.mk b) :
    exteriorProduct R D a = exteriorProduct R D b := by
  let γ : ThetaReflectionData.rationalGamma R.A :=
    ⟨a / b, QuotientGroup.eq_iff_div_mem.mp h⟩
  have ha : a = γ.val * b := by simp [γ]
  rw [ha]
  exact GlobalProjectOrbitCoefficients.exteriorProduct_gamma R D E b γ

include E in
theorem exteriorProduct_supported (a : Fˣ) (ha : exteriorProduct R D a ≠ 0)
    (p : P) :
    0 ≤ ThetaBranch.order p.val a ∧
      (ThetaBranch.order p.val a % 3 = 0 ∨ ThetaBranch.order p.val a % 3 = 1) := by
  have hp : D.exteriorValue R p a ≠ 0 := by
    intro hz
    exact ha (finprod_eq_zero _ p hz
      (GlobalProjectForwardCoefficients.exteriorProduct_finite R D E a))
  rw [E.rational_exact] at hp
  unfold ThetaBranch.sphericalFactor sexticSphericalCoefficient at hp
  split_ifs at hp <;> simp_all <;> omega

include E in
theorem exteriorProduct_eq_prod (a : Fˣ) (s : Finset P)
    (hs : ∀ p ∉ s, ThetaBranch.order p.val a = 0) :
    exteriorProduct R D a = ∏ p ∈ s, D.exteriorValue R p a := by
  apply finprod_eq_prod_of_mulSupport_subset
  intro p hp
  by_contra hn
  apply hp
  beta_reduce
  rw [E.rational_exact]
  exact sphericalFactor_order_zero R p a (hs p hn)

include E in
/-- The CRT coefficient belongs to the preserved actual exterior data.
The high K-type replacement has not changed this exterior product. -/
theorem exteriorProduct_generator (c : ExteriorSquarefreeIdeal R.A.cS)
    (n : R.A.Exterior) :
    exteriorProduct R D (forwardGenerator R c n) =
      R.probe.coefficients.gammaTwo c /
        ((Real.sqrt (R.A.exteriorNorm c.val) : ℂ) * (R.A.exteriorNorm n : ℂ)) := by
  let s := ThetaBranch.CanonicalCoefficientProof.extSupport R.A c.val ∪
    ThetaBranch.CanonicalCoefficientProof.extSupport R.A n
  have hc (p : P) (hp : p ∉ s) : idealPrimeExponent p.val.asIdeal c.val.val = 0 := by
    apply ThetaBranch.CanonicalCoefficientProof.exp_zero
    exact fun h => hp (Finset.mem_union_left _
      (by simpa only [ThetaBranch.CanonicalCoefficientProof.mem_extSupport] using h))
  have hn (p : P) (hp : p ∉ s) : idealPrimeExponent p.val.asIdeal n.val = 0 := by
    apply ThetaBranch.CanonicalCoefficientProof.exp_zero
    exact fun h => hp (Finset.mem_union_right _
      (by simpa only [ThetaBranch.CanonicalCoefficientProof.mem_extSupport] using h))
  let b := ∏ p ∈ s, R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) ^
    (idealPrimeExponent p.val.asIdeal c.val.val + 3 * idealPrimeExponent p.val.asIdeal n.val)
  have he : (QuotientGroup.mk (forwardGenerator R c n) : ThetaReflectionData.Frequency R.A) =
      QuotientGroup.mk b := forwardGenerator_primeProduct R c n s hc hn
  rw [exteriorProduct_eq_of_frequency_eq R D E _ b he,
    exteriorProduct_eq_prod R D E b s (by
      intro p hp
      rw [← ThetaBranch.CanonicalCoordinateProof.order_eq_of_frequency_eq R.A _ _ he p,
        forwardGenerator_order, hc p hp, hn p hp]
      simp)]
  exact E.crt_product c n s
    (exterior_factorization R c.val s Finset.subset_union_left)
    (exterior_factorization R n s Finset.subset_union_right)

variable (θ : HeckeCharacter F) (C : FiniteFixedSource.Source R θ)
  (L : FiniteLocalHighK.Input R θ C)

local notation "DC" => C.projected.base.factorization
local notation "k" => QuotientGroup.mk' R.A.sixthPowers

theorem period_eq_of_frequency_eq
    (hS : conductorPlaces F θ ⊆ R.A.Sf) (u : R.A.UnitQuotient)
    (a b : Fˣ)
    (h : (QuotientGroup.mk a : ThetaReflectionData.Frequency R.A) = QuotientGroup.mk b) :
    GlobalTargetPeriod.period R θ u (R.A.diagonal a) =
      GlobalTargetPeriod.period R θ u (R.A.diagonal b) := by
  let γ : ThetaReflectionData.rationalGamma R.A :=
    ⟨a / b, QuotientGroup.eq_iff_div_mem.mp h⟩
  have ha : a = γ.val * b := by simp [γ]
  have hg : GlobalTargetPeriod.period R θ u (R.A.diagonal γ.val) = 1 := by
    obtain ⟨v, hv, he⟩ := Subgroup.mem_map.mp γ.property
    rw [← he]
    exact GlobalTargetPeriod.period_diagonal_unit_sixth R θ hS u ⟨v, hv⟩
  rw [ha, map_mul, map_mul, hg, one_mul]

variable (Adata : ThetaArithmeticData F ((R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))))
  (H : GlobalProjectLocalDigitTables.Input R (C.projected.base.factorization) Adata)
  (hS : conductorPlaces F θ ⊆ R.A.Sf)
  (u : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
  (j : GlobalProjectWeightedDigits.Places R m → Fin 6)
  (marked : GlobalProjectWeightedDigits.Places R m → Bool)

local notation "weight" => GlobalProjectLiteralDigitWeights.tensorWeight R Adata m j marked

include H hS in
theorem directTerm_eq_of_frequency_eq (w : InfinitePlace F) (l : PositiveAxis)
    (a b : Fˣ)
    (h : (QuotientGroup.mk a : ThetaReflectionData.Frequency R.A) = QuotientGroup.mk b) :
    GlobalProjectOrbitEvaluation.directTerm R θ C L u m weight w l a =
      GlobalProjectOrbitEvaluation.directTerm R θ C L u m weight w l b := by
  let γ : ThetaReflectionData.rationalGamma R.A :=
    ⟨a / b, QuotientGroup.eq_iff_div_mem.mp h⟩
  have ha : a = γ.val * b := by simp [γ]
  have hs : GlobalProjectForwardCoefficients.scalar R DC m weight a =
      GlobalProjectForwardCoefficients.scalar R DC m weight b := by
    rw [ha]
    exact GlobalProjectForwardCoefficients.scalar_gamma R DC Adata
      C.projected.base.exterior H m j marked b γ
  have hc : k (R.A.diagonal a) = k (R.A.diagonal b) :=
    congrArg (ThetaReflectionData.frequencyClass R.A) h
  have hq : ThetaSheetExactUnfolding.q R.A a = ThetaSheetExactUnfolding.q R.A b := by
    apply Subtype.ext
    exact congrArg (ThetaReflectionData.frequencyNorm R.A) h
  rw [GlobalProjectOrbitEvaluation.directTerm, GlobalProjectOrbitEvaluation.directTerm,
    hs, period_eq_of_frequency_eq R θ hS u a b h, hc, hq]

theorem directTerm_support (w : InfinitePlace F) (l : PositiveAxis)
    (ξ : ThetaReflectionData.Frequency R.A)
    (hξ : GlobalProjectOrbitEvaluation.directTerm R θ C L u m weight w l (Quotient.out ξ) ≠ 0) :
    ξ ∈ Set.range (forwardFrequency R) := by
  have hb : ThetaReflectionData.rationalClass R.A (Quotient.out ξ) ∈
      R.probe.correction.B := by
    by_contra hn
    have hn' : (QuotientGroup.mk (R.A.diagonal (Quotient.out ξ)) : R.A.V) ∉
        R.probe.correction.B := hn
    exact hξ (by simp [GlobalProjectOrbitEvaluation.directTerm, hn, hn'])
  have he : exteriorProduct R DC (Quotient.out ξ) ≠ 0 := by
    intro hz
    apply hξ
    change GlobalProjectDigitProduct.forwardCoefficient R m weight (Quotient.out ξ) *
      exteriorProduct R DC (Quotient.out ξ) * _ * _ * _ = 0
    rw [hz]
    simp
  obtain ⟨cn, hcn⟩ := forwardFrequency_exists R (Quotient.out ξ) hb
    (exteriorProduct_supported R DC C.projected.base.exterior _ he)
  exact ⟨cn, hcn.trans (Quotient.out_eq ξ)⟩

include H hS in
/-- Exact reindexing of the quotient series, including its zero terms. -/
theorem direct_frequency_reindex (w : InfinitePlace F) (l : PositiveAxis) :
    (∑' ξ : ThetaReflectionData.Frequency R.A,
      GlobalProjectOrbitEvaluation.directTerm R θ C L u m weight w l (Quotient.out ξ)) =
      ∑' cn : ForwardIndex R,
        GlobalProjectOrbitEvaluation.directTerm R θ C L u m weight w l
          (forwardGenerator R cn.1 cn.2) := by
  rw [← (forwardFrequency_injective R).tsum_eq
    (fun ξ => directTerm_support R θ C L Adata u m j marked w l ξ)]
  apply tsum_congr
  intro cn
  exact directTerm_eq_of_frequency_eq R θ C L Adata H hS u m j marked w l _ _
    (Quotient.out_eq (forwardFrequency R cn))

include H hS in
/-- Absolute convergence is preserved by the proved injective index map. -/
theorem direct_generator_norm_summable (w : InfinitePlace F) (l : PositiveAxis)
    (h : Summable (fun ξ : ThetaReflectionData.Frequency R.A =>
      ‖GlobalProjectOrbitEvaluation.directTerm R θ C L u m weight w l (Quotient.out ξ)‖)) :
    Summable (fun cn : ForwardIndex R =>
      ‖GlobalProjectOrbitEvaluation.directTerm R θ C L u m weight w l
        (forwardGenerator R cn.1 cn.2)‖) := by
  apply (h.comp_injective (forwardFrequency_injective R)).congr
  intro cn
  exact congrArg norm (directTerm_eq_of_frequency_eq R θ C L Adata H hS u m j marked w l _ _
    (Quotient.out_eq (forwardFrequency R cn)))

end ThetaGlobal.GlobalProjectDirectReindex
