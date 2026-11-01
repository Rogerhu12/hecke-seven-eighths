import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalAllocatedCosts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityProfileMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondSourceNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCoefficientNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondFactorIdentification
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonNormalization

/-!
# Each actual normalized child pays its own harmonic label weight

The three arithmetic costs are chosen by `withCosts`; the frozen scalar
comes from the second divisor's own original central normalizations.
The original Gauss normalizers, the common correlation, the exact child
width and one slot-removal loss then leave the inverse common radical
and the inverse second divisor.  No finite-family mass bound is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis LocalFiniteSums CommonSupportMass

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ} {ω ψ : HeckeCharacter F}
variable {V H HL HR : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k l : ℕ}

namespace ActualAllocatedSource.Calibration.NormalizedCapacityData.Child

variable {s : ActualAllocatedSource A V H k} {D : s.Calibration (σ := σ) ω ψ}
variable {G : D.NormalizedCapacityData} (out : G.Child)

/-- Bound each selected prime factor, keep its actual removal set, and
combine the exact loss exponent with the unchanged child width. -/
theorem weight_width_le
    (Z rowCost scalarCost fiberCost primeCost budget : ℝ) (cap : ℕ)
    (hZ : 1 ≤ Z) (hbase : s.base = Z)
    (hrow : D.rowBound ≤ rowCost) (hscalar : D.scalarBound ≤ scalarCost)
    (hfiber : (D.fiberBound : ℝ) ≤ fiberCost)
    (hprime : ∀ i, G.primeBound i ≤ primeCost) (hprimeOne : 1 ≤ primeCost)
    (hcap : s.allocation.keep.card ≤ cap)
    (hbudget : D.parameters.m + D.parameters.q + G.exponent ≤ budget) :
    out.weight * Z ^ (out.parameters.m + out.parameters.q) ≤
      rowCost * scalarCost * fiberCost * primeCost ^ cap * Z ^ budget := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hrow0 : 0 ≤ rowCost := D.rowBound_nonneg.trans hrow
  have hscalar0 : 0 ≤ scalarCost := D.scalarBound_nonneg.trans hscalar
  have hfiber0 : 0 ≤ fiberCost := (Nat.cast_nonneg D.fiberBound).trans hfiber
  have hmass : D.mass ≤ rowCost * scalarCost * fiberCost :=
    mul_le_mul (mul_le_mul hrow hscalar D.scalarBound_nonneg hrow0)
      hfiber (Nat.cast_nonneg _) (mul_nonneg hrow0 hscalar0)
  have hprod : (∏ i ∈ out.removed, G.primeBound i) ≤ primeCost ^ cap :=
    selected_factor_product_le out.removed G.primeBound primeCost cap hprimeOne
      (by simpa only [Fintype.card_fin] using hcap)
      (fun i _ => G.primeBound_nonneg i) (fun i _ => hprime i)
  calc
    _ = D.mass * (∏ i ∈ out.removed, G.primeBound i) *
        Z ^ (D.parameters.m + D.parameters.q + G.exponent) := by
      rw [out.width_eq]
      unfold weight NormalizedCapacityData.loss
      simp only [hbase, Real.rpow_add hz]
      ring
    _ ≤ (rowCost * scalarCost * fiberCost) * primeCost ^ cap * Z ^ budget :=
      mul_le_mul
        (mul_le_mul hmass hprod (Finset.prod_nonneg fun i _ => G.primeBound_nonneg i)
          (mul_nonneg (mul_nonneg hrow0 hscalar0) hfiber0))
        (Real.rpow_le_rpow_of_exponent_le hZ hbudget)
        (Real.rpow_nonneg hz.le _) (by positivity)
    _ = _ := by ring

end ActualAllocatedSource.Calibration.NormalizedCapacityData.Child

namespace ActualAllocatedSource.Calibration.NormalizedCapacityData

variable {s : ActualAllocatedSource A V H k} {D : s.Calibration (σ := σ) ω ψ}
variable (G : D.NormalizedCapacityData)

/-- Bind the removal loss to the literal common-ideal logarithms.
The only additional budget is the displayed primitive clipping/mesh
error, which is chosen in the original margin schedule. -/
theorem exponent_le_common_allowance
    (Z w boundary ell δ : ℝ) (I J : Ideal (𝓞 F)) (hbase : s.base = Z)
    (hb₂ : G.b₂ = (idealLogLength Z I + idealLogLength Z J) / 2)
    (hp₂ : G.p₂ = idealLogLength Z (commonRadical I J))
    (hw : G.geometry.w = w) (hboundary : G.boundary = boundary) (hell : G.ell = ell)
    (herror : (G.supportError + (G.rawClipError +
        (Real.log G.leftAnnulus + Real.log G.rightAnnulus) / Real.log Z) + G.widthError) / 6 +
      D.parameters.κ * G.mesh ≤ δ) :
    G.exponent ≤ secondCommonChildAllowance Z w boundary ell I J + δ := by
  unfold exponent secondCommonChildAllowance
  rw [hbase, hb₂, hp₂, hw, hboundary, hell]
  linarith

theorem width_loss_budget_le
    (Z a₀ q wo krow g w boundary ell δ : ℝ) (I J T R : Ideal (𝓞 F))
    (hbase : s.base = Z)
    (hwidth : D.parameters.m + D.parameters.q ≤ secondCommonChildWidth Z a₀ q wo krow g I J T R)
    (hb₂ : G.b₂ = (idealLogLength Z I + idealLogLength Z J) / 2)
    (hp₂ : G.p₂ = idealLogLength Z (commonRadical I J))
    (hw : G.geometry.w = w) (hboundary : G.boundary = boundary) (hell : G.ell = ell)
    (herror : (G.supportError + (G.rawClipError +
        (Real.log G.leftAnnulus + Real.log G.rightAnnulus) / Real.log Z) + G.widthError) / 6 +
      D.parameters.κ * G.mesh ≤ δ) :
    D.parameters.m + D.parameters.q + G.exponent ≤
      secondCommonChildWidth Z a₀ q wo krow g I J T R +
        secondCommonChildAllowance Z w boundary ell I J + δ := by
  have h := G.exponent_le_common_allowance Z w boundary ell δ I J hbase
    hb₂ hp₂ hw hboundary hell herror
  linarith

end ActualAllocatedSource.Calibration.NormalizedCapacityData

variable {sL : ActualAllocatedSource A V HL k} {sR : ActualAllocatedSource A V HR l}
variable {DL : sL.Calibration (σ := σ) ω ψ} {DR : sR.Calibration (σ := σ) ω ψ}
variable {«GL» : DL.NormalizedCapacityData} {GR : DR.NormalizedCapacityData}

theorem SecondColumnFactors.normalizer_eq_extra {Ray : Type*}
    (P : SecondColumnFactors F Ray k) (N₁ N₂ : ℝ) (scale : Fin k → ℝ)
    (hleft : P.leftNormalizer = (Real.sqrt N₁ : ℂ)⁻¹)
    (hright : P.rightNormalizer = (Real.sqrt N₂ : ℂ)⁻¹)
    (hslot : ∀ i, P.slotNormalizer i = (Real.sqrt (scale i) : ℂ)⁻¹) :
    P.normalizer = extraGaussNormalizer N₁ N₂ scale := by
  unfold SecondColumnFactors.normalizer extraGaussNormalizer
  rw [hleft, hright]
  congr 1
  exact funext hslot

/-- Primitive field costs on both sides give the actual kernel scalar.
The square roots together pay each common cost once. -/
theorem normalizedCapacityPairWeight_le_costs
    (left : «GL».Child) (right : GR.Child) (originalLeft originalRight : ℂ)
    (Z parentWidth rowCost scalarCost fiberCost primeCost budget : ℝ) (cap : ℕ)
    (hZ : 1 ≤ Z) (hbaseL : sL.base = Z) (hbaseR : sR.base = Z)
    (hrowL : DL.rowBound ≤ rowCost) (hrowR : DR.rowBound ≤ rowCost)
    (hscalarL : DL.scalarBound ≤ scalarCost) (hscalarR : DR.scalarBound ≤ scalarCost)
    (hfiberL : (DL.fiberBound : ℝ) ≤ fiberCost) (hfiberR : (DR.fiberBound : ℝ) ≤ fiberCost)
    (hprimeL : ∀ i, «GL».primeBound i ≤ primeCost)
    (hprimeR : ∀ i, GR.primeBound i ≤ primeCost) (hprimeOne : 1 ≤ primeCost)
    (hcapL : sL.allocation.keep.card ≤ cap) (hcapR : sR.allocation.keep.card ≤ cap)
    (hbudgetL : DL.parameters.m + DL.parameters.q + «GL».exponent ≤ budget)
    (hbudgetR : DR.parameters.m + DR.parameters.q + GR.exponent ≤ budget) :
    normalizedCapacityPairWeight left right originalLeft originalRight Z parentWidth ≤
      ‖originalLeft‖ * ‖originalRight‖ *
        (rowCost * scalarCost * fiberCost * primeCost ^ cap) * Z ^ (budget - parentWidth) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  let Q := rowCost * scalarCost * fiberCost * primeCost ^ cap * Z ^ budget
  have hrow0 := DL.rowBound_nonneg.trans hrowL
  have hscalar0 := DL.scalarBound_nonneg.trans hscalarL
  have hfiber0 := (Nat.cast_nonneg DL.fiberBound).trans hfiberL
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hl := Real.sqrt_le_sqrt (left.weight_width_le Z rowCost scalarCost fiberCost
    primeCost budget cap hZ hbaseL hrowL hscalarL hfiberL hprimeL hprimeOne hcapL hbudgetL)
  have hr := Real.sqrt_le_sqrt (right.weight_width_le Z rowCost scalarCost fiberCost
    primeCost budget cap hZ hbaseR hrowR hscalarR hfiberR hprimeR hprimeOne hcapR hbudgetR)
  have hp : Real.sqrt (left.weight * Z ^ (left.parameters.m + left.parameters.q)) *
      Real.sqrt (right.weight * Z ^ (right.parameters.m + right.parameters.q)) ≤ Q := by
    apply (mul_le_mul hl hr (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq
    exact Real.mul_self_sqrt hQ
  calc
    _ = (‖originalLeft‖ * ‖originalRight‖) *
        (Real.sqrt (left.weight * Z ^ (left.parameters.m + left.parameters.q)) *
          Real.sqrt (right.weight * Z ^ (right.parameters.m + right.parameters.q))) /
          Z ^ parentWidth := by
      rw [Real.sqrt_mul left.weight_nonneg, Real.sqrt_mul right.weight_nonneg]
      unfold normalizedCapacityPairWeight
      ring
    _ ≤ (‖originalLeft‖ * ‖originalRight‖) * Q / Z ^ parentWidth :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (Real.rpow_nonneg hz.le _)
    _ = _ := by
      dsimp only [Q]
      rw [Real.rpow_sub hz]
      ring

section CommonRow

variable [IsPrincipalIdealRing A.R]

/-- The row bound uses the actual orbital radius and the proved
gcd/unit-radical correlation majorant. -/
def secondCommonRowCost (r : {r : ℝ // 0 < r}) (mask : Finset (HeightOneSpectrum A.R))
    (D E T : Ideal (𝓞 F)) : ℝ :=
  ‖secondOrbitalScalar (K := F) (S := A.Sf) r mask‖ *
    ((Ideal.absNorm (gcd D E) : ℝ) / (Ideal.absNorm T : ℝ)) /
      (Real.sqrt (Ideal.absNorm D : ℝ) * Real.sqrt (Ideal.absNorm E : ℝ))

theorem secondCommonRowCost_nonneg (r : {r : ℝ // 0 < r})
    (mask : Finset (HeightOneSpectrum A.R)) (D E T : Ideal (𝓞 F)) :
    0 ≤ secondCommonRowCost (A := A) r mask D E T := by
  unfold secondCommonRowCost
  positivity

/-- A genuine original row has this cost on its fixed unit-radical
label.  The complete correlation estimate is proved by the original
local table; only the remaining single phase has a norm premise. -/
theorem FirstCommonCharacterBlock.original_row_cost_bound
    {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
    {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
    {DE : Ideal (𝓞 F) × Ideal (𝓞 F)}
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (r : {r : ℝ // 0 < r}) (mask : Finset (HeightOneSpectrum A.R))
    (phase : ℂ) (hphase : ‖phase‖ ≤ 1) (a d : A.R)
    (ha : A.Generates (primePowerProduct b.primes b.leftMultiplicity) a)
    (hd : A.Generates (primePowerProduct b.primes b.rightMultiplicity) d)
    (h : A.R) (T : Ideal (𝓞 F)) (hT : (b.secondUnitRadical C h).val = T) :
    ‖(phase * secondOrbitalScalar (K := F) (S := A.Sf) r mask /
        ((Real.sqrt (Ideal.absNorm DE.1 : ℝ) : ℂ) *
          (Real.sqrt (Ideal.absNorm DE.2 : ℝ) : ℂ))) *
      b.secondCorrelation (σ := σ) a d ha hd h‖ ≤
      secondCommonRowCost (A := A) r mask DE.1 DE.2 T := by
  have hc := b.secondCorrelation_norm_le C a d ha hd h
  rw [hT] at hc
  have hp := mul_le_of_le_one_left
    (norm_nonneg (secondOrbitalScalar (K := F) (S := A.Sf) r mask)) hphase
  have hden : 0 ≤ Real.sqrt (Ideal.absNorm DE.1 : ℝ) *
      Real.sqrt (Ideal.absNorm DE.2 : ℝ) := by positivity
  have hq := div_le_div_of_nonneg_right hp hden
  simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (mul_le_mul hq hc (norm_nonneg _)
    (div_nonneg (norm_nonneg _) hden)).trans_eq
  unfold secondCommonRowCost
  ring

/-- All original normalizations cancel against the explicit numerical
child budget, leaving the same second common-support radical. -/
theorem secondCommonRowCost_budget_le
    (Z : ℝ) (hZ : 1 < Z) (a₀ q wo w boundary krow g ell NL NR : ℝ)
    (r : {r : ℝ // 0 < r}) (mask : Finset (HeightOneSpectrum A.R))
    (D E T R : Ideal (𝓞 F)) (hD : D ≠ 0) (hE : E ≠ 0) (hT : T ≠ 0)
    (hrow : Z ^ (-krow - g) ≤
      r.val * (sIntegerElementNorm F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
        (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) mask)).val)
    (hcentral : Z ^ a₀ ≤ Real.sqrt NL * Real.sqrt NR) :
    (1 / (Real.sqrt NL * Real.sqrt NR)) * secondCommonRowCost (A := A) r mask D E T *
      Z ^ (secondCommonChildWidth Z a₀ q wo krow g D E T R +
        secondCommonChildAllowance Z w boundary ell D E) ≤
      orbitalFieldFactor F * Z ^ (a₀ + q + wo + w + boundary + ell) /
        (Ideal.absNorm (commonRadical D E) : ℝ) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hs := second_source_normalized_scalar_bound Z hZ a₀ krow g NL NR r mask hrow hcentral
  have hc : 0 ≤ (Ideal.absNorm (gcd D E) : ℝ) / (Ideal.absNorm T : ℝ) := by positivity
  have hd : 0 ≤ Real.sqrt (Ideal.absNorm D : ℝ) * Real.sqrt (Ideal.absNorm E : ℝ) := by positivity
  have hp := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hs hc) hd)
    (Real.rpow_nonneg hz.le
      (secondCommonChildWidth Z a₀ q wo krow g D E T R +
        secondCommonChildAllowance Z w boundary ell D E))
  have he := second_actual_scalar_budget_identity Z hZ (orbitalFieldFactor F)
    a₀ q wo w (boundary + ell) krow g 0 D E T R hD hE hT
  have hb : secondCommonChildAllowance Z w (boundary + ell) 0 D E =
      secondCommonChildAllowance Z w boundary ell D E := by
    unfold secondCommonChildAllowance
    ring
  rw [hb] at he
  simp only [neg_zero, Real.rpow_zero, one_mul] at he
  calc
    _ = (‖secondOrbitalScalar (K := F) (S := A.Sf) r mask‖ /
        (Real.sqrt NL * Real.sqrt NR) *
          ((Ideal.absNorm (gcd D E) : ℝ) / (Ideal.absNorm T : ℝ)) /
          (Real.sqrt (Ideal.absNorm D : ℝ) * Real.sqrt (Ideal.absNorm E : ℝ))) *
        Z ^ (secondCommonChildWidth Z a₀ q wo krow g D E T R +
          secondCommonChildAllowance Z w boundary ell D E) := by
      unfold secondCommonRowCost
      ring
    _ ≤ _ := hp
    _ = _ := by
      rw [he]
      congr 2
      ring

/-- A same-label bound for the actual child kernel scalar.  Its only
cost inputs are the separately chosen row/scalar/fiber factors, each
normalized prime bound, and the original numerical width ledger. -/
theorem normalizedCapacityPairWeight_second_harmonic
    (left : «GL».Child) (right : GR.Child) (originalLeft originalRight : ℂ)
    (Z : ℝ) (hZ : 1 < Z)
    (parentWidth a₀ q wo w boundary krow g ell NL NR δ ε : ℝ)
    (r : {r : ℝ // 0 < r}) (mask : Finset (HeightOneSpectrum A.R))
    (D E T R L : Ideal (𝓞 F)) (hD : D ≠ 0) (hE : E ≠ 0) (hT : T ≠ 0) (hL : L ≠ 0)
    (hrow : Z ^ (-krow - g) ≤
      r.val * (sIntegerElementNorm F (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
        (sIntegerMaskGenerator F (A.Sf : Set (HeightOneSpectrum (𝓞 F))) mask)).val)
    (hcentral : Z ^ a₀ ≤ Real.sqrt NL * Real.sqrt NR)
    (hnormalizers : ‖originalLeft‖ * ‖originalRight‖ =
      1 / (Real.sqrt NL * Real.sqrt NR))
    (frozenCost fiberCost primeCost : ℝ) (cap : ℕ) (hfrozen : 1 ≤ frozenCost)
    (hbaseL : sL.base = Z) (hbaseR : sR.base = Z)
    (hrowL : DL.rowBound ≤ secondCommonRowCost (A := A) r mask D E T)
    (hrowR : DR.rowBound ≤ secondCommonRowCost (A := A) r mask D E T)
    (hscalarL : DL.scalarBound ≤ frozenCost ^ cap / (Ideal.absNorm L : ℝ))
    (hscalarR : DR.scalarBound ≤ frozenCost ^ cap / (Ideal.absNorm L : ℝ))
    (hfiberL : (DL.fiberBound : ℝ) ≤ fiberCost) (hfiberR : (DR.fiberBound : ℝ) ≤ fiberCost)
    (hprimeL : ∀ i, «GL».primeBound i ≤ primeCost)
    (hprimeR : ∀ i, GR.primeBound i ≤ primeCost) (hprime : 1 ≤ primeCost)
    (hcapL : sL.allocation.keep.card ≤ cap) (hcapR : sR.allocation.keep.card ≤ cap)
    (hbudgetL : DL.parameters.m + DL.parameters.q + «GL».exponent ≤
      secondCommonChildWidth Z a₀ q wo krow g D E T R +
        secondCommonChildAllowance Z w boundary ell D E + δ)
    (hbudgetR : DR.parameters.m + DR.parameters.q + GR.exponent ≤
      secondCommonChildWidth Z a₀ q wo krow g D E T R +
        secondCommonChildAllowance Z w boundary ell D E + δ)
    (hparent : parentWidth = a₀ + q) (hreserve : w + boundary + δ ≤ ε) :
    normalizedCapacityPairWeight left right originalLeft originalRight Z parentWidth ≤
      (frozenCost ^ cap * fiberCost * primeCost ^ cap * orbitalFieldFactor F) *
        Z ^ (ε + wo + ell) /
          (Ideal.absNorm (commonRadical D E) : ℝ) / (Ideal.absNorm L : ℝ) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hfrozen0 : 0 ≤ frozenCost := zero_le_one.trans hfrozen
  have hprime0 : 0 ≤ primeCost := zero_le_one.trans hprime
  have hfiber0 : 0 ≤ fiberCost := (Nat.cast_nonneg DL.fiberBound).trans hfiberL
  let budget := secondCommonChildWidth Z a₀ q wo krow g D E T R +
    secondCommonChildAllowance Z w boundary ell D E
  let M := frozenCost ^ cap * fiberCost * primeCost ^ cap / (Ideal.absNorm L : ℝ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hcost := normalizedCapacityPairWeight_le_costs left right originalLeft originalRight
    Z parentWidth (secondCommonRowCost (A := A) r mask D E T)
    (frozenCost ^ cap / (Ideal.absNorm L : ℝ)) fiberCost primeCost (budget + δ) cap
    hZ.le hbaseL hbaseR hrowL hrowR hscalarL hscalarR hfiberL hfiberR hprimeL hprimeR
    hprime hcapL hcapR hbudgetL hbudgetR
  have hcommon := secondCommonRowCost_budget_le Z hZ a₀ q wo w boundary krow g ell NL NR
    r mask D E T R hD hE hT hrow hcentral
  calc
    _ ≤ ‖originalLeft‖ * ‖originalRight‖ *
        (secondCommonRowCost (A := A) r mask D E T *
          (frozenCost ^ cap / (Ideal.absNorm L : ℝ)) * fiberCost * primeCost ^ cap) *
        Z ^ (budget + δ - parentWidth) := hcost
    _ = M * ((1 / (Real.sqrt NL * Real.sqrt NR)) *
        secondCommonRowCost (A := A) r mask D E T * Z ^ budget) *
        Z ^ (δ - parentWidth) := by
      rw [hnormalizers, show budget + δ - parentWidth = budget + (δ - parentWidth) by ring,
        Real.rpow_add hz]
      dsimp only [M]
      ring
    _ ≤ M * (orbitalFieldFactor F * Z ^ (a₀ + q + wo + w + boundary + ell) /
        (Ideal.absNorm (commonRadical D E) : ℝ)) * Z ^ (δ - parentWidth) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcommon hM)
        (Real.rpow_nonneg hz.le _)
    _ = (frozenCost ^ cap * fiberCost * primeCost ^ cap * orbitalFieldFactor F) *
        Z ^ ((w + boundary + δ) + wo + ell) /
          (Ideal.absNorm (commonRadical D E) : ℝ) / (Ideal.absNorm L : ℝ) := by
      rw [show M * (orbitalFieldFactor F * Z ^ (a₀ + q + wo + w + boundary + ell) /
          (Ideal.absNorm (commonRadical D E) : ℝ)) * Z ^ (δ - parentWidth) =
        (M * orbitalFieldFactor F / (Ideal.absNorm (commonRadical D E) : ℝ)) *
          (Z ^ (a₀ + q + wo + w + boundary + ell) * Z ^ (δ - parentWidth)) by ring,
        ← Real.rpow_add hz,
        show (a₀ + q + wo + w + boundary + ell) + (δ - parentWidth) =
          (w + boundary + δ) + wo + ell by rw [hparent]; ring]
      dsimp only [M]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
          (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hfrozen0 _) hfiber0)
            (pow_nonneg hprime0 _)) (orbitalFieldFactor_nonneg F))) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)

end CommonRow

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.normalizedCapacityPairWeight_le_costs
#print axioms HeckeSkeleton.Moments.EngineStep.secondCommonRowCost_budget_le
#print axioms HeckeSkeleton.Moments.EngineStep.normalizedCapacityPairWeight_second_harmonic
