import ThetaGlobal.GlobalProjectDigitProduct
import ThetaGlobal.GlobalProjectDigitSupport

/-!
# One-place exterior digit tables and their exact global finite product

`Input` contains only local formulas: the actual reference-vector
diagonal value, the nonzero residue digit average at one exterior place,
the zeroth local Weyl scalar, and the finite forward Fourier mask.
Its matrix argument is literally `A(x) W N(-s/g_p)` for the fixed allowed
generator.  It contains no global period, theta identity, frequency
reindexing, summability, or Mellin kernel identity.
`LocalDigitInput` constructs this certificate for the actual exterior
source; the fixed-source entry does not require it as an extra premise.

The zero digit is proved from compact invariance.  Marked averages are
then derived from the exact identity `q⁻¹ = delta₀ - digitMask₀`; they are
not independent choices.  Finally finite product algebra gives the
actual global exterior coefficient and its expansion over active sets.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section

namespace ThetaGlobal.GlobalProjectLocalDigitTables

open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources DedekindZetaZeroFree.OrbitExpansion
open DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.GlobalProjectDigitProduct ThetaGlobal.GlobalProjectSignedExtraction
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)
  {Q : AdmissibleFlatSources R} {T : Realization R Q}
  (D : SourceFactorization R Q T)

local notation "Sf" => (R.A.Sf : Set (HeightOneSpectrum (𝓞 F)))
local notation "P" => ThetaBranch.ExteriorPrime R.A

def skeletonPrime (p : P) : ExteriorPrime F Sf := ⟨p.val, p.property⟩

variable (Adata : ThetaArithmeticData F Sf)

def unitPhase (p : P) (x : Fˣ) : ℂ :=
  thetaPrimeCharacter F Sf Adata (skeletonPrime R p)
    (ThetaBranch.unitResidue p.val (ThetaBranch.localUnit R.A R.probe.allowed p x))

def sphericalValue (p : P) (x : Fˣ) : ℂ :=
  if ThetaBranch.order p.val x < 0 then 0 else
    sphericalDigit F Sf Adata (skeletonPrime R p) (ThetaBranch.order p.val x).toNat *
      unitPhase R Adata p x ^ (2 * (ThetaBranch.order p.val x).toNat)

def activeValue (p : P) (j : Fin 6) (x : Fˣ) : ℂ :=
  if ThetaBranch.order p.val x + 2 < 0 then 0 else
    localWeylScalar F Sf Adata (skeletonPrime R p) j
      (ThetaBranch.order p.val x + 2).toNat *
      unitPhase R Adata p x ^ localWeylExponent j (ThetaBranch.order p.val x + 2).toNat

def markedActive (p : P) (x : Fˣ) : ℂ :=
  if ThetaBranch.order p.val x = -2 then
    (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)⁻¹ *
      thetaGamma F Sf Adata (exteriorPrimeIdeal F Sf (skeletonPrime R p)) 2 *
      unitPhase R Adata p x ^ 2
  else 0

/-- The explicitly permitted local exterior digit boundary.  Every
quantified equality is at one fixed finite place, with the repository's
actual canonical representation and actual spherical reference vector. -/
structure Input : Prop where
  diagonal : ∀ (p : P) (x : Fˣ), D.exteriorValue R p x = sphericalValue R Adata p x
  nonzero_digits : ∀ (p : P) (j : Fin 6) (x : Fˣ)
      (L : ThetaDigitAverage.Residue p.val → 𝓞 F),
      (∀ t, Ideal.Quotient.mk p.val.asIdeal (L t) = t) →
      (∑ t ∈ Finset.univ.erase (0 : ThetaDigitAverage.Residue p.val),
        digitMask F Sf Adata (skeletonPrime R p) j t * localDigit R D p x (L t)) =
        activeValue R Adata p j x
  zeroth_weyl : ∀ (p : P),
      -localWeylScalar F Sf Adata (skeletonPrime R p) 0 0 =
        (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ)⁻¹ *
          thetaGamma F Sf Adata (exteriorPrimeIdeal F Sf (skeletonPrime R p)) 2
  forward_mask : ∀ (p : P) (j : Fin 6) (t : ThetaDigitAverage.Residue p.val),
      (∑ v : ThetaDigitAverage.Residue p.val,
        digitMask F Sf Adata (skeletonPrime R p) j v * Characters.psi R p (t * v)) =
        if t = 0 then 0 else thetaPrimeCharacter F Sf Adata (skeletonPrime R p) t ^ j.val

theorem zero_localDigit (p : P) (x : Fˣ) (s : 𝓞 F)
    (hs : Ideal.Quotient.mk p.val.asIdeal s = 0) :
    localDigit R D p x s = D.exteriorValue R p x := by
  have hm : s ∈ p.val.asIdeal := Ideal.Quotient.eq_zero_iff_mem.mp hs
  have hv := DigitMasks.valuation_le_exp_neg_one
    ((p.val.valuation_lt_one_iff_mem (K := F) s).mpr hm)
  let t : F := -(s : F) / (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F)
  have ht : algebraMap F (p.val.adicCompletion F) t ∈ KPTameCompact.O F p.val := by
    apply OrbitFrequencies.completion_integer_of_valuation_le_one
    change p.val.valuation F (-(s : F) /
      (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p) : F)) ≤ 1
    rw [map_div₀, Valuation.map_neg, DigitMasks.generator_valuation R p]
    exact (div_le_one₀ (by simp)).mpr hv
  have h := OrbitFrequencies.exterior_integral_digit_value R D p
    (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x) ⟨_, ht⟩
  rw [OrbitFrequencies.exterior_diagonal_slot] at h
  simpa only [localDigit, t, map_div₀, map_neg,
    IsScalarTower.algebraMap_apply (𝓞 F) F (p.val.adicCompletion F)] using h

theorem digitMask_zero (p : P) (j : Fin 6) :
    digitMask F Sf Adata (skeletonPrime R p) j 0 =
      if j.val = 0 then 1 - (p.val.asIdeal.absNorm : ℂ)⁻¹ else 0 := by
  by_cases hj : j.val = 0
  · simp [digitMask, hj]
  · have hz : -(j.val : ℤ) ≠ 0 := by omega
    simp [digitMask, hj, hz]

variable (H : Input R D Adata)

include H in
theorem ordinary_average (p : P) (j : Fin 6) (x : Fˣ)
    (L : ThetaDigitAverage.Residue p.val → 𝓞 F)
    (hL : ∀ t, Ideal.Quotient.mk p.val.asIdeal (L t) = t) :
    (∑ t : ThetaDigitAverage.Residue p.val,
      digitMask F Sf Adata (skeletonPrime R p) j t * localDigit R D p x (L t)) =
      (if j.val = 0 then 1 - (p.val.asIdeal.absNorm : ℂ)⁻¹ else 0) *
        sphericalValue R Adata p x + activeValue R Adata p j x := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ThetaDigitAverage.Residue p.val)),
    H.nonzero_digits p j x L hL, zero_localDigit R D p x (L 0) (hL 0),
    H.diagonal p x, digitMask_zero]
  ring

include H in
theorem neg_active_zero (p : P) (x : Fˣ) :
    -activeValue R Adata p 0 x = markedActive R Adata p x := by
  by_cases hx : ThetaBranch.order p.val x = -2
  · simp only [activeValue, markedActive, hx, Int.reduceNeg, Int.reduceAdd,
      Int.lt_irrefl, ↓reduceIte, Int.toNat_zero, localWeylExponent,
      Fin.val_zero, Nat.reduceSub, Nat.reduceMod, neg_mul]
    rw [H.zeroth_weyl]
  · rw [markedActive, if_neg hx]
    by_cases he : ThetaBranch.order p.val x + 2 < 0
    · simp [activeValue, he]
    · have hn : (ThetaBranch.order p.val x + 2).toNat ≠ 0 := by omega
      rw [activeValue, if_neg he,
        GlobalProjectFrequency.localWeylScalar_zero_digit_positive F Sf Adata _ _ hn]
      simp

include H in
theorem marked_average (p : P) (x : Fˣ)
    (L : ThetaDigitAverage.Residue p.val → 𝓞 F)
    (hL : ∀ t, Ideal.Quotient.mk p.val.asIdeal (L t) = t) :
    (∑ t : ThetaDigitAverage.Residue p.val,
      (p.val.asIdeal.absNorm : ℂ)⁻¹ * localDigit R D p x (L t)) =
      (p.val.asIdeal.absNorm : ℂ)⁻¹ * sphericalValue R Adata p x +
        markedActive R Adata p x := by
  calc
    _ = (∑ t : ThetaDigitAverage.Residue p.val,
        ((if t = 0 then 1 else 0) - digitMask F Sf Adata (skeletonPrime R p) 0 t) *
          localDigit R D p x (L t)) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [← GlobalProjectLiteralDigitWeights.marked_eq_delta_sub_zero_digit]
    _ = localDigit R D p x (L 0) -
        ∑ t : ThetaDigitAverage.Residue p.val,
          digitMask F Sf Adata (skeletonPrime R p) 0 t * localDigit R D p x (L t) := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      simp
    _ = _ := by
      rw [zero_localDigit R D p x (L 0) (hL 0), H.diagonal,
        ordinary_average R D Adata H p 0 x L hL]
      simp only [Fin.val_zero, ↓reduceIte]
      have ha := neg_active_zero R D Adata H p x
      linear_combination ha

def inactiveCoefficient (p : P) (j : Fin 6) (marked : Bool) (x : Fˣ) : ℂ :=
  (if marked then (p.val.asIdeal.absNorm : ℂ)⁻¹ else
    if j.val = 0 then 1 - (p.val.asIdeal.absNorm : ℂ)⁻¹ else 0) *
      sphericalValue R Adata p x

def activeCoefficient (p : P) (j : Fin 6) (marked : Bool) (x : Fˣ) : ℂ :=
  if marked then markedActive R Adata p x else activeValue R Adata p j x

include H in
theorem literal_local_average (p : P) (j : Fin 6) (marked : Bool) (x : Fˣ)
    (L : ThetaDigitAverage.Residue p.val → 𝓞 F)
    (hL : ∀ t, Ideal.Quotient.mk p.val.asIdeal (L t) = t) :
    (∑ t : ThetaDigitAverage.Residue p.val,
      (if marked then (p.val.asIdeal.absNorm : ℂ)⁻¹ else
        digitMask F Sf Adata (skeletonPrime R p) j t) * localDigit R D p x (L t)) =
      inactiveCoefficient R Adata p j marked x + activeCoefficient R Adata p j marked x := by
  cases marked with
  | false => exact ordinary_average R D Adata H p j x L hL
  | true => exact marked_average R D Adata H p x L hL

include H in
/-- The global digit coefficient is obtained by multiplying the local
tables on the exact auxiliary row.  Each prime uses its actual residue
lift, with the independent prescribed digit and mark tag. -/
theorem reverseCoefficient_literal_product (m : ThetaReflectionData.Row R.A)
    (j : GlobalProjectWeightedDigits.Places R m → Fin 6)
    (marked : GlobalProjectWeightedDigits.Places R m → Bool) (x : Fˣ) :
    reverseCoefficient R D m (GlobalProjectLiteralDigitWeights.tensorWeight R Adata m j marked) x =
      (∏ p : RowPrime R m,
        inactiveCoefficient R Adata (exteriorRowPrime R m p) (j p) (marked p) x +
          activeCoefficient R Adata (exteriorRowPrime R m p) (j p) (marked p) x) *
        offRowProduct R D m x := by
  rw [GlobalProjectLiteralDigitWeights.tensorWeight,
    reverseCoefficient_product R D m x]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  exact literal_local_average R D Adata H (exteriorRowPrime R m p) (j p) (marked p) x
    ((ThetaDigitAverage.residueLifts _).lift p)
    ((ThetaDigitAverage.residueLifts _).residue_lift p)

include H in
/-- Expansion over actual active local places, before the supported
rational frequencies are regrouped into the three independent ideals. -/
theorem reverseCoefficient_active_expansion (m : ThetaReflectionData.Row R.A)
    (j : GlobalProjectWeightedDigits.Places R m → Fin 6)
    (marked : GlobalProjectWeightedDigits.Places R m → Bool) (x : Fˣ) :
    reverseCoefficient R D m (GlobalProjectLiteralDigitWeights.tensorWeight R Adata m j marked) x =
      ∑ A : Finset (RowPrime R m),
        (∏ p ∈ A, activeCoefficient R Adata (exteriorRowPrime R m p) (j p) (marked p) x) *
        (∏ p ∈ Aᶜ, inactiveCoefficient R Adata (exteriorRowPrime R m p) (j p) (marked p) x) *
        offRowProduct R D m x := by
  rw [reverseCoefficient_literal_product R D Adata H]
  simp_rw [add_comm (inactiveCoefficient R Adata _ _ _ x)]
  rw [Fintype.prod_add, Finset.sum_mul]

include H in
theorem offRowProduct_literal (m : ThetaReflectionData.Row R.A) (x : Fˣ) :
    offRowProduct R D m x =
      ∏ᶠ p : P, if p ∈ exteriorRows R m then 1 else sphericalValue R Adata p x := by
  apply finprod_congr
  intro p
  simp only [H.diagonal]

end ThetaGlobal.GlobalProjectLocalDigitTables
