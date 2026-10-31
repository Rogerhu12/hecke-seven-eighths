import ThetaGlobal.FiniteLocalHighK

/-!
# The actual two sheet Mellin transforms with a common normalization

The local pairs are multiplied using the actual polar and norm-sheet Haar
transport.  Both profiles are divided by the same source scalar and the
same reflected local constant.  Consequently the reflected Mellin
prefactor is one and the direct prefactor is the stored C₀.  Their quotient
is precisely the skeleton's reflectionMultiplier, including A₀^(2s).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
noncomputable section

namespace ThetaGlobal.FiniteNormalizedMellin

open NumberField MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.ThetaProfileHaarSheets
open DedekindZetaZeroFree.ThetaPositiveSheetMellin
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton.Global
open ThetaGlobal.FiniteLocalHighK ThetaGlobal.FiniteSheetMellin
open scoped Classical NumberField BigOperators

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (θ : HeckeCharacter F)
variable (C : FiniteFixedSource.Source R θ) (L : Input R θ C)

local notation "Sf" => (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
local notation "D" => C.projected.base.factorization
local notation "M" => FiniteLocalHighK.finiteMellinData R θ C L

def complexPlaceEquiv : InfinitePlace F ≃ {w : InfinitePlace F // w.IsComplex} where
  toFun w := ⟨w, R.A.complex_place w⟩
  invFun w := w.val
  left_inv _ := rfl
  right_inv _ := rfl

theorem gammaPair_product (s : ℂ) :
    (∏ w : InfinitePlace F, gammaPair R θ w s) = archGammaProduct F θ s :=
  Fintype.prod_equiv (complexPlaceEquiv R) _ _ (fun _ => rfl)

def directGammaProduct (s : ℂ) : ℂ :=
  ∏ v : {v : InfinitePlace F // v.IsComplex},
    Complex.Gamma ((archShift F θ v : ℂ) + s - Complex.I * archRadial F θ v + 1 / 6) *
      Complex.Gamma ((archShift F θ v : ℂ) + s - Complex.I * archRadial F θ v - 1 / 6)

theorem directGammaPair_product (s : ℂ) :
    (∏ w : InfinitePlace F, directGammaPair R θ w s) = directGammaProduct (F := F) θ s :=
  Fintype.prod_equiv (complexPlaceEquiv R) _ _ (fun _ => rfl)

def archProfile (reflected : Bool) : ∀ w : InfinitePlace F, w.Completionˣ → ℂ :=
  fun w => localProfile R θ (L.functional w) (L.vector w) w reflected

theorem direct_product_mellin (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re) :
    (∏ w : InfinitePlace F, ∫ z,
      archWeighted (archProfile R θ C L false) s w z
        ∂archHaar R.A w (C.transport.angularHaar w)) =
      directConstant R θ C L * (A₀ R θ C L : ℂ) ^ s * directGammaProduct θ s := by
  have h : (∏ w : InfinitePlace F, ∫ z,
      archWeighted (archProfile R θ C L false) s w z
        ∂archHaar R.A w (C.transport.angularHaar w)) =
      ∏ w : InfinitePlace F,
        L.directConstant w * (L.scale w : ℂ) ^ s * directGammaPair R θ w s :=
    Finset.prod_congr rfl (fun w _ => L.direct_mellin w s hs)
  rw [h, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    ← FiniteMellinRatio.ofReal_prod_cpow _ L.scale (fun w => (L.scale_pos w).le),
    directGammaPair_product] <;> rfl

theorem reflected_product_mellin (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re) :
    (∏ w : InfinitePlace F, ∫ z,
      archWeighted (archProfile R θ C L true) s w z
        ∂archHaar R.A w (C.transport.angularHaar w)) =
      reflectedConstant R θ C L * (A₀ R θ C L : ℂ) ^ s * archGammaProduct F θ s := by
  have h : (∏ w : InfinitePlace F, ∫ z,
      archWeighted (archProfile R θ C L true) s w z
        ∂archHaar R.A w (C.transport.angularHaar w)) =
      ∏ w : InfinitePlace F,
        L.reflectedConstant w * (L.scale w : ℂ) ^ s * gammaPair R θ w s :=
    Finset.prod_congr rfl (fun w _ => L.reflected_mellin w s hs)
  rw [h, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    ← FiniteMellinRatio.ofReal_prod_cpow _ L.scale (fun w => (L.scale_pos w).le),
    gammaPair_product] <;> rfl

def direct (v₀ : InfinitePlace F) : PositiveAxis → ℂ :=
  FiniteDirectMellin.directSheet R C.projected.cutoffs
    (reflectedConstant R θ C L)⁻¹ (archProfile R θ C L false) v₀

def reflected (u : R.A.UnitQuotient) (κ : SixthLocalClasses F Sf)
    (v₀ : InfinitePlace F) : PositiveAxis → ℂ :=
  FiniteSheetMellin.reflectedSheet R D θ
    (reflectedConstant R θ C L)⁻¹ (archProfile R θ C L true) u κ v₀

/-- The actual Fourier scalar is retained on both sides before the
common normalization; this identity does not drop it silently. -/
theorem direct_common_normalization (W : ℂ) (v₀ : InfinitePlace F)
    (t : PositiveAxis) :
    FiniteDirectMellin.directSheet R C.projected.cutoffs W
      (archProfile R θ C L false) v₀ t =
        (W * reflectedConstant R θ C L) * direct R θ C L v₀ t := by
  unfold direct FiniteDirectMellin.directSheet FiniteDirectMellin.directTensor
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_const_mul]
  field_simp [reflectedConstant_nonzero R θ C L]
  <;> ring

theorem reflected_common_normalization (W : ℂ) (u : R.A.UnitQuotient)
    (κ : SixthLocalClasses F Sf) (v₀ : InfinitePlace F) (t : PositiveAxis) :
    FiniteSheetMellin.reflectedSheet R D θ W
      (archProfile R θ C L true) u κ v₀ t =
        (W * reflectedConstant R θ C L) * reflected R θ C L u κ v₀ t := by
  unfold reflected FiniteSheetMellin.reflectedSheet FiniteSheetMellin.reflectedTensor
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_const_mul]
  field_simp [reflectedConstant_nonzero R θ C L]
  <;> ring

theorem direct_mellin (v₀ : InfinitePlace F) (s : ℂ)
    (hs : -(1 / 3 : ℝ) < s.re) :
    (∫ t : PositiveAxis, (t.val : ℂ) ^ s * direct R θ C L v₀ t ∂positiveHaar) =
      (M).C₀ * ((M).A₀ : ℂ) ^ s * directGammaProduct θ s := by
  have h := FiniteDirectMellin.direct_sheet_mellin R C.transport C.projected.cutoffs
    (reflectedConstant R θ C L)⁻¹ (archProfile R θ C L false) v₀ s
    (fun w => L.direct_integrable w s hs)
  rw [direct_product_mellin] at h
  · change _ = C₀ R θ C L * (A₀ R θ C L : ℂ) ^ s * _
    rw [direct, h]
    unfold C₀ FiniteMellinRatio.normalization
    ring
  · exact hs

theorem reflected_mellin (u : R.A.UnitQuotient) (κ : SixthLocalClasses F Sf)
    (v₀ : InfinitePlace F) (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re) :
    (∫ t : PositiveAxis, (t.val : ℂ) ^ s * reflected R θ C L u κ v₀ t ∂positiveHaar) =
      ((M).A₀ : ℂ) ^ s * finiteMellinFactor F Sf M u κ s * archGammaProduct F θ s := by
  have h := FiniteSheetMellin.reflected_sheet_mellin R D C.transport θ C.projected.cutoffs
    (C₀ R θ C L) (C₀_ne_zero R θ C L) (A₀ R θ C L) (A₀_pos R θ C L)
    (reflectedConstant R θ C L)⁻¹ (archProfile R θ C L true) u κ v₀ s hs
    (fun w => L.reflected_integrable w s hs)
  rw [reflected_product_mellin R θ C L s hs] at h
  change _ = (A₀ R θ C L : ℂ) ^ s * _ * _
  have hM : finiteMellinFactor F Sf M u κ s = finiteMellinFactor F Sf
      (ProjectedFiniteMellin.targetFiniteMellinData R C.projected.base.factorization C.transport
        (C₀ R θ C L) (C₀_ne_zero R θ C L) (A₀ R θ C L) (A₀_pos R θ C L) θ) u κ s := rfl
  rw [reflected, h, hM]
  field_simp [reflectedConstant_nonzero R θ C L]
  <;> ring

/-- The spectral quotient of the two *actual* normalized sheet profiles
is the literal target reflection multiplier, on the common Mellin strip. -/
theorem mellin_ratio (u : R.A.UnitQuotient) (κ : SixthLocalClasses F Sf)
    (v₀ : InfinitePlace F) (s : ℂ)
    (hs : -(1 / 3 : ℝ) < s.re) (hs' : s.re < 1 / 3) :
    (∫ t : PositiveAxis, (t.val : ℂ) ^ s * reflected R θ C L u κ v₀ t ∂positiveHaar) /
      (∫ t : PositiveAxis, (t.val : ℂ) ^ (-s) * direct R θ C L v₀ t ∂positiveHaar) =
        reflectionMultiplier F Sf M θ u κ s := by
  rw [reflected_mellin R θ C L u κ v₀ s hs,
    direct_mellin R θ C L v₀ (-s) (by simpa using neg_lt_neg hs')]
  let n₁ (v : {v : InfinitePlace F // v.IsComplex}) : ℂ :=
    Complex.Gamma ((archShift F θ v : ℂ) + s + Complex.I * archRadial F θ v + 1 / 6)
  let n₂ (v : {v : InfinitePlace F // v.IsComplex}) : ℂ :=
    Complex.Gamma ((archShift F θ v : ℂ) + s + Complex.I * archRadial F θ v - 1 / 6)
  let d₁ (v : {v : InfinitePlace F // v.IsComplex}) : ℂ :=
    Complex.Gamma ((archShift F θ v : ℂ) - s - Complex.I * archRadial F θ v + 1 / 6)
  let d₂ (v : {v : InfinitePlace F // v.IsComplex}) : ℂ :=
    Complex.Gamma ((archShift F θ v : ℂ) - s - Complex.I * archRadial F θ v - 1 / 6)
  have h := FiniteMellinRatio.same_vector_ratio
    (I := {v : InfinitePlace F // v.IsComplex})
    1 1 (M).C₀ 1 one_ne_zero one_ne_zero (M).C₀_ne_zero one_ne_zero
    (M).A₀ (M).A₀_pos s (finiteMellinFactor F Sf M u κ s)
    (fun v => n₁ v * n₂ v) (fun v => d₁ v * d₂ v)
  rw [FiniteMellinRatio.product_pair_quotient] at h
  simpa only [one_mul, mul_one, FiniteMellinRatio.normalization, div_one,
    reflectionMultiplier, archGammaProduct, directGammaProduct,
    n₁, n₂, d₁, d₂, sub_eq_add_neg] using h


end ThetaGlobal.FiniteNormalizedMellin
