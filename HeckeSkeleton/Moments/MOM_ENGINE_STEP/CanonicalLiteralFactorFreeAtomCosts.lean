import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAtomCosts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralProfileFactorExtraction

/-!
# Frozen prime costs after extracting the complete profile factor

Dividing a transformed occurrence by its original positive scale
factor leaves `φ(y) * y^(-1 + δ₁ + δ₂)`, where `y` is the same original
prime-norm ratio.  Its actual annulus-weighted square is therefore
`y^(-1 + 2*(δ₁+δ₂)) * ‖φ(y)‖²`.  The original open prime window gives
`1 < y` whenever that occurrence is nonzero.

The bound remains the original squared profile bound.  The complete
residual factor is paid in the row scalar, not inserted into an atom
budget or lost when the actual source table is redistributed.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support

namespace CanonicalLiteralFactorFreeAtomCosts

/-- Cancellation uses the original occurrence scale, before any
second common or allocation divisor is extracted. -/
theorem transform_divide_factor (N np δ₁ δ₂ : ℝ)
    (hN : 0 < N) (hp : 0 < np) (z : ℂ) :
    ((((z * (Real.sqrt N : ℂ)) * (np ^ (-1 : ℝ) : ℂ)) *
        (np ^ δ₁ : ℂ)) * (np ^ δ₂ : ℂ)) *
        (CanonicalLiteralProfileScalars.plainFactor N N δ₁ δ₂ : ℂ)⁻¹ =
      z * ((np / N) ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ : ℂ) := by
  have hratio : 0 < np / N := div_pos hp hN
  have hmul : N * (np / N) = np := by field_simp [hN.ne'] <;> ring
  have hpower := CanonicalLiteralProfileScalars.normPower_product hN hratio δ₁ δ₂
  rw [hmul] at hpower
  have hfactor : (CanonicalLiteralProfileScalars.plainFactor N N δ₁ δ₂ : ℂ) ≠ 0 := by
    exact_mod_cast (CanonicalLiteralProfileScalars.plainFactor_pos hN hN δ₁ δ₂).ne'
  calc
    _ = z * (Real.sqrt N : ℂ) *
        ((np ^ (-1 : ℝ) : ℂ) * (np ^ δ₁ : ℂ) * (np ^ δ₂ : ℂ)) *
        (CanonicalLiteralProfileScalars.plainFactor N N δ₁ δ₂ : ℂ)⁻¹ := by ring
    _ = z * (Real.sqrt N : ℂ) *
        ((N ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ : ℂ) *
          ((np / N) ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ : ℂ)) *
        (CanonicalLiteralProfileScalars.plainFactor N N δ₁ δ₂ : ℂ)⁻¹ := by rw [hpower]
    _ = ((CanonicalLiteralProfileScalars.plainFactor N N δ₁ δ₂ : ℂ) *
        (CanonicalLiteralProfileScalars.plainFactor N N δ₁ δ₂ : ℂ)⁻¹) *
        (z * ((np / N) ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ : ℂ)) := by
      simp only [CanonicalLiteralProfileScalars.plainFactor, Complex.ofReal_mul]
      ring
    _ = _ := by rw [mul_inv_cancel₀ hfactor, one_mul]

theorem weighted_power_norm_sq (y δ₁ δ₂ : ℝ) (hy : 0 < y) (z : ℂ) :
    y * ‖z * (y ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ : ℂ)‖ ^ 2 =
      y ^ (-1 + 2 * (δ₁ + δ₂)) * ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_of_nonneg (Real.rpow_nonneg hy.le _), mul_pow]
  have hexponent : y * (y ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂) ^ 2 =
      y ^ (-1 + 2 * (δ₁ + δ₂)) := by
    calc
      _ = y ^ (1 : ℝ) * y ^ (CanonicalLiteralProfileScalars.exponent δ₁ δ₂ * (2 : ℝ)) := by
        rw [Real.rpow_one, Real.rpow_mul_natCast hy.le]
      _ = y ^ (1 + CanonicalLiteralProfileScalars.exponent δ₁ δ₂ * 2) :=
        (Real.rpow_add hy _ _).symm
      _ = _ := by congr 1; unfold CanonicalLiteralProfileScalars.exponent; ring
  calc
    _ = (y * (y ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂) ^ 2) * ‖z‖ ^ 2 := by ring
    _ = _ := by rw [hexponent]

end CanonicalLiteralFactorFreeAtomCosts

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (power firstFixed poolFixed unitFixed : A.Exterior)
variable (firstElement poolElement unitElement : A.R)
variable (hfirst : A.Generates firstFixed firstElement)
variable (hpool : A.Generates poolFixed poolElement)
variable (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ)

theorem redistributedSecondInput_primeAtomCost_eq
    (i : Fin b.keep.card) (p : HeightOneSpectrum (𝓞 K)) :
    (d.redistributedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).primeAtomCost i p =
      ((Ideal.absNorm p.asIdeal : ℝ) / d.base ^ d.length (SlotRestriction.index b.keep i)) ^
          (-1 + 2 * (δ₁ + δ₂)) * ‖d.slotWeight (SlotRestriction.index b.keep i) p‖ ^ 2 := by
  have hN : 0 < d.base ^ d.length (SlotRestriction.index b.keep i) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _
  have hp : (0 : ℝ) < Ideal.absNorm p.asIdeal := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot)
  change ((Ideal.absNorm p.asIdeal : ℝ) / d.base ^ d.length (SlotRestriction.index b.keep i)) *
      ‖((((d.slotWeight (SlotRestriction.index b.keep i) p *
        (Real.sqrt (d.base ^ d.length (SlotRestriction.index b.keep i)) : ℂ)) *
        ((Ideal.absNorm p.asIdeal : ℝ) ^ (-1 : ℝ) : ℂ)) *
        ((Ideal.absNorm p.asIdeal : ℝ) ^ δ₁ : ℂ)) *
        ((Ideal.absNorm p.asIdeal : ℝ) ^ δ₂ : ℂ)) *
        (CanonicalLiteralProfileScalars.plainFactor
          (d.base ^ d.length (SlotRestriction.index b.keep i))
          (d.base ^ d.length (SlotRestriction.index b.keep i)) δ₁ δ₂ : ℂ)⁻¹‖ ^ 2 = _
  rw [CanonicalLiteralFactorFreeAtomCosts.transform_divide_factor _ _ δ₁ δ₂ hN hp]
  exact CanonicalLiteralFactorFreeAtomCosts.weighted_power_norm_sq _ δ₁ δ₂
    (div_pos hp hN) _

/-- Only the original occurrence being nonzero is needed for its
scale lower bound.  The zero branch is handled exactly. -/
theorem redistributedSecondInput_primeAtomCost_le
    (hδ : δ₁ + δ₂ ≤ 1 / 2) (i : Fin b.keep.card) (p : HeightOneSpectrum (𝓞 K))
    (hscale : d.slotWeight (SlotRestriction.index b.keep i) p ≠ 0 →
      d.base ^ d.length (SlotRestriction.index b.keep i) ≤ (Ideal.absNorm p.asIdeal : ℝ)) :
    (d.redistributedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).primeAtomCost i p ≤
      ‖d.slotWeight (SlotRestriction.index b.keep i) p‖ ^ 2 := by
  rw [d.redistributedSecondInput_primeAtomCost_eq b P R power firstFixed poolFixed unitFixed
    firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ i p]
  by_cases hz : d.slotWeight (SlotRestriction.index b.keep i) p = 0
  · simp only [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, le_refl]
  have hratio : (1 : ℝ) ≤ (Ideal.absNorm p.asIdeal : ℝ) /
      d.base ^ d.length (SlotRestriction.index b.keep i) := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _)).mpr
    simpa only [one_mul] using hscale hz
  have hpower := Real.rpow_le_one_of_one_le_of_nonpos hratio
    (show -1 + 2 * (δ₁ + δ₂) ≤ 0 by linarith)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hpower (sq_nonneg _)

end CanonicalLiteralRectangles.Atoms

namespace CompleteMovingRowRecipe

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (ξ : X)
variable (W : NormProfileRecipe (fun _ : PUnit => data ξ))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
variable (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)

local notation "seed" => Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂

/-- Every actual frozen or common prime in the redistributed table
is paid from the original parent window, with no completed-table
estimate supplied by the caller. -/
theorem literalOriginalAtoms_redistributedSecondInput_primeAtomCost_le
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {B : ℝ}
    (original : RawProfileWindow rowDomain heightDomain window orders (data ξ) B)
    (hzero : (0, 0) ∈ orders) (ht : t ∈ heightDomain)
    (hprime : ∀ j, Function.support (original.primeRep j t) ⊆ Set.Ioo (1 : ℝ) 2)
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch seed.plain₁ seed.plain₂ seed.slots support)
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement)
    (δ₁ δ₂ : ℝ) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (i : Fin b.keep.card) (p : HeightOneSpectrum (𝓞 K)) :
    (seed.redistributedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).primeAtomCost i p ≤ B ^ 2 := by
  have hscale : seed.slotWeight (SlotRestriction.index b.keep i) p ≠ 0 →
      seed.base ^ seed.length (SlotRestriction.index b.keep i) ≤ (Ideal.absNorm p.asIdeal : ℝ) := by
    intro hn
    have hrep : original.primeRep (SlotRestriction.index b.keep i) t
        ((Ideal.absNorm p.asIdeal : ℝ) /
          Z ^ ((data ξ).geometry.slots (SlotRestriction.index b.keep i)).length) ≠ 0 := by
      change ((data ξ).geometry.slots (SlotRestriction.index b.keep i)).profile t
        ((Ideal.absNorm p.asIdeal : ℝ) /
          Z ^ ((data ξ).geometry.slots (SlotRestriction.index b.keep i)).length) ≠ 0 at hn
      simpa only [original.prime_eq] using hn
    have hratio := (hprime (SlotRestriction.index b.keep i) hrep).1
    have h := (lt_div_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ)
      ((data ξ).geometry.slots (SlotRestriction.index b.keep i)).length)).mp hratio
    simpa only [one_mul] using h.le
  apply (seed.redistributedSecondInput_primeAtomCost_le b P R power firstFixed poolFixed unitFixed
    firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hδ i p hscale).trans
  exact pow_le_pow_left₀ (norm_nonneg _)
    (Q.literalOriginalAtoms_slot_norm_le ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      original hzero ht (SlotRestriction.index b.keep i) p) 2

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralFactorFreeAtomCosts.transform_divide_factor
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralFactorFreeAtomCosts.weighted_power_norm_sq
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.redistributedSecondInput_primeAtomCost_eq
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalAtoms_redistributedSecondInput_primeAtomCost_le
