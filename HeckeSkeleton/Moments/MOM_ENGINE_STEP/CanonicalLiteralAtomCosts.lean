import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFrozenBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralScalarNormalForm
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPlainBalance
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLogProfileBounds

/-!
# Uniform costs of the actual frozen prime occurrences

The two norm transforms insert `sqrt N * Np^(-1 + δ₁ + δ₂)` at
each original prime occurrence. Its annulus-weighted squared norm is
exactly `Np^(-1 + 2 * (δ₁ + δ₂))` times the original squared profile.
Thus, when the two tilts sum to at most one half, this cost is bounded
by the original pointwise profile bound. No central scale, retained
slot count, row class or extracted column scalar enters that bound.

The equalities below transport this computed cost through the actual
common extraction, atlas casts, full deletion, constant stripping and
reciprocal plain balancing. They apply to the existing common and
allocation witnesses used by `CanonicalLiteralArithmeticInput`.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

namespace CanonicalLiteralAtomCosts

/-- Exact cancellation of the same central scale. In particular an
annulus factor is not paid again after the original inverse norm. -/
theorem weighted_transform_norm_sq (N np δ₁ δ₂ : ℝ)
    (hN : 0 < N) (hp : 0 < np) (z : ℂ) :
    (np / N) *
        ‖(((z * (Real.sqrt N : ℂ)) * (np ^ (-1 : ℝ) : ℂ)) *
          (np ^ δ₁ : ℂ)) * (np ^ δ₂ : ℂ)‖ ^ 2 =
      np ^ (-1 + 2 * (δ₁ + δ₂)) * ‖z‖ ^ 2 := by
  let e : ℝ := -1 + δ₁ + δ₂
  have hpow : (np ^ (-1 : ℝ) : ℂ) * (np ^ δ₁ : ℂ) * (np ^ δ₂ : ℂ) =
      (np ^ e : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul,
      ← Real.rpow_add hp, ← Real.rpow_add hp]
  have hshape : (((z * (Real.sqrt N : ℂ)) * (np ^ (-1 : ℝ) : ℂ)) *
      (np ^ δ₁ : ℂ)) * (np ^ δ₂ : ℂ) = z * (Real.sqrt N : ℂ) * (np ^ e : ℂ) := by
    calc
      _ = z * (Real.sqrt N : ℂ) *
          ((np ^ (-1 : ℝ) : ℂ) * (np ^ δ₁ : ℂ) * (np ^ δ₂ : ℂ)) := by ring
      _ = _ := by rw [hpow]
  have hexponent : np * (np ^ e) ^ 2 = np ^ (-1 + 2 * (δ₁ + δ₂)) := by
    calc
      _ = np ^ (1 : ℝ) * np ^ (e * (2 : ℝ)) := by
        rw [Real.rpow_one, Real.rpow_mul_natCast hp.le]
      _ = np ^ (1 + e * 2) := (Real.rpow_add hp _ _).symm
      _ = _ := by congr 1; dsimp only [e]; ring
  rw [hshape, norm_mul, norm_mul,
    Complex.norm_of_nonneg (Real.sqrt_nonneg N),
    Complex.norm_of_nonneg (Real.rpow_nonneg hp.le e),
    mul_pow, mul_pow, Real.sq_sqrt hN.le]
  calc
    _ = ((np / N) * N) * (np ^ e) ^ 2 * ‖z‖ ^ 2 := by ring
    _ = (np * (np ^ e) ^ 2) * ‖z‖ ^ 2 := by rw [div_mul_cancel₀ _ hN.ne']
    _ = _ := by rw [hexponent]

theorem weighted_transform_norm_sq_le (N np δ₁ δ₂ : ℝ)
    (hN : 0 < N) (hp : 1 ≤ np) (hδ : δ₁ + δ₂ ≤ 1 / 2) (z : ℂ) :
    (np / N) *
        ‖(((z * (Real.sqrt N : ℂ)) * (np ^ (-1 : ℝ) : ℂ)) *
          (np ^ δ₁ : ℂ)) * (np ^ δ₂ : ℂ)‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  rw [weighted_transform_norm_sq N np δ₁ δ₂ hN (zero_lt_one.trans_le hp) z]
  have hpower := Real.rpow_le_one_of_one_le_of_nonpos hp
    (show -1 + 2 * (δ₁ + δ₂) ≤ 0 by linarith)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hpower (sq_nonneg ‖z‖)

end CanonicalLiteralAtomCosts

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)

/-- The exact individual quantity used in both frozen-bound records. -/
def primeAtomCost (i : Fin k) (p : HeightOneSpectrum (𝓞 K)) : ℝ :=
  ((Ideal.absNorm p.asIdeal : ℝ) / d.base ^ d.length i) * ‖d.slotWeight i p‖ ^ 2

theorem primeAtomCost_nonneg (i : Fin k) (p : HeightOneSpectrum (𝓞 K)) :
    0 ≤ d.primeAtomCost i p :=
  mul_nonneg (div_nonneg (Nat.cast_nonneg _)
    (Real.rpow_nonneg (zero_lt_one.trans d.base_gt_one).le _)) (sq_nonneg _)

@[simp] theorem primeAtomCost_scale (c : ℂ) (i : Fin k)
    (p : HeightOneSpectrum (𝓞 K)) :
    (d.scale c).primeAtomCost i p = d.primeAtomCost i p := rfl

@[simp] theorem primeAtomCost_balancePlain (c : Bool → ℝ) (i : Fin k)
    (p : HeightOneSpectrum (𝓞 K)) :
    (d.balancePlain c).primeAtomCost i p = d.primeAtomCost i p := rfl

@[simp] theorem primeAtomCost_deleteMask (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (i : Fin k) (p : HeightOneSpectrum (𝓞 K)) :
    (d.deleteMask M).primeAtomCost i p = d.primeAtomCost i p := rfl

@[simp] theorem primeAtomCost_extract {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
    (i : Fin b.keep.card) (p : HeightOneSpectrum (𝓞 K)) :
    (d.extract b).primeAtomCost i p =
      d.primeAtomCost (SlotRestriction.index b.keep i) p := rfl

@[simp] theorem primeAtomCost_onAtlas {A : SArithmeticData K} {I : Type*}
    {columns : Finset I} {ideal : I → A.Exterior}
    (T : SourceCartesianAtlas columns ideal) (h : k = T.slotCount)
    (i : Fin T.slotCount) (p : HeightOneSpectrum (𝓞 K)) :
    (d.onAtlas T h).primeAtomCost i p = d.primeAtomCost (Fin.cast h.symm i) p := by
  cases h
  rfl

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)

@[simp] theorem primeAtomCost_movingSingleton
    (I : A.Exterior) (a : A.R) (ha : A.Generates I a)
    (i : Fin k) (p : HeightOneSpectrum (𝓞 K)) :
    (d.movingSingleton P R I a ha).primeAtomCost i p = d.primeAtomCost i p := rfl

/-- This calculation uses the actual two-transform table, not a bound
on a completed child profile. All arithmetic masks remain in its
separate original character dictionary. -/
theorem secondInput_primeAtomCost_le
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement)
    (δ₁ δ₂ : ℝ) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (i : Fin b.keep.card) (p : HeightOneSpectrum (𝓞 K)) :
    (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).primeAtomCost i p ≤
      ‖d.slotWeight (SlotRestriction.index b.keep i) p‖ ^ 2 := by
  have hp : (1 : ℝ) ≤ Ideal.absNorm p.asIdeal := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot)
  exact CanonicalLiteralAtomCosts.weighted_transform_norm_sq_le
    (d.base ^ d.length (SlotRestriction.index b.keep i))
    (Ideal.absNorm p.asIdeal : ℝ) δ₁ δ₂
    (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _) hp hδ
    (d.slotWeight (SlotRestriction.index b.keep i) p)

/-- The common record uses these same numerical fields. Restricting
its physical rows does not alter either side of this identity. -/
@[simp] theorem commonAtomBounds_atomCost
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
    (hmask : d.characters.MaskIndicator) (i : Fin k) :
    (d.commonAtomBounds b hmask).annulus i *
      (d.commonAtomBounds b hmask).profile i = d.primeAtomCost i (b.witness.2 i) := rfl

variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {H J : Type*} [Fintype J] [DecidableEq J]

/-- The second allocation is paid on its actual occurrence witness;
the inverse norm of the second divisor remains in `scalarBound`. -/
@[simp] theorem frozenBounds_atomCost
    (S : ActualSecondCorrelationRows A σ H J)
    (C : A.GeneralArithmeticContext σ η htrace)
    (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
    (ideal : AllocationColumn K k → A.Exterior)
    (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
      (ideal i).val = allocationColumnIdeal i)
    (firstSign : ℝ) (rectangle : Bool) (L : Ideal (𝓞 K))
    (selection : primeSupport L → Finset (Fin (k + 2)))
    (hne : (pairedAllocatedColumns L selection d.plain₁ d.plain₂ d.slots
      id id HeightOneSpectrum.asIdeal).Nonempty)
    (hmask : d.characters.MaskIndicator) (hL : Squarefree L)
    (hselection : selection ∈ AllocationMass.idealAllocations L (k + 2)) (i : Fin k) :
    let f := (d.factors S side χ ideal hideal firstSign rectangle).frame C L selection hne
    let B := d.frozenBounds S C side χ ideal hideal firstSign rectangle L selection hne
      hmask hL hselection
    B.annulus i * B.profile i = d.primeAtomCost i (f.allocation.witness.2 i) := by
  cases side <;> rfl

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

/-- Only the original fixed seminorm window is used to bound the
literal seed at every prime, independently of every occurrence label. -/
theorem literalOriginalAtoms_slot_norm_le
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {B : ℝ}
    (original : RawProfileWindow rowDomain heightDomain window orders (data ξ) B)
    (hzero : (0, 0) ∈ orders) (ht : t ∈ heightDomain)
    (i : Fin (data ξ).geometry.slotCount) (p : HeightOneSpectrum (𝓞 K)) :
    ‖(Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).slotWeight i p‖ ≤ B := by
  change ‖((data ξ).geometry.slots i).profile t
    ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ ((data ξ).geometry.slots i).length)‖ ≤ B
  rw [original.prime_eq]
  exact (SchwartzMap.norm_le_seminorm ℂ _ _).trans
    ((Seminorm.le_finset_sup_apply hzero).trans (original.prime_bound i t ht))

/-- Before the transforms, the original annulus is paid once per
frozen occurrence. A prime outside the profile support has zero cost. -/
theorem literalOriginalAtoms_primeAtomCost_le
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {B : ℝ}
    (original : RawProfileWindow rowDomain heightDomain window orders (data ξ) B)
    (hzero : (0, 0) ∈ orders) (ht : t ∈ heightDomain)
    (annulus : ℝ) (hannulus : 0 ≤ annulus) (hwindow : window ⊆ Set.Iic annulus)
    (i : Fin (data ξ).geometry.slotCount) (p : HeightOneSpectrum (𝓞 K)) :
    (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).primeAtomCost i p ≤
      annulus * B ^ 2 := by
  let seed := Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
  by_cases hz : seed.slotWeight i p = 0
  · simp only [CanonicalLiteralRectangles.Atoms.primeAtomCost, hz,
      norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
    exact mul_nonneg hannulus (sq_nonneg _)
  have hrep : original.primeRep i t
      ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ ((data ξ).geometry.slots i).length) ≠ 0 := by
    change ((data ξ).geometry.slots i).profile t
      ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ ((data ξ).geometry.slots i).length) ≠ 0 at hz
    simpa only [original.prime_eq] using hz
  have hratio := hwindow (original.prime_support i t ht hrep)
  have hnorm := Q.literalOriginalAtoms_slot_norm_le ξ W a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ original hzero ht i p
  exact mul_le_mul hratio (pow_le_pow_left₀ (norm_nonneg _) hnorm 2)
    (sq_nonneg _) hannulus

/-- After the real two transforms the annulus is already cancelled
by the same norm denominator. This is the bound for every original
common or frozen occurrence in the current second-stage table. -/
theorem literalOriginalAtoms_secondInput_primeAtomCost_le
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)} {B : ℝ}
    (original : RawProfileWindow rowDomain heightDomain window orders (data ξ) B)
    (hzero : (0, 0) ∈ orders) (ht : t ∈ heightDomain)
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch
      (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₁
      (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₂
      (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).slots support)
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement)
    (δ₁ δ₂ : ℝ) (hδ : δ₁ + δ₂ ≤ 1 / 2)
    (i : Fin b.keep.card) (p : HeightOneSpectrum (𝓞 K)) :
    ((Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).secondInput
      (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).primeAtomCost i p ≤ B ^ 2 := by
  apply ((Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂)
    .secondInput_primeAtomCost_le P R b power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hδ i p).trans
  exact pow_le_pow_left₀ (norm_nonneg _)
    (Q.literalOriginalAtoms_slot_norm_le ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      original hzero ht (SlotRestriction.index b.keep i) p) 2

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralAtomCosts.weighted_transform_norm_sq
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.secondInput_primeAtomCost_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.frozenBounds_atomCost
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalAtoms_secondInput_primeAtomCost_le
