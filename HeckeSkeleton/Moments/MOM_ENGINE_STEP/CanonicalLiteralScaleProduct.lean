import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralScalarNormalForm
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalGaussScaleProduction

/-!
# The original scale product after actual occurrence extraction

An upper window on each original prime profile gives the upper scale
product needed by the actual capacity ledger. Every removed occurrence
appears in the frozen ideal. Its fixed annulus cost is paid explicitly;
neither a final raw-degree bound nor a child bound is assumed.

The same product is preserved by both Mellin factors, reciprocal plain
balancing, constant extraction, the exact Gauss normalization and the
original atlas transport. Thus the calculation applies to both actual
centered rectangles and to zero slots without a separate argument.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

namespace RawProfileWindow

variable {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)} {amplitude : ℝ}
variable (profiles : RawProfileWindow rowDomain heightDomain window seminorms d amplitude)

include profiles in
theorem primeNorm_le_annulus_mul_scale (B Z t : ℝ) (hZ : 0 < Z)
    (ht : t ∈ heightDomain) (hwindow : ∀ x ∈ window, x ≤ B)
    (i : Fin d.geometry.slotCount) (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length)) :
    (Ideal.absNorm p.asIdeal : ℝ) ≤ B * Z ^ (d.geometry.slots i).length := by
  have hprofile := ((d.geometry.slots i).support_spec t
    (Z ^ (d.geometry.slots i).length) p).mp hp
  have hrep : profiles.primeRep i t
      ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length) ≠ 0 := by
    simpa only [profiles.prime_eq] using hprofile
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp
    (hwindow _ (profiles.prime_support i t ht hrep))

end RawProfileWindow

namespace SupportCartesianBranch

variable {k : ℕ} {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {P : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch S₁ S₂ S P)

/-- Every original frozen prime occurs in this product. The bound is
the upper-annulus counterpart of the already proved Gauss lower bound. -/
theorem residualGaussScale_mul_frozenNorm_le
    (Z : ℝ) (length : Fin k → ℝ) (X₁ X₂ B : ℝ) (cap : ℕ)
    (hZ : 0 < Z) (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂)
    (hB : 1 ≤ B) (hcap : k ≤ cap)
    (hprime : ∀ i ∈ Finset.univ \ b.keep,
      (Ideal.absNorm (b.witness.2 i).asIdeal : ℝ) ≤ B * Z ^ length i) :
    b.residualGaussScale Z length X₁ X₂ *
        (Ideal.absNorm (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂
          b.keep b.witness.2) : ℝ) ≤
      B ^ cap * (X₁ * X₂ * ∏ i, Z ^ length i) := by
  have hcard : (Finset.univ \ b.keep).card ≤ cap :=
    (by simpa only [Fintype.card_fin] using
      (Finset.card_le_univ (Finset.univ \ b.keep))).trans hcap
  have hfrozen : (∏ i ∈ Finset.univ \ b.keep,
      (Ideal.absNorm (b.witness.2 i).asIdeal : ℝ)) ≤
      B ^ cap * ∏ i ∈ Finset.univ \ b.keep, Z ^ length i := by
    calc
      _ ≤ ∏ i ∈ Finset.univ \ b.keep, B * Z ^ length i :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) hprime
      _ = B ^ (Finset.univ \ b.keep).card *
          ∏ i ∈ Finset.univ \ b.keep, Z ^ length i := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB hcard)
        (Finset.prod_nonneg (fun _ _ => Real.rpow_nonneg hZ.le _))
  rw [b.residualGaussScale_mul_frozenNorm, b.originalScale_product]
  have hfactor : 0 ≤ X₁ * X₂ * ∏ j, Z ^ length (SlotRestriction.index b.keep j) :=
    mul_nonneg (mul_nonneg hX₁ hX₂)
      (Finset.prod_nonneg (fun _ _ => Real.rpow_nonneg hZ.le _))
  convert mul_le_mul_of_nonneg_left hfrozen hfactor using 1 <;> ring

end SupportCartesianBranch

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)

def scaleProduct (r : Bool) : ℝ :=
  d.scale₁ r * d.scale₂ r * ∏ i, d.base ^ d.length i

theorem scaleProduct_pos (r : Bool) : 0 < d.scaleProduct r :=
  mul_pos (mul_pos (d.scale₁_pos r) (d.scale₂_pos r))
    (Finset.prod_pos (fun _ _ => Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _))

theorem scaleProduct_eq_sum (r : Bool) :
    d.scaleProduct r = d.scale₁ r * d.scale₂ r * d.base ^ (∑ i, d.length i) := by
  rw [scaleProduct, Real.rpow_sum_of_pos (zero_lt_one.trans d.base_gt_one)]

/-- A window on the original individual prime occurrences, not on a
transformed polynomial or an output scale. -/
def PrimeNormWindow (B : ℝ) : Prop :=
  ∀ i, ∀ p ∈ d.slots i, (Ideal.absNorm p.asIdeal : ℝ) ≤ B * d.base ^ d.length i

variable {d} {B : ℝ}

theorem PrimeNormWindow.extract (h : d.PrimeNormWindow B)
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) :
    (d.extract b).PrimeNormWindow B := by
  intro i p hp
  exact h (SlotRestriction.index b.keep i) p (Finset.mem_filter.mp hp).1

theorem PrimeNormWindow.onAtlas (h : d.PrimeNormWindow B)
    {A : SArithmeticData K} {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal) (count : k = T.slotCount)
    (hslots : ∀ i, T.reindex.slots (Fin.cast count i) = d.slots i) :
    (d.onAtlas T count).PrimeNormWindow B := by
  cases count
  intro i p hp
  exact h i p (hslots i ▸ hp)

theorem PrimeNormWindow.onAtlas_dictionary (h : d.PrimeNormWindow B)
    {A : SArithmeticData K} {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal) (index : AllocationColumn K k → ι)
    (e : T.literalDictionary = ⟨k, (d.plain₁, d.plain₂), d.slots, index⟩) :
    (d.onAtlas T (congrArg Sigma.fst e).symm).PrimeNormWindow B := by
  rw [d.onAtlas_eq_cast T index e]
  have hcast {l : ℕ} (count : k = l) :
      (cast (congrArg (CanonicalLiteralRectangles.Atoms (K := K)) count) d).PrimeNormWindow B := by
    cases count
    exact h
  exact hcast (congrArg Sigma.fst e).symm

theorem PrimeNormWindow.scale (h : d.PrimeNormWindow B) (c : ℂ) :
    (d.scale c).PrimeNormWindow B := h

theorem PrimeNormWindow.balancePlain (h : d.PrimeNormWindow B) (c : Bool → ℝ) :
    (d.balancePlain c).PrimeNormWindow B := h

theorem PrimeNormWindow.deleteMask (h : d.PrimeNormWindow B)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.deleteMask M).PrimeNormWindow B := h

variable (d)

theorem extract_scaleProduct_mul_frozenNorm_le (hprime : d.PrimeNormWindow B)
    (hB : 1 ≤ B) (cap : ℕ) (hcap : k ≤ cap)
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) (r : Bool) :
    (d.extract b).scaleProduct r *
        (Ideal.absNorm (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂
          b.keep b.witness.2) : ℝ) ≤ B ^ cap * d.scaleProduct r :=
  b.residualGaussScale_mul_frozenNorm_le d.base d.length (d.scale₁ r) (d.scale₂ r) B cap
    (zero_lt_one.trans d.base_gt_one) (d.scale₁_pos r).le (d.scale₂_pos r).le hB hcap
    (fun i _ => hprime i (b.witness.2 i) (Finset.mem_filter.mp (b.witness_slots i)).1)

theorem scale_scaleProduct (c : ℂ) (r : Bool) : (d.scale c).scaleProduct r = d.scaleProduct r := rfl
theorem normPower_scaleProduct (δ : ℝ) (r : Bool) : (d.normPower δ).scaleProduct r = d.scaleProduct r := rfl
theorem balancePlain_scaleProduct (c : Bool → ℝ) (r : Bool) :
    (d.balancePlain c).scaleProduct r = d.scaleProduct r := rfl
theorem deleteMask_scaleProduct (M : HeckeGeneral.Analysis.NonzeroIdeal K) (r : Bool) :
    (d.deleteMask M).scaleProduct r = d.scaleProduct r := rfl

theorem onAtlas_scaleProduct {A : SArithmeticData K} {ι : Type*}
    {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal) (count : k = T.slotCount) (r : Bool) :
    (d.onAtlas T count).scaleProduct r = d.scaleProduct r := by
  cases count
  rfl

section TwoStages

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
variable (power firstFixed poolFixed unitFixed : A.Exterior)
variable (firstElement poolElement unitElement : A.R)
variable (hfirst : A.Generates firstFixed firstElement)
variable (hpool : A.Generates poolFixed poolElement)
variable (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ)

theorem secondInput_scaleProduct (r : Bool) :
    (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).scaleProduct r =
        (d.extract b).scaleProduct r := rfl

theorem secondInputCore_scaleProduct (r : Bool) :
    (d.secondInputCore P R b firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).scaleProduct r =
        (d.extract b).scaleProduct r := rfl

theorem secondInput_primeNormWindow (h : d.PrimeNormWindow B) :
    (d.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).PrimeNormWindow B :=
  h.extract b

theorem secondInputCore_primeNormWindow (h : d.PrimeNormWindow B) :
    (d.secondInputCore P R b firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).PrimeNormWindow B :=
  h.extract b

end TwoStages

/-- This consumes the original occurrence window and an earlier
proved original scale product. The full frozen ideal is subtracted
exactly, while its fixed annulus power remains visible. -/
theorem extract_scaleProduct_le_power (hprime : d.PrimeNormWindow B)
    (hB : 1 ≤ B) (cap : ℕ) (hcap : k ≤ cap)
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) (r : Bool)
    (degree error : ℝ) (hproduct : d.scaleProduct r ≤ d.base ^ degree)
    (herror : B ^ cap ≤ d.base ^ error) :
    (d.extract b).scaleProduct r ≤
      d.base ^ (degree - idealLogLength d.base
        (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2) + error) := by
  have hz := zero_lt_one.trans d.base_gt_one
  have hn := rpow_idealLogLength d.base d.base_gt_one
    (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2)
    (frozenSourceIdeal_ne_zero _ _ _ _)
  have hnpos : 0 < (Ideal.absNorm (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂
      b.keep b.witness.2) : ℝ) := by
    rw [← hn]
    exact Real.rpow_pos_of_pos hz _
  have hcost := (d.extract_scaleProduct_mul_frozenNorm_le hprime hB cap hcap b r).trans
    (mul_le_mul herror hproduct (d.scaleProduct_pos r).le (Real.rpow_nonneg hz.le _))
  have hexponent : degree - idealLogLength d.base
      (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2) + error =
      (error + degree) - idealLogLength d.base
        (frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2) := by ring
  rw [hexponent, Real.rpow_sub hz, Real.rpow_add hz, hn]
  exact (le_div_iff₀ hnpos).mpr hcost

end CanonicalLiteralRectangles.Atoms

namespace CompleteMovingRowRecipe

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (ξ : X)
variable (W : NormProfileRecipe (fun _ : PUnit => data ξ))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
variable (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)

theorem literalOriginalAtoms_scaleProduct (r : Bool)
    (hcomparison : Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂)) :
    (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).scaleProduct r =
      Z ^ (a.n₁ + a.n₂ + (data ξ).geometry.totalLength) := by
  have hz := zero_lt_one.trans hZ
  cases r <;>
    simp only [CanonicalLiteralRectangles.Atoms.scaleProduct, literalOriginalAtoms,
      Bool.false_eq_true, if_false, if_true, hcomparison, SlotGeometry.totalLength,
      Real.rpow_add hz, Real.rpow_sum_of_pos hz]

theorem literalOriginalAtoms_primeNormWindow
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)} {amplitude : ℝ}
    (profiles : RawProfileWindow rowDomain heightDomain window seminorms (data ξ) amplitude)
    (B : ℝ) (ht : t ∈ heightDomain) (hwindow : ∀ x ∈ window, x ≤ B) :
    (Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂).PrimeNormWindow B := by
  intro i p hp
  exact profiles.primeNorm_le_annulus_mul_scale B Z t (zero_lt_one.trans hZ) ht hwindow
    i p (Finset.mem_filter.mp hp).1

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.residualGaussScale_mul_frozenNorm_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.extract_scaleProduct_le_power
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalAtoms_scaleProduct
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalAtoms_primeNormWindow
