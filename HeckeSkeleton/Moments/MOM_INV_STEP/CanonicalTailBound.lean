import HeckeSkeleton.Moments.MOM_INV_STEP.FirstDualTruncation
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualPoissonScale
import HeckeSkeleton.Moments.MOM_INV_STEP.OuterFrequencyTail
import HeckeGeneral.Bridge.TraceSchwartzFourierBounds

/-!
# Bounds for the actual canonical high-frequency series

The orbit coefficient below is the literal primitive Fourier coefficient,
including its Poisson factor. Its bound follows from the exact Gauss norm.
The tail estimate uses the proved orbital Schwartz tail and a product
budget for the actual radius. Constants precede every arithmetic source,
test function, radius and current length parameter.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalTailBound

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton MeasureTheory
open ActualFiniteSource ConductorMasks PrimitivePoissonSource PrimitiveFourier
  ActualPoissonScale FirstDualTruncation CanonicalBlock CanonicalPoissonSplit
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Ext" => ExteriorIdeal K Sset

theorem primitiveCoefficient_norm_le_one (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (q : OS ⧸ Ideal.span ({primitiveModulus K S D B t} : Set OS)) :
    ‖primitiveCoefficient K S D B t q‖ ≤ 1 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [primitiveCoefficient_mk, norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro p hp
  have hval : (t p.val).val ≠ 0 := (ZMod.val_ne_zero _).mpr (Finset.mem_filter.mp hp).2
  rw [MulChar.pow_apply' _ hval, norm_pow]
  apply pow_le_one₀ (norm_nonneg _)
  by_cases hz : sIntegerSexticResidueMap K Sset p.val (B.outside p.val p.property) a = 0
  · rw [hz, sexticResidueCharacter_zero, norm_zero]
    norm_num
  · exact (sexticResidueCharacter_norm K D.root6 D.primitive6 D.embedding p.val
      (B.awaySix p.val p.property) _ hz).le

theorem primitive_prefactor_norm_le (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS) :
    ‖sIntegerMaskPoissonFactor K S (primitiveModulus K S D B t)
      (primitiveModulus_ne_zero K S D B t) r d * primitiveGauss K S D B t‖ ≤
        fieldConstant K / r.val := by
  rw [primitive_prefactor_norm]
  have hd := one_le_sIntegerElementNorm K Sset d
  have hq : (1 : ℝ) ≤ (primitiveIdeal B.support t).absNorm := by
    exact_mod_cast Nat.succ_le_of_lt
      (Ideal.absNorm_pos_of_nonZeroDivisors (primitiveExterior K S B t).val)
  have hs : 1 ≤ Real.sqrt ((primitiveIdeal B.support t).absNorm : ℝ) :=
    by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hq
  apply div_le_div_of_nonneg_left (fieldConstant_nonneg K) r.property
  have hp := one_le_mul_of_one_le_of_one_le hd hs
  simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hp r.property.le

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (hΓ : Γ ≤ (powMonoidHom 6 :
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
  ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)).range)

local notation "Orbit" => SIntegerOrbits K Sset Γ

theorem primitiveOrbitCoefficient_norm_le_one (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (q : Orbit) :
    ‖primitiveOrbitCoefficient K S D Γ hΓ B t q‖ ≤ 1 := by
  refine Quotient.inductionOn q (fun a => ?_)
  rw [primitiveOrbitCoefficient_mk]
  exact primitiveCoefficient_norm_le_one K S D B t _

/-- The literal Fourier weight together with its actual prefactor. -/
theorem prefactor_fourier_norm_le (B : PrimeBlock K Sset)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS) (q : Orbit) :
    ‖sIntegerMaskPoissonFactor K S (primitiveModulus K S D B t)
      (primitiveModulus_ne_zero K S D B t) r d *
      sIntegerPeriodicFourierOrbitWeight K Sset D.different_outside Γ
        (primitiveModulus K S D B t) (primitiveModulus_ne_zero K S D B t)
        (primitiveCoefficient K S D B t) (primitiveCoefficient_invariant K S D Γ hΓ B t)
        d.val q‖ ≤ fieldConstant K / r.val := by
  rw [primitiveFourierOrbitWeight_eq K S D Γ hΓ B t d.val q]
  calc
    _ = ‖sIntegerMaskPoissonFactor K S (primitiveModulus K S D B t)
        (primitiveModulus_ne_zero K S D B t) r d * primitiveGauss K S D B t‖ *
          ‖primitiveCoefficient K S D B t (Ideal.Quotient.mk _ d.val)‖ *
            ‖primitiveOrbitCoefficient K S D Γ hΓ B t q‖ := by
      simp only [norm_mul, norm_star]
      ring
    _ ≤ ‖sIntegerMaskPoissonFactor K S (primitiveModulus K S D B t)
        (primitiveModulus_ne_zero K S D B t) r d * primitiveGauss K S D B t‖ * 1 * 1 := by
      gcongr
      · exact primitiveCoefficient_norm_le_one K S D B t _
      · exact primitiveOrbitCoefficient_norm_le_one K S D Γ hΓ B t q
    _ ≤ _ := by
      simpa only [mul_one] using primitive_prefactor_norm_le K S D B t r d

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [Γ.FiniteIndex]
  [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

include ν in
/-- One fixed decay order works for an entire bounded family of current
length budgets. The cutoff remains the current Z^(R+tau), not a larger
ball substituted to conceal a lost length exponent. -/
theorem exists_primitive_tail_bound_uniform
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (Rmax tauMin savingMax : ℝ) (hRmax : 0 ≤ Rmax)
    (htauMin : 0 < tauMin) (hsavingMax : 0 ≤ savingMax) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ (B : PrimeBlock K Sset) (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
      (φ : SchwartzMap V ℂ) (M : Finset (HeightOneSpectrum OS))
      (r : {r : ℝ // 0 < r}) (δ : Finset (HeightOneSpectrum OS))
      (Z R tau saving : ℝ),
      1 ≤ Z → 0 ≤ R → R ≤ Rmax → tauMin ≤ tau →
      0 ≤ saving → saving ≤ savingMax →
      r.val * (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val *
        ((primitiveIdeal B.support t).absNorm : ℝ) ≤ Z ^ R →
      let b := block K S D Γ hΓ B t φ h hlc hcs M r
      ‖b.prefactor δ * primitiveTail K S D Γ μv b δ (Z ^ (R + tau))‖ ≤
        A * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          (fieldConstant K / r.val) * Z ^ (-saving) := by
  obtain ⟨T, hT, horder⟩ := OuterFrequencyTail.exists_tail_order
    Rmax tauMin savingMax hRmax htauMin hsavingMax
  let L := traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  let m : ℕ := Module.finrank ℤ L + ⌈(Module.finrank ℚ K : ℝ) * T⌉₊ + 1
  have hm : Module.finrank ℤ L < m := by dsimp only [m]; omega
  have hmorder : (Module.finrank ℚ K : ℝ) * T ≤ m := by
    have hc := Nat.le_ceil ((Module.finrank ℚ K : ℝ) * T)
    have hn : ⌈(Module.finrank ℚ K : ℝ) * T⌉₊ ≤ m := by dsimp only [m]; omega
    exact hc.trans (by exact_mod_cast hn)
  have hfinite := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport
    K S ν μv h hlc hcs
  obtain ⟨C, hC, hb⟩ := OuterFrequencyTail.exists_outer_frequency_tail_bound
    K Sset Γ (sIntegerFiniteFourierTestFunction K S μv h)
      hfinite.1.continuous hfinite.2 T hT m hm hmorder
  obtain ⟨s, F, _hF, hFT⟩ := traceSchwartzFourier_real_seminorm_bound K m 0
  have hFT' (φ : SchwartzMap V ℂ) :
      SchwartzMap.seminorm ℂ m 0 (traceSchwartzFourier K φ) ≤
        (F : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ := by
    simpa only [SchwartzMap.seminorm_apply] using hFT φ
  refine ⟨s, C * (F : ℝ), mul_nonneg hC F.property, ?_⟩
  intro B t φ M r δ Z R tau saving hZ hR hRR htau hsaving hss hbudget
  dsimp only
  let b := block K S D Γ hΓ B t φ h hlc hcs M r
  let d := sIntegerMaskGenerator K Sset δ
  let ρ := sIntegerMaskDualRadius K S (primitiveModulus K S D B t)
    (primitiveModulus_ne_zero K S D B t) r d
  let w : Orbit → ℂ := fun q => b.prefactor δ *
    sIntegerPeriodicFourierOrbitWeight K Sset D.different_outside Γ
      (primitiveModulus K S D B t) (primitiveModulus_ne_zero K S D B t)
      (primitiveCoefficient K S D B t) (primitiveCoefficient_invariant K S D Γ hΓ B t)
      d.val q
  have hρ : Z ^ (-R) ≤ ρ.val :=
    primitive_dual_radius_lower K S D B t r d Z R (zero_lt_one.trans_le hZ) hbudget
  have hcurrent : R + tau * (1 - T) ≤ -saving := by
    calc
      _ ≤ Rmax + tauMin * (1 - T) :=
        add_le_add hRR (mul_le_mul_of_nonpos_right htau (by linarith))
      _ ≤ -savingMax := horder
      _ ≤ _ := neg_le_neg hss
  have htail := hb (traceSchwartzFourier K φ) Z R tau saving ρ hZ hR
    (htauMin.le.trans htau) hρ hcurrent w (fieldConstant K / r.val)
    (div_nonneg (fieldConstant_nonneg K) r.property.le)
    (fun q => prefactor_fourier_norm_le K S D Γ hΓ B t r d q)
  have he : b.prefactor δ * primitiveTail K S D Γ μv b δ (Z ^ (R + tau)) =
      ∑' q : {q : Orbit // Z ^ (R + tau) < (sIntegerOrbitNorm K Sset Γ q).val},
        w q.val * sUnitOrbitalProfile K Sset
          (sLocalTensorTestFunction K Sset (traceSchwartzFourier K φ)
            (sIntegerFiniteFourierTestFunction K S μv h))
          ⟨ρ.val * (sIntegerOrbitNorm K Sset Γ q.val).val,
            mul_pos ρ.property (sIntegerOrbitNorm K Sset Γ q.val).property⟩ := by
    rw [primitiveTail, ← tsum_mul_left]
    apply tsum_congr
    intro q
    dsimp only [dualTerm, sIntegerPeriodicFourierProfileTerm, w, b, block, d, ρ]
    ring
  change ‖b.prefactor δ * primitiveTail K S D Γ μv b δ (Z ^ (R + tau))‖ ≤ _
  rw [he]
  apply htail.2.trans
  calc
    _ ≤ (fieldConstant K / r.val) * C *
        ((F : ℝ) * s.sup (schwartzSeminormFamily ℝ V ℂ) φ) * Z ^ (-saving) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hZ) _)
      exact mul_le_mul_of_nonneg_left (hFT' φ)
        (mul_nonneg (div_nonneg (fieldConstant_nonneg K) r.property.le) hC)
    _ = _ := by ring

/-- The exact divisor signs have norm one. -/
theorem divisorCoefficient_norm (b : ActualMaskedPoissonBlock K S Γ)
    (δ : Finset (HeightOneSpectrum OS)) : ‖b.divisorCoefficient δ‖ = 1 := by
  rw [ActualMaskedPoissonBlock.divisorCoefficient,
    (IdealMobiusMask.squarefree_primeProduct δ).moebius_eq,
    Int.cast_pow, Int.cast_neg, Int.cast_one, norm_pow]
  simp

theorem dualTail_norm_le (b : ActualMaskedPoissonBlock K S Γ) (H U : ℝ)
    (hU : 0 ≤ U)
    (hb : ∀ δ ∈ b.mask.powerset,
      ‖b.prefactor δ * primitiveTail K S D Γ μv b δ H‖ ≤ U) :
    ‖dualTail K S D Γ μv b H‖ ≤ (2 : ℝ) ^ b.mask.card * U := by
  unfold dualTail
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _δ ∈ b.mask.powerset, U := by
      apply Finset.sum_le_sum
      intro δ hδ
      rw [norm_mul, divisorCoefficient_norm, one_mul]
      exact hb δ hδ
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat]

variable {σ : Type*}

def coefficientMaskMass (C : ColumnData K S σ) (f : Ext)
    (P : Finset ((Ext × Ext) × (Ext × Ext)))
    (M : Finset (HeightOneSpectrum OS)) : ℝ :=
  ∑ p ∈ P, ‖pairWeight K S D C f p‖ *
    (2 : ℝ) ^ (M ∪ principalMask K S (pairSupport K S D p.1.2 p.2.2 p.1.1 p.2.1)
      (pairExponent K S p.1.2 p.2.2 p.1.1 p.2.1)).card

def sourceSubsetTail (C : ColumnData K S σ) (f : Ext)
    (P : Finset ((Ext × Ext) × (Ext × Ext))) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r}) (H : ℝ) : ℂ :=
  ∑ p ∈ P, pairWeight K S D C f p *
    dualTail K S D Γ μv (primitivePairBlock K S D Γ hΓ p.1 p.2 φ h hlc hcs M r) H

include ν in
/-- Every subfamily, in particular the principal and nonprincipal
tails, is bounded by its actual absolute coefficient and mask mass. -/
theorem exists_sourceSubsetTail_bound_uniform
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (Rmax tauMin savingMax : ℝ) (hRmax : 0 ≤ Rmax)
    (htauMin : 0 < tauMin) (hsavingMax : 0 ≤ savingMax) :
    ∃ s : Finset (ℕ × ℕ), ∃ A : ℝ, 0 ≤ A ∧
      ∀ {σ : Type*} (C : ColumnData K S σ) (f : Ext)
      (P : Finset ((Ext × Ext) × (Ext × Ext))) (φ : SchwartzMap V ℂ)
      (M : Finset (HeightOneSpectrum OS)) (r : {r : ℝ // 0 < r})
      (Z R tau saving : ℝ),
      1 ≤ Z → 0 ≤ R → R ≤ Rmax → tauMin ≤ tau →
      0 ≤ saving → saving ≤ savingMax →
      (∀ p ∈ P, ∀ δ ⊆ (primitivePairBlock K S D Γ hΓ p.1 p.2 φ h hlc hcs M r).mask,
        r.val * (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val *
          ((primitiveIdeal (pairSupport K S D p.1.2 p.2.2 p.1.1 p.2.1).support
            (pairExponent K S p.1.2 p.2.2 p.1.1 p.2.1)).absNorm : ℝ) ≤ Z ^ R) →
      ‖sourceSubsetTail K S D Γ hΓ μv C f P φ h hlc hcs M r (Z ^ (R + tau))‖ ≤
        coefficientMaskMass K S D C f P M *
          (A * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
            (fieldConstant K / r.val) * Z ^ (-saving)) := by
  obtain ⟨s, A, hA, hb⟩ := exists_primitive_tail_bound_uniform
    K S D Γ hΓ μv ν h hlc hcs Rmax tauMin savingMax hRmax htauMin hsavingMax
  refine ⟨s, A, hA, ?_⟩
  intro σ C f P φ M r Z R tau saving hZ hR hRR htau hsaving hss hbudget
  let U := A * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
    (fieldConstant K / r.val) * Z ^ (-saving)
  have hU : 0 ≤ U := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hA (apply_nonneg _ _))
        (div_nonneg (fieldConstant_nonneg K) r.property.le))
      (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  have hp (p) (hp : p ∈ P) :
      ‖dualTail K S D Γ μv
        (primitivePairBlock K S D Γ hΓ p.1 p.2 φ h hlc hcs M r)
        (Z ^ (R + tau))‖ ≤
      (2 : ℝ) ^ (M ∪ principalMask K S
        (pairSupport K S D p.1.2 p.2.2 p.1.1 p.2.1)
        (pairExponent K S p.1.2 p.2.2 p.1.1 p.2.1)).card * U := by
    apply dualTail_norm_le K S D Γ μv _ _ U hU
    intro δ hδ
    exact hb _ _ φ M r δ Z R tau saving hZ hR hRR htau hsaving hss
      (hbudget p hp δ (Finset.mem_powerset.mp hδ))
  unfold sourceSubsetTail
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ P, ‖pairWeight K S D C f p‖ *
        ((2 : ℝ) ^ (M ∪ principalMask K S
          (pairSupport K S D p.1.2 p.2.2 p.1.1 p.2.1)
          (pairExponent K S p.1.2 p.2.2 p.1.1 p.2.1)).card * U) := by
      apply Finset.sum_le_sum
      intro p hp'
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hp p hp') (norm_nonneg _)
    _ = coefficientMaskMass K S D C f P M * U := by
      unfold coefficientMaskMass
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      ring

end HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalTailBound

end

