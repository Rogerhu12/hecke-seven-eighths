import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCorrelationSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.GeneratedCorrelation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonSupportSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonMass

/-!
# The actual normalized mass of the second common-support labels

The Poisson factor is the one obtained after the genuine quotient-cardinality
cancellation.  The correlation is the complete correlation at the original
frequency and with independently chosen actual generators.  Its gcd and
unit-radical bound is proved by the local table and CRT transport.

Multiplying these factors, the two central norm factors, one pool density,
and the literal child budget `M' + (b₂ - p₂ + w + B + ell)` leaves precisely
the inverse common radical.  The sum over the actual finite label set is
then bounded by the proved harmonic common-support count.  No bound on an
aggregate label weight is an input.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

section Poisson

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

/-- The actual Möbius coefficient and the fixed field factor retain only
the genuine inverse dilation radius after cardinality cancellation. -/
theorem secondOrbitalScalar_norm_le
    (r : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K))) :
    ‖secondOrbitalScalar (K := K) (S := S) r D‖ ≤
      orbitalFieldFactor K /
        (r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
          (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val) := by
  let N : ℝ := (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
    (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val
  have hN : 0 < N := (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
    (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).property
  have hμ : ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ ≤ 1 := by
    unfold UniqueFactorizationMonoid.moebius
    split_ifs <;> simp
  have hF := orbitalFieldFactor_nonneg K
  change ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ) *
    ((r.val * N : ℝ) : ℂ)⁻¹ * (orbitalFieldFactor K : ℂ)‖ ≤ _
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos r.property hN), Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hF]
  calc
    _ ≤ 1 * (r.val * N)⁻¹ * orbitalFieldFactor K :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hμ (inv_nonneg.mpr (mul_pos r.property hN).le)) hF
    _ = _ := by dsimp [N]; ring

theorem secondOrbitalScalar_norm_le_rpow
    (Z : ℝ) (hZ : 1 < Z) (a₀ krow g : ℝ)
    (r : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)))
    (hscale : Z ^ (a₀ - krow - g) ≤
      r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val) :
    ‖secondOrbitalScalar (K := K) (S := S) r D‖ ≤
      orbitalFieldFactor K * Z ^ (krow + g - a₀) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hpow : 0 < Z ^ (a₀ - krow - g) := Real.rpow_pos_of_pos hz _
  apply (secondOrbitalScalar_norm_le r D).trans
  calc
    _ ≤ orbitalFieldFactor K * (1 / Z ^ (a₀ - krow - g)) := by
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hpow hscale)
          (orbitalFieldFactor_nonneg K)
    _ = _ := by
      rw [show krow + g - a₀ = -(a₀ - krow - g) by ring, Real.rpow_neg hz.le]
      ring

end Poisson

/-- The two child lengths in §4.8, using literal ideal logarithms. -/
def secondCommonChildWidth (Z a₀ q wo krow g : ℝ)
    (D E T V : Ideal (𝓞 K)) : ℝ :=
  (2 * a₀ - krow - g - idealLogLength Z (gcd D E) - idealLogLength Z V) +
    (q + wo + idealLogLength Z T + idealLogLength Z V)

def secondCommonChildAllowance (Z w B ell : ℝ) (D E : Ideal (𝓞 K)) : ℝ :=
  (idealLogLength Z D + idealLogLength Z E) / 2 -
    idealLogLength Z (commonRadical D E) + w + B + ell

/-- Every factor occurs once: pool density, inverse Poisson radius,
complete correlation, central normalization, and the child allowance. -/
theorem second_scalar_budget_identity
    (Z : ℝ) (hZ : 0 < Z) (F a₀ q wo w B krow g ell b₂ p₂ g₂ t₂ V₂ : ℝ) :
    Z ^ (-ell) * (F * Z ^ (krow + g - a₀)) * (Z ^ g₂ / Z ^ t₂) / Z ^ b₂ *
        Z ^ ((2 * a₀ - krow - g - g₂ - V₂) + (q + wo + t₂ + V₂) +
          (b₂ - p₂ + w + B + ell)) =
      F * Z ^ (a₀ + q + wo + w + B) / Z ^ p₂ := by
  calc
    _ = F * (Z ^ (-ell) * Z ^ (krow + g - a₀) * (Z ^ g₂ / Z ^ t₂) /
        Z ^ b₂ * Z ^ ((2 * a₀ - krow - g - g₂ - V₂) + (q + wo + t₂ + V₂) +
          (b₂ - p₂ + w + B + ell))) := by ring
    _ = F * Z ^ (a₀ + q + wo + w + B - p₂) := by
      rw [← Real.rpow_sub hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ,
        ← Real.rpow_sub hZ, ← Real.rpow_add hZ]
      congr 1
      congr 1
      ring
    _ = _ := by rw [Real.rpow_sub hZ]; ring

theorem second_central_norm_eq_rpow (Z : ℝ) (hZ : 1 < Z)
    (D E : Ideal (𝓞 K)) (hD : D ≠ 0) (hE : E ≠ 0) :
    Z ^ ((idealLogLength Z D + idealLogLength Z E) / 2) =
      Real.sqrt (Ideal.absNorm D : ℝ) * Real.sqrt (Ideal.absNorm E : ℝ) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  rw [show (idealLogLength Z D + idealLogLength Z E) / 2 =
    idealLogLength Z D * (1 / 2) + idealLogLength Z E * (1 / 2) by ring,
    Real.rpow_add hz, Real.rpow_mul hz.le, Real.rpow_mul hz.le,
    rpow_idealLogLength Z hZ D hD, rpow_idealLogLength Z hZ E hE,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]

theorem second_actual_scalar_budget_identity
    (Z : ℝ) (hZ : 1 < Z) (F a₀ q wo w B krow g ell : ℝ)
    (D E T V : Ideal (𝓞 K)) (hD : D ≠ 0) (hE : E ≠ 0) (hT : T ≠ 0) :
    Z ^ (-ell) * (F * Z ^ (krow + g - a₀)) *
        ((Ideal.absNorm (gcd D E) : ℝ) / (Ideal.absNorm T : ℝ)) /
        (Real.sqrt (Ideal.absNorm D : ℝ) * Real.sqrt (Ideal.absNorm E : ℝ)) *
        Z ^ (secondCommonChildWidth Z a₀ q wo krow g D E T V +
          secondCommonChildAllowance Z w B ell D E) =
      F * Z ^ (a₀ + q + wo + w + B) /
        (Ideal.absNorm (commonRadical D E) : ℝ) := by
  have he := second_scalar_budget_identity Z (zero_lt_one.trans hZ)
    F a₀ q wo w B krow g ell
    ((idealLogLength Z D + idealLogLength Z E) / 2)
    (idealLogLength Z (commonRadical D E)) (idealLogLength Z (gcd D E))
    (idealLogLength Z T) (idealLogLength Z V)
  simpa only [rpow_idealLogLength Z hZ (gcd D E) (gcd_ne_zero_of_left hD),
    rpow_idealLogLength Z hZ T hT, second_central_norm_eq_rpow Z hZ D E hD hE,
    rpow_idealLogLength Z hZ (commonRadical D E) (commonRadical_ne_zero D E),
    secondCommonChildWidth, secondCommonChildAllowance] using he

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]

section Block

variable {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

def FirstCommonCharacterBlock.secondUnitRadical
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS) (h : A.R) : A.Exterior :=
  unitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity h

def FirstCommonCharacterBlock.secondNonunitRadical
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS) (h : A.R) : A.Exterior :=
  nonunitFrequencyRadical C b.primes b.leftMultiplicity b.rightMultiplicity h

/-- The complete actual common correlation, with the supplied original
generators.  Its phase is never replaced by a canonical-generator phase. -/
def FirstCommonCharacterBlock.secondCorrelation
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (a d : A.R)
    (ha : A.Generates (primePowerProduct b.primes b.leftMultiplicity) a)
    (hd : A.Generates (primePowerProduct b.primes b.rightMultiplicity) d)
    (h : A.R) : ℂ :=
  generatedIdealCorrelation (σ := σ)
    (primePowerProduct b.primes b.leftMultiplicity)
    (primePowerProduct b.primes b.rightMultiplicity) a d ha hd h

theorem FirstCommonCharacterBlock.secondCorrelation_norm_le
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS) (a d : A.R)
    (ha : A.Generates (primePowerProduct b.primes b.leftMultiplicity) a)
    (hd : A.Generates (primePowerProduct b.primes b.rightMultiplicity) d)
    (h : A.R) :
    ‖b.secondCorrelation (σ := σ) a d ha hd h‖ ≤
      (Ideal.absNorm (gcd DE.1 DE.2) : ℝ) /
        (Ideal.absNorm (b.secondUnitRadical C h).val : ℝ) := by
  have he := actual_complete_correlation_gcd_radical_bound_of_generates
    C b.primes b.primes_injective b.leftMultiplicity b.rightMultiplicity
    b.left_positive a d ha hd h
  change ‖b.secondCorrelation (σ := σ) a d ha hd h‖ ≤
    (Ideal.absNorm (gcd (primePowerProduct b.primes b.leftMultiplicity).val
      (primePowerProduct b.primes b.rightMultiplicity).val) : ℝ) /
      (Ideal.absNorm (b.secondUnitRadical C h).val : ℝ) at he
  simpa only [b.common_left, b.common_right] using he

/-- The actual normalized scalar after assigning the specified child
budget.  Both common central factors and the pool density occur once. -/
def FirstCommonCharacterBlock.secondNormalizedWeight
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (Z a₀ q wo w B krow g ell density : ℝ)
    (r : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (a d : A.R)
    (ha : A.Generates (primePowerProduct b.primes b.leftMultiplicity) a)
    (hd : A.Generates (primePowerProduct b.primes b.rightMultiplicity) d)
    (h : A.R) : ℝ :=
  density * ‖secondOrbitalScalar (K := K) (S := A.Sf) r D‖ *
    ‖b.secondCorrelation (σ := σ) a d ha hd h‖ /
    (Real.sqrt (Ideal.absNorm DE.1 : ℝ) * Real.sqrt (Ideal.absNorm DE.2 : ℝ)) *
    Z ^ (secondCommonChildWidth Z a₀ q wo krow g DE.1 DE.2
        (b.secondUnitRadical C h).val (b.secondNonunitRadical C h).val +
      secondCommonChildAllowance Z w B ell DE.1 DE.2)

theorem FirstCommonCharacterBlock.secondNormalizedWeight_le
    (b : FirstCommonCharacterBlock fullI fullJ DE)
    (C : A.GeneralArithmeticContext σ η hS)
    (Z : ℝ) (hZ : 1 < Z) (a₀ q wo w B krow g ell density densityBound : ℝ)
    (hB : 0 ≤ densityBound) (hdensity : density ≤ densityBound * Z ^ (-ell))
    (r : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
    (hscale : Z ^ (a₀ - krow - g) ≤
      r.val * (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
        (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val)
    (a d : A.R)
    (ha : A.Generates (primePowerProduct b.primes b.leftMultiplicity) a)
    (hd : A.Generates (primePowerProduct b.primes b.rightMultiplicity) d)
    (h : A.R) :
    b.secondNormalizedWeight C Z a₀ q wo w B krow g ell density r D a d ha hd h ≤
      densityBound * orbitalFieldFactor K * Z ^ (a₀ + q + wo + w + B) /
        (Ideal.absNorm (commonRadical DE.1 DE.2) : ℝ) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hD : DE.1 ≠ 0 := by
    rw [← b.common_left]
    exact (primePowerProduct b.primes b.leftMultiplicity).property.1
  have hE : DE.2 ≠ 0 := by
    rw [← b.common_right]
    exact (primePowerProduct b.primes b.rightMultiplicity).property.1
  have hρ : 0 ≤ densityBound * Z ^ (-ell) :=
    mul_nonneg hB (Real.rpow_nonneg hz.le _)
  have hscalar := secondOrbitalScalar_norm_le_rpow Z hZ a₀ krow g r D hscale
  have hcorr := b.secondCorrelation_norm_le C a d ha hd h
  have hfirst := mul_le_mul hdensity hscalar (norm_nonneg _) hρ
  have hsecond := mul_le_mul hfirst hcorr (norm_nonneg _)
    (mul_nonneg hρ (mul_nonneg (orbitalFieldFactor_nonneg K) (Real.rpow_nonneg hz.le _)))
  have hthird := div_le_div_of_nonneg_right hsecond
    (mul_nonneg (Real.sqrt_nonneg (Ideal.absNorm DE.1 : ℝ))
      (Real.sqrt_nonneg (Ideal.absNorm DE.2 : ℝ)))
  have hfourth := mul_le_mul_of_nonneg_right hthird
    (Real.rpow_nonneg hz.le
      (secondCommonChildWidth Z a₀ q wo krow g DE.1 DE.2
          (b.secondUnitRadical C h).val (b.secondNonunitRadical C h).val +
        secondCommonChildAllowance Z w B ell DE.1 DE.2))
  unfold FirstCommonCharacterBlock.secondNormalizedWeight
  apply hfourth.trans_eq
  calc
    _ = densityBound *
      (Z ^ (-ell) * (orbitalFieldFactor K * Z ^ (krow + g - a₀)) *
        ((Ideal.absNorm (gcd DE.1 DE.2) : ℝ) /
          (Ideal.absNorm (b.secondUnitRadical C h).val : ℝ)) /
        (Real.sqrt (Ideal.absNorm DE.1 : ℝ) * Real.sqrt (Ideal.absNorm DE.2 : ℝ)) *
        Z ^ (secondCommonChildWidth Z a₀ q wo krow g DE.1 DE.2
            (b.secondUnitRadical C h).val (b.secondNonunitRadical C h).val +
          secondCommonChildAllowance Z w B ell DE.1 DE.2)) := by ring
    _ = _ := by
      rw [second_actual_scalar_budget_identity Z hZ (orbitalFieldFactor K)
        a₀ q wo w B krow g ell DE.1 DE.2
        (b.secondUnitRadical C h).val (b.secondNonunitRadical C h).val
        hD hE (b.secondUnitRadical C h).property.1]
      ring

end Block

/-- Uniform mass for the actual complete common-support labels and every
frequency in their retained unit/nonunit partitions.  The counting
constant is chosen before all moving ideals, generators, and scales.
The only density input is a single scalar bound; `actual_pool_density_bound`
below obtains it from the literal pool cardinality. -/
theorem actual_second_normalized_common_mass
    (C : A.GeneralArithmeticContext σ η hS)
    (size ε : ℝ) (hsize : 0 ≤ size) (hε : 0 < ε) :
    ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ Z : ℝ, 1 < Z →
    ∀ s : Ideal (𝓞 K), Squarefree s → s ≠ 0 → ∀ labels : Finset (Label K),
      (∀ v ∈ labels, Valid s v) →
      (∀ v ∈ labels, (Ideal.absNorm v.1.1 : ℝ) ≤ Z ^ size ∧
        (Ideal.absNorm v.1.2 : ℝ) ≤ Z ^ size) →
    ∀ {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior},
    ∀ blocks : ∀ v : labels, FirstCommonCharacterBlock fullI fullJ v.val.1,
    ∀ a d h : labels → A.R,
    ∀ ha : ∀ v : labels, A.Generates
      (primePowerProduct (blocks v).primes (blocks v).leftMultiplicity) (a v),
    ∀ hd : ∀ v : labels, A.Generates
      (primePowerProduct (blocks v).primes (blocks v).rightMultiplicity) (d v),
    ∀ a₀ q wo w B krow g ell density densityBound : ℝ,
      0 ≤ densityBound → density ≤ densityBound * Z ^ (-ell) →
    ∀ r : {r : ℝ // 0 < r}, ∀ divisors : labels → Finset (HeightOneSpectrum A.R),
      (∀ v : labels, Z ^ (a₀ - krow - g) ≤
        r.val * (sIntegerElementNorm K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
          (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) (divisors v))).val) →
      (∑ v : labels,
        (blocks v).secondNormalizedWeight C Z a₀ q wo w B krow g ell density r
          (divisors v) (a v) (d v) (ha v) (hd v) (h v)) ≤
        (Cbound * densityBound * orbitalFieldFactor K) *
          Z ^ ((a₀ + q + wo + w + B) + ε) / (Ideal.absNorm s : ℝ) := by
  obtain ⟨Cbound, hC, hmass⟩ := common_radical_harmonic_mass (K := K) size ε hsize hε
  refine ⟨Cbound, hC, ?_⟩
  intro Z hZ s hs hs0 labels hvalid hnorm α β fullI fullJ blocks a d h ha hd
    a₀ q wo w B krow g ell density densityBound hDensityBound hdensity r divisors hscale
  let F : ℝ := densityBound * orbitalFieldFactor K * Z ^ (a₀ + q + wo + w + B)
  have hF : 0 ≤ F := mul_nonneg
    (mul_nonneg hDensityBound (orbitalFieldFactor_nonneg K))
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  calc
    _ ≤ ∑ v : labels, F *
        (1 / (Ideal.absNorm (commonRadical v.val.1.1 v.val.1.2) : ℝ)) := by
      apply Finset.sum_le_sum
      intro v _
      apply ((blocks v).secondNormalizedWeight_le C Z hZ a₀ q wo w B krow g ell
        density densityBound hDensityBound hdensity r (divisors v) (hscale v)
        (a v) (d v) (ha v) (hd v) (h v)).trans_eq
      dsimp only [F]
      ring
    _ = F * ∑ v : labels,
        1 / (Ideal.absNorm (commonRadical v.val.1.1 v.val.1.2) : ℝ) := by
      rw [Finset.mul_sum]
    _ = F * ∑ v ∈ labels,
        1 / (Ideal.absNorm (commonRadical v.1.1 v.1.2) : ℝ) := by
      exact congrArg (fun x : ℝ => F * x) (Finset.sum_coe_sort labels
        (fun v : Label K => 1 / (Ideal.absNorm (commonRadical v.1.1 v.1.2) : ℝ)))
    _ ≤ F * (Cbound * Z ^ ε / (Ideal.absNorm s : ℝ)) :=
      mul_le_mul_of_nonneg_left (hmass Z hZ.le s hs hs0 labels hvalid hnorm) hF
    _ = _ := by
      rw [Real.rpow_add (zero_lt_one.trans hZ)]
      dsimp only [F]
      ring

/-- A literal pool-cardinality lower bound pays for its single reciprocal
average.  The finite representation bound is multiplied exactly once. -/
theorem actual_pool_density_bound {ι : Type*} (pool : Finset ι) (fiber : ℕ)
    (Z : ℝ) (hZ : 0 < Z) (ell poolConstant : ℝ)
    (hcard : Z ^ ell ≤ poolConstant * (pool.card : ℝ)) :
    (fiber : ℝ) / (pool.card : ℝ) ≤
      ((fiber : ℝ) * poolConstant) * Z ^ (-ell) := by
  have hpow : 0 < Z ^ ell := Real.rpow_pos_of_pos hZ _
  have hpool : 0 < (pool.card : ℝ) := by
    by_contra hn
    have he : (pool.card : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg _)
    rw [he, mul_zero] at hcard
    exact (not_le_of_gt hpow) hcard
  have hinv : 1 / (pool.card : ℝ) ≤ poolConstant * Z ^ (-ell) := by
    rw [Real.rpow_neg hZ.le, ← div_eq_mul_inv]
    exact (div_le_div_iff₀ hpool hpow).mpr (by simpa only [one_mul] using hcard)
  calc
    _ = (fiber : ℝ) * (1 / (pool.card : ℝ)) := by ring
    _ ≤ (fiber : ℝ) * (poolConstant * Z ^ (-ell)) :=
      mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _)
    _ = _ := by ring

theorem amplifier_squaredCentral_moving_density (e : AmplifierValuation)
    (Z : ℝ) (hZ : 1 < Z) (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    e.squaredCentral (Ideal.absNorm I : ℝ) ≤
      Z ^ (-((e.movingMultiplicity : ℝ) * idealLogLength Z I)) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hnorm : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
  cases e <;> simp only [AmplifierValuation.squaredCentral,
    AmplifierValuation.movingMultiplicity, Nat.cast_one, Nat.cast_zero,
    one_mul, zero_mul, neg_zero, Real.rpow_zero]
  · exact le_of_eq (by rw [Real.rpow_neg hz.le, rpow_idealLogLength Z hZ I hI])
  · exact amplifier_error_squared_le_one .six (Ideal.absNorm I : ℝ) hnorm
  · exact le_of_eq (by rw [Real.rpow_neg hz.le, rpow_idealLogLength Z hZ I hI])

/-- The correction from the genuine local Gauss table pays for its moving
support.  It is the squared norm of the original complex difference. -/
theorem actual_amplifier_error_moving_density
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation) (Z : ℝ) (hZ : 1 < Z) :
    ‖centralPrimePower C p e.multiplicity 0 -
      centralPrimePower C p e.multiplicity 6‖ ^ 2 ≤
      Z ^ (-((e.movingMultiplicity : ℝ) * idealLogLength Z (primeIdeal p).val)) := by
  have he : ‖centralPrimePower C p e.multiplicity 0 -
      centralPrimePower C p e.multiplicity 6‖ ^ 2 =
      e.squaredCentral (Ideal.absNorm (primeIdeal p).val : ℝ) := by
    rw [centralPrimePower_difference_norm_sq]
    cases e <;> norm_num [AmplifierValuation.multiplicity, AmplifierValuation.squaredCentral,
      Q, SArithmeticData.exteriorNorm, idealNorm]
  rw [he]
  exact amplifier_squaredCentral_moving_density e Z hZ (primeIdeal p).val
    (primeIdeal p).property.1

/-- Consequently the one correction coefficient cancels `wₒ` exactly in
the parent allowance; there is no second pool-density charge. -/
theorem actual_amplifier_error_parent_budget
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation) (Z : ℝ) (hZ : 1 < Z) (x : ℝ) :
    ‖centralPrimePower C p e.multiplicity 0 -
      centralPrimePower C p e.multiplicity 6‖ ^ 2 *
      Z ^ (x + (e.movingMultiplicity : ℝ) * idealLogLength Z (primeIdeal p).val) ≤
      Z ^ x := by
  apply (mul_le_mul_of_nonneg_right
    (actual_amplifier_error_moving_density C p e Z hZ)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)).trans_eq
  rw [← Real.rpow_add (zero_lt_one.trans hZ)]
  congr 1
  ring

end HeckeSkeleton.Moments.EngineStep

end

#print axioms HeckeSkeleton.Moments.EngineStep.second_actual_scalar_budget_identity
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.secondNormalizedWeight_le
#print axioms HeckeSkeleton.Moments.EngineStep.actual_second_normalized_common_mass
#print axioms HeckeSkeleton.Moments.EngineStep.actual_pool_density_bound
#print axioms HeckeSkeleton.Moments.EngineStep.actual_amplifier_error_parent_budget


