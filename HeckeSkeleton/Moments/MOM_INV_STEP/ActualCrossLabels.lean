import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalGroupedGauss
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalCubeLabels
import HeckeSkeleton.Moments.MOM_INV_STEP.SexticEvenness

/-!
# Actual CRT cross symbols and the first column labels

The prime evaluation in the constructed packet is identified with the
literal ideal symbol. Reciprocity then reassembles its cross symbols
into rows on the selected ideal generators. Every nonvanishing statement
used to reduce a sixth-root exponent follows from actual coprimality.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualCrossLabels

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open ActualFiniteSource ConductorMasks PrimitivePoissonSource PrimitiveFourier
  PrimitivePacketCRT CanonicalGroupedGauss CanonicalConductor
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "E" => CanonicalIdealRow.exteriorMonoid K S
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

def singletonBlock (p : ExteriorPrime K Sset) : PrimeBlock K Sset where
  support := {p.val}
  outside q hq := by simpa only [Finset.mem_singleton.mp hq] using p.property
  awaySix q hq := by
    simpa only [Finset.mem_singleton.mp hq] using D.away_six p.val p.property

theorem primeScalar_eq_idealSymbol (p : ExteriorPrime K Sset) (a : OS) :
    primeScalar K S D p.val a = idealSymbol K Sset D (exteriorPrimeIdeal K Sset p) a := by
  have hone : (1 : ZMod 6) ≠ 0 := by decide
  have hE : primitiveExterior K S (singletonBlock K S D p) (fun _ => (1 : ZMod 6)) =
      exteriorPrimeIdeal K Sset p := by
    apply Subtype.ext
    apply Subtype.ext
    change IdealMobiusMask.primeProduct
      (activeSupport {p.val} (fun _ => (1 : ZMod 6))) = p.val.asIdeal
    simp only [activeSupport, hone, ne_eq, not_false_eq_true,
      Finset.filter_true, IdealMobiusMask.primeProduct, Finset.prod_singleton]
  have h := primitiveIdeal_symbol_eq_product K S D
    (singletonBlock K S D p) (fun _ => (1 : ZMod 6)) a
  rw [hE] at h
  simpa only [singletonBlock, activeSupport, hone, ne_eq, not_false_eq_true,
    Finset.filter_true, Finset.prod_singleton] using h.symm

theorem primeScalar_generator_eq_row (hallowed : AllowedGeneratorInput K Sset D)
    (u : Ext) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ Sset) :
    primeScalar K S D p (D.generator u) =
      CanonicalIdealRow.row K S D hallowed u (CanonicalCubeLabels.prime K S p) := by
  calc
    _ = idealSymbol K Sset D (exteriorPrimeIdeal K Sset ⟨p, hp⟩) (D.generator u) :=
      primeScalar_eq_idealSymbol K S D ⟨p, hp⟩ _
    _ = idealSymbol K Sset D u (D.generator (exteriorPrimeIdeal K Sset ⟨p, hp⟩)) :=
      hallowed.reciprocity _ u
    _ = _ := by
      simp only [CanonicalIdealRow.row_apply, CanonicalCubeLabels.prime, dif_pos hp,
        CanonicalIdealRow.generator, CanonicalIdealRow.primeIdeal,
        CanonicalIdealRow.toExterior_ofExterior]

theorem idealSymbol_primitiveModulus_eq_product
    (hallowed : AllowedGeneratorInput K Sset D) (u : Ext)
    (B : PrimeBlock K Sset) (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    idealSymbol K Sset D u (primitiveModulus K S D B t) =
      ∏ p ∈ activeSupport B.support t,
        CanonicalIdealRow.row K S D hallowed u (CanonicalCubeLabels.prime K S p) := by
  change idealSymbol K Sset D u (D.generator (primitiveExterior K S B t)) = _
  rw [hallowed.reciprocity u (primitiveExterior K S B t), primitiveIdeal_symbol_eq_product]
  apply Finset.prod_congr rfl
  intro p hp
  exact primeScalar_generator_eq_row K S D hallowed u p
    (B.outside p (Finset.mem_filter.mp hp).1)

theorem primitiveCoefficient_generator_eq_product
    (hallowed : AllowedGeneratorInput K Sset D) (u : Ext)
    (B : PrimeBlock K Sset) (t : HeightOneSpectrum (𝓞 K) → ZMod 6) :
    primitiveCoefficient K S D B t (Ideal.Quotient.mk _ (D.generator u)) =
      ∏ p ∈ activeSupport B.support t,
        CanonicalIdealRow.row K S D hallowed u (CanonicalCubeLabels.prime K S p) ^ (t p).val := by
  rw [primitiveCoefficient_mk_eq_product]
  apply Finset.prod_congr rfl
  intro p hp
  rw [primeScalar_generator_eq_row K S D hallowed u p
    (B.outside p (Finset.mem_filter.mp hp).1)]

/-- The two directed symbols of a uniform residual packet become one
finite product on that same actual residual ideal. -/
theorem crossFactor_uniform_left (hallowed : AllowedGeneratorInput K Sset D)
    (B₁ B₂ : PrimeBlock K Sset) (t : HeightOneSpectrum (𝓞 K) → ZMod 6) (j : ℕ)
    (ht : ∀ p ∈ activeSupport B₁.support t, (t p).val = j) :
    crossFactor K S D B₁ B₂ t =
      ∏ p ∈ activeSupport B₂.support t,
        CanonicalIdealRow.row K S D hallowed (primitiveExterior K S B₁ t)
            (CanonicalCubeLabels.prime K S p) ^ j *
          CanonicalIdealRow.row K S D hallowed (primitiveExterior K S B₁ t)
            (CanonicalCubeLabels.prime K S p) ^ (t p).val := by
  unfold crossFactor
  rw [primitiveCoefficient_uniform K S D B₁ t j ht]
  change idealSymbol K Sset D (primitiveExterior K S B₁ t) (primitiveModulus K S D B₂ t) ^ j *
    primitiveCoefficient K S D B₂ t (Ideal.Quotient.mk _ (D.generator (primitiveExterior K S B₁ t))) = _
  rw [idealSymbol_primitiveModulus_eq_product K S D hallowed,
    primitiveCoefficient_generator_eq_product K S D hallowed,
    ← Finset.prod_pow, ← Finset.prod_mul_distrib]

/-- A one/five residual cross factor is exactly one, with its actual
coprimality proved from disjoint prime supports. -/
theorem crossFactor_one_five_eq_one (hallowed : AllowedGeneratorInput K Sset D)
    (B₁ B₂ : PrimeBlock K Sset) (hdisj : Disjoint B₁.support B₂.support)
    (t : HeightOneSpectrum (𝓞 K) → ZMod 6)
    (h₁ : ∀ p ∈ activeSupport B₁.support t, (t p).val = 1)
    (h₂ : ∀ p ∈ activeSupport B₂.support t, (t p).val = 5) :
    crossFactor K S D B₁ B₂ t = 1 := by
  let I₁ := primitiveExterior K S B₁ t
  let I₂ := primitiveExterior K S B₂ t
  have hcop : IsCoprime I₁.val.val I₂.val.val :=
    primitiveIdeals_coprime K S B₁ B₂ hdisj t
  have hmask := CanonicalIdealRow.row_mask K S D hallowed I₁
    (CanonicalIdealRow.ofExterior K S I₂)
  simp only [CubeAlgebra.sixthMask, CanonicalIdealRow.row_apply,
    CanonicalIdealRow.generator_ofExterior, CanonicalIdealRow.ofExterior_val,
    if_pos hcop] at hmask
  unfold crossFactor
  rw [primitiveCoefficient_uniform K S D B₁ t 1 h₁,
    primitiveCoefficient_uniform K S D B₂ t 5 h₂, pow_one]
  change idealSymbol K Sset D I₁ (D.generator I₂) *
    idealSymbol K Sset D I₂ (D.generator I₁) ^ 5 = 1
  rw [hallowed.reciprocity I₂ I₁, ← pow_succ']
  simpa only [if_pos hcop] using hmask

theorem residual_cross_eq_one (hallowed : AllowedGeneratorInput K Sset D)
    (n₁ n₂ b₁ b₂ : Ext) :
    crossFactor K S D (leftBlock K S D n₁ n₂ b₁ b₂)
      (rightBlock K S D n₁ n₂ b₁ b₂) (pairExponent K S n₁ n₂ b₁ b₂) = 1 := by
  apply crossFactor_one_five_eq_one K S D hallowed _ _
    (left_right_disjoint K S D n₁ n₂ b₁ b₂)
  · intro p hp
    rw [left_digit K S D n₁ n₂ b₁ b₂ p (Finset.mem_filter.mp hp).1]
    rfl
  · intro p hp
    rw [right_digit K S D n₁ n₂ b₁ b₂ p (Finset.mem_filter.mp hp).1]
    rfl

private theorem left_active_factor (z : ℂ) (hz : z ^ 6 = 1)
    (parityBit ε₁ ε₂ : Bool)
    (ht : CubeAlgebra.conductorExponent parityBit ε₁ ε₂ ≠ 0) :
    z * z ^ (CubeAlgebra.conductorExponent parityBit ε₁ ε₂).val =
      z ^ CubeAlgebra.crtExponent false parityBit ε₁ ε₂ := by
  have he : ((CubeAlgebra.conductorExponent parityBit ε₁ ε₂).val + 1) % 6 =
      CubeAlgebra.crtExponent false parityBit ε₁ ε₂ := by
    revert ht
    cases parityBit <;> cases ε₁ <;> cases ε₂ <;> decide
  rw [← pow_succ', pow_eq_pow_mod _ hz, he]

private theorem right_active_factor (z : ℂ) (hz : z ^ 6 = 1)
    (parityBit ε₁ ε₂ : Bool)
    (ht : CubeAlgebra.conductorExponent parityBit ε₁ ε₂ ≠ 0) :
    z ^ 5 * z ^ (CubeAlgebra.conductorExponent parityBit ε₁ ε₂).val =
      (star z) ^ CubeAlgebra.crtExponent true parityBit ε₁ ε₂ := by
  have hstar : z ^ 5 = star z := GaussConjugation.pow_five_eq_conj z (Or.inr hz)
  rw [← hstar, ← pow_mul, ← pow_add]
  have he : (5 + (CubeAlgebra.conductorExponent parityBit ε₁ ε₂).val) % 6 =
      (5 * CubeAlgebra.crtExponent true parityBit ε₁ ε₂) % 6 := by
    revert ht
    cases parityBit <;> cases ε₁ <;> cases ε₂ <;> decide
  rw [pow_eq_pow_mod (5 + (CubeAlgebra.conductorExponent parityBit ε₁ ε₂).val) hz,
    pow_eq_pow_mod (5 * CubeAlgebra.crtExponent true parityBit ε₁ ε₂) hz, he]

private theorem row_crt_left {R ι : Type*} [CommMonoid R] (χ : R →* ℂ)
    (p : ι → R) (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hχ : ∀ i ∈ B, χ (p i) ^ 6 = 1) :
    (∏ i ∈ B.filter (fun i => CubeAlgebra.conductorExponent
        (CubeAlgebra.parity (v i)) (ε₁ i) (ε₂ i) ≠ 0),
      χ (p i) * χ (p i) ^
        (CubeAlgebra.conductorExponent (CubeAlgebra.parity (v i)) (ε₁ i) (ε₂ i)).val) =
      χ (CubeAlgebra.crtLabel p B v ε₁ ε₂ false) := by
  simp only [CubeAlgebra.crtLabel, CubeAlgebra.primeProduct, map_prod, map_pow,
    Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases ht : CubeAlgebra.conductorExponent (CubeAlgebra.parity (v i)) (ε₁ i) (ε₂ i) = 0
  · simp [CubeAlgebra.crtExponent, ht]
  · rw [if_pos ht]
    exact left_active_factor (χ (p i)) (hχ i hi) _ _ _ ht

private theorem row_crt_right {R ι : Type*} [CommMonoid R] (χ : R →* ℂ)
    (p : ι → R) (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hχ : ∀ i ∈ B, χ (p i) ^ 6 = 1) :
    (∏ i ∈ B.filter (fun i => CubeAlgebra.conductorExponent
        (CubeAlgebra.parity (v i)) (ε₁ i) (ε₂ i) ≠ 0),
      χ (p i) ^ 5 * χ (p i) ^
        (CubeAlgebra.conductorExponent (CubeAlgebra.parity (v i)) (ε₁ i) (ε₂ i)).val) =
      star (χ (CubeAlgebra.crtLabel p B v ε₁ ε₂ true)) := by
  simp only [CubeAlgebra.crtLabel, CubeAlgebra.primeProduct, map_prod, map_pow,
    star_prod, star_pow, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases ht : CubeAlgebra.conductorExponent (CubeAlgebra.parity (v i)) (ε₁ i) (ε₂ i) = 0
  · simp [CubeAlgebra.crtExponent, ht]
  · rw [if_pos ht]
    exact right_active_factor (χ (p i)) (hχ i hi) _ _ _ ht

theorem cube_prime_row_sixth (hallowed : AllowedGeneratorInput K Sset D)
    (u b₁ b₂ : Ext) (hcop : IsCoprime u.val.val (b₁.val.val * b₂.val.val).radical)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ CubeLabels.cubePrimeSupport b₁.val b₂.val) :
    CanonicalIdealRow.row K S D hallowed u (CanonicalCubeLabels.prime K S p) ^ 6 = 1 := by
  have hd : p.asIdeal ∣ (b₁.val.val * b₂.val.val).radical := by
    change p.asIdeal ∣ (b₁.val * b₂.val).val.radical
    rw [FirstSourceDecomposition.radical_eq_primeProduct (b₁.val * b₂.val)]
    exact Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (𝓞 K) => q.asIdeal) hp
  have hcop' : IsCoprime u.val.val (CanonicalCubeLabels.prime K S p).val.val := by
    rw [CanonicalCubeLabels.prime_val K S p
      (CanonicalCubeLabels.cubeSupport_outside K S b₁ b₂ p hp)]
    exact hcop.of_isCoprime_of_dvd_right hd
  simpa only [CubeAlgebra.sixthMask, if_pos hcop'] using
    CanonicalIdealRow.row_mask K S D hallowed u (CanonicalCubeLabels.prime K S p)

theorem cube_active_on_original_support (n₁ n₂ b₁ b₂ : Ext) :
    activeSupport (cubeBlock K S D n₁ n₂ b₁ b₂).support (pairExponent K S n₁ n₂ b₁ b₂) =
      (CubeLabels.cubePrimeSupport b₁.val b₂.val).filter (fun p =>
        CubeAlgebra.conductorExponent (CubeAlgebra.parity (CubeLabels.cubeMultiplicity b₁.val b₂.val p))
          (squarefreeBit K S n₁ p) (squarefreeBit K S n₂ p) ≠ 0) := by
  rw [cube_active]
  simpa only [cubeBlock, pairExponent_eq_cubeMultiplicity] using cubeActive_eq K S D n₁ n₂ b₁ b₂

theorem left_cube_cross (hallowed : AllowedGeneratorInput K Sset D)
    (n₁ n₂ b₁ b₂ : Ext) :
    crossFactor K S D (leftBlock K S D n₁ n₂ b₁ b₂)
        (cubeBlock K S D n₁ n₂ b₁ b₂) (pairExponent K S n₁ n₂ b₁ b₂) =
      idealSymbol K Sset D (leftIdeal K S D n₁ n₂ b₁ b₂)
        (CanonicalIdealRow.generator K S D (CanonicalCubeLabels.crt K S b₁ b₂
          (squarefreeBit K S n₁) (squarefreeBit K S n₂) false)) := by
  have hcop : IsCoprime (leftIdeal K S D n₁ n₂ b₁ b₂).val.val
      (b₁.val.val * b₂.val.val).radical := by
    rw [leftIdeal_val]
    exact (first_source_coprime K S D n₁ n₂ b₁ b₂).2.2.of_mul_left_left.of_mul_left_right
  have hleft : ∀ p ∈ activeSupport (leftBlock K S D n₁ n₂ b₁ b₂).support
      (pairExponent K S n₁ n₂ b₁ b₂), (pairExponent K S n₁ n₂ b₁ b₂ p).val = 1 := by
    intro p hp
    rw [left_digit K S D n₁ n₂ b₁ b₂ p (Finset.mem_filter.mp hp).1]
    rfl
  rw [crossFactor_uniform_left K S D hallowed _ _ _ 1 hleft,
    cube_active_on_original_support K S D n₁ n₂ b₁ b₂]
  simp only [pow_one, pairExponent_eq_cubeMultiplicity]
  rw [← CanonicalIdealRow.row_apply K S D hallowed]
  exact row_crt_left _ (CanonicalCubeLabels.prime K S) _ _ _ _
    (cube_prime_row_sixth K S D hallowed _ b₁ b₂ hcop)

theorem right_cube_cross (hallowed : AllowedGeneratorInput K Sset D)
    (n₁ n₂ b₁ b₂ : Ext) :
    crossFactor K S D (rightBlock K S D n₁ n₂ b₁ b₂)
        (cubeBlock K S D n₁ n₂ b₁ b₂) (pairExponent K S n₁ n₂ b₁ b₂) =
      star (idealSymbol K Sset D (rightIdeal K S D n₁ n₂ b₁ b₂)
        (CanonicalIdealRow.generator K S D (CanonicalCubeLabels.crt K S b₁ b₂
          (squarefreeBit K S n₁) (squarefreeBit K S n₂) true))) := by
  have hcop : IsCoprime (rightIdeal K S D n₁ n₂ b₁ b₂).val.val
      (b₁.val.val * b₂.val.val).radical := by
    rw [rightIdeal_val]
    exact (first_source_coprime K S D n₁ n₂ b₁ b₂).2.2.of_mul_left_right
  have hright : ∀ p ∈ activeSupport (rightBlock K S D n₁ n₂ b₁ b₂).support
      (pairExponent K S n₁ n₂ b₁ b₂), (pairExponent K S n₁ n₂ b₁ b₂ p).val = 5 := by
    intro p hp
    rw [right_digit K S D n₁ n₂ b₁ b₂ p (Finset.mem_filter.mp hp).1]
    rfl
  rw [crossFactor_uniform_left K S D hallowed _ _ _ 5 hright,
    cube_active_on_original_support K S D n₁ n₂ b₁ b₂]
  simp only [pairExponent_eq_cubeMultiplicity]
  rw [← CanonicalIdealRow.row_apply K S D hallowed]
  exact row_crt_right _ (CanonicalCubeLabels.prime K S) _ _ _ _
    (cube_prime_row_sixth K S D hallowed _ b₁ b₂ hcop)

/-- All six directed CRT symbols are now exactly the two column-label
rows. The residual-residual cross factor has been evaluated, not bounded. -/
theorem sourceCross_eq_crt_rows (hallowed : AllowedGeneratorInput K Sset D)
    (n₁ n₂ b₁ b₂ : Ext) :
    sourceCross K S D n₁ n₂ b₁ b₂ =
      idealSymbol K Sset D (leftIdeal K S D n₁ n₂ b₁ b₂)
        (CanonicalIdealRow.generator K S D (CanonicalCubeLabels.crt K S b₁ b₂
          (squarefreeBit K S n₁) (squarefreeBit K S n₂) false)) *
      star (idealSymbol K Sset D (rightIdeal K S D n₁ n₂ b₁ b₂)
        (CanonicalIdealRow.generator K S D (CanonicalCubeLabels.crt K S b₁ b₂
          (squarefreeBit K S n₁) (squarefreeBit K S n₂) true))) := by
  unfold sourceCross
  rw [residual_cross_eq_one K S D hallowed, left_cube_cross K S D hallowed,
    right_cube_cross K S D hallowed, one_mul]

/-- The genuine first Gauss factor has exactly one actual residual
factor per column and one cube factor common to the pair. -/
theorem pair_normalizedGauss_eq_column_factors (hallowed : AllowedGeneratorInput K Sset D)
    (n₁ n₂ b₁ b₂ : Ext) :
    normalizedPrimitiveGauss K S D (pairSupport K S D n₁ n₂ b₁ b₂)
        (pairExponent K S n₁ n₂ b₁ b₂) =
      normalizedPrimitiveGauss K S D (cubeBlock K S D n₁ n₂ b₁ b₂)
          (pairExponent K S n₁ n₂ b₁ b₂) *
        (thetaGamma K Sset D (leftIdeal K S D n₁ n₂ b₁ b₂) 1 *
          idealSymbol K Sset D (leftIdeal K S D n₁ n₂ b₁ b₂)
            (CanonicalIdealRow.generator K S D (CanonicalCubeLabels.crt K S b₁ b₂
              (squarefreeBit K S n₁) (squarefreeBit K S n₂) false))) *
        star (thetaGamma K Sset D (rightIdeal K S D n₁ n₂ b₁ b₂) 1 *
          idealSymbol K Sset D (rightIdeal K S D n₁ n₂ b₁ b₂)
            (CanonicalIdealRow.generator K S D (CanonicalCubeLabels.crt K S b₁ b₂
              (squarefreeBit K S n₁) (squarefreeBit K S n₂) true))) := by
  rw [pair_normalizedGauss_grouped K S D n₁ n₂ b₁ b₂ hallowed,
    sourceCross_eq_crt_rows K S D hallowed,
    SexticEvenness.thetaGamma_five_eq_conj K Sset D]
  simp only [star_mul, Complex.star_def]
  ring

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualCrossLabels
