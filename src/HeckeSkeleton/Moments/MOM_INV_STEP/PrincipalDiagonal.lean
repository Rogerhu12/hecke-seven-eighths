import HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalLocus

/-!
# The actual diagonal underlying the principal first source

The zero primitive conductor forces the two squarefree columns to agree.
It also forces the product of the two cube variables to be a square ideal.
These are consequences of the actual local exponent table, not additional
diagonal assumptions on the source.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalDiagonal

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton
open ActualFiniteSource ConductorMasks PrimitivePoissonSource CanonicalConductor
  CubeAlgebra
open scoped Classical BigOperators nonZeroDivisors

theorem conductorExponent_zero_iff (par ε₁ ε₂ : Bool) :
    conductorExponent par ε₁ ε₂ = 0 ↔ par = false ∧ ε₁ = ε₂ := by
  cases par <;> cases ε₁ <;> cases ε₂ <;> decide

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset

theorem exponent_zero_of_principal (n₁ n₂ b₁ b₂ : Ext)
    (hprincipal : activeSupport (pairSupport K S D n₁ n₂ b₁ b₂).support
      (pairExponent K S n₁ n₂ b₁ b₂) = ∅)
    (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ (pairSupport K S D n₁ n₂ b₁ b₂).support) :
    pairExponent K S n₁ n₂ b₁ b₂ p = 0 := by
  by_contra hne
  have hmem : p ∈ activeSupport (pairSupport K S D n₁ n₂ b₁ b₂).support
      (pairExponent K S n₁ n₂ b₁ b₂) := Finset.mem_filter.mpr ⟨hp, hne⟩
  rw [hprincipal] at hmem
  exact Finset.notMem_empty p hmem

theorem column_bits_eq_of_principal (n₁ n₂ b₁ b₂ : Ext)
    (hprincipal : activeSupport (pairSupport K S D n₁ n₂ b₁ b₂).support
      (pairExponent K S n₁ n₂ b₁ b₂) = ∅)
    (p : HeightOneSpectrum (𝓞 K)) :
    squarefreeBit K S n₁ p = squarefreeBit K S n₂ p := by
  by_cases hp : p ∈ (pairSupport K S D n₁ n₂ b₁ b₂).support
  · have hz := exponent_zero_of_principal K S D n₁ n₂ b₁ b₂ hprincipal p hp
    rw [pairExponent_eq_cubeMultiplicity] at hz
    exact ((conductorExponent_zero_iff _ _ _).mp hz).2
  · have hn₁ : ¬p.asIdeal ∣ n₁.val.val := by
      intro h
      exact hp ((mem_pairSupport K S D n₁ n₂ b₁ b₂ p).mpr
        (Or.inr (Or.inr (Or.inl h))))
    have hn₂ : ¬p.asIdeal ∣ n₂.val.val := by
      intro h
      exact hp ((mem_pairSupport K S D n₁ n₂ b₁ b₂ p).mpr
        (Or.inr (Or.inr (Or.inr h))))
    simp only [squarefreeBit, hn₁, hn₂, decide_false]

/-- Actual squarefree source columns coincide on the zero conductor. -/
theorem columns_eq_of_principal (n₁ n₂ b₁ b₂ : Ext)
    (hn₁ : Squarefree n₁.val.val) (hn₂ : Squarefree n₂.val.val)
    (hprincipal : activeSupport (pairSupport K S D n₁ n₂ b₁ b₂).support
      (pairExponent K S n₁ n₂ b₁ b₂) = ∅) : n₁ = n₂ := by
  have hs : FirstSourceDecomposition.primeSupport n₁.val =
      FirstSourceDecomposition.primeSupport n₂.val := by
    ext p
    rw [FirstSourceDecomposition.mem_primeSupport,
      FirstSourceDecomposition.mem_primeSupport]
    have hb := column_bits_eq_of_principal K S D n₁ n₂ b₁ b₂ hprincipal p
    change decide (p.asIdeal ∣ n₁.val.val) = decide (p.asIdeal ∣ n₂.val.val) at hb
    exact decide_eq_decide.mp hb
  apply Subtype.ext
  apply Subtype.ext
  calc
    n₁.val.val = IdealMobiusMask.primeProduct
        (FirstSourceDecomposition.primeSupport n₁.val) :=
      (FirstSourceDecomposition.primeProduct_support n₁.val hn₁).symm
    _ = IdealMobiusMask.primeProduct (FirstSourceDecomposition.primeSupport n₂.val) :=
      congrArg IdealMobiusMask.primeProduct hs
    _ = n₂.val.val := FirstSourceDecomposition.primeProduct_support n₂.val hn₂

/-- The square root is the actual q₀ J₂ from the cube decomposition. -/
theorem cube_product_square_of_principal (n₁ n₂ b₁ b₂ : Ext)
    (hprincipal : activeSupport (pairSupport K S D n₁ n₂ b₁ b₂).support
      (pairExponent K S n₁ n₂ b₁ b₂) = ∅) :
    b₁.val.val * b₂.val.val =
      (CubeLabels.q0 b₁.val b₂.val (squarefreeBit K S n₁) (squarefreeBit K S n₂) *
        CubeLabels.J2 b₁.val b₂.val (squarefreeBit K S n₁) (squarefreeBit K S n₂)) ^ 2 := by
  have hR := ((PrincipalLocus.pair_active_empty_iff K S D n₁ n₂ b₁ b₂).mp
    hprincipal).2.2
  have hsd := CubeLabels.s_dvd_R1 b₁.val b₂.val
    (squarefreeBit K S n₁) (squarefreeBit K S n₂)
  rw [hR] at hsd
  have hs : CubeLabels.s b₁.val b₂.val = 1 := by
    rw [Ideal.one_eq_top] at hsd ⊢
    apply le_antisymm le_top
    exact Ideal.dvd_iff_le.mp hsd
  rw [CubeLabels.actual_cube_decomposition b₁.val b₂.val
    (squarefreeBit K S n₁) (squarefreeBit K S n₂), hs, mul_one, mul_pow]

/-- Both restrictions needed to count the actual first principal term. -/
theorem principal_source_diagonal (n₁ n₂ b₁ b₂ : Ext)
    (hn₁ : Squarefree n₁.val.val) (hn₂ : Squarefree n₂.val.val)
    (hprincipal : activeSupport (pairSupport K S D n₁ n₂ b₁ b₂).support
      (pairExponent K S n₁ n₂ b₁ b₂) = ∅) :
    n₁ = n₂ ∧ ∃ q : Ideal (𝓞 K), q ^ 2 = b₁.val.val * b₂.val.val := by
  refine ⟨columns_eq_of_principal K S D n₁ n₂ b₁ b₂ hn₁ hn₂ hprincipal, ?_⟩
  exact ⟨_, (cube_product_square_of_principal K S D n₁ n₂ b₁ b₂ hprincipal).symm⟩

end HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalDiagonal

end
