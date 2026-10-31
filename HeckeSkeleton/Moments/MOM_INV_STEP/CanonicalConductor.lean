import HeckeSkeleton.Moments.MOM_INV_STEP.PrimitivePoissonSource
import HeckeSkeleton.Moments.MOM_INV_STEP.CubeLabels
import HeckeSkeleton.Moments.MOM_INV_STEP.SupportPartition
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourceDecomposition

/-!
# The actual first conductor and the manuscript's ideal labels

The conductor used by `PrimitivePoissonSource` is identified with
`u₁ * u₂ * R₁` using the actual valuations of `b₁ * b₂`.  The complementary
principal support is the common residual support together with the
principal cube support.  These identities are derived from ideal
divisibility and the local digit table, rather than included as inputs to
the Poisson packet.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalConductor

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton
open ActualFiniteSource PrimitivePoissonSource ConductorMasks CubeAlgebra
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

def squarefreeBit (n : ExteriorIdeal K Sset) (p : HeightOneSpectrum (𝓞 K)) : Bool :=
  decide (p.asIdeal ∣ n.val.val)

/-- The local zero/one extraction label is the actual cube-supported
part of the original ideal, with no separate label-identification input. -/
theorem aLabel_eq_extracted (n b₁ b₂ : ExteriorIdeal K Sset) :
    aLabel HeightOneSpectrum.asIdeal (CubeLabels.cubePrimeSupport b₁.val b₂.val)
      (squarefreeBit K S n) = FirstSourceDecomposition.A n.val b₁.val b₂.val := by
  rw [CubeLabels.ideal_bit_product]
  apply congrArg IdealMobiusMask.primeProduct
  ext p
  change (p ∈ (FirstSourceDecomposition.primeSupport (b₁.val * b₂.val)).filter
      (fun p => squarefreeBit K S n p)) ↔
    p ∈ FirstSourceDecomposition.primeSupport n.val ∩
      FirstSourceDecomposition.primeSupport (b₁.val * b₂.val)
  simp only [Finset.mem_filter, Finset.mem_inter, FirstSourceDecomposition.mem_primeSupport,
    squarefreeBit, decide_eq_true_eq, and_comm]

theorem aLabel_eq_gcd (n b₁ b₂ : ExteriorIdeal K Sset)
    (hn : Squarefree n.val.val) :
    aLabel HeightOneSpectrum.asIdeal (CubeLabels.cubePrimeSupport b₁.val b₂.val)
      (squarefreeBit K S n) = gcd n.val.val (b₁.val.val * b₂.val.val).radical :=
  (aLabel_eq_extracted K S n b₁ b₂).trans
    (FirstSourceDecomposition.A_eq_gcd n.val b₁.val b₂.val hn)

/-- The local digit and the actual ideal-product valuation use the same
exponent, including primes outside the cube support. -/
theorem pairExponent_eq_cubeMultiplicity (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset)
    (p : HeightOneSpectrum (𝓞 K)) :
    pairExponent K S n₁ n₂ b₁ b₂ p =
      conductorExponent (parity (CubeLabels.cubeMultiplicity b₁.val b₂.val p))
        (squarefreeBit K S n₁ p) (squarefreeBit K S n₂ p) := by
  simp only [pairExponent, squarefreeBit, CubeLabels.cubeMultiplicity_eq_sum,
    ideal_multiplicity_eq_primeExponents]

theorem cubeSupport_subset_pairSupport (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset) :
    CubeLabels.cubePrimeSupport b₁.val b₂.val ⊆
      (pairSupport K S D n₁ n₂ b₁ b₂).support := by
  intro p hp
  have hd : p.asIdeal ∣ b₁.val.val * b₂.val.val :=
    (FirstSourceDecomposition.mem_primeSupport (b₁.val * b₂.val) p).mp hp
  apply (mem_pairSupport K S D n₁ n₂ b₁ b₂ p).mpr
  rcases p.prime.dvd_mul.mp hd with h₁ | h₂
  · exact Or.inl h₁
  · exact Or.inr (Or.inl h₂)

theorem cubeSupport_eq_positive_filter (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset) :
    CubeLabels.cubePrimeSupport b₁.val b₂.val =
      (pairSupport K S D n₁ n₂ b₁ b₂).support.filter
        (fun p => 0 < CubeLabels.cubeMultiplicity b₁.val b₂.val p) := by
  ext p
  constructor
  · intro hp
    exact Finset.mem_filter.mpr
      ⟨cubeSupport_subset_pairSupport K S D n₁ n₂ b₁ b₂ hp,
        CubeLabels.cubeMultiplicity_pos b₁.val b₂.val p hp⟩
  · intro hp
    exact Finsupp.mem_support_iff.mpr (Nat.ne_of_gt (Finset.mem_filter.mp hp).2)

def u₁ (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset) : Ideal (𝓞 K) :=
  IdealMobiusMask.primeProduct
    (SupportPartition.leftResidual (pairSupport K S D n₁ n₂ b₁ b₂).support
      (CubeLabels.cubeMultiplicity b₁.val b₂.val)
      (squarefreeBit K S n₁) (squarefreeBit K S n₂))

def u₂ (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset) : Ideal (𝓞 K) :=
  IdealMobiusMask.primeProduct
    (SupportPartition.rightResidual (pairSupport K S D n₁ n₂ b₁ b₂).support
      (CubeLabels.cubeMultiplicity b₁.val b₂.val)
      (squarefreeBit K S n₁) (squarefreeBit K S n₂))

def commonResidualIdeal (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset) : Ideal (𝓞 K) :=
  IdealMobiusMask.primeProduct
    (SupportPartition.commonResidual (pairSupport K S D n₁ n₂ b₁ b₂).support
      (CubeLabels.cubeMultiplicity b₁.val b₂.val)
      (squarefreeBit K S n₁) (squarefreeBit K S n₂))

def cubePrincipalIdeal (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset) : Ideal (𝓞 K) :=
  IdealMobiusMask.primeProduct ((CubeLabels.cubePrimeSupport b₁.val b₂.val).filter
    (fun p => pairExponent K S n₁ n₂ b₁ b₂ p = 0))

theorem cubeActive_eq (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset) :
    SupportPartition.cubeActive (pairSupport K S D n₁ n₂ b₁ b₂).support
      (CubeLabels.cubeMultiplicity b₁.val b₂.val)
      (squarefreeBit K S n₁) (squarefreeBit K S n₂) =
    (CubeLabels.cubePrimeSupport b₁.val b₂.val).filter
      (fun p => pairExponent K S n₁ n₂ b₁ b₂ p ≠ 0) := by
  rw [cubeSupport_eq_positive_filter K S D n₁ n₂ b₁ b₂]
  ext p
  simp only [SupportPartition.cubeActive, Finset.mem_filter,
    pairExponent_eq_cubeMultiplicity, and_assoc]

theorem cubePrincipal_eq (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset) :
    SupportPartition.cubePrincipal (pairSupport K S D n₁ n₂ b₁ b₂).support
      (CubeLabels.cubeMultiplicity b₁.val b₂.val)
      (squarefreeBit K S n₁) (squarefreeBit K S n₂) =
    (CubeLabels.cubePrimeSupport b₁.val b₂.val).filter
      (fun p => pairExponent K S n₁ n₂ b₁ b₂ p = 0) := by
  rw [cubeSupport_eq_positive_filter K S D n₁ n₂ b₁ b₂]
  ext p
  simp only [SupportPartition.cubePrincipal, Finset.mem_filter,
    pairExponent_eq_cubeMultiplicity, and_assoc]

/-- The primitive conductor in the genuine packet is exactly `u₁u₂R₁`.
No squarefreeness assumption is needed for this support identity. -/
theorem primitiveIdeal_eq_u₁_mul_u₂_mul_R1 (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset) :
    primitiveIdeal (pairSupport K S D n₁ n₂ b₁ b₂).support
        (pairExponent K S n₁ n₂ b₁ b₂) =
      u₁ K S D n₁ n₂ b₁ b₂ * u₂ K S D n₁ n₂ b₁ b₂ *
        CubeLabels.R1 b₁.val b₂.val (squarefreeBit K S n₁) (squarefreeBit K S n₂) := by
  simp only [primitiveIdeal, activeSupport, IdealMobiusMask.primeProduct,
    pairExponent_eq_cubeMultiplicity]
  rw [SupportPartition.primitive_product]
  rw [cubeActive_eq K S D n₁ n₂ b₁ b₂]
  simp only [u₁, u₂, CubeLabels.R1, IdealMobiusMask.primeProduct,
    pairExponent_eq_cubeMultiplicity]

theorem pairSupport_positive (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset)
    (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ (pairSupport K S D n₁ n₂ b₁ b₂).support) :
    0 < bit (squarefreeBit K S n₁ p) + bit (squarefreeBit K S n₂ p) +
      CubeLabels.cubeMultiplicity b₁.val b₂.val p := by
  have h := supported_prime_positive K b₁.val.val b₂.val.val n₁.val.val n₂.val.val
    (nonZeroDivisors.coe_ne_zero b₁.val) (nonZeroDivisors.coe_ne_zero b₂.val) p
    ((mem_pairSupport K S D n₁ n₂ b₁ b₂ p).mp hp)
  simpa only [squarefreeBit, CubeLabels.cubeMultiplicity_eq_sum,
    ideal_multiplicity_eq_primeExponents, Nat.add_assoc] using h

/-- The old principal local factors have their exact common-residual and
cube-principal ideal factors; none are discarded by the conductor split. -/
theorem principalIdeal_eq_common_mul_cube (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset) :
    principalIdeal (pairSupport K S D n₁ n₂ b₁ b₂).support
        (pairExponent K S n₁ n₂ b₁ b₂) =
      commonResidualIdeal K S D n₁ n₂ b₁ b₂ * cubePrincipalIdeal K S n₁ n₂ b₁ b₂ := by
  simp only [principalIdeal, principalSupport, IdealMobiusMask.primeProduct,
    pairExponent_eq_cubeMultiplicity]
  rw [SupportPartition.principal_product _ _ _ _ _
    (pairSupport_positive K S D n₁ n₂ b₁ b₂)]
  rw [cubePrincipal_eq K S D n₁ n₂ b₁ b₂]
  rfl

/-- The complete cube radical is the product of its active and principal
parts.  This records the principal puncture without ideal division. -/
theorem cubeRadical_eq_R1_mul_principal (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset) :
    IdealMobiusMask.primeProduct (CubeLabels.cubePrimeSupport b₁.val b₂.val) =
      CubeLabels.R1 b₁.val b₂.val (squarefreeBit K S n₁) (squarefreeBit K S n₂) *
        cubePrincipalIdeal K S n₁ n₂ b₁ b₂ := by
  have h := period_eq_primitive_mul_principal (CubeLabels.cubePrimeSupport b₁.val b₂.val)
    (pairExponent K S n₁ n₂ b₁ b₂)
  simpa only [primitiveIdeal, activeSupport, principalIdeal, principalSupport,
    CubeLabels.R1, cubePrincipalIdeal, pairExponent_eq_cubeMultiplicity] using h

/-- The conductor's left factor is the actual residual obtained by the
successive gcd extractions from the original source columns. -/
theorem u₁_eq_residual (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset) :
    u₁ K S D n₁ n₂ b₁ b₂ =
      FirstSourceDecomposition.u n₁.val n₂.val b₁.val b₂.val := by
  have hs : FirstSourceDecomposition.primeSupport n₁.val ⊆
      (pairSupport K S D n₁ n₂ b₁ b₂).support := by
    intro p hp
    apply (mem_pairSupport K S D n₁ n₂ b₁ b₂ p).mpr
    exact Or.inr (Or.inr (Or.inl
      ((FirstSourceDecomposition.mem_primeSupport n₁.val p).mp hp)))
  have h := FirstSourceDecomposition.residualSupport_eq_leftResidual
    n₁.val n₂.val b₁.val b₂.val (pairSupport K S D n₁ n₂ b₁ b₂).support hs
  change IdealMobiusMask.primeProduct
    (SupportPartition.leftResidual (pairSupport K S D n₁ n₂ b₁ b₂).support
      (fun p => primeExponents (b₁.val * b₂.val) p)
      (fun p => decide (p.asIdeal ∣ n₁.val.val))
      (fun p => decide (p.asIdeal ∣ n₂.val.val))) =
    IdealMobiusMask.primeProduct
      (FirstSourceDecomposition.residualSupport n₁.val n₂.val b₁.val b₂.val)
  exact congrArg IdealMobiusMask.primeProduct h.symm

theorem u₂_eq_residual (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset) :
    u₂ K S D n₁ n₂ b₁ b₂ =
      FirstSourceDecomposition.u n₂.val n₁.val b₁.val b₂.val := by
  have hs : FirstSourceDecomposition.primeSupport n₂.val ⊆
      (pairSupport K S D n₁ n₂ b₁ b₂).support := by
    intro p hp
    apply (mem_pairSupport K S D n₁ n₂ b₁ b₂ p).mpr
    exact Or.inr (Or.inr (Or.inr
      ((FirstSourceDecomposition.mem_primeSupport n₂.val p).mp hp)))
  have h := FirstSourceDecomposition.residualSupport_eq_rightResidual
    n₁.val n₂.val b₁.val b₂.val (pairSupport K S D n₁ n₂ b₁ b₂).support hs
  change IdealMobiusMask.primeProduct
    (SupportPartition.rightResidual (pairSupport K S D n₁ n₂ b₁ b₂).support
      (fun p => primeExponents (b₁.val * b₂.val) p)
      (fun p => decide (p.asIdeal ∣ n₁.val.val))
      (fun p => decide (p.asIdeal ∣ n₂.val.val))) =
    IdealMobiusMask.primeProduct
      (FirstSourceDecomposition.residualSupport n₂.val n₁.val b₁.val b₂.val)
  exact congrArg IdealMobiusMask.primeProduct h.symm

theorem commonResidualIdeal_eq_C (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset) :
    commonResidualIdeal K S D n₁ n₂ b₁ b₂ =
      FirstSourceDecomposition.C n₁.val n₂.val b₁.val b₂.val := by
  have hs : FirstSourceDecomposition.primeSupport n₁.val ⊆
      (pairSupport K S D n₁ n₂ b₁ b₂).support := by
    intro p hp
    apply (mem_pairSupport K S D n₁ n₂ b₁ b₂ p).mpr
    exact Or.inr (Or.inr (Or.inl
      ((FirstSourceDecomposition.mem_primeSupport n₁.val p).mp hp)))
  have h := FirstSourceDecomposition.commonSupport_eq_commonResidual
    n₁.val n₂.val b₁.val b₂.val (pairSupport K S D n₁ n₂ b₁ b₂).support hs
  change IdealMobiusMask.primeProduct
    (SupportPartition.commonResidual (pairSupport K S D n₁ n₂ b₁ b₂).support
      (fun p => primeExponents (b₁.val * b₂.val) p)
      (fun p => decide (p.asIdeal ∣ n₁.val.val))
      (fun p => decide (p.asIdeal ∣ n₂.val.val))) =
    IdealMobiusMask.primeProduct
      (FirstSourceDecomposition.commonSupport n₁.val n₂.val b₁.val b₂.val)
  exact congrArg IdealMobiusMask.primeProduct h.symm

/-- The source decomposition and the conductor use exactly the same
residual and common ideals. Both actual original columns are recovered. -/
theorem first_source_decomposition (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset)
    (hn₁ : Squarefree n₁.val.val) (hn₂ : Squarefree n₂.val.val) :
    n₁.val.val = FirstSourceDecomposition.A n₁.val b₁.val b₂.val *
        commonResidualIdeal K S D n₁ n₂ b₁ b₂ * u₁ K S D n₁ n₂ b₁ b₂ ∧
      n₂.val.val = FirstSourceDecomposition.A n₂.val b₁.val b₂.val *
        commonResidualIdeal K S D n₁ n₂ b₁ b₂ * u₂ K S D n₁ n₂ b₁ b₂ := by
  rw [u₁_eq_residual, u₂_eq_residual, commonResidualIdeal_eq_C]
  exact FirstSourceDecomposition.first_decomposition n₁.val n₂.val b₁.val b₂.val hn₁ hn₂

theorem first_source_coprime (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset) :
    IsCoprime (u₁ K S D n₁ n₂ b₁ b₂) (u₂ K S D n₁ n₂ b₁ b₂) ∧
      IsCoprime (commonResidualIdeal K S D n₁ n₂ b₁ b₂)
        (u₁ K S D n₁ n₂ b₁ b₂ * u₂ K S D n₁ n₂ b₁ b₂) ∧
      IsCoprime (commonResidualIdeal K S D n₁ n₂ b₁ b₂ *
        u₁ K S D n₁ n₂ b₁ b₂ * u₂ K S D n₁ n₂ b₁ b₂)
        (b₁.val.val * b₂.val.val).radical := by
  rw [u₁_eq_residual, u₂_eq_residual, commonResidualIdeal_eq_C]
  exact FirstSourceDecomposition.first_factors_coprime n₁.val n₂.val b₁.val b₂.val

/-- The radius normalization in the actual primitive Poisson block uses
the norm of precisely the named conductor `u₁u₂R₁`. -/
theorem primitiveModulus_norm_eq_named_conductor
    (n₁ n₂ b₁ b₂ : ExteriorIdeal K Sset) :
    (sIntegerElementNorm K Sset
      ⟨primitiveModulus K S D (pairSupport K S D n₁ n₂ b₁ b₂)
          (pairExponent K S n₁ n₂ b₁ b₂),
        primitiveModulus_ne_zero K S D (pairSupport K S D n₁ n₂ b₁ b₂)
          (pairExponent K S n₁ n₂ b₁ b₂)⟩).val =
      ((u₁ K S D n₁ n₂ b₁ b₂ * u₂ K S D n₁ n₂ b₁ b₂ *
        CubeLabels.R1 b₁.val b₂.val (squarefreeBit K S n₁) (squarefreeBit K S n₂)).absNorm : ℝ) := by
  rw [primitiveModulus_norm, primitiveIdeal_eq_u₁_mul_u₂_mul_R1]

end HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalConductor
