import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalNormPools
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalFirstEnergy

/-!
# True residual norm windows for complete original dyadic pools

The first independent column domains are reconstructed into the original
squarefree ideal pool. Their lower and upper norm bounds therefore follow
from the original source annulus and the frozen extracted ideal.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstNormPoolEnergy

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open FirstSourceDecomposition FirstSourceReindexing FirstSourceColumns
  CanonicalFirstEnergy CanonicalNormPools
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset

def sideDomain (N : Finset Ext) (r₁ r₂ b₁ b₂ : Ext) (side : Bool) :=
  if side then rightDomain K S N r₁ r₂ b₁ b₂ else leftDomain K S N r₁ r₂ b₁ b₂

def residualScale (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext) (side : Bool) :
    {r : ℝ // 0 < r} :=
  ⟨X.val / ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ),
    div_pos X.property (by
      exact_mod_cast (Ideal.absNorm_pos_of_nonZeroDivisors
        (extractedFactor K S r₁ r₂ b₁ b₂ side).val))⟩

include D in
theorem domain_reconstruct (N : Finset Ext) (hN : ∀ n ∈ N, Squarefree n.val.val)
    (r₁ r₂ b₁ b₂ : Ext) (side : Bool)
    (U : Finset (HeightOneSpectrum (𝓞 K)))
    (hU : U ∈ sideDomain K S N r₁ r₂ b₁ b₂ side) :
    ∃ n ∈ N, n.val.val =
      (extractedFactor K S r₁ r₂ b₁ b₂ side).val.val * IdealMobiusMask.primeProduct U := by
  let A := if side then rightSupport K S r₂ b₁ b₂ else leftSupport K S r₁ b₁ b₂
  let C := CanonicalFirstEnergy.commonSupport K S r₁ r₂ b₁ b₂
  have hA : A ⊆ cubeSupport K S b₁ b₂ := by
    cases side
    · exact leftSupport_subset K S r₁ b₁ b₂
    · exact rightSupport_subset K S r₂ b₁ b₂
  have hu : U ∈ columnDomain (nonzeroRange K S N) (cubeSupport K S b₁ b₂) A C := by
    cases side <;> exact hU
  have hm := columnDomain_reconstruct_mem (nonzeroRange_squarefree K S N hN) hu
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hm
  have hf := columnDomain_reconstruct_factor hA
    (commonSupport_disjoint K S r₁ r₂ b₁ b₂) hu
  have hx : (extractedFactor K S r₁ r₂ b₁ b₂ side).val.val =
      IdealMobiusMask.primeProduct A * IdealMobiusMask.primeProduct C := by
    rw [extractedFactor_val K S D, CanonicalConductor.commonResidualIdeal_eq_C]
    cases side <;> rfl
  refine ⟨n, hn, ?_⟩
  rw [hx]
  have heval := congrArg (fun I : (Ideal (𝓞 K))⁰ => I.val) he
  exact heval.trans hf

include D in
theorem domain_height_window (X : {r : ℝ // 0 < r})
    (r₁ r₂ b₁ b₂ : Ext) (side : Bool)
    (U : Finset (HeightOneSpectrum (𝓞 K)))
    (hU : U ∈ sideDomain K S (dyadicPool K Sset X.val) r₁ r₂ b₁ b₂ side) :
    (residualScale K S X r₁ r₂ b₁ b₂ side).val ≤
        ((IdealMobiusMask.primeProduct U).absNorm : ℝ) ∧
      ((IdealMobiusMask.primeProduct U).absNorm : ℝ) ≤
        2 * (residualScale K S X r₁ r₂ b₁ b₂ side).val := by
  obtain ⟨n, hn, he⟩ := domain_reconstruct K S D (dyadicPool K Sset X.val)
    (fun n hn => dyadicPool_squarefree K Sset hn) r₁ r₂ b₁ b₂ side U hU
  obtain ⟨hsf, hlo, hhi⟩ := (mem_dyadicPool K Sset X.val n).mp hn
  have hE : 0 < ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ) := by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors
      (extractedFactor K S r₁ r₂ b₁ b₂ side).val
  have hnorm : height K Sset n =
      ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ) *
        ((IdealMobiusMask.primeProduct U).absNorm : ℝ) := by
    simp only [height, he, map_mul, Nat.cast_mul]
  rw [hnorm] at hlo hhi
  constructor
  · exact (div_le_iff₀ hE).mpr (by simpa only [mul_comm] using hlo)
  · change _ ≤ 2 * (X.val / _)
    rw [show 2 * (X.val / ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ)) =
      (2 * X.val) / ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ) by ring]
    exact (le_div_iff₀ hE).mpr (by simpa only [mul_comm] using hhi)

include D in
theorem leftDomain_height_window (X : {r : ℝ // 0 < r})
    (r₁ r₂ b₁ b₂ : Ext) (U : Finset (HeightOneSpectrum (𝓞 K)))
    (hU : U ∈ leftDomain K S (dyadicPool K Sset X.val) r₁ r₂ b₁ b₂) :
    (residualScale K S X r₁ r₂ b₁ b₂ false).val ≤
        ((IdealMobiusMask.primeProduct U).absNorm : ℝ) ∧
      ((IdealMobiusMask.primeProduct U).absNorm : ℝ) ≤
        2 * (residualScale K S X r₁ r₂ b₁ b₂ false).val :=
  domain_height_window K S D X r₁ r₂ b₁ b₂ false U hU

include D in
theorem rightDomain_height_window (X : {r : ℝ // 0 < r})
    (r₁ r₂ b₁ b₂ : Ext) (U : Finset (HeightOneSpectrum (𝓞 K)))
    (hU : U ∈ rightDomain K S (dyadicPool K Sset X.val) r₁ r₂ b₁ b₂) :
    (residualScale K S X r₁ r₂ b₁ b₂ true).val ≤
        ((IdealMobiusMask.primeProduct U).absNorm : ℝ) ∧
      ((IdealMobiusMask.primeProduct U).absNorm : ℝ) ≤
        2 * (residualScale K S X r₁ r₂ b₁ b₂ true).val :=
  domain_height_window K S D X r₁ r₂ b₁ b₂ true U hU

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstNormPoolEnergy

end

