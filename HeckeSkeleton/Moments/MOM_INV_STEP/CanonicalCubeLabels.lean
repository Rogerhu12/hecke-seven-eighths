import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalIdealRow
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstSourceDecomposition
import HeckeSkeleton.Moments.MOM_INV_STEP.ConductorMasks

/-!
# Selected generators of the actual cube labels

Every support and exponent in this file comes from the original ideals
b₁ and b₂. The exterior labels are proved to have exactly the underlying
ideals `CubeLabels.q0`, `CubeLabels.J2`, `CubeLabels.s` and `CubeLabels.J`.
Thus the generator-row identity and the arithmetic reconstruction use
the same actual labels, rather than separately supplied identifications.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalCubeLabels

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CubeAlgebra
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "E" => CanonicalIdealRow.exteriorMonoid K S

/-- This total family is used only on actual cube supports, whose primes
are proved exterior below. Its value on an excluded prime is the unit. -/
def prime (p : HeightOneSpectrum (𝓞 K)) : E :=
  if hp : p ∉ Sset then CanonicalIdealRow.primeIdeal K S ⟨p, hp⟩ else 1

theorem prime_val (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ Sset) :
    (prime K S p).val.val = p.asIdeal := by
  simp only [prime, dif_pos hp, CanonicalIdealRow.primeIdeal_val]

theorem cubeSupport_outside (b₁ b₂ : Ext) (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ CubeLabels.cubePrimeSupport b₁.val b₂.val) : p ∉ Sset := by
  have hd : p.asIdeal ∣ b₁.val.val * b₂.val.val :=
    (FirstSourceDecomposition.mem_primeSupport (b₁.val * b₂.val) p).mp hp
  rcases p.prime.dvd_mul.mp hd with hp | hp
  · exact b₁.property p hp
  · exact b₂.property p hp

theorem product_value (b₁ b₂ : Ext) (e : HeightOneSpectrum (𝓞 K) → ℕ) :
    (primeProduct (prime K S) (CubeLabels.cubePrimeSupport b₁.val b₂.val) e).val.val =
      primeProduct HeightOneSpectrum.asIdeal
        (CubeLabels.cubePrimeSupport b₁.val b₂.val) e := by
  rw [CanonicalIdealRow.product_idealValue]
  unfold primeProduct
  apply Finset.prod_congr rfl
  intro p hp
  change (prime K S p).val.val ^ e p = p.asIdeal ^ e p
  rw [prime_val K S p (cubeSupport_outside K S b₁ b₂ p hp)]

def radical (b₁ b₂ : Ext) : E :=
  cubeRadical (prime K S) (CubeLabels.cubePrimeSupport b₁.val b₂.val)

def q0 (b₁ b₂ : Ext) (ε₁ ε₂ : HeightOneSpectrum (𝓞 K) → Bool) : E :=
  b0Label (prime K S) (CubeLabels.cubePrimeSupport b₁.val b₂.val)
    (CubeLabels.cubeMultiplicity b₁.val b₂.val) ε₁ ε₂

def J2 (b₁ b₂ : Ext) (ε₁ ε₂ : HeightOneSpectrum (𝓞 K) → Bool) : E :=
  j2Label (prime K S) (CubeLabels.cubePrimeSupport b₁.val b₂.val)
    (CubeLabels.cubeMultiplicity b₁.val b₂.val) ε₁ ε₂

def s (b₁ b₂ : Ext) : E :=
  squarefreeLabel (prime K S) (CubeLabels.cubePrimeSupport b₁.val b₂.val)
    (CubeLabels.cubeMultiplicity b₁.val b₂.val)

def J (b₁ b₂ : Ext) (ε₁ ε₂ : HeightOneSpectrum (𝓞 K) → Bool) : E :=
  jLabel (prime K S) (CubeLabels.cubePrimeSupport b₁.val b₂.val)
    (CubeLabels.cubeMultiplicity b₁.val b₂.val) ε₁ ε₂

def A (b₁ b₂ : Ext) (ε : HeightOneSpectrum (𝓞 K) → Bool) : E :=
  aLabel (prime K S) (CubeLabels.cubePrimeSupport b₁.val b₂.val) ε

def crt (b₁ b₂ : Ext) (ε₁ ε₂ : HeightOneSpectrum (𝓞 K) → Bool) (side : Bool) : E :=
  crtLabel (prime K S) (CubeLabels.cubePrimeSupport b₁.val b₂.val)
    (CubeLabels.cubeMultiplicity b₁.val b₂.val) ε₁ ε₂ side

def dilation (b₁ b₂ : Ext) (ε₁ ε₂ : HeightOneSpectrum (𝓞 K) → Bool) : E :=
  dilationLabel (prime K S) (CubeLabels.cubePrimeSupport b₁.val b₂.val)
    (CubeLabels.cubeMultiplicity b₁.val b₂.val) ε₁ ε₂

@[simp] theorem q0_val (b₁ b₂ : Ext) (ε₁ ε₂ : HeightOneSpectrum (𝓞 K) → Bool) :
    (q0 K S b₁ b₂ ε₁ ε₂).val.val = CubeLabels.q0 b₁.val b₂.val ε₁ ε₂ :=
  product_value K S b₁ b₂ _

@[simp] theorem J2_val (b₁ b₂ : Ext) (ε₁ ε₂ : HeightOneSpectrum (𝓞 K) → Bool) :
    (J2 K S b₁ b₂ ε₁ ε₂).val.val = CubeLabels.J2 b₁.val b₂.val ε₁ ε₂ :=
  product_value K S b₁ b₂ _

@[simp] theorem s_val (b₁ b₂ : Ext) :
    (s K S b₁ b₂).val.val = CubeLabels.s b₁.val b₂.val :=
  product_value K S b₁ b₂ _

@[simp] theorem J_val (b₁ b₂ : Ext) (ε₁ ε₂ : HeightOneSpectrum (𝓞 K) → Bool) :
    (J K S b₁ b₂ ε₁ ε₂).val.val = CubeLabels.J b₁.val b₂.val ε₁ ε₂ :=
  product_value K S b₁ b₂ _

theorem A_val (b₁ b₂ : Ext) (ε : HeightOneSpectrum (𝓞 K) → Bool) :
    (A K S b₁ b₂ ε).val.val =
      aLabel HeightOneSpectrum.asIdeal (CubeLabels.cubePrimeSupport b₁.val b₂.val) ε :=
  product_value K S b₁ b₂ _

theorem A_val_eq_extracted (n b₁ b₂ : Ext) :
    (A K S b₁ b₂ (fun p => decide (p.asIdeal ∣ n.val.val))).val.val =
      FirstSourceDecomposition.A n.val b₁.val b₂.val := by
  rw [A_val, CubeLabels.ideal_bit_product]
  apply congrArg IdealMobiusMask.primeProduct
  ext p
  change (p ∈ (FirstSourceDecomposition.primeSupport (b₁.val * b₂.val)).filter
      (fun p => decide (p.asIdeal ∣ n.val.val))) ↔
    p ∈ FirstSourceDecomposition.primeSupport n.val ∩
      FirstSourceDecomposition.primeSupport (b₁.val * b₂.val)
  simp only [Finset.mem_filter, Finset.mem_inter, FirstSourceDecomposition.mem_primeSupport,
    decide_eq_true_eq, and_comm]

theorem A_val_eq_gcd (n b₁ b₂ : Ext) (hn : Squarefree n.val.val) :
    (A K S b₁ b₂ (fun p => decide (p.asIdeal ∣ n.val.val))).val.val =
      gcd n.val.val (b₁.val.val * b₂.val.val).radical :=
  (A_val_eq_extracted K S n b₁ b₂).trans
    (FirstSourceDecomposition.A_eq_gcd n.val b₁.val b₂.val hn)

theorem radical_val (b₁ b₂ : Ext) :
    (radical K S b₁ b₂).val.val = (b₁.val.val * b₂.val.val).radical := by
  change (radical K S b₁ b₂).val.val = (b₁.val * b₂.val).val.radical
  rw [FirstSourceDecomposition.radical_eq_primeProduct (b₁.val * b₂.val)]
  simpa only [radical, cubeRadical, primeProduct, pow_one,
    IdealMobiusMask.primeProduct] using product_value K S b₁ b₂ (fun _ => 1)

/-- The chosen-generator labels reconstruct the original cube ideals,
and their underlying arithmetic identity is the already proved one. -/
theorem cube_decomposition (b₁ b₂ : Ext)
    (ε₁ ε₂ : HeightOneSpectrum (𝓞 K) → Bool) :
    (CanonicalIdealRow.ofExterior K S b₁) * (CanonicalIdealRow.ofExterior K S b₂) =
      q0 K S b₁ b₂ ε₁ ε₂ ^ 2 * J2 K S b₁ b₂ ε₁ ε₂ ^ 2 * s K S b₁ b₂ := by
  apply Subtype.ext
  apply Subtype.ext
  change b₁.val.val * b₂.val.val =
    (q0 K S b₁ b₂ ε₁ ε₂).val.val ^ 2 *
      (J2 K S b₁ b₂ ε₁ ε₂).val.val ^ 2 * (s K S b₁ b₂).val.val
  rw [q0_val, J2_val, s_val]
  exact CubeLabels.actual_cube_decomposition b₁.val b₂.val ε₁ ε₂

theorem J_eq_s_mul_J2 (b₁ b₂ : Ext)
    (ε₁ ε₂ : HeightOneSpectrum (𝓞 K) → Bool) :
    J K S b₁ b₂ ε₁ ε₂ = s K S b₁ b₂ * J2 K S b₁ b₂ ε₁ ε₂ :=
  jLabel_eq_squarefree_mul_j2 _ _ _ _ _

theorem J_squarefree (b₁ b₂ : Ext)
    (ε₁ ε₂ : HeightOneSpectrum (𝓞 K) → Bool) :
    Squarefree (J K S b₁ b₂ ε₁ ε₂).val.val := by
  rw [J_val]
  exact CubeLabels.J_squarefree b₁.val b₂.val ε₁ ε₂

theorem s_coprime_J2 (b₁ b₂ : Ext)
    (ε₁ ε₂ : HeightOneSpectrum (𝓞 K) → Bool) :
    IsCoprime (s K S b₁ b₂).val.val (J2 K S b₁ b₂ ε₁ ε₂).val.val := by
  rw [s_val, J2_val]
  exact CubeLabels.s_coprime_J2 b₁.val b₂.val ε₁ ε₂

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)

include hallowed in
/-- The actual cube product fixes every label in the first-pass row.
The residual puncture is explicitly the radical of the actual q₀. -/
theorem first_pass_after_dual_dilation (n b₁ b₂ : Ext)
    (ε₁ ε₂ : HeightOneSpectrum (𝓞 K) → Bool) (side : Bool) (z : E) :
    ((if IsCoprime n.val.val (b₁.val.val * b₂.val.val).radical then 1 else 0) *
      idealSymbol K Sset D n (CanonicalIdealRow.generator K S D (A K S b₁ b₂ (if side then ε₂ else ε₁))) ^ 4 *
      idealSymbol K Sset D n (CanonicalIdealRow.generator K S D (crt K S b₁ b₂ ε₁ ε₂ side))) *
      star (idealSymbol K Sset D n (CanonicalIdealRow.generator K S D z)) =
    (idealSymbol K Sset D n (CanonicalIdealRow.generator K S D (J K S b₁ b₂ ε₁ ε₂)) ^ 4 *
      (if IsCoprime n.val.val (CubeLabels.q0 b₁.val b₂.val ε₁ ε₂).radical
        then 1 else 0)) *
      star (idealSymbol K Sset D n (CanonicalIdealRow.generator K S D (z * dilation K S b₁ b₂ ε₁ ε₂))) := by
  have h := CanonicalIdealRow.first_pass_after_dual_dilation K S D hallowed n
    (prime K S) (CubeLabels.cubePrimeSupport b₁.val b₂.val)
    (CubeLabels.cubeMultiplicity b₁.val b₂.val) ε₁ ε₂
    (CubeLabels.cubeMultiplicity_pos b₁.val b₂.val) side z
  change
    ((if IsCoprime n.val.val (radical K S b₁ b₂).val.val then 1 else 0) *
      idealSymbol K Sset D n (CanonicalIdealRow.generator K S D (A K S b₁ b₂ (if side then ε₂ else ε₁))) ^ 4 *
      idealSymbol K Sset D n (CanonicalIdealRow.generator K S D (crt K S b₁ b₂ ε₁ ε₂ side))) *
      star (idealSymbol K Sset D n (CanonicalIdealRow.generator K S D z)) =
    (idealSymbol K Sset D n (CanonicalIdealRow.generator K S D (J K S b₁ b₂ ε₁ ε₂)) ^ 4 *
      (if IsCoprime n.val.val (q0 K S b₁ b₂ ε₁ ε₂).val.val then 1 else 0)) *
      star (idealSymbol K Sset D n (CanonicalIdealRow.generator K S D (z * dilation K S b₁ b₂ ε₁ ε₂))) at h
  simpa only [radical_val, q0_val, ConductorMasks.coprime_radical_right_iff] using h

end HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalCubeLabels

end
