import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralAtlas
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocatedChildFamily
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocationKernel
import HeckePort.CenteredMoment.Mask
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.EffectiveChildSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralPhases
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassivePhases
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocationScalarNorm
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SlotMeshPreservation
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralWindows

set_option linter.unusedSectionVars false

/-!
# Finite deletion after the two actual Gauss transforms

A coprimality mask is expanded on the complete finite paired polynomial,
before any norm is taken. Every divisor is allocated to all original
occurrences: the two plain ideals and all prime slots. In particular,
the two rectangles of a centered coefficient are never separated here.

The resulting nonempty branches are actual `ActualColumnAllocation`s.
They retain the original coefficient, frequency and Fourier variable;
their quotient supports and frozen factors are computed by the existing
allocation API. No support-norm or source-energy estimate is an input.

The finite carriers in this file may be the full smooth-profile carriers.
Applying the identity only to a carrier already filtered by the same
mask is valid but does not enlarge that carrier.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open CanonicalOriginalPhaseCalibration WholeAllocation
open DedekindZetaZeroFree.LargeSieve

namespace CanonicalLiteralPassiveDeletion

variable {K : Type} [Field K] [NumberField K]
variable {X Y P : Type*} {k : ℕ}

/-- The finite mask identity holds for the complete complex summand. -/
theorem finite_mask (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (columns : Finset X) (I : X → Ideal (𝓞 K)) (C : X → ℂ) :
    (∑ x ∈ columns, (if IsCoprime (I x) M then (1 : ℂ) else 0) * C x) =
      ∑ D ∈ idealDivisors M, (moebius D : ℂ) *
        ∑ x ∈ columns with D ∣ I x, C x := by
  sorry

/-- All divisor allocations act on the same whole coefficient. A
nonsquarefree divisor disappears by its actual Möbius coefficient. -/
theorem paired_mask (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (C : (X × Y) × (Fin k → P) → ℂ) :
    (∑ x ∈ childCartesianColumns S₁ S₂ S,
      (if IsCoprime (I x.1.1 * J x.1.2 * ∏ i, A (x.2 i)) M then (1 : ℂ) else 0) *
        C x) =
      ∑ D ∈ idealDivisors M, (moebius D : ℂ) *
        ∑ v ∈ AllocationMass.idealAllocations D (k + 2),
          AllocationMass.sign (primeSupport D) v *
            ∑ x ∈ pairedAllocatedColumns D v S₁ S₂ S I J A, C x := by
  sorry

/-- The label stores the actual divisor and its occurrence allocation. -/
abbrev Label (K : Type) [Field K] [NumberField K] (k : ℕ) :=
  Σ D : Ideal (𝓞 K), primeSupport D → Finset (Fin (k + 2))

def labels (M : Ideal (𝓞 K)) (k : ℕ) : Finset (Label K k) :=
  (idealDivisors M).sigma (fun D => AllocationMass.idealAllocations D (k + 2))

def sign (a : Label K k) : ℂ :=
  (moebius a.1 : ℂ) * AllocationMass.sign (primeSupport a.1) a.2

def columns (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (a : Label K k) : Finset ((X × Y) × (Fin k → P)) :=
  pairedAllocatedColumns a.1 a.2 S₁ S₂ S I J A

/-- Empty allocated carriers are removed by their exact zero sum. -/
def liveLabels (M : Ideal (𝓞 K))
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K)) :
    Finset (Label K k) :=
  (labels M k).filter (fun a => (columns S₁ S₂ S I J A a).Nonempty)

theorem liveLabels_subset (M : Ideal (𝓞 K))
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K)) :
    liveLabels M S₁ S₂ S I J A ⊆ labels M k := by
  sorry

/-- The divisor is an actual divisor of the original finite mask. -/
theorem divisor_dvd_of_mem_liveLabels (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (a : Label K k) (ha : a ∈ liveLabels M S₁ S₂ S I J A) : a.1 ∣ M := by
  sorry

/-- The witness is chosen from the computed allocated finite carrier;
no nonempty-source hypothesis is added to the original polynomial. -/
def allocation (M : Ideal (𝓞 K))
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ I ∈ S₂, I ≠ 0)
    (a : {a : Label K k //
      a ∈ liveLabels M S₁ S₂ S id id HeightOneSpectrum.asIdeal}) :
    ActualColumnAllocation K k where
  divisor := a.val.1
  selection := a.val.2
  plain₁ := S₁
  plain₂ := S₂
  slots := S
  plain₁_nonzero := hS₁
  plain₂_nonzero := hS₂
  witness := (Finset.mem_filter.mp a.property).2.choose
  witness_mem := (Finset.mem_filter.mp a.property).2.choose_spec

@[simp] theorem allocation_columns (M : Ideal (𝓞 K))
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ I ∈ S₂, I ≠ 0)
    (a : {a : Label K k //
      a ∈ liveLabels M S₁ S₂ S id id HeightOneSpectrum.asIdeal}) :
    (allocation M S₁ S₂ S hS₁ hS₂ a).columns =
      columns S₁ S₂ S id id HeightOneSpectrum.asIdeal a.val := rfl

@[simp] theorem norm_sign_le_one (a : Label K k) : ‖sign a‖ ≤ 1 := by
  sorry

theorem paired_mask_labels (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (C : (X × Y) × (Fin k → P) → ℂ) :
    (∑ x ∈ childCartesianColumns S₁ S₂ S,
      (if IsCoprime (I x.1.1 * J x.1.2 * ∏ i, A (x.2 i)) M then (1 : ℂ) else 0) *
        C x) =
      ∑ a ∈ labels M k, sign a * ∑ x ∈ columns S₁ S₂ S I J A a, C x := by
  sorry

section Fourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Fourier parameter and every original location remain unchanged
throughout the finite mask expansion. -/
theorem joint_mask_labels (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (C : (X × Y) × (Fin k → P) → ℂ)
    (x : (X × Y) × (Fin k → P) → V) (ξ : V) :
    jointFourierColumn (childCartesianColumns S₁ S₂ S)
      (fun v => (if IsCoprime (I v.1.1 * J v.1.2 * ∏ i, A (v.2 i)) M
        then (1 : ℂ) else 0) * C v) x ξ =
      ∑ a ∈ labels M k, sign a *
        jointFourierColumn (columns S₁ S₂ S I J A a) C x ξ := by
  sorry

theorem joint_mask_liveLabels (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (C : (X × Y) × (Fin k → P) → ℂ)
    (x : (X × Y) × (Fin k → P) → V) (ξ : V) :
    jointFourierColumn (childCartesianColumns S₁ S₂ S)
      (fun v => (if IsCoprime (I v.1.1 * J v.1.2 * ∏ i, A (v.2 i)) M
        then (1 : ℂ) else 0) * C v) x ξ =
      ∑ a ∈ liveLabels M S₁ S₂ S I J A, sign a *
        jointFourierColumn (columns S₁ S₂ S I J A a) C x ξ := by
  sorry

/-- Every surviving summand has the genuine quotient and frozen-slot
data required by `ActualColumnAllocation.centered_joint_polynomial`. -/
theorem joint_mask_allocations (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ I ∈ S₂, I ≠ 0)
    (C : AllocationColumn K k → ℂ) (x : AllocationColumn K k → V) (ξ : V) :
    jointFourierColumn (childCartesianColumns S₁ S₂ S)
      (fun v => (if IsCoprime (allocationColumnIdeal v) M then (1 : ℂ) else 0) * C v)
      x ξ =
      ∑ a ∈ (liveLabels M S₁ S₂ S id id HeightOneSpectrum.asIdeal).attach,
        sign a.val *
          jointFourierColumn (allocation M S₁ S₂ S hS₁ hS₂ a).columns C x ξ := by
  sorry

/-- Literal deletion of a whole two-rectangle table is the preceding
finite expansion, with the original normalizer and subtraction. -/
theorem atoms_deleteMask_joint
    (d : CanonicalLiteralRectangles.Atoms (K := K) k)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (x : AllocationColumn K k → V) (ξ : V) :
    jointFourierColumn (childCartesianColumns d.plain₁ d.plain₂ d.slots)
      (d.deleteMask M).whole x ξ =
      ∑ a ∈ labels M.val k, sign a *
        jointFourierColumn
          (columns d.plain₁ d.plain₂ d.slots id id HeightOneSpectrum.asIdeal a)
          d.whole x ξ := by
  sorry

theorem atoms_deleteMask_allocations
    (d : CanonicalLiteralRectangles.Atoms (K := K) k)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (x : AllocationColumn K k → V) (ξ : V) :
    jointFourierColumn (childCartesianColumns d.plain₁ d.plain₂ d.slots)
      (d.deleteMask M).whole x ξ =
      ∑ a ∈ (liveLabels M.val d.plain₁ d.plain₂ d.slots
        id id HeightOneSpectrum.asIdeal).attach,
        sign a.val * jointFourierColumn
          (allocation M.val d.plain₁ d.plain₂ d.slots
            d.plain₁_nonzero d.plain₂_nonzero a).columns d.whole x ξ := by
  sorry

/-- Weighted finite Minkowski separates the computed labels without
introducing a cardinality factor or changing the original row weight. -/
theorem sqrt_joint_energy_mask_le {H : Type*}
    (M : Ideal (𝓞 K)) (hM : M ≠ 0) (rows : Finset H)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (q : H → ℂ) (C : H → (X × Y) × (Fin k → P) → ℂ)
    (x : H → (X × Y) × (Fin k → P) → V) (ξ : V) :
    Real.sqrt (jointColumnEnergy rows (childCartesianColumns S₁ S₂ S) q
      (fun h v => (if IsCoprime (I v.1.1 * J v.1.2 * ∏ i, A (v.2 i)) M
        then (1 : ℂ) else 0) * C h v) x ξ) ≤
      ∑ a ∈ labels M k,
        Real.sqrt (jointColumnEnergy rows (columns S₁ S₂ S I J A a) q C x ξ) := by
  sorry

/-- Both independent deletion families stay under the same kernel.
This pointwise form applies directly to the original product of the
two nonnegative Fourier kernels, without substituting a measure. -/
theorem joint_integrand_mask_le {H X' Y' P' : Type*} {l : ℕ}
    (M N : Ideal (𝓞 K)) (hM : M ≠ 0) (hN : N ≠ 0) (rows : Finset H)
    (S₁ : Finset X) (S₂ : Finset Y) (S : Fin k → Finset P)
    (T₁ : Finset X') (T₂ : Finset Y') (T : Fin l → Finset P')
    (I : X → Ideal (𝓞 K)) (J : Y → Ideal (𝓞 K)) (A : P → Ideal (𝓞 K))
    (I' : X' → Ideal (𝓞 K)) (J' : Y' → Ideal (𝓞 K)) (A' : P' → Ideal (𝓞 K))
    (q : H → ℂ) (C : H → (X × Y) × (Fin k → P) → ℂ)
    (E : H → (X' × Y') × (Fin l → P') → ℂ)
    (x : H → (X × Y) × (Fin k → P) → V)
    (y : H → (X' × Y') × (Fin l → P') → V)
    (ξ : V) (kernel : ℝ) (hkernel : 0 ≤ kernel) :
    kernel *
      (Real.sqrt (jointColumnEnergy rows (childCartesianColumns S₁ S₂ S) q
        (fun h v => (if IsCoprime (I v.1.1 * J v.1.2 * ∏ i, A (v.2 i)) M
          then (1 : ℂ) else 0) * C h v) x ξ) *
       Real.sqrt (jointColumnEnergy rows (childCartesianColumns T₁ T₂ T) q
        (fun h v => (if IsCoprime (I' v.1.1 * J' v.1.2 * ∏ i, A' (v.2 i)) N
          then (1 : ℂ) else 0) * E h v) y ξ)) ≤
      ∑ a ∈ labels M k, ∑ b ∈ labels N l, kernel *
        (Real.sqrt (jointColumnEnergy rows (columns S₁ S₂ S I J A a) q C x ξ) *
         Real.sqrt (jointColumnEnergy rows (columns T₁ T₂ T I' J' A' b) q E y ξ)) := by
  sorry

end Fourier
end CanonicalLiteralPassiveDeletion
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# Restoring the full smooth finite carrier before passive deletion

The original finite source already has exact single-occurrence
arithmetic and effective-support dictionaries. These suffice to replace
its filtered carrier by the full finite support of the same smooth
profiles. No allowed-row, cutoff, capacity or support-norm budget is
needed for this equality.

After this equality the finite passive-mask expansion acts on the
unfiltered profile carrier. Its divisor branches therefore contain the
actual quotient ideals, rather than disappearing merely because the
old maximal-valuation carrier already avoided every deleted prime.
The original Fourier variable and every individual profile are fixed.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

namespace CanonicalLiteralProfileCarrier

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ω ψ : HeckeCharacter K} {k : ℕ}

/-- Forget only the nonzero proof, retaining every original ideal in
the finite smooth-profile support. -/
def idealCarrier (S : Finset (HeckeGeneral.Analysis.NonzeroIdeal K)) :
    Finset (Ideal (𝓞 K)) := S.image Subtype.val

theorem idealCarrier_nonzero (S : Finset (HeckeGeneral.Analysis.NonzeroIdeal K)) :
    ∀ I ∈ idealCarrier S, I ≠ 0 := by
  sorry

/-- The raw ideal presentation is exactly the nonzero-ideal source,
including its complete frequency and every original column location. -/
theorem raw_joint_idealCarrier
    (T : FixedChildCharacters K k) (g h' : A.R)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (S₁ S₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal K → V)
    (x : Fin k → HeightOneSpectrum (𝓞 K) → V) (ξ : V) :
    jointFourierColumn (childCartesianColumns (idealCarrier S₁) (idealCarrier S₂) S)
      (rawSourceCoefficient (σ := σ) T g h' N₁ N₂ Z length w₁ w₂ w)
      (rawSourceLocation x₁ x₂ x) ξ =
      jointFourierColumn (childCartesianColumns S₁ S₂ S)
        (T.coefficient (σ := σ) g h' N₁ N₂ Z length w₁ w₂ w)
        (childCartesianLocation x₁ x₂ x) ξ := by
  sorry

/-- Changing only finite carriers follows from the actual calibrated
single atoms. The larger carriers need contain only their corresponding
smooth profile supports. -/
theorem calibrated_support_change
    (T : FixedChildCharacters K k) (d : MomentData K ω ψ)
    (count : d.geometry.slotCount = k) (length : Fin k → ℝ)
    (hlength : ∀ i, (d.geometry.slots i).length = length (Fin.cast count i))
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (g h' : A.R)
    (D : T.Calibration (σ := σ) d count u g h')
    (N₁ N₂ Z t : ℝ)
    (S₁ S₂ U₁ U₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K))
    (S U : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (hS₁ : EffectivePlainSupport d d.plainTest₁ u N₁ t S₁)
    (hS₂ : EffectivePlainSupport d d.plainTest₂ u N₂ t S₂)
    (hS : ∀ i, EffectivePrimeSupport d i u Z t (S (Fin.cast count i)))
    (hU₁ : d.plainTest₁.support u t N₁ ⊆ U₁)
    (hU₂ : d.plainTest₂.support u t N₂ ⊆ U₂)
    (hU : ∀ i, (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length) ⊆
      U (Fin.cast count i))
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal K → V)
    (x : Fin k → HeightOneSpectrum (𝓞 K) → V) (ξ : V)
    (hW₁ : ∀ I, w₁ I * jointPhase ξ (x₁ I) =
      d.plainTest₁.profile u t (idealNorm K I / N₁))
    (hW₂ : ∀ I, w₂ I * jointPhase ξ (x₂ I) =
      d.plainTest₂.profile u t (idealNorm K I / N₂))
    (hW : ∀ i p, w (Fin.cast count i) p * jointPhase ξ (x (Fin.cast count i) p) =
      (d.geometry.slots i).profile t
        ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length)) :
    jointFourierColumn (childCartesianColumns S₁ S₂ S)
      (T.coefficient (σ := σ) g h' N₁ N₂ Z length w₁ w₂ w)
      (childCartesianLocation x₁ x₂ x) ξ =
      jointFourierColumn (childCartesianColumns U₁ U₂ U)
        (T.coefficient (σ := σ) g h' N₁ N₂ Z length w₁ w₂ w)
        (childCartesianLocation x₁ x₂ x) ξ := by
  sorry

/-- In particular the source may use its full finite profile supports
before the nonzero-ideal proofs are forgotten and divisors allocated. -/
theorem calibrated_full_profile_carrier
    (d : MomentData K ω ψ) (T : FixedChildCharacters K d.geometry.slotCount)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (g h' : A.R)
    (D : T.Calibration (σ := σ) d rfl u g h')
    (N₁ N₂ Z t : ℝ)
    (S₁ S₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K))
    (S : Fin d.geometry.slotCount → Finset (HeightOneSpectrum (𝓞 K)))
    (hS₁ : EffectivePlainSupport d d.plainTest₁ u N₁ t S₁)
    (hS₂ : EffectivePlainSupport d d.plainTest₂ u N₂ t S₂)
    (hS : ∀ i, EffectivePrimeSupport d i u Z t (S i))
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 K) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal K → V)
    (x : Fin d.geometry.slotCount → HeightOneSpectrum (𝓞 K) → V) (ξ : V)
    (hW₁ : ∀ I, w₁ I * jointPhase ξ (x₁ I) =
      d.plainTest₁.profile u t (idealNorm K I / N₁))
    (hW₂ : ∀ I, w₂ I * jointPhase ξ (x₂ I) =
      d.plainTest₂.profile u t (idealNorm K I / N₂))
    (hW : ∀ i p, w i p * jointPhase ξ (x i p) =
      (d.geometry.slots i).profile t
        ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length)) :
    jointFourierColumn (childCartesianColumns S₁ S₂ S)
      (T.coefficient (σ := σ) g h' N₁ N₂ Z
        (fun i => (d.geometry.slots i).length) w₁ w₂ w)
      (childCartesianLocation x₁ x₂ x) ξ =
      jointFourierColumn
        (childCartesianColumns
          (idealCarrier (d.plainTest₁.support u t N₁))
          (idealCarrier (d.plainTest₂.support u t N₂))
          (fun i => (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length)))
        (rawSourceCoefficient (σ := σ) T g h' N₁ N₂ Z
          (fun i => (d.geometry.slots i).length) w₁ w₂ w)
        (rawSourceLocation x₁ x₂ x) ξ := by
  sorry

end CanonicalLiteralProfileCarrier
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# Calibrated finite sources enter the passive divisor expansion

The equality of the old source and the reduced source is supplied only
by their single-ideal and single-prime calibration dictionaries. The
complete polynomial identity is proved here, after restoring the full
finite smooth-profile carrier. No allowed-row or norm window is used.

The centered raw theorem retains its one original subtraction and its
common Gauss normalizer. Every surviving label constructs the genuine
allocation consumed by `ActualColumnAllocation.centered_joint_polynomial`.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments
open CanonicalOriginalPhaseCalibration

namespace CanonicalLiteralCalibratedDeletion

open CanonicalLiteralPassiveDeletion CanonicalLiteralProfileCarrier

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {k : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ω ψ : HeckeCharacter K}

/-- The actual moving frequency is unchanged by factoring the fixed
coprimality mask out of a complete source coefficient. -/
theorem coefficient_deleteMask
    (T : FixedChildCharacters K k) (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (g h' : A.R) (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (v : (HeckeGeneral.Analysis.NonzeroIdeal K × HeckeGeneral.Analysis.NonzeroIdeal K) ×
      (Fin k → HeightOneSpectrum (𝓞 K))) :
    (T.deleteMask M).coefficient (σ := σ) g h' N₁ N₂ Z length w₁ w₂ w v =
      T.coefficient (σ := σ) g h' N₁ N₂ Z length w₁ w₂ w v *
        originalCoprimeMask M (childIndexIdeal v) := by
  sorry

theorem raw_coefficient_deleteMask
    (T : FixedChildCharacters K k) (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (g h' : A.R) (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) (h₁ : i.1.1 ≠ 0) (h₂ : i.1.2 ≠ 0) :
    rawSourceCoefficient (σ := σ) (T.deleteMask M) g h' N₁ N₂ Z length w₁ w₂ w i =
      rawSourceCoefficient (σ := σ) T g h' N₁ N₂ Z length w₁ w₂ w i *
        originalCoprimeMask M (allocationColumnIdeal i) := by
  sorry

theorem raw_joint_allocations
    (T : FixedChildCharacters K k) (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (g h' : A.R) (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ I ∈ S₂, I ≠ 0)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal K → V)
    (x : Fin k → HeightOneSpectrum (𝓞 K) → V) (ξ : V) :
    jointFourierColumn (childCartesianColumns S₁ S₂ S)
      (rawSourceCoefficient (σ := σ) (T.deleteMask M) g h' N₁ N₂ Z length w₁ w₂ w)
      (rawSourceLocation x₁ x₂ x) ξ =
      ∑ a ∈ (liveLabels M.val S₁ S₂ S id id HeightOneSpectrum.asIdeal).attach,
        sign a.val * jointFourierColumn (allocation M.val S₁ S₂ S hS₁ hS₂ a).columns
          (rawSourceCoefficient (σ := σ) T g h' N₁ N₂ Z length w₁ w₂ w)
          (rawSourceLocation x₁ x₂ x) ξ := by
  sorry

/-- Both rectangles have the same finite label and the same frozen
scalar. Their subtraction and original Gauss normalizer stay intact. -/
theorem raw_centered_joint_allocations
    (T : FixedChildCharacters K k) (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (g h' : A.R) (X₁ X₂ Y₁ Y₂ Z : ℝ) (length : Fin k → ℝ)
    (S₁ S₂ : Finset (Ideal (𝓞 K))) (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (hS₁ : ∀ I ∈ S₁, I ≠ 0) (hS₂ : ∀ I ∈ S₂, I ≠ 0)
    (w₁ w₂ v₁ v₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal K → V)
    (x : Fin k → HeightOneSpectrum (𝓞 K) → V) (normalizer : ℂ) (ξ : V) :
    jointFourierColumn (childCartesianColumns S₁ S₂ S)
      (fun i => normalizer *
        (rawSourceCoefficient (σ := σ) (T.deleteMask M) g h' X₁ X₂ Z length w₁ w₂ w i -
         rawSourceCoefficient (σ := σ) (T.deleteMask M) g h' Y₁ Y₂ Z length v₁ v₂ w i))
      (rawSourceLocation x₁ x₂ x) ξ =
      ∑ a ∈ (liveLabels M.val S₁ S₂ S id id HeightOneSpectrum.asIdeal).attach,
        sign a.val * jointFourierColumn (allocation M.val S₁ S₂ S hS₁ hS₂ a).columns
          (fun i => normalizer *
            (rawSourceCoefficient (σ := σ) T g h' X₁ X₂ Z length w₁ w₂ w i -
             rawSourceCoefficient (σ := σ) T g h' Y₁ Y₂ Z length v₁ v₂ w i))
          (rawSourceLocation x₁ x₂ x) ξ := by
  sorry

/-- The old source's actual atom dictionaries and its effective support
give the enlarged masked polynomial. The new divisor labels and their
nonempty witnesses are then constructed internally on that carrier. -/
theorem calibrated_passive_allocations
    (old T : FixedChildCharacters K k) (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (d : MomentData K ω ψ) (count : d.geometry.slotCount = k)
    (length : Fin k → ℝ)
    (hlength : ∀ i, (d.geometry.slots i).length = length (Fin.cast count i))
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (g h' : A.R)
    (Dold : old.Calibration (σ := σ) d count u g h')
    (Dpaid : (T.deleteMask M).Calibration (σ := σ) d count u g h')
    (N₁ N₂ Z t : ℝ)
    (S₁ S₂ U₁ U₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K))
    (S U : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (hS₁ : EffectivePlainSupport d d.plainTest₁ u N₁ t S₁)
    (hS₂ : EffectivePlainSupport d d.plainTest₂ u N₂ t S₂)
    (hS : ∀ i, EffectivePrimeSupport d i u Z t (S (Fin.cast count i)))
    (hU₁ : d.plainTest₁.support u t N₁ ⊆ U₁)
    (hU₂ : d.plainTest₂.support u t N₂ ⊆ U₂)
    (hU : ∀ i, (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length) ⊆
      U (Fin.cast count i))
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal K → V)
    (x : Fin k → HeightOneSpectrum (𝓞 K) → V) (ξ : V)
    (hW₁ : ∀ I, w₁ I * jointPhase ξ (x₁ I) =
      d.plainTest₁.profile u t (idealNorm K I / N₁))
    (hW₂ : ∀ I, w₂ I * jointPhase ξ (x₂ I) =
      d.plainTest₂.profile u t (idealNorm K I / N₂))
    (hW : ∀ i p, w (Fin.cast count i) p * jointPhase ξ (x (Fin.cast count i) p) =
      (d.geometry.slots i).profile t
        ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length)) :
    jointFourierColumn (childCartesianColumns S₁ S₂ S)
      (old.coefficient (σ := σ) g h' N₁ N₂ Z length w₁ w₂ w)
      (childCartesianLocation x₁ x₂ x) ξ =
      ∑ a ∈ (liveLabels M.val (idealCarrier U₁) (idealCarrier U₂) U
        id id HeightOneSpectrum.asIdeal).attach,
        sign a.val * jointFourierColumn
          (allocation M.val (idealCarrier U₁) (idealCarrier U₂) U
            (idealCarrier_nonzero U₁) (idealCarrier_nonzero U₂) a).columns
          (rawSourceCoefficient (σ := σ) T g h' N₁ N₂ Z length w₁ w₂ w)
          (rawSourceLocation x₁ x₂ x) ξ := by
  sorry

end CanonicalLiteralCalibratedDeletion
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# One fixed smooth carrier for both original rectangles

The two plain carriers are the unions of their actual frozen profile
supports at the two quotient scales.  The slots use their original
finite supports.  These carriers are selected before the row, its time,
the Fourier parameter and the rectangle.  Filtering only by the fixed
exterior condition keeps every nonzero term of the actual child mask.

In particular no passive first-prime deletion is built into this
carrier.  Its later Moebius expansion can therefore produce nontrivial
quotient branches.  All support statements below follow from the actual
profiles and masks, without an allowed-row or support-norm premise.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralRectangles.Atoms.ProfileData

variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)

theorem left_support_frozen (r : Bool) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (t N : ℝ) : (W.left r).support u t N = (W.left r).support 1 0 N := by
  sorry

theorem right_support_frozen (r : Bool) (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (t N : ℝ) : (W.right r).support u t N = (W.right r).support 1 0 N := by
  sorry

theorem slot_support_frozen (j : Fin k) (t N : ℝ) :
    (W.slot j).support t N = (W.slot j).support 0 N := by
  sorry

def smoothPlain₁ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K) :=
  (W.left false).support 1 0 (d.scale₁ false / idealNorm K (B.plainDivisor 0)) ∪
    (W.left true).support 1 0 (d.scale₁ true / idealNorm K (B.plainDivisor 0))

def smoothPlain₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K) :=
  (W.right false).support 1 0
      (d.scale₂ false / idealNorm K (B.plainDivisor (Fin.succ 0))) ∪
    (W.right true).support 1 0
      (d.scale₂ true / idealNorm K (B.plainDivisor (Fin.succ 0)))

def smoothSlots (i : Fin B.keep.card) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (W.slot (SlotRestriction.index B.keep i)).support 0
    (d.base ^ d.length (SlotRestriction.index B.keep i))

theorem left_support_subset_smooth (r : Bool)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t : ℝ) :
    (W.left r).support u t (d.scale₁ r / idealNorm K (B.plainDivisor 0)) ⊆
      W.smoothPlain₁ B := by
  sorry

theorem right_support_subset_smooth (r : Bool)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t : ℝ) :
    (W.right r).support u t
        (d.scale₂ r / idealNorm K (B.plainDivisor (Fin.succ 0))) ⊆
      W.smoothPlain₂ B := by
  sorry

theorem fourierLeft_support_subset_smooth (r : Bool) (sign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t : ℝ) :
    (W.fourierLeft r sign negative ξ).support u t
        (d.scale₁ r / idealNorm K (B.plainDivisor 0)) ⊆ W.smoothPlain₁ B := by
  sorry

theorem fourierRight_support_subset_smooth (r : Bool) (sign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t : ℝ) :
    (W.fourierRight r sign negative ξ).support u t
        (d.scale₂ r / idealNorm K (B.plainDivisor (Fin.succ 0))) ⊆ W.smoothPlain₂ B := by
  sorry

theorem fourierSlot_support_eq_smooth (sign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) (i : Fin B.keep.card) (t : ℝ) :
    (W.fourierSlot (SlotRestriction.index B.keep i) sign negative ξ).support t
        (d.base ^ d.length (SlotRestriction.index B.keep i)) = W.smoothSlots B i := by
  sorry

variable (A : SArithmeticData K)

def exteriorSmoothPlain₁ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K) :=
  (W.smoothPlain₁ B).filter (fun I => IsCoprime I.val A.cS)

def exteriorSmoothPlain₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K) :=
  (W.smoothPlain₂ B).filter (fun I => IsCoprime I.val A.cS)

def exteriorSmoothSlots (i : Fin B.keep.card) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (W.smoothSlots B i).filter (fun p => IsCoprime p.asIdeal A.cS)

theorem exteriorSmoothPlain₁_coprime (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : I ∈ W.exteriorSmoothPlain₁ B A) : IsCoprime I.val A.cS := by
  sorry

theorem exteriorSmoothPlain₂_coprime (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : I ∈ W.exteriorSmoothPlain₂ B A) : IsCoprime I.val A.cS := by
  sorry

theorem exteriorSmoothSlots_coprime (i : Fin B.keep.card)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ W.exteriorSmoothSlots B A i) :
    IsCoprime p.asIdeal A.cS := by
  sorry

end CanonicalLiteralRectangles.Atoms.ProfileData

namespace CanonicalLiteralSmoothCarrier

open CanonicalLiteralAllocatedData CanonicalLiteralAllocatedSupport

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
variable (leftMultiplicity rightMultiplicity : ι → ℕ) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) (m q : ℝ)
variable (inverse : IdealTest K) (index : Fin k → Fin parent.geometry.slotCount)
variable (rectangle : Bool) (firstSign : ℝ) (negative : Bool)

local notation "child" => data P R W B F parent oldMoving correction hcorr C p
  leftMultiplicity rightMultiplicity pattern ν remaining extra m q inverse index
  rectangle firstSign negative

/-- Both rectangle choices and every actual row use the same exterior
carrier.  Only the fixed S-condition is filtered; the passive deletion
has not been used to shrink this carrier. -/
theorem actual_effectiveSupports (ξ : WithLp 2 (ℝ × ℝ))
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    EffectivePlainSupport (child ξ) (child ξ).plainTest₁ u
        (d.scale₁ rectangle / idealNorm K (B.plainDivisor 0)) (height ξ)
        (W.exteriorSmoothPlain₁ B A) ∧
      EffectivePlainSupport (child ξ) (child ξ).plainTest₂ u
        (d.scale₂ rectangle / idealNorm K (B.plainDivisor (Fin.succ 0))) (height ξ)
        (W.exteriorSmoothPlain₂ B A) ∧
      ∀ i : Fin (child ξ).geometry.slotCount,
        EffectivePrimeSupport (child ξ) i u d.base (height ξ)
          (W.exteriorSmoothSlots B A i) := by
  sorry

end CanonicalLiteralSmoothCarrier
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# Both calibrated rectangles enter one passive allocation

The source is restored on a common effective carrier before taking its
one centered difference.  The complete difference, with its original
normalizer and Fourier variable, is then expanded into the computed
nonempty passive allocations.  No energy or whole-polynomial identity
is supplied as an input; only the individual atom calibrations and
their actual effective supports enter the proof.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

namespace CanonicalLiteralCenteredPassive

open CanonicalLiteralPassiveDeletion CanonicalLiteralProfileCarrier
open CanonicalLiteralCalibratedDeletion

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ω ψ : HeckeCharacter K} {k : ℕ}

theorem joint_normalized_difference {I : Type*} (columns : Finset I)
    (normalizer : ℂ) (a b : I → ℂ) (x : I → V) (ξ : V) :
    jointFourierColumn columns (fun i => normalizer * (a i - b i)) x ξ =
      normalizer * (jointFourierColumn columns a x ξ -
        jointFourierColumn columns b x ξ) := by
  sorry

/-- The two effective-support transports are joined before the
Moebius sum.  Hence there is one label and one actual allocation for
both original rectangles, including the absent comparison rectangle. -/
theorem calibrated_centered_allocations
    (old T : FixedChildCharacters K k) (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (d : Bool → MomentData K ω ψ) (count : ∀ r, (d r).geometry.slotCount = k)
    (length : Fin k → ℝ)
    (hlength : ∀ r i, ((d r).geometry.slots i).length = length (Fin.cast (count r) i))
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (g h' : A.R)
    (Dold : ∀ r, old.Calibration (σ := σ) (d r) (count r) u g h')
    (Dpaid : ∀ r, (T.deleteMask M).Calibration (σ := σ) (d r) (count r) u g h')
    (N₁ N₂ : Bool → ℝ) (Z t : ℝ)
    (S₁ S₂ U₁ U₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K))
    (S U : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (hS₁ : ∀ r, EffectivePlainSupport (d r) (d r).plainTest₁ u (N₁ r) t S₁)
    (hS₂ : ∀ r, EffectivePlainSupport (d r) (d r).plainTest₂ u (N₂ r) t S₂)
    (hS : ∀ r i, EffectivePrimeSupport (d r) i u Z t (S (Fin.cast (count r) i)))
    (hU₁ : ∀ r, EffectivePlainSupport (d r) (d r).plainTest₁ u (N₁ r) t U₁)
    (hU₂ : ∀ r, EffectivePlainSupport (d r) (d r).plainTest₂ u (N₂ r) t U₂)
    (hU : ∀ r i, EffectivePrimeSupport (d r) i u Z t (U (Fin.cast (count r) i)))
    (w₁ w₂ : Bool → HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (x₁ x₂ : HeckeGeneral.Analysis.NonzeroIdeal K → V)
    (x : Fin k → HeightOneSpectrum (𝓞 K) → V) (normalizer : ℂ) (ξ : V)
    (hW₁ : ∀ r I, w₁ r I * jointPhase ξ (x₁ I) =
      (d r).plainTest₁.profile u t (idealNorm K I / N₁ r))
    (hW₂ : ∀ r I, w₂ r I * jointPhase ξ (x₂ I) =
      (d r).plainTest₂.profile u t (idealNorm K I / N₂ r))
    (hW : ∀ r i p, w (Fin.cast (count r) i) p *
        jointPhase ξ (x (Fin.cast (count r) i) p) =
      ((d r).geometry.slots i).profile t
        ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ ((d r).geometry.slots i).length)) :
    jointFourierColumn (childCartesianColumns S₁ S₂ S)
      (fun i => normalizer *
        (old.coefficient (σ := σ) g h' (N₁ false) (N₂ false) Z length
            (w₁ false) (w₂ false) w i -
          old.coefficient (σ := σ) g h' (N₁ true) (N₂ true) Z length
            (w₁ true) (w₂ true) w i))
      (childCartesianLocation x₁ x₂ x) ξ =
      ∑ a ∈ (liveLabels M.val (idealCarrier U₁) (idealCarrier U₂) U
        id id HeightOneSpectrum.asIdeal).attach,
        sign a.val * jointFourierColumn
          (allocation M.val (idealCarrier U₁) (idealCarrier U₂) U
            (idealCarrier_nonzero U₁) (idealCarrier_nonzero U₂) a).columns
          (fun i => normalizer *
            (rawSourceCoefficient (σ := σ) T g h' (N₁ false) (N₂ false) Z length
                (w₁ false) (w₂ false) w i -
              rawSourceCoefficient (σ := σ) T g h' (N₁ true) (N₂ true) Z length
                (w₁ true) (w₂ true) w i))
          (rawSourceLocation x₁ x₂ x) ξ := by
  sorry

end CanonicalLiteralCenteredPassive
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# Literal atoms on an actual passive-deletion allocation

The quotient supports and retained occurrences are computed by the
existing `ActualColumnAllocation`. Both original rectangles use the
same frozen arithmetic scalar. Their subtraction remains intact, and
all removed Gauss scales are retained in the first plain Gauss scale.

The finite polynomial identity retains the original location composed
with the actual occurrence reconstruction. No source equality, support
budget or new normalization estimate is assumed.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support
open CanonicalLiteralProfileCarrier

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralAllocationAtoms

/-- Forgetting the nonzero proofs preserves the complete finite sum. -/
theorem sum_idealCarrier {k : ℕ}
    (S₁ S₂ : Finset (HeckeGeneral.Analysis.NonzeroIdeal K))
    (S : Fin k → Finset (HeightOneSpectrum (𝓞 K)))
    (f : AllocationColumn K k → ℂ) :
    (∑ i ∈ childCartesianColumns (idealCarrier S₁) (idealCarrier S₂) S, f i) =
      ∑ i ∈ childCartesianColumns S₁ S₂ S, f ((i.1.1.val, i.1.2.val), i.2) := by
  sorry

/-- The same two allocated plain factors and the original frozen slots. -/
def reconstruct {k : ℕ} (B : ActualColumnAllocation K k)
    (i : AllocationColumn K B.keep.card) : AllocationColumn K k :=
  (((B.plainDivisor 0).val * i.1.1,
      (B.plainDivisor (Fin.succ 0)).val * i.1.2),
    SlotRestriction.extend B.keep B.witness.2 i.2)

end CanonicalLiteralAllocationAtoms

namespace CanonicalLiteralRectangles.Atoms

variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable (B : ActualColumnAllocation K k)

/-- The table on the genuine quotient carrier of the allocated branch. -/
def allocate : CanonicalLiteralRectangles.Atoms (K := K) B.keep.card where
  characters := d.characters.restrictSlots B.keep
  plain₁ := idealCarrier B.childPlain₁
  plain₂ := idealCarrier B.childPlain₂
  slots := B.childSlots
  plain₁_nonzero := idealCarrier_nonzero B.childPlain₁
  plain₂_nonzero := idealCarrier_nonzero B.childPlain₂
  centered := d.centered
  scale₁ r := d.scale₁ r / idealNorm K (B.plainDivisor 0)
  scale₂ r := d.scale₂ r / idealNorm K (B.plainDivisor (Fin.succ 0))
  scale₁_pos r := div_pos (d.scale₁_pos r) (idealNorm_pos K _)
  scale₂_pos r := div_pos (d.scale₂_pos r) (idealNorm_pos K _)
  base := d.base
  base_gt_one := d.base_gt_one
  length i := d.length (SlotRestriction.index B.keep i)
  length_pos i := d.length_pos (SlotRestriction.index B.keep i)
  leftWeight r I := d.leftWeight r (B.plainDivisor 0 * I)
  rightWeight r I := d.rightWeight r (B.plainDivisor (Fin.succ 0) * I)
  slotWeight i := d.slotWeight (SlotRestriction.index B.keep i)
  gauss₁ := d.gauss₁ * ∏ i ∈ Finset.univ \ B.keep, d.gaussSlot i
  gauss₂ := d.gauss₂
  gaussSlot i := d.gaussSlot (SlotRestriction.index B.keep i)
  gauss₁_pos := mul_pos d.gauss₁_pos (Finset.prod_pos (fun i _ => d.gaussSlot_pos i))
  gauss₂_pos := d.gauss₂_pos
  gaussSlot_pos i := d.gaussSlot_pos (SlotRestriction.index B.keep i)

theorem allocate_gaussScale :
    extraGaussScale (d.allocate B).gauss₁ (d.allocate B).gauss₂
        (d.allocate B).gaussSlot =
      extraGaussScale d.gauss₁ d.gauss₂ d.gaussSlot := by
  sorry

@[simp] theorem allocate_normalizer : (d.allocate B).normalizer = d.normalizer := by
  sorry

theorem allocate_rectangleLeftWeight (r : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.allocate B).rectangleLeftWeight r I =
      d.rectangleLeftWeight r (B.plainDivisor 0 * I) := by
  sorry

/-- The actual frozen arithmetic and prime-profile scalar, common to
both rectangles. The additional Gauss normalizer stays in the table. -/
def allocationScalar : ℂ :=
  d.characters.bareFrozenScalar (B.plainDivisor 0) (B.plainDivisor (Fin.succ 0))
    d.base d.length B.keep B.witness.2 d.slotWeight

theorem allocate_term (r : Bool) (i : AllocationColumn K B.keep.card)
    (h₁ : i.1.1 ≠ 0) (h₂ : i.1.2 ≠ 0) :
    d.term r (CanonicalLiteralAllocationAtoms.reconstruct B i) =
      d.allocationScalar B * (d.allocate B).term r i := by
  sorry

/-- The centered subtraction is preserved before taking any norm. -/
theorem allocate_whole (i : AllocationColumn K B.keep.card)
    (h₁ : i.1.1 ≠ 0) (h₂ : i.1.2 ≠ 0) :
    d.whole (CanonicalLiteralAllocationAtoms.reconstruct B i) =
      d.allocationScalar B * (d.allocate B).whole i := by
  sorry

/-- Exact transport of the actual allocated polynomial. The location
is composed with reconstruction, including every frozen occurrence. -/
theorem allocate_polynomial {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (point : AllocationColumn K k → V) (ξ : V) :
    jointFourierColumn B.columns d.whole point ξ =
      d.allocationScalar B *
        jointFourierColumn
          (childCartesianColumns (d.allocate B).plain₁ (d.allocate B).plain₂
            (d.allocate B).slots)
          (d.allocate B).whole
          (fun i => point (CanonicalLiteralAllocationAtoms.reconstruct B i)) ξ := by
  sorry

section Frequency

variable {A : SArithmeticData K} {σ : K →+* ℂ}

/-- The original actual frequency is evaluated at every occurrence. -/
def frequencyTerm (g h : A.R) (r : Bool) (i : AllocationColumn K k) : ℂ :=
  d.normalizer * rawSourceCoefficient (σ := σ) d.characters g h
    (d.scale₁ r) (d.scale₂ r) d.base d.length
    (d.rectangleLeftWeight r) (d.rightWeight r) d.slotWeight i

def frequencyWhole (g h : A.R) (i : AllocationColumn K k) : ℂ :=
  d.frequencyTerm (σ := σ) g h false i - d.frequencyTerm (σ := σ) g h true i

/-- The actual frozen residue belongs to the original allocation
scalar. It is never replaced by a unit or another chosen character. -/
theorem allocate_frequency_term (g h : A.R) (r : Bool)
    (i : AllocationColumn K B.keep.card) (h₁ : i.1.1 ≠ 0) (h₂ : i.1.2 ≠ 0) :
    d.frequencyTerm (σ := σ) g h r (CanonicalLiteralAllocationAtoms.reconstruct B i) =
      B.scalar (σ := σ) d.characters g h d.base d.length d.slotWeight *
        (d.allocate B).frequencyTerm (σ := σ) g h r i := by
  sorry

theorem allocate_frequency_whole (g h : A.R)
    (i : AllocationColumn K B.keep.card) (h₁ : i.1.1 ≠ 0) (h₂ : i.1.2 ≠ 0) :
    d.frequencyWhole (σ := σ) g h (CanonicalLiteralAllocationAtoms.reconstruct B i) =
      B.scalar (σ := σ) d.characters g h d.base d.length d.slotWeight *
        (d.allocate B).frequencyWhole (σ := σ) g h i := by
  sorry

/-- The exact allocated polynomial with the same complete actual
frequency, both original rectangles, and one original normalizer. -/
theorem allocate_frequency_polynomial {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (g h : A.R) (point : AllocationColumn K k → V) (ξ : V) :
    jointFourierColumn B.columns (d.frequencyWhole (σ := σ) g h) point ξ =
      B.scalar (σ := σ) d.characters g h d.base d.length d.slotWeight *
        jointFourierColumn
          (childCartesianColumns (d.allocate B).plain₁ (d.allocate B).plain₂
            (d.allocate B).slots)
          ((d.allocate B).frequencyWhole (σ := σ) g h)
          (fun i => point (CanonicalLiteralAllocationAtoms.reconstruct B i)) ξ := by
  sorry

end Frequency

namespace ProfileData

variable {d} (W : d.ProfileData)

/-- Quotient scales retain the same frozen smooth functions. Only
their ideal arguments and surviving occurrence indices are changed. -/
def allocate : (d.allocate B).ProfileData where
  left := W.left
  right := W.right
  slot i := W.slot (SlotRestriction.index B.keep i)
  slot_length i := W.slot_length (SlotRestriction.index B.keep i)
  left_positive := W.left_positive
  right_positive := W.right_positive
  slot_positive i := W.slot_positive (SlotRestriction.index B.keep i)
  left_frozen := W.left_frozen
  right_frozen := W.right_frozen
  slot_frozen i := W.slot_frozen (SlotRestriction.index B.keep i)
  left_eval r u t I := by
    change (W.left r).profile u t
      (idealNorm K I / (d.scale₁ r / idealNorm K (B.plainDivisor 0))) = _
    rw [CanonicalLiteralProfileData.quotient_argument, W.left_eval,
      d.allocate_rectangleLeftWeight]
  right_eval r u t I := by
    change (W.right r).profile u t
      (idealNorm K I / (d.scale₂ r / idealNorm K (B.plainDivisor (Fin.succ 0)))) = _
    rw [CanonicalLiteralProfileData.quotient_argument, W.right_eval] <;> rfl
  slot_eval i t p := W.slot_eval (SlotRestriction.index B.keep i) t p

@[simp] theorem allocate_left (r : Bool) : (W.allocate B).left r = W.left r := rfl
@[simp] theorem allocate_right (r : Bool) : (W.allocate B).right r = W.right r := rfl
@[simp] theorem allocate_slot (i : Fin B.keep.card) :
    (W.allocate B).slot i = W.slot (SlotRestriction.index B.keep i) := rfl

end ProfileData
end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# Paid moving characters with the passive deletion outside the source

The first and unit factors are unchanged.  An amplifier factor is
replaced by its proved reduced active element, and the original extra
deletion together with the valuation-six prime mask is kept as a separate
finite mask.  The paid source uses only the original remaining ideal.

All identities are proved on individual ideal or prime coefficients.
On the original fixed-S gate they follow from the genuine generated
residue identities; off that gate the full source term vanishes by its
actual residue.  No equality of the two complete Hecke-character records
is assumed.  These identities precede the finite passive-mask expansion
and the selection of any new normalized child.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.CanonicalLiteralPaidCharacters

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open CanonicalLiteralPhaseCalibration
open CanonicalOriginalPhaseCalibration (originalCoprimeMask)

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {k : ℕ}

/-- Only the literal pool factor is replaced. The first and unit
elements, including their actual chosen generators, remain identical. -/
def reducedPhases (F : FixedPhases A) (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (e : AmplifierValuation) : FixedPhases A :=
  { F with
    poolIdeal := CanonicalLiteralPassivePhases.activeIdeal p e
    poolElement := CanonicalLiteralPassivePhases.activeElement C p e
    pool_generates := CanonicalLiteralPassivePhases.activeElement_generates C p e }

/-- This is expanded by finite Mobius inversion, not added to the paid
source's moving support or remaining ideal. Overlap is permitted. -/
def passiveMask (extra : HeckeGeneral.Analysis.NonzeroIdeal K)
    (p : ExteriorPrime A) (e : AmplifierValuation) :
    HeckeGeneral.Analysis.NonzeroIdeal K :=
  extra * exteriorMomentIdeal (CanonicalLiteralPassivePhases.passiveIdeal p e)

@[simp] theorem reducedPhases_poolMoving (F : FixedPhases A)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A)
    (e : AmplifierValuation) :
    (reducedPhases F C p e).poolMoving P R =
      CanonicalLiteralPassivePhases.activeMoving P R C p e := rfl

@[simp] theorem coprimeMask_one (I : Ideal (𝓞 K)) :
    originalCoprimeMask (1 : HeckeGeneral.Analysis.NonzeroIdeal K) I = 1 := by
  sorry

theorem coprimeMask_mul (M N : HeckeGeneral.Analysis.NonzeroIdeal K)
    (I : Ideal (𝓞 K)) :
    originalCoprimeMask (M * N) I =
      originalCoprimeMask M I * originalCoprimeMask N I := by
  sorry

/-- The exact three original residues in a single plain coefficient. -/
theorem applyCharacters_plain (F : FixedPhases A) (T : FixedChildCharacters K k)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (extra : HeckeGeneral.Analysis.NonzeroIdeal K)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) (hJ : IsCoprime J.val A.cS) :
    sourcePlainCoefficient (F.applyCharacters P R T extra).plain
        (F.applyCharacters P R T extra).plainTwist (F.applyCharacters P R T extra).mask J =
      sourcePlainCoefficient T.plain T.plainTwist T.mask J *
        actualIdealResidue (A := A) (σ := σ) J.val F.firstElement *
        actualIdealResidue (A := A) (σ := σ) J.val F.poolElement *
        actualIdealResidue (A := A) (σ := σ) J.val F.unitElement *
        originalCoprimeMask extra J.val := by
  sorry

theorem applyCharacters_prime (F : FixedPhases A) (T : FixedChildCharacters K k)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (extra : HeckeGeneral.Analysis.NonzeroIdeal K)
    (i : Fin k) (q : HeightOneSpectrum (𝓞 K)) (hq : IsCoprime q.asIdeal A.cS) :
    sourcePrimeCoefficient ((F.applyCharacters P R T extra).slot i)
        ((F.applyCharacters P R T extra).slotTwist i) (F.applyCharacters P R T extra).mask q =
      sourcePrimeCoefficient (T.slot i) (T.slotTwist i) T.mask q *
        actualIdealResidue (A := A) (σ := σ) q.asIdeal F.firstElement *
        actualIdealResidue (A := A) (σ := σ) q.asIdeal F.poolElement *
        actualIdealResidue (A := A) (σ := σ) q.asIdeal F.unitElement *
        originalCoprimeMask extra q.asIdeal := by
  sorry

theorem applyCharacters_plain_delete (F : FixedPhases A) (T : FixedChildCharacters K k)
    (extra J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    sourcePlainCoefficient (F.applyCharacters P R T extra).plain
        (F.applyCharacters P R T extra).plainTwist (F.applyCharacters P R T extra).mask J =
      sourcePlainCoefficient (F.applyCharacters P R T 1).plain
        (F.applyCharacters P R T 1).plainTwist (F.applyCharacters P R T 1).mask J *
        originalCoprimeMask extra J.val := by
  sorry

theorem applyCharacters_prime_delete (F : FixedPhases A) (T : FixedChildCharacters K k)
    (extra : HeckeGeneral.Analysis.NonzeroIdeal K) (i : Fin k)
    (q : HeightOneSpectrum (𝓞 K)) :
    sourcePrimeCoefficient ((F.applyCharacters P R T extra).slot i)
        ((F.applyCharacters P R T extra).slotTwist i) (F.applyCharacters P R T extra).mask q =
      sourcePrimeCoefficient ((F.applyCharacters P R T 1).slot i)
        ((F.applyCharacters P R T 1).slotTwist i) (F.applyCharacters P R T 1).mask q *
        originalCoprimeMask extra q.asIdeal := by
  sorry

/-- The amplifier reduction is proved against the actual original
generated element, without identifying whole character records. -/
theorem applyCharacters_plain_reduced (F : FixedPhases A) (T : FixedChildCharacters K k)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (extra J : HeckeGeneral.Analysis.NonzeroIdeal K) (hJ : IsCoprime J.val A.cS) :
    sourcePlainCoefficient (F.applyCharacters P R T extra).plain
        (F.applyCharacters P R T extra).plainTwist (F.applyCharacters P R T extra).mask J =
      sourcePlainCoefficient ((reducedPhases F C p e).applyCharacters P R T 1).plain
        ((reducedPhases F C p e).applyCharacters P R T 1).plainTwist
        ((reducedPhases F C p e).applyCharacters P R T 1).mask J *
        originalCoprimeMask (passiveMask extra p e) J.val := by
  sorry

theorem applyCharacters_prime_reduced (F : FixedPhases A) (T : FixedChildCharacters K k)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (extra : HeckeGeneral.Analysis.NonzeroIdeal K)
    (i : Fin k) (q : HeightOneSpectrum (𝓞 K)) (hq : IsCoprime q.asIdeal A.cS) :
    sourcePrimeCoefficient ((F.applyCharacters P R T extra).slot i)
        ((F.applyCharacters P R T extra).slotTwist i) (F.applyCharacters P R T extra).mask q =
      sourcePrimeCoefficient (((reducedPhases F C p e).applyCharacters P R T 1).slot i)
        (((reducedPhases F C p e).applyCharacters P R T 1).slotTwist i)
        ((reducedPhases F C p e).applyCharacters P R T 1).mask q *
        originalCoprimeMask (passiveMask extra p e) q.asIdeal := by
  sorry

private theorem plain_term_of_gate (T U : FixedChildCharacters K k)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (he : ∀ J : HeckeGeneral.Analysis.NonzeroIdeal K, IsCoprime J.val A.cS →
      sourcePlainCoefficient T.plain T.plainTwist T.mask J =
        sourcePlainCoefficient U.plain U.plainTwist U.mask J * originalCoprimeMask M J.val)
    (g h : A.R) (w : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ) (N : ℝ)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    sourcePlainTerm (σ := σ) T.plain T.plainTwist T.mask g h w N J =
      sourcePlainTerm (σ := σ) U.plain U.plainTwist U.mask g h w N J *
        originalCoprimeMask M J.val := by
  sorry

private theorem prime_term_of_gate (T U : FixedChildCharacters K k)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (he : ∀ (i : Fin k) (q : HeightOneSpectrum (𝓞 K)), IsCoprime q.asIdeal A.cS →
      sourcePrimeCoefficient (T.slot i) (T.slotTwist i) T.mask q =
        sourcePrimeCoefficient (U.slot i) (U.slotTwist i) U.mask q *
          originalCoprimeMask M q.asIdeal)
    (g h : A.R) (w : HeightOneSpectrum (𝓞 K) → ℂ) (N : ℝ)
    (i : Fin k) (q : HeightOneSpectrum (𝓞 K)) :
    sourcePrimeTerm (σ := σ) (T.slot i) (T.slotTwist i) T.mask g h w N q =
      sourcePrimeTerm (σ := σ) (U.slot i) (U.slotTwist i) U.mask g h w N q *
        originalCoprimeMask M q.asIdeal := by
  sorry

section Source

variable {ω ψ : HeckeCharacter K}

/-- The canonical arithmetic source that the new child will calibrate.
Only the original remaining ideal enters its full-support mask. -/
def paidSourceCharacters (F : FixedPhases A) (parent : MomentData K ω ψ)
    (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
    (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (index : Fin k → Fin parent.geometry.slotCount) : FixedChildCharacters K k :=
  CanonicalAppendedPhaseCalibration.sourceCharacters P R parent (F.moving P R oldMoving)
    correction remaining index

@[simp] theorem paidSourceCharacters_restrictSlots (F : FixedPhases A)
    (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
    (correction : HeckeCharacter K) (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)
    (index : Fin k → Fin parent.geometry.slotCount) (keep : Finset (Fin k)) :
    (paidSourceCharacters P R F parent oldMoving correction remaining index).restrictSlots keep =
      paidSourceCharacters P R F parent oldMoving correction remaining
        (fun i => index (SlotRestriction.index keep i)) := rfl

variable (F : FixedPhases A) (parent : MomentData K ω ψ)
variable (oldMoving : OriginalMovingFactors A P R) (correction : HeckeCharacter K)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (index : Fin k → Fin parent.geometry.slotCount)

private theorem sourceCharacters_one_plain (J : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hJ : IsCoprime J.val A.cS) :
    sourcePlainCoefficient
        (sourceCharacters P R F parent oldMoving correction remaining 1 index).plain
        (sourceCharacters P R F parent oldMoving correction remaining 1 index).plainTwist
        (sourceCharacters P R F parent oldMoving correction remaining 1 index).mask J =
      sourcePlainCoefficient
        (paidSourceCharacters P R F parent oldMoving correction remaining index).plain
        (paidSourceCharacters P R F parent oldMoving correction remaining index).plainTwist
        (paidSourceCharacters P R F parent oldMoving correction remaining index).mask J := by
  sorry

private theorem sourceCharacters_one_prime (i : Fin k) (q : HeightOneSpectrum (𝓞 K))
    (hq : IsCoprime q.asIdeal A.cS) :
    sourcePrimeCoefficient
        ((sourceCharacters P R F parent oldMoving correction remaining 1 index).slot i)
        ((sourceCharacters P R F parent oldMoving correction remaining 1 index).slotTwist i)
        (sourceCharacters P R F parent oldMoving correction remaining 1 index).mask q =
      sourcePrimeCoefficient
        ((paidSourceCharacters P R F parent oldMoving correction remaining index).slot i)
        ((paidSourceCharacters P R F parent oldMoving correction remaining index).slotTwist i)
        (paidSourceCharacters P R F parent oldMoving correction remaining index).mask q := by
  sorry

/-- Direct/main sources require only removal of the separate finite
deletion from the paid source. No phase replacement is involved. -/
theorem source_plain_delete (J : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hJ : IsCoprime J.val A.cS) :
    sourcePlainCoefficient
        (sourceCharacters P R F parent oldMoving correction remaining extra index).plain
        (sourceCharacters P R F parent oldMoving correction remaining extra index).plainTwist
        (sourceCharacters P R F parent oldMoving correction remaining extra index).mask J =
      sourcePlainCoefficient
        (paidSourceCharacters P R F parent oldMoving correction remaining index).plain
        (paidSourceCharacters P R F parent oldMoving correction remaining index).plainTwist
        (paidSourceCharacters P R F parent oldMoving correction remaining index).mask J *
        originalCoprimeMask extra J.val := by
  sorry

theorem source_prime_delete (i : Fin k) (q : HeightOneSpectrum (𝓞 K))
    (hq : IsCoprime q.asIdeal A.cS) :
    sourcePrimeCoefficient
        ((sourceCharacters P R F parent oldMoving correction remaining extra index).slot i)
        ((sourceCharacters P R F parent oldMoving correction remaining extra index).slotTwist i)
        (sourceCharacters P R F parent oldMoving correction remaining extra index).mask q =
      sourcePrimeCoefficient
        ((paidSourceCharacters P R F parent oldMoving correction remaining index).slot i)
        ((paidSourceCharacters P R F parent oldMoving correction remaining index).slotTwist i)
        (paidSourceCharacters P R F parent oldMoving correction remaining index).mask q *
        originalCoprimeMask extra q.asIdeal := by
  sorry

theorem source_plain_reduced
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) (hJ : IsCoprime J.val A.cS) :
    sourcePlainCoefficient
        (sourceCharacters P R F parent oldMoving correction remaining extra index).plain
        (sourceCharacters P R F parent oldMoving correction remaining extra index).plainTwist
        (sourceCharacters P R F parent oldMoving correction remaining extra index).mask J =
      sourcePlainCoefficient
        (paidSourceCharacters P R (reducedPhases F C p e) parent oldMoving correction remaining index).plain
        (paidSourceCharacters P R (reducedPhases F C p e) parent oldMoving correction remaining index).plainTwist
        (paidSourceCharacters P R (reducedPhases F C p e) parent oldMoving correction remaining index).mask J *
        originalCoprimeMask (passiveMask extra p e) J.val := by
  sorry

theorem source_prime_reduced
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (i : Fin k) (q : HeightOneSpectrum (𝓞 K)) (hq : IsCoprime q.asIdeal A.cS) :
    sourcePrimeCoefficient
        ((sourceCharacters P R F parent oldMoving correction remaining extra index).slot i)
        ((sourceCharacters P R F parent oldMoving correction remaining extra index).slotTwist i)
        (sourceCharacters P R F parent oldMoving correction remaining extra index).mask q =
      sourcePrimeCoefficient
        ((paidSourceCharacters P R (reducedPhases F C p e) parent oldMoving correction remaining index).slot i)
        ((paidSourceCharacters P R (reducedPhases F C p e) parent oldMoving correction remaining index).slotTwist i)
        (paidSourceCharacters P R (reducedPhases F C p e) parent oldMoving correction remaining index).mask q *
        originalCoprimeMask (passiveMask extra p e) q.asIdeal := by
  sorry

/-- The direct/main single-ideal identity holds on the full smooth
support, without an exterior-ideal condition on its argument. -/
theorem source_plain_term_delete (g h : A.R)
    (w : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ) (N : ℝ)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    let old := sourceCharacters P R F parent oldMoving correction remaining extra index
    let paid := paidSourceCharacters P R F parent oldMoving correction remaining index
    sourcePlainTerm (σ := σ) old.plain old.plainTwist old.mask g h w N J =
      sourcePlainTerm (σ := σ) paid.plain paid.plainTwist paid.mask g h w N J *
        originalCoprimeMask extra J.val := by
  sorry

theorem source_prime_term_delete (g h : A.R)
    (w : HeightOneSpectrum (𝓞 K) → ℂ) (N : ℝ) (i : Fin k) (q : HeightOneSpectrum (𝓞 K)) :
    let old := sourceCharacters P R F parent oldMoving correction remaining extra index
    let paid := paidSourceCharacters P R F parent oldMoving correction remaining index
    sourcePrimeTerm (σ := σ) (old.slot i) (old.slotTwist i) old.mask g h w N q =
      sourcePrimeTerm (σ := σ) (paid.slot i) (paid.slotTwist i) paid.mask g h w N q *
        originalCoprimeMask extra q.asIdeal := by
  sorry

/-- The reduced amplifier source and its entire passive deletion are
identified on every nonzero ideal before a new child is constructed. -/
theorem source_plain_term_reduced
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (g h : A.R) (w : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ) (N : ℝ)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    let old := sourceCharacters P R F parent oldMoving correction remaining extra index
    let paid := paidSourceCharacters P R (reducedPhases F C p e) parent oldMoving correction
      remaining index
    sourcePlainTerm (σ := σ) old.plain old.plainTwist old.mask g h w N J =
      sourcePlainTerm (σ := σ) paid.plain paid.plainTwist paid.mask g h w N J *
        originalCoprimeMask (passiveMask extra p e) J.val := by
  sorry

theorem source_prime_term_reduced
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (g h : A.R) (w : HeightOneSpectrum (𝓞 K) → ℂ) (N : ℝ)
    (i : Fin k) (q : HeightOneSpectrum (𝓞 K)) :
    let old := sourceCharacters P R F parent oldMoving correction remaining extra index
    let paid := paidSourceCharacters P R (reducedPhases F C p e) parent oldMoving correction
      remaining index
    sourcePrimeTerm (σ := σ) (old.slot i) (old.slotTwist i) old.mask g h w N q =
      sourcePrimeTerm (σ := σ) (paid.slot i) (paid.slotTwist i) paid.mask g h w N q *
        originalCoprimeMask (passiveMask extra p e) q.asIdeal := by
  sorry

private def calibrationOfGate
    {T U : FixedChildCharacters K k} (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hray : U.fixedRay = T.fixedRay)
    (hplain : ∀ J : HeckeGeneral.Analysis.NonzeroIdeal K, IsCoprime J.val A.cS →
      sourcePlainCoefficient T.plain T.plainTwist T.mask J =
        sourcePlainCoefficient U.plain U.plainTwist U.mask J * originalCoprimeMask M J.val)
    (hprime : ∀ (i : Fin k) (q : HeightOneSpectrum (𝓞 K)), IsCoprime q.asIdeal A.cS →
      sourcePrimeCoefficient (T.slot i) (T.slotTwist i) T.mask q =
        sourcePrimeCoefficient (U.slot i) (U.slotTwist i) U.mask q *
          originalCoprimeMask M q.asIdeal)
    {d : MomentData K ω ψ} {count : d.geometry.slotCount = k}
    {u : HeckeGeneral.Analysis.NonzeroIdeal K} {g h : A.R}
    (original : T.Calibration (σ := σ) d count u g h) :
    (U.deleteMask M).Calibration (σ := σ) d count u g h where
  fixedRay_mem_theta θ hθ := by
    change θ ∈ U.fixedRay at hθ
    exact original.fixedRay_mem_theta θ (hray ▸ hθ)
  plain J := by
    rw [original.plain J]
    by_cases hJ : IsCoprime J.val A.cS
    · rw [hplain J hJ, U.deleteMask_plain M J]
    · have hz : actualIdealResidue (A := A) (σ := σ) J.val g = 0 :=
        dif_neg (fun h => hJ h.2)
      simp only [hz, mul_zero, zero_mul]
  slot i q := by
    rw [original.slot i q]
    by_cases hq : IsCoprime q.asIdeal A.cS
    · rw [hprime (Fin.cast count i) q hq, U.deleteMask_prime M (Fin.cast count i) q]
    · have hz : actualIdealResidue (A := A) (σ := σ) q.asIdeal g = 0 :=
        dif_neg (fun h => hq h.2)
      simp only [hz, mul_zero, zero_mul]

/-- The old actual atom dictionary constructs the masked paid
dictionary on exactly the same data and extracted row. -/
def calibration_delete (d : MomentData K ω ψ) (count : d.geometry.slotCount = k)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (g h : A.R)
    (original : (sourceCharacters P R F parent oldMoving correction remaining extra index).Calibration
      (σ := σ) d count u g h) :
    ((paidSourceCharacters P R F parent oldMoving correction remaining index).deleteMask extra).Calibration
      (σ := σ) d count u g h :=
  calibrationOfGate extra rfl
    (source_plain_delete P R F parent oldMoving correction remaining extra index)
    (source_prime_delete P R F parent oldMoving correction remaining extra index) original

/-- Pool reduction supplies the same masked calibration without a
whole-character or whole-polynomial premise. -/
def calibration_reduced
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (e : AmplifierValuation)
    (hpool : F.poolElement = generator C p ^ (2 * e.multiplicity))
    (d : MomentData K ω ψ) (count : d.geometry.slotCount = k)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (g h : A.R)
    (original : (sourceCharacters P R F parent oldMoving correction remaining extra index).Calibration
      (σ := σ) d count u g h) :
    ((paidSourceCharacters P R (reducedPhases F C p e) parent oldMoving correction remaining index).deleteMask
      (passiveMask extra p e)).Calibration (σ := σ) d count u g h :=
  calibrationOfGate (passiveMask extra p e) rfl
    (source_plain_reduced P R F parent oldMoving correction remaining extra index hroot hemb C p e hpool)
    (source_prime_reduced P R F parent oldMoving correction remaining extra index hroot hemb C p e hpool)
    original

end Source
end HeckeSkeleton.Moments.EngineStepV2.CanonicalLiteralPaidCharacters

end

set_option quotPrecheck false

/-!
# The actual finite source after passive-mask allocation

One exterior smooth carrier is fixed for both original rectangles.
Its single-occurrence functions are the same quotient profiles of the
original second allocation.  Only the paid characters replace the old
characters.  Passive labels are computed on this enlarged carrier,
and each surviving label supplies its actual quotient table.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum

namespace CanonicalLiteralPassiveSource

open CanonicalLiteralPassiveDeletion CanonicalLiteralProfileCarrier
open CanonicalLiteralCenteredPassive CanonicalLiteralAllocatedData
open CanonicalLiteralPhaseCalibration

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k)

/-- A fixed table with the original quotient profiles and complete
Gauss normalization, on the untruncated exterior smooth carrier. -/
def table (A : SArithmeticData K) (T : FixedChildCharacters K B.keep.card) :
    CanonicalLiteralRectangles.Atoms (K := K) B.keep.card :=
  { d.allocate B with
    characters := T
    plain₁ := idealCarrier (W.exteriorSmoothPlain₁ B A)
    plain₂ := idealCarrier (W.exteriorSmoothPlain₂ B A)
    slots := W.exteriorSmoothSlots B A
    plain₁_nonzero := idealCarrier_nonzero _
    plain₂_nonzero := idealCarrier_nonzero _ }

def profiles (A : SArithmeticData K) (T : FixedChildCharacters K B.keep.card) :
    (table W B A T).ProfileData where
  left := (W.allocate B).left
  right := (W.allocate B).right
  slot := (W.allocate B).slot
  slot_length := (W.allocate B).slot_length
  left_positive := (W.allocate B).left_positive
  right_positive := (W.allocate B).right_positive
  slot_positive := (W.allocate B).slot_positive
  left_frozen := (W.allocate B).left_frozen
  right_frozen := (W.allocate B).right_frozen
  slot_frozen := (W.allocate B).slot_frozen
  left_eval := (W.allocate B).left_eval
  right_eval := (W.allocate B).right_eval
  slot_eval := (W.allocate B).slot_eval

@[simp] theorem table_normalizer (A : SArithmeticData K)
    (T : FixedChildCharacters K B.keep.card) : (table W B A T).normalizer = d.normalizer := by
  sorry

def plainLocation₁ (firstSign : ℝ) (negative : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) : WithLp 2 (ℝ × ℝ) :=
  CanonicalLiteralProfileData.orientedLocation negative
    (CanonicalLiteralLocations.plain firstSign (B.plainDivisor 0 * I))

def plainLocation₂ (firstSign : ℝ) (negative : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) : WithLp 2 (ℝ × ℝ) :=
  CanonicalLiteralProfileData.orientedLocation negative
    (CanonicalLiteralLocations.plain firstSign (B.plainDivisor (Fin.succ 0) * I))

def slotLocation (firstSign : ℝ) (negative : Bool) (i : Fin B.keep.card)
    (p : HeightOneSpectrum (𝓞 K)) : WithLp 2 (ℝ × ℝ) :=
  CanonicalLiteralProfileData.orientedLocation negative
    (CanonicalLiteralLocations.prime firstSign (SlotRestriction.index B.keep i) p)

def centeredColumn (T : FixedChildCharacters K B.keep.card)
    (g h : A.R) (firstSign : ℝ) (negative : Bool) (ξ : WithLp 2 (ℝ × ℝ)) : ℂ :=
  d.normalizer *
    (jointFourierColumn B.childColumns
      (T.coefficient (σ := σ) g h
        (d.scale₁ false / idealNorm K (B.plainDivisor 0))
        (d.scale₂ false / idealNorm K (B.plainDivisor (Fin.succ 0))) d.base
        (fun i => d.length (SlotRestriction.index B.keep i))
        (fun I => d.rectangleLeftWeight false (B.plainDivisor 0 * I))
        (fun I => d.rightWeight false (B.plainDivisor (Fin.succ 0) * I))
        (fun i => d.slotWeight (SlotRestriction.index B.keep i)))
      (childCartesianLocation (plainLocation₁ B firstSign negative)
        (plainLocation₂ B firstSign negative) (slotLocation B firstSign negative)) ξ -
     jointFourierColumn B.childColumns
      (T.coefficient (σ := σ) g h
        (d.scale₁ true / idealNorm K (B.plainDivisor 0))
        (d.scale₂ true / idealNorm K (B.plainDivisor (Fin.succ 0))) d.base
        (fun i => d.length (SlotRestriction.index B.keep i))
        (fun I => d.rectangleLeftWeight true (B.plainDivisor 0 * I))
        (fun I => d.rightWeight true (B.plainDivisor (Fin.succ 0) * I))
        (fun i => d.slotWeight (SlotRestriction.index B.keep i)))
      (childCartesianLocation (plainLocation₁ B firstSign negative)
        (plainLocation₂ B firstSign negative) (slotLocation B firstSign negative)) ξ)

def labels (A : SArithmeticData K) (M : HeckeGeneral.Analysis.NonzeroIdeal K) :=
  liveLabels M.val (idealCarrier (W.exteriorSmoothPlain₁ B A))
    (idealCarrier (W.exteriorSmoothPlain₂ B A)) (W.exteriorSmoothSlots B A)
    id id HeightOneSpectrum.asIdeal

def branch (A : SArithmeticData K) (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (a : { a // a ∈ labels W B A M }) : ActualColumnAllocation K B.keep.card :=
  allocation M.val (idealCarrier (W.exteriorSmoothPlain₁ B A))
    (idealCarrier (W.exteriorSmoothPlain₂ B A)) (W.exteriorSmoothSlots B A)
    (idealCarrier_nonzero _) (idealCarrier_nonzero _) a

def passiveColumn (T : FixedChildCharacters K B.keep.card)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K) (g h : A.R)
    (firstSign : ℝ) (negative : Bool) (ξ : WithLp 2 (ℝ × ℝ)) : ℂ :=
  ∑ a ∈ (labels W B A M).attach,
    sign a.val * jointFourierColumn (branch W B A M a).columns
      ((table W B A T).frequencyWhole (σ := σ) g h)
      (rawSourceLocation (plainLocation₁ B firstSign negative)
        (plainLocation₂ B firstSign negative) (slotLocation B firstSign negative)) ξ

theorem table_frequencyWhole (T : FixedChildCharacters K B.keep.card)
    (g h : A.R) (i : AllocationColumn K B.keep.card) :
    (table W B A T).frequencyWhole (σ := σ) g h i =
      d.normalizer *
        (rawSourceCoefficient (σ := σ) T g h
          (d.scale₁ false / idealNorm K (B.plainDivisor 0))
          (d.scale₂ false / idealNorm K (B.plainDivisor (Fin.succ 0))) d.base
          (fun j => d.length (SlotRestriction.index B.keep j))
          (fun I => d.rectangleLeftWeight false (B.plainDivisor 0 * I))
          (fun I => d.rightWeight false (B.plainDivisor (Fin.succ 0) * I))
          (fun j => d.slotWeight (SlotRestriction.index B.keep j)) i -
         rawSourceCoefficient (σ := σ) T g h
          (d.scale₁ true / idealNorm K (B.plainDivisor 0))
          (d.scale₂ true / idealNorm K (B.plainDivisor (Fin.succ 0))) d.base
          (fun j => d.length (SlotRestriction.index B.keep j))
          (fun I => d.rectangleLeftWeight true (B.plainDivisor 0 * I))
          (fun I => d.rightWeight true (B.plainDivisor (Fin.succ 0) * I))
          (fun j => d.slotWeight (SlotRestriction.index B.keep j)) i) := by
  sorry

/-- Each passive summand is now the genuine quotient table and its
actual frequency-dependent frozen scalar.  Nothing is estimated in
this identity. -/
theorem passiveColumn_eq_quotients (T : FixedChildCharacters K B.keep.card)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K) (g h : A.R)
    (firstSign : ℝ) (negative : Bool) (ξ : WithLp 2 (ℝ × ℝ)) :
    passiveColumn (σ := σ) W B T M g h firstSign negative ξ =
      ∑ a ∈ (labels W B A M).attach,
        sign a.val *
          ((branch W B A M a).scalar (σ := σ) T g h
            (table W B A T).base (table W B A T).length (table W B A T).slotWeight *
            jointFourierColumn
              (childCartesianColumns ((table W B A T).allocate (branch W B A M a)).plain₁
                ((table W B A T).allocate (branch W B A M a)).plain₂
                ((table W B A T).allocate (branch W B A M a)).slots)
              (((table W B A T).allocate (branch W B A M a)).frequencyWhole (σ := σ) g h)
              (fun i => rawSourceLocation (plainLocation₁ B firstSign negative)
                (plainLocation₂ B firstSign negative) (slotLocation B firstSign negative)
                (CanonicalLiteralAllocationAtoms.reconstruct (branch W B A M a) i)) ξ) := by
  sorry

section PhaseChoice

variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- The original first path determines this choice before any passive
allocation.  The amplified case records only its actual pool element. -/
inductive PhaseChoice (F : FixedPhases A) (C : A.GeneralArithmeticContext σ η hS) where
  | unamplified
  | amplified (p : ExteriorPrime A) (e : AmplifierValuation)
      (pool_element : F.poolElement = generator C p ^ (2 * e.multiplicity))

namespace PhaseChoice

variable {F : FixedPhases A} {C : A.GeneralArithmeticContext σ η hS}

def phases (choice : PhaseChoice F C) : FixedPhases A :=
  match choice with
  | .unamplified => F
  | .amplified p e _ => CanonicalLiteralPaidCharacters.reducedPhases F C p e

def mask (choice : PhaseChoice F C) (extra : HeckeGeneral.Analysis.NonzeroIdeal K) :
    HeckeGeneral.Analysis.NonzeroIdeal K :=
  match choice with
  | .unamplified => extra
  | .amplified p e _ => CanonicalLiteralPaidCharacters.passiveMask extra p e

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K}

def calibration (choice : PhaseChoice F C)
    (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
    (correction : HeckeCharacter K) (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
    (index : Fin k → Fin parent.geometry.slotCount)
    (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
    (data : MomentData K ω ψ) (count : data.geometry.slotCount = k)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (g h : A.R)
    (original : (sourceCharacters P R F parent oldMoving correction remaining extra index).Calibration
      (σ := σ) data count u g h) :
    ((CanonicalLiteralPaidCharacters.paidSourceCharacters P R choice.phases parent oldMoving
      correction remaining index).deleteMask (choice.mask extra)).Calibration
      (σ := σ) data count u g h := by
  cases choice with
  | unamplified =>
    exact CanonicalLiteralPaidCharacters.calibration_delete P R F parent oldMoving
      correction remaining extra index data count u g h original
  | amplified p e hpool =>
    exact CanonicalLiteralPaidCharacters.calibration_reduced P R F parent oldMoving
      correction remaining extra index hroot hemb C p e hpool data count u g h original

end PhaseChoice
end PhaseChoice

section ActualSource

variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K}
variable (F : FixedPhases A) (parent : MomentData K ω ψ)
variable (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (S : ActualSecondCorrelationRows A σ H ι)
variable (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) (m q : ℝ)
variable (inverse : IdealTest K) (index : Fin k → Fin parent.geometry.slotCount)
variable (firstSign : ℝ) (negative : Bool)
variable (hone : (1 : HeckeCharacter K) ∈ parent.theta)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (row : CanonicalOriginalPhaseCalibration.PatternSector P S C pattern ν)

local notation "child" => (fun r ξ => CanonicalLiteralAllocatedData.data P R W B F parent
  oldMoving correction hcorr C S.primes S.leftMultiplicity S.rightMultiplicity pattern ν
  remaining extra m q inverse index r firstSign negative ξ)
local notation "rowIdeal" => (S.extractedRow C row.val.val).momentIdeal
local notation "rowElement" => (S.extractedRow C row.val.val).element
local notation "signedFactor" => (if negative then -(S.factor C row.val.val.val)
  else S.factor C row.val.val.val)

/-- Both signs use the original extracted row and the original chosen
unit-sector representative.  The right side changes only its actual
frequency sign and the already recorded Fourier locations. -/
def actualSignedDictionary (rectangle : Bool) (ξ : WithLp 2 (ℝ × ℝ)) :
    ((sourceCharacters P R F parent oldMoving correction remaining extra index).restrictSlots
      B.keep).Calibration (σ := σ) (child rectangle ξ) rfl rowIdeal signedFactor rowElement := by
  cases negative with
  | false =>
    exact CanonicalLiteralAllocatedData.actualDictionary P R W B F parent oldMoving
      correction hcorr C pattern ν remaining extra m q inverse index rectangle firstSign false
      S hone hroot hemb row ξ
  | true =>
    exact CanonicalLiteralAllocatedData.actualNegativeDictionary P R W B F parent oldMoving
      correction hcorr C pattern ν remaining extra m q inverse index rectangle firstSign true
      S hone hroot hemb row ξ

include hcorr m q inverse hone hroot hemb in
/-- The actual row, mask, source characters and finite support
construct the passive expansion.  There is no final support bound,
allowed-row assumption or supplied whole-column identity. -/
theorem actual_centered_allocations
    (choice : PhaseChoice F C)
    (hcharacters : d.characters = sourceCharacters P R F parent oldMoving correction
      remaining extra index)
    (firstSupport : Finset (Ideal (𝓞 K))) (hfirst : ∀ v ∈ firstSupport, Prime v)
    (hextra : extra = literalDeletionIdeal firstSupport hfirst)
    (hl : ∀ i, 0 < S.leftMultiplicity i) (hr : ∀ i, 0 < S.rightMultiplicity i)
    (support : d.SupportData ((primeSupport A.cS ∪ firstSupport) ∪
      primeSupport (primePowerProduct S.primes S.leftMultiplicity).val))
    (hplain₁ : B.plain₁ = d.plain₁) (hplain₂ : B.plain₂ = d.plain₂)
    (hslots : B.slots = d.slots) (ξ : WithLp 2 (ℝ × ℝ)) :
    centeredColumn (σ := σ) (d := d) B (d.characters.restrictSlots B.keep)
      signedFactor rowElement firstSign negative ξ =
    passiveColumn (σ := σ) W B
      ((CanonicalLiteralPaidCharacters.paidSourceCharacters P R choice.phases parent oldMoving
        correction remaining index).restrictSlots B.keep)
      (choice.mask extra) signedFactor rowElement firstSign negative ξ := by
  sorry

end ActualSource

end CanonicalLiteralPassiveSource
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# Actual side frames for the passive allocations

The complete smooth carrier already filters each original occurrence
against the fixed bad-prime ideal.  Its product is therefore a genuine
exterior ideal.  The total ideal map below uses that exact product on
the carrier and the unit only outside it.

Each frame uses the allocation already stored in the live passive
label, including its original witness.  The paid characters, individual
weights, quotient scales, Gauss factors and residual log locations are
read from the same table.  No new source identity, nonempty witness or
energy estimate is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum

namespace CanonicalLiteralPassiveFrames

open CanonicalLiteralProfileCarrier CanonicalLiteralPassiveSource

variable {K : Type} [Field K] [NumberField K] {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k) (A : SArithmeticData K)

def smoothColumns : Finset (AllocationColumn K B.keep.card) :=
  childCartesianColumns (idealCarrier (W.exteriorSmoothPlain₁ B A))
    (idealCarrier (W.exteriorSmoothPlain₂ B A)) (W.exteriorSmoothSlots B A)

theorem columnIdeal_ne_zero (i : AllocationColumn K B.keep.card)
    (hi : i ∈ smoothColumns W B A) : allocationColumnIdeal i ≠ 0 := by
  sorry

private theorem idealCarrier_coprime
    (S : Finset (HeckeGeneral.Analysis.NonzeroIdeal K))
    (hS : ∀ I ∈ S, IsCoprime I.val A.cS)
    (I : Ideal (𝓞 K)) (hI : I ∈ idealCarrier S) : IsCoprime I A.cS := by
  sorry

theorem columnIdeal_coprime (i : AllocationColumn K B.keep.card)
    (hi : i ∈ smoothColumns W B A) : IsCoprime (allocationColumnIdeal i) A.cS := by
  sorry

/-- The unit outside the finite carrier only makes the map total. -/
def columnExterior (i : AllocationColumn K B.keep.card) : A.Exterior :=
  if hi : i ∈ smoothColumns W B A then
    ⟨allocationColumnIdeal i, columnIdeal_ne_zero W B A i hi,
      Ideal.isCoprime_iff_sup_eq.mp (columnIdeal_coprime W B A i hi)⟩
  else unitExterior A

theorem columnExterior_val_of_mem (i : AllocationColumn K B.keep.card)
    (hi : i ∈ smoothColumns W B A) :
    (columnExterior W B A i).val = allocationColumnIdeal i := by
  sorry

variable (paid : FixedChildCharacters K B.keep.card)
variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (R : ActualSecondCorrelationRows A σ H ι) (side : SecondColumnSide)
variable (M : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W B A M })

/-- The frame stores the existing passive allocation verbatim. -/
def frame (firstSign : ℝ) (rectangle : Bool) :
    SecondSideFrame (V := WithLp 2 (ℝ × ℝ)) C R PUnit.{1} side B.keep.card where
  allocation := branch W B A M a
  characters := paid
  phaseCharacter := 1
  dictionary := (table W B A paid).dictionary
    (side.phase PUnit.{1} (1 : (PUnit.{1} × PUnit.{1}) →* Circle)) rectangle
  base_gt_one := (table W B A paid).base_gt_one
  length_pos := (table W B A paid).length_pos
  ideal := columnExterior W B A
  ideal_product i hi := columnExterior_val_of_mem W B A i hi
  gaussScale₁ := (table W B A paid).gauss₁
  gaussScale₂ := (table W B A paid).gauss₂
  gaussSlotScale := (table W B A paid).gaussSlot
  gaussScale₁_pos := (table W B A paid).gauss₁_pos
  gaussScale₂_pos := (table W B A paid).gauss₂_pos
  gaussSlotScale_pos := (table W B A paid).gaussSlot_pos
  leftLocation _ := CanonicalLiteralLocations.plain firstSign
  rightLocation _ := CanonicalLiteralLocations.plain firstSign
  slotLocation _ := CanonicalLiteralLocations.prime firstSign

variable (firstSign : ℝ) (rectangle : Bool)

@[simp] theorem frame_allocation :
    (frame W B A paid C R side M a firstSign rectangle).allocation = branch W B A M a := rfl

@[simp] theorem frame_witness :
    (frame W B A paid C R side M a firstSign rectangle).allocation.witness =
      (branch W B A M a).witness := rfl

@[simp] theorem frame_characters :
    (frame W B A paid C R side M a firstSign rectangle).characters = paid := rfl

@[simp] theorem frame_normalizationScale :
    (frame W B A paid C R side M a firstSign rectangle).normalizationScale =
      extraGaussScale d.gauss₁ d.gauss₂ d.gaussSlot := by
  sorry

@[simp] theorem frame_normalizer :
    (frame W B A paid C R side M a firstSign rectangle).normalizer = d.normalizer := by
  sorry

@[simp] theorem frame_source_allocation :
    (frame W B A paid C R side M a firstSign rectangle).source.allocation =
      branch W B A M a := by
  sorry

@[simp] theorem frame_source_characters (h : R.live) :
    (frame W B A paid C R side M a firstSign rectangle).source.characters h = paid := by
  sorry

@[simp] theorem frame_source_scale₁ :
    (frame W B A paid C R side M a firstSign rectangle).source.scale₁ =
      d.scale₁ rectangle / idealNorm K (B.plainDivisor 0) := by
  sorry

@[simp] theorem frame_source_scale₂ :
    (frame W B A paid C R side M a firstSign rectangle).source.scale₂ =
      d.scale₂ rectangle / idealNorm K (B.plainDivisor (Fin.succ 0)) := by
  sorry

@[simp] theorem frame_source_base :
    (frame W B A paid C R side M a firstSign rectangle).source.base = d.base := by
  sorry

@[simp] theorem frame_source_length (j : Fin B.keep.card) :
    (frame W B A paid C R side M a firstSign rectangle).source.length j =
      d.length (SlotRestriction.index B.keep j) := by
  sorry

@[simp] theorem frame_leftLocation (h : H) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (frame W B A paid C R side M a firstSign rectangle).leftLocation h I =
      CanonicalLiteralLocations.plain firstSign I := rfl

@[simp] theorem frame_rightLocation (h : H) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (frame W B A paid C R side M a firstSign rectangle).rightLocation h I =
      CanonicalLiteralLocations.plain firstSign I := rfl

@[simp] theorem frame_slotLocation (h : H) (j : Fin B.keep.card)
    (p : HeightOneSpectrum (𝓞 K)) :
    (frame W B A paid C R side M a firstSign rectangle).slotLocation h j p =
      CanonicalLiteralLocations.prime firstSign j p := rfl

end CanonicalLiteralPassiveFrames
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# Passive allocation under the original finite row measure

The original second allocation has a genuine row-dependent frozen
residue.  Its exact polynomial identity is retained first.  Its uniform
single-atom bound is then used inside the weighted finite square norm.
The passive expansion uses weighted Minkowski with the same rows and
Fourier parameter.  No common divisor is imposed on the two sides.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

namespace CanonicalLiteralPassiveEnergy

open CanonicalLiteralPassiveSource CanonicalLiteralPassiveDeletion

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (B : ActualColumnAllocation K k)

def canonicalPoint (firstSign : ℝ) (negative : Bool) :
    AllocationColumn K k → WithLp 2 (ℝ × ℝ) :=
  rawSourceLocation
    (fun I => CanonicalLiteralProfileData.orientedLocation negative
      (CanonicalLiteralLocations.plain firstSign I))
    (fun I => CanonicalLiteralProfileData.orientedLocation negative
      (CanonicalLiteralLocations.plain firstSign I))
    (fun i p => CanonicalLiteralProfileData.orientedLocation negative
      (CanonicalLiteralLocations.prime firstSign i p))

def originalFrozenLocation (firstSign : ℝ) (negative : Bool) : WithLp 2 (ℝ × ℝ) :=
  frozenSourceLocation B.keep B.witness.2
    (fun i p => CanonicalLiteralProfileData.orientedLocation negative
      (CanonicalLiteralLocations.prime firstSign i p))

private theorem joint_scalar {I V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (columns : Finset I) (z : ℂ) (c : I → ℂ) (x : I → V) (ξ : V) :
    jointFourierColumn columns (fun i => z * c i) x ξ =
      z * jointFourierColumn columns c x ξ := by
  sorry

/-- The old allocation scalar contains its entire actual frequency.
The frozen translation has modulus one but is present in this identity. -/
theorem originalColumn_eq_centered (g h : A.R) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    jointFourierColumn B.columns (d.frequencyWhole (σ := σ) g h)
      (canonicalPoint firstSign negative) ξ =
      B.scalar (σ := σ) d.characters g h d.base d.length d.slotWeight *
        jointPhase ξ (originalFrozenLocation B firstSign negative) *
          centeredColumn (σ := σ) (d := d) B (d.characters.restrictSlots B.keep)
            g h firstSign negative ξ := by
  sorry

theorem originalColumn_norm (g h : A.R) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    ‖jointFourierColumn B.columns (d.frequencyWhole (σ := σ) g h)
      (canonicalPoint firstSign negative) ξ‖ =
      ‖B.scalar (σ := σ) d.characters g h d.base d.length d.slotWeight‖ *
        ‖centeredColumn (σ := σ) (d := d) B (d.characters.restrictSlots B.keep)
          g h firstSign negative ξ‖ := by
  sorry

/-- A row-uniform bound on the actual old frozen scalar is used before
the square root.  It is not treated as a constant complex phase. -/
theorem original_sqrt_le_centered {H : Type*} (rows : Finset H)
    (weight : H → ℂ) (g h : H → A.R) (firstSign : ℝ) (negative : Bool)
    (E : ℝ) (hE : 0 ≤ E)
    (hscalar : ∀ j ∈ rows,
      ‖B.scalar (σ := σ) d.characters (g j) (h j) d.base d.length d.slotWeight‖ ^ 2 ≤ E)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    Real.sqrt (jointColumnEnergy rows B.columns weight
      (fun j => d.frequencyWhole (σ := σ) (g j) (h j))
      (fun _ => canonicalPoint firstSign negative) ξ) ≤
      Real.sqrt E * Real.sqrt
        (∑ j ∈ rows, ‖weight j‖ *
          ‖centeredColumn (σ := σ) (d := d) B (d.characters.restrictSlots B.keep)
            (g j) (h j) firstSign negative ξ‖ ^ 2) := by
  sorry

variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}

/-- The required old scalar bound comes from its actual individual
arithmetic factors and frozen profiles.  The original shared divisor
norm remains in the denominator. -/
theorem original_sqrt_le_of_atoms {H : Type*}
    (C : A.GeneralArithmeticContext σ η hS)
    (rows : Finset H) (weight : H → ℂ) (g h : H → A.R)
    (firstSign : ℝ) (negative : Bool) (annulus profile : Fin k → ℝ)
    (hplain₁ : ‖sourcePlainCoefficient d.characters.plain d.characters.plainTwist
      d.characters.mask (B.plainDivisor 0)‖ ≤ 1)
    (hplain₂ : ‖sourcePlainCoefficient d.characters.plain d.characters.plainTwist
      d.characters.mask (B.plainDivisor (Fin.succ 0))‖ ≤ 1)
    (hprime : ∀ i ∈ Finset.univ \ B.keep,
      ‖sourcePrimeCoefficient (d.characters.slot i) (d.characters.slotTwist i)
        d.characters.mask (B.witness.2 i)‖ ≤ 1)
    (hannulus : ∀ i ∈ Finset.univ \ B.keep,
      (Ideal.absNorm (B.witness.2 i).asIdeal : ℝ) ≤ annulus i * d.base ^ d.length i)
    (hprofile : ∀ i ∈ Finset.univ \ B.keep, ‖d.slotWeight i (B.witness.2 i)‖ ^ 2 ≤ profile i)
    (hA : ∀ i, 0 ≤ annulus i) (hP : ∀ i, 0 ≤ profile i)
    (hsquarefree : Squarefree B.divisor)
    (hselection : B.selection ∈ AllocationMass.idealAllocations B.divisor (k + 2))
    (ξ : WithLp 2 (ℝ × ℝ)) :
    Real.sqrt (jointColumnEnergy rows B.columns weight
      (fun j => d.frequencyWhole (σ := σ) (g j) (h j))
      (fun _ => canonicalPoint firstSign negative) ξ) ≤
      Real.sqrt ((∏ i ∈ Finset.univ \ B.keep, annulus i * profile i) /
        (Ideal.absNorm B.divisor : ℝ)) * Real.sqrt
        (∑ j ∈ rows, ‖weight j‖ *
          ‖centeredColumn (σ := σ) (d := d) B (d.characters.restrictSlots B.keep)
            (g j) (h j) firstSign negative ξ‖ ^ 2) := by
  sorry

section PassiveMinkowski

variable (W : d.ProfileData) (T : FixedChildCharacters K B.keep.card)
variable (M : HeckeGeneral.Analysis.NonzeroIdeal K)

/-- The fixed live label set is separated inside the original finite
row norm.  Its genuine signs cost at most one; no label count is used. -/
theorem sqrt_passiveColumn_le {H : Type*} (rows : Finset H)
    (weight : H → ℂ) (g h : H → A.R) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    Real.sqrt (∑ j ∈ rows, ‖weight j‖ *
      ‖passiveColumn (σ := σ) W B T M (g j) (h j) firstSign negative ξ‖ ^ 2) ≤
      ∑ a ∈ (CanonicalLiteralPassiveSource.labels W B A M).attach,
        Real.sqrt (jointColumnEnergy rows (branch W B A M a).columns weight
          (fun j => (table W B A T).frequencyWhole (σ := σ) (g j) (h j))
          (fun _ => rawSourceLocation (plainLocation₁ B firstSign negative)
            (plainLocation₂ B firstSign negative) (slotLocation B firstSign negative)) ξ) := by
  sorry

end PassiveMinkowski
end CanonicalLiteralPassiveEnergy
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# Remove zero passive coefficients before producing children

The new finite carrier is a filter of the existing attached live
labels.  Every element is still the original label and stores exactly
the same allocation witness.  A nonzero signed coefficient forces its
divisor to be squarefree, so the later frozen-scalar estimate needs no
new squarefreeness premise.  Zero coefficients are removed by an exact
finite-sum identity before applying weighted Minkowski.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum

namespace CanonicalLiteralPassiveNonzero

open CanonicalLiteralPassiveSource CanonicalLiteralPassiveDeletion

variable {K : Type} [Field K] [NumberField K] {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k) (A : SArithmeticData K)
variable (M : HeckeGeneral.Analysis.NonzeroIdeal K)

def nonzeroLabels :=
  (CanonicalLiteralPassiveSource.labels W B A M).attach.filter
    (fun a => sign a.val ≠ 0)

theorem nonzeroLabels_subset :
    nonzeroLabels W B A M ⊆ (CanonicalLiteralPassiveSource.labels W B A M).attach := by
  sorry

variable (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W B A M })

theorem sign_ne_zero (ha : a ∈ nonzeroLabels W B A M) : sign a.val ≠ 0 := by
  sorry

theorem divisor_squarefree (ha : a ∈ nonzeroLabels W B A M) :
    Squarefree (branch W B A M a).divisor := by
  sorry

/-- The original live allocation already has a valid occurrence
selection. The additional nonzero filter never changes that selection. -/
theorem selection_mem :
    (branch W B A M a).selection ∈
      AllocationMass.idealAllocations (branch W B A M a).divisor
        (B.keep.card + 2) := by
  sorry

variable {σ : K →+* ℂ}
variable (paid : FixedChildCharacters K B.keep.card)

/-- The actual centered column is unchanged when its zero signed
terms are removed. All retained labels have their original type. -/
theorem passiveColumn_eq_sum_nonzero (g h : A.R)
    (firstSign : ℝ) (negative : Bool) (ξ : WithLp 2 (ℝ × ℝ)) :
    passiveColumn (σ := σ) W B paid M g h firstSign negative ξ =
      ∑ a ∈ nonzeroLabels W B A M,
        sign a.val * jointFourierColumn (branch W B A M a).columns
          ((table W B A paid).frequencyWhole (σ := σ) g h)
          (rawSourceLocation (plainLocation₁ B firstSign negative)
            (plainLocation₂ B firstSign negative) (slotLocation B firstSign negative)) ξ := by
  sorry

/-- Weighted Minkowski is used only after the zero coefficients have
been removed. Every resulting branch therefore has a squarefree
divisor proved by `divisor_squarefree`. -/
theorem sqrt_passiveColumn_le_nonzero {H : Type*} (rows : Finset H)
    (weight : H → ℂ) (g h : H → A.R) (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    Real.sqrt (∑ j ∈ rows, ‖weight j‖ *
      ‖passiveColumn (σ := σ) W B paid M (g j) (h j) firstSign negative ξ‖ ^ 2) ≤
      ∑ a ∈ nonzeroLabels W B A M,
        Real.sqrt (jointColumnEnergy rows (branch W B A M a).columns weight
          (fun j => (table W B A paid).frequencyWhole (σ := σ) (g j) (h j))
          (fun _ => rawSourceLocation (plainLocation₁ B firstSign negative)
            (plainLocation₂ B firstSign negative) (slotLocation B firstSign negative)) ξ) := by
  sorry

end CanonicalLiteralPassiveNonzero
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# Passive branches on the same finite row measure

The old second allocation contributes a fixed translation through its
two plain divisors.  It is retained in the polynomial identity and then
removed from the square norm by the unit modulus of the Fourier phase.
Each nonzero passive label is subsequently bounded by its two actual
rectangle frames.  Rows, frequencies, allocation witnesses and the
continuous Fourier parameter are unchanged.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

namespace CanonicalLiteralPassiveFrameEnergy

open CanonicalLiteralPassiveSource CanonicalLiteralPassiveEnergy
open CanonicalLiteralPassiveFrames CanonicalLiteralPassiveNonzero

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

private theorem plain_mul (firstSign : ℝ)
    (I J : HeckeGeneral.Analysis.NonzeroIdeal K) :
    CanonicalLiteralLocations.plain firstSign (I * J) =
      CanonicalLiteralLocations.plain firstSign I +
        CanonicalLiteralLocations.plain firstSign J := by
  sorry

private theorem oriented_add (negative : Bool) (x y : WithLp 2 (ℝ × ℝ)) :
    CanonicalLiteralProfileData.orientedLocation negative (x + y) =
      CanonicalLiteralProfileData.orientedLocation negative x +
        CanonicalLiteralProfileData.orientedLocation negative y := by
  sorry

variable (B : ActualColumnAllocation K k)

def plainTranslation (firstSign : ℝ) (negative : Bool) : WithLp 2 (ℝ × ℝ) :=
  CanonicalLiteralProfileData.orientedLocation negative
      (CanonicalLiteralLocations.plain firstSign (B.plainDivisor 0)) +
    CanonicalLiteralProfileData.orientedLocation negative
      (CanonicalLiteralLocations.plain firstSign (B.plainDivisor (Fin.succ 0)))

/-- The translation is independent of every residual column. -/
theorem shifted_location (firstSign : ℝ) (negative : Bool)
    (i : AllocationColumn K B.keep.card) :
    rawSourceLocation (plainLocation₁ B firstSign negative)
      (plainLocation₂ B firstSign negative)
      (CanonicalLiteralPassiveSource.slotLocation B firstSign negative) i =
        plainTranslation B firstSign negative + canonicalPoint firstSign negative i := by
  sorry

private theorem joint_translation {J V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (columns : Finset J) (c : J → ℂ) (x : J → V) (z ξ : V) :
    jointFourierColumn columns c (fun i => z + x i) ξ =
      jointPhase ξ z * jointFourierColumn columns c x ξ := by
  sorry

/-- Only the common Fourier phase is discarded; the coefficient and
the actual allocation carrier remain the same. -/
theorem shifted_energy {H : Type*} (rows : Finset H)
    (columns : Finset (AllocationColumn K B.keep.card))
    (weight : H → ℂ) (c : H → AllocationColumn K B.keep.card → ℂ)
    (firstSign : ℝ) (negative : Bool) (ξ : WithLp 2 (ℝ × ℝ)) :
    jointColumnEnergy rows columns weight c
      (fun _ => rawSourceLocation (plainLocation₁ B firstSign negative)
        (plainLocation₂ B firstSign negative)
        (CanonicalLiteralPassiveSource.slotLocation B firstSign negative)) ξ =
      jointColumnEnergy rows columns weight c
        (fun _ => canonicalPoint firstSign negative) ξ := by
  sorry

private theorem energy_scalar {H J V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (rows : Finset H) (columns : Finset J) (weight : H → ℂ)
    (c : H → J → ℂ) (x : H → J → V) (ξ : V) (z : ℂ) :
    jointColumnEnergy rows columns weight (fun h i => z * c h i) x ξ =
      ‖z‖ ^ 2 * jointColumnEnergy rows columns weight c x ξ := by
  sorry

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (paid : FixedChildCharacters K B.keep.card)
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (R : ActualSecondCorrelationRows A σ H ι)
variable (M : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W B A M })

/-- This is the source energy of the stored frame, with its complete
original Gauss normalizer already included in the frequency term. -/
theorem frame_energy (firstSign : ℝ) (negative rectangle : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    (frame W B A paid C R (if negative then .right else .left)
      M a firstSign rectangle).energy ξ =
      jointColumnEnergy (Finset.univ : Finset R.live) (branch W B A M a).columns
        (fun h => R.weight h.val * R.correlation h.val)
        (fun h => (table W B A paid).frequencyTerm (σ := σ)
          (if negative then -(R.factor C h.val) else R.factor C h.val)
          (R.extractedRow C h).element rectangle)
        (fun _ => canonicalPoint firstSign negative) ξ := by
  sorry

/-- The complete difference is split only after the passive source
identity and its fixed translation have been proved. -/
theorem sqrt_branch_le_frames (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    Real.sqrt (jointColumnEnergy (Finset.univ : Finset R.live)
      (branch W B A M a).columns (fun h => R.weight h.val * R.correlation h.val)
      (fun h => (table W B A paid).frequencyWhole (σ := σ)
        (if negative then -(R.factor C h.val) else R.factor C h.val)
        (R.extractedRow C h).element)
      (fun _ => rawSourceLocation (plainLocation₁ B firstSign negative)
        (plainLocation₂ B firstSign negative)
        (CanonicalLiteralPassiveSource.slotLocation B firstSign negative)) ξ) ≤
      Real.sqrt ((frame W B A paid C R (if negative then .right else .left)
        M a firstSign false).energy ξ) +
        Real.sqrt ((frame W B A paid C R (if negative then .right else .left)
          M a firstSign true).energy ξ) := by
  sorry

/-- Every retained label is the original label and allocation. The
nonzero filter supplies squarefreeness for the later scalar bounds. -/
theorem sqrt_passiveColumn_le_frames (firstSign : ℝ) (negative : Bool)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    Real.sqrt (∑ h : R.live, ‖R.weight h.val * R.correlation h.val‖ *
      ‖passiveColumn (σ := σ) W B paid M
        (if negative then -(R.factor C h.val) else R.factor C h.val)
        (R.extractedRow C h).element firstSign negative ξ‖ ^ 2) ≤
      ∑ a ∈ nonzeroLabels W B A M,
        (Real.sqrt ((frame W B A paid C R (if negative then .right else .left)
          M a firstSign false).energy ξ) +
          Real.sqrt ((frame W B A paid C R (if negative then .right else .left)
            M a firstSign true).energy ξ)) := by
  sorry

end CanonicalLiteralPassiveFrameEnergy
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# Effective support of each actual passive quotient

The paid table uses the complete smooth carrier, filtered only by the
fixed exterior condition. Its support certificate is constructed from
the original profiles. An allocated plain divisor divides its actual
witness and is therefore coprime to the fixed modulus as well.

For the new child, a nonzero mask supplies that same fixed coprimality.
The quotient-profile identity then puts the product of the actual plain
divisor and the residual ideal into the full smooth carrier. The two
plain supports and the retained prime support follow on the stored
allocation, without a passive avoidance or support-norm assumption.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.CanonicalLiteralPassiveSupport

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open CanonicalLiteralSupport CanonicalLiteralProfileCarrier
open CanonicalLiteralPassiveSource CanonicalLiteralAllocatedData

variable {K : Type} [Field K] [NumberField K] {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k) (A : SArithmeticData K)

/-- This support record is an output of the actual frozen profiles;
the passive primes have not been filtered out of its carrier. -/
def tableSupport (paid : FixedChildCharacters K B.keep.card) :
    (table W B A paid).SupportData (primeSupport A.cS) where
  left_avoids I hI := by
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    exact (coprime_support_iff J.val A.cS A.cS_ne_zero).mp
      (W.exteriorSmoothPlain₁_coprime B A J hJ)
  right_avoids I hI := by
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    exact (coprime_support_iff J.val A.cS A.cS_ne_zero).mp
      (W.exteriorSmoothPlain₂_coprime B A J hJ)
  slot_avoids j p hp :=
    (coprime_support_iff p.asIdeal A.cS A.cS_ne_zero).mp
      (W.exteriorSmoothSlots_coprime B A j p hp)
  left_mem r I hI havoid := by
    refine Finset.mem_image.mpr ⟨I, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · apply W.left_support_subset_smooth B r 1 0
      apply ((W.left r).support_spec 1 0 _ I).mpr
      change ((profiles W B A paid).left r).profile 1 0
        (idealNorm K I / (table W B A paid).scale₁ r) ≠ 0
      rw [(profiles W B A paid).left_eval]
      exact hI
    · exact (coprime_support_iff I.val A.cS A.cS_ne_zero).mpr havoid
  right_mem r I hI havoid := by
    refine Finset.mem_image.mpr ⟨I, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · apply W.right_support_subset_smooth B r 1 0
      apply ((W.right r).support_spec 1 0 _ I).mpr
      change ((profiles W B A paid).right r).profile 1 0
        (idealNorm K I / (table W B A paid).scale₂ r) ≠ 0
      rw [(profiles W B A paid).right_eval]
      exact hI
    · exact (coprime_support_iff I.val A.cS A.cS_ne_zero).mpr havoid
  slot_mem j p hp havoid := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · apply ((W.slot (SlotRestriction.index B.keep j)).support_spec 0 _ p).mpr
      change ((profiles W B A paid).slot j).profile 0
        ((Ideal.absNorm p.asIdeal : ℝ) /
          (table W B A paid).base ^ (table W B A paid).length j) ≠ 0
      rw [(profiles W B A paid).slot_eval]
      exact hp
    · exact (coprime_support_iff p.asIdeal A.cS A.cS_ne_zero).mpr havoid

variable (M : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W B A M })

/-- The divisor is the actual occurrence divisor of the stored
witness, so no new coprimality premise is needed for the quotient. -/
theorem leftDivisor_coprime :
    IsCoprime ((branch W B A M a).plainDivisor 0).val A.cS := by
  sorry

theorem rightDivisor_coprime :
    IsCoprime ((branch W B A M a).plainDivisor (Fin.succ 0)).val A.cS := by
  sorry

section ActualData

variable {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K}
variable (paid : FixedChildCharacters K B.keep.card)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
variable (leftMultiplicity rightMultiplicity : ι → ℕ) (pattern : ι → Bool)
variable (ν : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining : HeckeGeneral.Analysis.NonzeroIdeal K) (m q : ℝ)
variable (inverse : IdealTest K) (index : Fin k → Fin parent.geometry.slotCount)
variable (rectangle : Bool) (firstSign : ℝ) (negative : Bool)

local notation "child" => data P R (profiles W B A paid) (branch W B A M a) F parent
  oldMoving correction hcorr C p leftMultiplicity rightMultiplicity pattern ν remaining 1 m q
  inverse (fun j => index (SlotRestriction.index B.keep j)) rectangle firstSign negative

/-- The actual appended child already contains the fixed exterior
mask; no passive-prime avoidance is assumed or inferred here. -/
theorem mask_nonzero_coprime (ξ : WithLp 2 (ℝ × ℝ))
    (u I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hmask : maskValue (child ξ) u I.val ≠ 0) : IsCoprime I.val A.cS := by
  sorry

/-- Both plain quotient supports and the twice-retained prime support
belong to the stored passive allocation. All support certificates are
constructed internally from the original profiles and the actual mask. -/
theorem effectiveSupports (κ : ℝ) (ξ : WithLp 2 (ℝ × ℝ))
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) :
    EffectivePlainSupport (child ξ) (child ξ).plainTest₁ u
        (d.base ^ (parameters (table W B A paid) (branch W B A M a)
          rectangle m q κ).n₁) (height ξ) (branch W B A M a).childPlain₁ ∧
      EffectivePlainSupport (child ξ) (child ξ).plainTest₂ u
        (d.base ^ (parameters (table W B A paid) (branch W B A M a)
          rectangle m q κ).n₂) (height ξ) (branch W B A M a).childPlain₂ ∧
      ∀ i : Fin (child ξ).geometry.slotCount,
        EffectivePrimeSupport (child ξ) i u d.base (height ξ)
          ((branch W B A M a).childSlots (Fin.cast
            (data_count P R (profiles W B A paid) (branch W B A M a) F parent oldMoving
              correction hcorr C p leftMultiplicity rightMultiplicity pattern ν remaining 1
              m q inverse (fun j => index (SlotRestriction.index B.keep j))
              rectangle firstSign negative ξ) i)) := by
  sorry

end ActualData

end HeckeSkeleton.Moments.EngineStepV2.CanonicalLiteralPassiveSupport

end

/-!
# The stored passive frame and its original occurrence dictionary

The explicit passive frame is the existing factor-frame constructor
on exactly the same actual allocation. Its witness comes from the
same attached label and nonempty finite carrier.

The original slot dictionary is restricted only by the first stored
allocation's keep map. A passive child then uses that map followed by
its own keep map. Neither construction chooses a new occurrence or
changes its original length.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.CanonicalLiteralPassiveFrames

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments
open CanonicalLiteralPassiveSource

variable {K : Type} [Field K] [NumberField K] {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (B : ActualColumnAllocation K k) (A : SArithmeticData K)
variable (paid : FixedChildCharacters K B.keep.card)
variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (R : ActualSecondCorrelationRows A σ H ι) (side : SecondColumnSide)
variable (M : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W B A M })
variable (firstSign : ℝ) (rectangle : Bool)

/-- Both constructors store the same actual witness; the nonempty
proof is the one already contained in the original attached label. -/
theorem frame_eq_factors_frame :
    frame W B A paid C R side M a firstSign rectangle =
      ((table W B A paid).factors R side
        (1 : (PUnit.{1} × PUnit.{1}) →* Circle)
        (columnExterior W B A) (columnExterior_val_of_mem W B A)
        firstSign rectangle).frame C a.val.1 a.val.2
          ((Finset.mem_filter.mp a.property).2) := rfl

variable {ω ψ : HeckeCharacter K}

/-- The table's pre-passive slots are the original first allocation's
retained occurrences, with their original lengths. -/
def tableOriginalSlots (parent : MomentData K ω ψ)
    (slots : OriginalSlotDictionary parent d.length) :
    OriginalSlotDictionary parent (table W B A paid).length where
  index :=
    { toFun := fun i => slots.index (SlotRestriction.index B.keep i)
      inj' := by
        intro i j hij
        have he := slots.index.injective hij
        apply B.keep.equivFin.symm.injective
        apply Subtype.ext
        exact he }
  length_eq i := slots.length_eq (SlotRestriction.index B.keep i)

@[simp] theorem tableOriginalSlots_index (parent : MomentData K ω ψ)
    (slots : OriginalSlotDictionary parent d.length) (i : Fin B.keep.card) :
    (tableOriginalSlots W B A paid parent slots).index i =
      slots.index (SlotRestriction.index B.keep i) := rfl

theorem tableOriginalSlots_length (parent : MomentData K ω ψ)
    (slots : OriginalSlotDictionary parent d.length) (i : Fin B.keep.card) :
    (table W B A paid).length i =
      (parent.geometry.slots (slots.index (SlotRestriction.index B.keep i))).length := by
  sorry

/-- The negative right source preserves the same occurrence lengths. -/
def frameOriginalSlots (parent : MomentData K ω ψ)
    (slots : OriginalSlotDictionary parent d.length) :
    OriginalSlotDictionary parent
      (frame W B A paid C R side M a firstSign rectangle).source.length := by
  cases side <;> exact tableOriginalSlots W B A paid parent slots

@[simp] theorem frameOriginalSlots_index (parent : MomentData K ω ψ)
    (slots : OriginalSlotDictionary parent d.length) (i : Fin B.keep.card) :
    (frameOriginalSlots W B A paid C R side M a firstSign rectangle parent slots).index i =
      slots.index (SlotRestriction.index B.keep i) := by
  sorry

/-- A child retains two actual keep maps in order. No new embedding
or capacity choice is used to identify the original slot. -/
theorem frame_childLength_eq_parent (parent : MomentData K ω ψ)
    (slots : OriginalSlotDictionary parent d.length)
    (i : Fin (frame W B A paid C R side M a firstSign rectangle).source.allocation.keep.card) :
    (frame W B A paid C R side M a firstSign rectangle).source.childLength i =
      (parent.geometry.slots (slots.index (SlotRestriction.index B.keep
        (SlotRestriction.index
          (frame W B A paid C R side M a firstSign rectangle).source.allocation.keep i)))).length := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2.CanonicalLiteralPassiveFrames

end

/-!
# Original analytic profiles on the actual passive branches

An occurrence allocation changes the two norm scales and retains a
subset of the prime slots.  Its smooth functions are exactly the old
functions.  The original Schwartz representatives, seminorm bounds and
open prime annulus therefore pass to the allocated table without an
extra analytic cost.

The final constructors use the actual enlarged smooth table and the
actual live passive label.  Their input is the already computed
original profile certificate; no finished branch window is assumed.
The clipping cost still uses the new branch's actual parameters.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open DedekindZetaZeroFree
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K] {k : ℕ}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable {W : d.ProfileData} {window : Set ℝ}

namespace CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel

variable (E : W.SchwartzModel window)

/-- The actual allocation preserves both plain representatives and
selects the original representatives of exactly the retained slots. -/
def allocate (allocation : ActualColumnAllocation K k) :
    (W.allocate allocation).SchwartzModel window where
  left := E.left
  right := E.right
  slot j := E.slot (SlotRestriction.index allocation.keep j)
  left_eq := E.left_eq
  right_eq := E.right_eq
  slot_eq j := E.slot_eq (SlotRestriction.index allocation.keep j)
  left_support := E.left_support
  right_support := E.right_support
  slot_support j := E.slot_support (SlotRestriction.index allocation.keep j)

@[simp] theorem allocate_left (allocation : ActualColumnAllocation K k) (r : Bool) :
    (E.allocate allocation).left r = E.left r := rfl

@[simp] theorem allocate_right (allocation : ActualColumnAllocation K k) (r : Bool) :
    (E.allocate allocation).right r = E.right r := rfl

@[simp] theorem allocate_slot (allocation : ActualColumnAllocation K k)
    (j : Fin allocation.keep.card) :
    (E.allocate allocation).slot j = E.slot (SlotRestriction.index allocation.keep j) := rfl

theorem allocate_prime_support (allocation : ActualColumnAllocation K k)
    (hprime : ∀ j, Function.support (E.slot j) ⊆ Set.Ioo (1 : ℝ) 2) :
    ∀ j, Function.support ((E.allocate allocation).slot j) ⊆ Set.Ioo (1 : ℝ) 2 := by
  sorry

end CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel

namespace CanonicalLiteralFullKappaInput.ComputedProfiles

variable {s : Finset (ℕ × ℕ)} {originalBound : ℝ}
variable (T : CanonicalLiteralFullKappaInput.ComputedProfiles W window s originalBound)

/-- All finite orders and numerical bounds were selected before the
passive label.  The actual quotient operation preserves them. -/
def allocate (allocation : ActualColumnAllocation K k) :
    CanonicalLiteralFullKappaInput.ComputedProfiles
      (W.allocate allocation) window s originalBound where
  model := T.model.allocate allocation
  bound := T.bound
  bound_nonneg := T.bound_nonneg
  original_bound := T.original_bound
  left_bound := T.left_bound
  right_bound := T.right_bound
  slot_bound r j := T.slot_bound r (SlotRestriction.index allocation.keep j)
  prime_window := T.model.allocate_prime_support allocation T.prime_window

@[simp] theorem allocate_bound (allocation : ActualColumnAllocation K k) :
    (T.allocate allocation).bound = T.bound := rfl

@[simp] theorem allocate_rawCoefficient (allocation : ActualColumnAllocation K k)
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (firstSign : ℝ) (rectangle : Bool) :
    (T.allocate allocation).rawCoefficient hcompact hpositive firstSign rectangle =
      T.rawCoefficient hcompact hpositive firstSign rectangle := rfl

/-- This compares the two certificates at the same explicit parameter
record. It does not identify different branch clipping parameters. -/
@[simp] theorem allocate_coefficient (allocation : ActualColumnAllocation K k)
    (Z : ℝ) (parameters : RealParameters)
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (firstSign : ℝ) (rectangle : Bool) :
    (T.allocate allocation).coefficient Z parameters hcompact hpositive firstSign rectangle =
      T.coefficient Z parameters hcompact hpositive firstSign rectangle := rfl

/-- The complete smooth carrier only replaces finite supports and
the arithmetic characters. Its individual norm functions are unchanged. -/
def passiveTable (allocation : ActualColumnAllocation K k)
    (A : SArithmeticData K) (paid : FixedChildCharacters K allocation.keep.card) :
    CanonicalLiteralFullKappaInput.ComputedProfiles
      (CanonicalLiteralPassiveSource.profiles W allocation A paid) window s originalBound :=
  (T.allocate allocation).reprofile
    (CanonicalLiteralPassiveSource.profiles W allocation A paid)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

@[simp] theorem passiveTable_bound (allocation : ActualColumnAllocation K k)
    (A : SArithmeticData K) (paid : FixedChildCharacters K allocation.keep.card) :
    (T.passiveTable allocation A paid).bound = T.bound := rfl

/-- A genuine live passive label gives its own quotient table. The
certificate is constructed by the two actual occurrence restrictions. -/
def passiveBranch (allocation : ActualColumnAllocation K k)
    (A : SArithmeticData K) (paid : FixedChildCharacters K allocation.keep.card)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W allocation A M }) :
    CanonicalLiteralFullKappaInput.ComputedProfiles
      ((CanonicalLiteralPassiveSource.profiles W allocation A paid).allocate
        (CanonicalLiteralPassiveSource.branch W allocation A M a)) window s originalBound :=
  (T.passiveTable allocation A paid).allocate
    (CanonicalLiteralPassiveSource.branch W allocation A M a)

@[simp] theorem passiveBranch_bound (allocation : ActualColumnAllocation K k)
    (A : SArithmeticData K) (paid : FixedChildCharacters K allocation.keep.card)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W allocation A M }) :
    (T.passiveBranch allocation A paid M a).bound = T.bound := rfl

@[simp] theorem passiveBranch_slot (allocation : ActualColumnAllocation K k)
    (A : SArithmeticData K) (paid : FixedChildCharacters K allocation.keep.card)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W allocation A M })
    (j : Fin (CanonicalLiteralPassiveSource.branch W allocation A M a).keep.card) :
    (T.passiveBranch allocation A paid M a).model.slot j =
      T.model.slot (SlotRestriction.index allocation.keep
        (SlotRestriction.index (CanonicalLiteralPassiveSource.branch W allocation A M a).keep j)) :=
  rfl

theorem passiveBranch_prime_support (allocation : ActualColumnAllocation K k)
    (A : SArithmeticData K) (paid : FixedChildCharacters K allocation.keep.card)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W allocation A M }) :
    ∀ j, Function.support ((T.passiveBranch allocation A paid M a).model.slot j) ⊆
      Set.Ioo (1 : ℝ) 2 := by
  sorry

@[simp] theorem passiveBranch_rawCoefficient (allocation : ActualColumnAllocation K k)
    (A : SArithmeticData K) (paid : FixedChildCharacters K allocation.keep.card)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W allocation A M })
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (firstSign : ℝ) (rectangle : Bool) :
    (T.passiveBranch allocation A paid M a).rawCoefficient hcompact hpositive firstSign rectangle =
      T.rawCoefficient hcompact hpositive firstSign rectangle := rfl

end CanonicalLiteralFullKappaInput.ComputedProfiles
end HeckeSkeleton.Moments.EngineStepV2

end

