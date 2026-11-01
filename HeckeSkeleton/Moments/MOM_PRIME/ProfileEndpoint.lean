import HeckeSkeleton.Moments.MOM_PRIME.AbsoluteBounds
import HeckeGeneral.Analysis.MomentSlotScaleChange

/-!
# The endpoint for a whole family of varying prime profiles

The physical prime profiles can contain their own norm powers after the
global contour parameters are fixed. Their supports and lengths need not
identify their values with the original real prime windows. This interface
therefore calibrates only the total selected length. Slot count, annular
support, and a common polynomial bound on the actual prime profiles are
separate explicit hypotheses for the entire family.

The constant precedes the family, all its source indices, characters,
heights, and profiles. The only height cost is `2 * g.slots * H`. There is
no field or hypothesis asserting an energy or prime-product estimate.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- Actual moment data with the source's row width and selected total
length. The prime profiles may vary throughout the dependent index family.
No equality with the original untwisted prime geometry is required. -/
structure PrimeProfileEndpointFamily (g : PrimeWindowGeometry)
    (ω ψ : HeckeCharacter K) (Index : ℝ → ℝ → Type*) (Sector : Type*) where
  shell : ∀ Z T, Index Z T → ℝ
  shell_pos : ∀ Z T i, 0 < shell Z T i
  selected : ∀ Z T, Index Z T → Finset (Fin g.slots)
  data : ∀ Z T, Index Z T → Sector → MomentData K ω ψ
  parameters : ∀ Z T, Index Z T → RealParameters
  row_width : ∀ Z T i, (parameters Z T i).m + (parameters Z T i).q = 1
  total_length : ∀ Z T i s, (data Z T i s).geometry.totalLength =
    ∑ _j ∈ selected Z T i,
      HeckeGeneral.ThetaSkeleton.TIP.slotLength g.slots (shell Z T i)

variable {K} {g : PrimeWindowGeometry} {ω ψ : HeckeCharacter K}
  {Index : ℝ → ℝ → Type*} {Sector : Type*}

namespace PrimeProfileEndpointFamily

def base (F : PrimeProfileEndpointFamily K g ω ψ Index Sector)
    {Z T} (i : Index Z T) : ℝ := Z ^ F.shell Z T i

def selectedLength (F : PrimeProfileEndpointFamily K g ω ψ Index Sector)
    {Z T} (i : Index Z T) : ℝ :=
  ∑ _j ∈ F.selected Z T i,
    HeckeGeneral.ThetaSkeleton.TIP.slotLength g.slots (F.shell Z T i)

/-- The literal finite sector sum, with the original rows and masks. -/
def energy [Fintype Sector] (F : PrimeProfileEndpointFamily K g ω ψ Index Sector)
    {Z T} (i : Index Z T) : ℝ :=
  ∑ s : Sector, ∑ u ∈ pairedRows (F.data Z T i s) (F.parameters Z T i) (F.base i),
    ‖slotProduct (F.data Z T i s) u (F.base i) 0‖ ^ 2

theorem one_le_base (F : PrimeProfileEndpointFamily K g ω ψ Index Sector)
    {Z T} (i : Index Z T) (hZ : 1 ≤ Z) : 1 ≤ F.base i :=
  Real.one_le_rpow hZ (F.shell_pos Z T i).le

end PrimeProfileEndpointFamily

/-- A common bound on the actual prime profiles, chosen for the entire
family. It concerns individual profile values and contains no finite-sum
or energy inequality. It is independent of the three ideal tests. -/
def WholePrimeProfileControl (F : PrimeProfileEndpointFamily K g ω ψ Index Sector)
    (B H : ℝ) : Prop :=
  ∀ (Z T : ℝ) (i : Index Z T), 1 ≤ Z → 0 ≤ T → ∀ s : Sector,
    (F.data Z T i s).geometry.slotCount ≤ g.slots ∧
      (∀ j, Function.support (((F.data Z T i s).geometry.slots j).profile 0) ⊆
        Ioo (1 : ℝ) 2) ∧
      (∀ j y, ‖((F.data Z T i s).geometry.slots j).profile 0 y‖ ≤ B * (1 + T) ^ H)

variable (K)

/-- The whole-family endpoint with its explicit polynomial height cost.
The constant is chosen before every family, model, profile and source
index, from the common slot count and profile bound. -/
theorem paired_primes_endpoint_profiles (g : PrimeWindowGeometry) (Sector : Type*)
    [Fintype Sector] (B H : ℝ) (hB : 0 ≤ B) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ω ψ : HeckeCharacter K} {Index : ℝ → ℝ → Type*}
      (F : PrimeProfileEndpointFamily K g ω ψ Index Sector),
      WholePrimeProfileControl F B H →
      ∀ (Z T : ℝ) (i : Index Z T), 1 ≤ Z → 0 ≤ T →
        F.energy i ≤ C * F.base i ^ (1 + F.selectedLength i) *
          (1 + T) ^ (2 * (g.slots : ℝ) * H) := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_pairedPrimeAbsoluteBound K g.slots B hB
  refine ⟨((Fintype.card Sector : ℝ) + 1) * C₀, by positivity, ?_⟩
  intro ω ψ Index F hprofiles Z T i hZ hT
  have hbase := F.one_le_base i hZ
  have hheight : 1 ≤ 1 + T := by linarith
  have hs (s : Sector) :
      (∑ u ∈ pairedRows (F.data Z T i s) (F.parameters Z T i) (F.base i),
        ‖slotProduct (F.data Z T i s) u (F.base i) 0‖ ^ 2) ≤
          C₀ * F.base i ^ (1 + F.selectedLength i) *
            (1 + T) ^ (2 * (g.slots : ℝ) * H) := by
    obtain ⟨hn, hann, hprof⟩ := hprofiles Z T i hZ hT s
    have h := hbound (F.data Z T i s) (F.parameters Z T i) (F.base i) 0
      (1 + T) H hbase hheight hH (by rw [F.row_width]; norm_num) hn hann hprof
    simpa only [F.row_width, F.total_length, PrimeProfileEndpointFamily.selectedLength] using h
  calc
    _ ≤ ∑ _s : Sector, C₀ * F.base i ^ (1 + F.selectedLength i) *
        (1 + T) ^ (2 * (g.slots : ℝ) * H) :=
      Finset.sum_le_sum (fun s _ => hs s)
    _ = (Fintype.card Sector : ℝ) * C₀ * F.base i ^ (1 + F.selectedLength i) *
        (1 + T) ^ (2 * (g.slots : ℝ) * H) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ ((Fintype.card Sector : ℝ) + 1) * C₀ * F.base i ^ (1 + F.selectedLength i) *
        (1 + T) ^ (2 * (g.slots : ℝ) * H) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith) hC₀.le)
          (Real.rpow_nonneg (zero_le_one.trans hbase) _))
        (Real.rpow_nonneg (zero_le_one.trans hheight) _)

/-- The `UniformMomentBound` order, with height exponent `2 * g.slots * H`,
ceiling one, and threshold one. The scalar and threshold precede even the
choice of family. Fixing a family and imposing any bin or eligibility
restrictions only specializes this estimate. -/
theorem paired_primes_endpoint_profiles_uniform (g : PrimeWindowGeometry) (Sector : Type*)
    [Fintype Sector] (B H : ℝ) (hB : 0 ≤ B) (hH : 0 ≤ H) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ A ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
        ∃ Z₀ k : ℝ, 1 ≤ Z₀ ∧ 0 ≤ k ∧
          ∀ {ω ψ : HeckeCharacter K} {Index : ℝ → ℝ → Type*}
            (F : PrimeProfileEndpointFamily K g ω ψ Index Sector),
            WholePrimeProfileControl F B H →
            ∀ Z : ℝ, Z₀ ≤ Z → ∀ i : Index Z (Z ^ τ),
              F.energy i ≤ k * F.base i ^ (1 + F.selectedLength i + δ) *
                (1 + Z ^ τ) ^ A := by
  obtain ⟨C, hC, hbound⟩ := paired_primes_endpoint_profiles K g Sector B H hB hH
  refine ⟨2 * (g.slots : ℝ) * H, 1, by positivity, zero_lt_one, ?_⟩
  intro τ _ _
  refine ⟨1, C, le_rfl, hC.le, ?_⟩
  intro ω ψ Index F hprofiles Z hZ i
  have hT : 0 ≤ Z ^ τ := Real.rpow_nonneg (zero_le_one.trans hZ) _
  exact (hbound F hprofiles Z (Z ^ τ) i hZ hT).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (F.one_le_base i hZ) (by linarith)) hC.le)
      (Real.rpow_nonneg (by linarith : 0 ≤ 1 + Z ^ τ) _))

end HeckeSkeleton.Moments.MOM_PRIME
