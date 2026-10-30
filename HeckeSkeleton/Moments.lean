import HeckeSkeleton.Theta
import HeckeGeneral.Analysis.TInputParameterUniformMoments
import HeckeSkeleton.HighArithmeticInputs
import HeckeAxiom.QuadraticSieve
import CubicSieve.Complete

/-! Exploratory actual I/P pipeline, revised §§4–5 and §7.
This file intentionally contains named admissions. None is native verified.
The existing cache arithmetic/fiber proofs are migration candidates; the
canonical recursions, KP consumption and full kappa range are separate gaps.
The 5/6-capped old PRegion and ParameterUniformPInput are never used here.
All finite energies below are the original MomentInputs polynomials.
-/
set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton
open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K]

local instance momentSectorFintype (c : TargetContext K) :
    Fintype (SixthUnitClasses K (places K c)) := Fintype.ofFinite _

/-- The index belongs to the ONE actual expansion, including its original
selected slots. No arbitrary finite row family is substituted. -/
structure SourceMomentIndex (c : TargetContext K) (Z T : ℝ) : Type 1 where
  block : Fin ((targetData K c).expansion Z T).blockCount
  label : (((targetData K c).expansion Z T).block block).Label
  t : ℝ
  t_lower : 1 ≤ t
  t_upper : t ≤ 3 / 2
  subdivision : Fin
    (((((targetData K c).expansion Z T).block block).amplitudeSet label).subdivisionCount t)
  selected : Finset (Fin c.geometry.slots)

variable {K}
variable {c : TargetContext K} {Z T : ℝ}
abbrev momentBlock (i : SourceMomentIndex K c Z T) :=
  ((targetData K c).expansion Z T).block i.block
abbrev momentAmplitude (i : SourceMomentIndex K c Z T) :=
  (momentBlock i).amplitudeSet i.label
abbrev momentWitness (i : SourceMomentIndex K c Z T) :=
  (momentAmplitude i).subdivision i.t i.subdivision
def momentBase (i : SourceMomentIndex K c Z T) : ℝ := Z ^ (momentBlock i).shell
def selectedLength (i : SourceMomentIndex K c Z T) : ℝ :=
  ∑ _j ∈ i.selected,
    HeckeGeneral.ThetaSkeleton.TIP.slotLength c.geometry.slots (momentBlock i).shell
def SourceMomentIndex.noSlots (i : SourceMomentIndex K c Z T) :
    SourceMomentIndex K c Z T := { i with selected := ∅ }

def inverseParameters (i : SourceMomentIndex K c Z T) : RealParameters :=
  ⟨1, (momentWitness i).inverseLength, selectedLength i, 0, 0, 0, 2 * c.family.B - 1⟩
def pairedParameters (i : SourceMomentIndex K c Z T) : RealParameters :=
  ⟨1, 0, selectedLength i, 0, (momentWitness i).plainLength,
    (momentWitness i).plainLength, 2 * c.family.B - 1⟩

/-- Revised full range, with the genuine unrestricted zero-slot alternative. -/
def ExtendedPRegion (a : RealParameters) : Prop :=
  3 / 4 ≤ a.κ ∧ a.κ ≤ 1 ∧
    (a.z = 0 ∨ (0 < a.z ∧ a.n₁ + a.n₂ + 6 * a.κ * a.z ≤ a.m + a.q))

def inverseCapacity (i : SourceMomentIndex K c Z T) : Prop :=
  (momentWitness i).inverseLength + 2 * selectedLength i ≤ 1 - 2 * c.family.lamA ∧
  2 * (momentWitness i).inverseLength + 8 * selectedLength i ≤ 3 - 2 * c.family.lamA
def pairedCapacity (i : SourceMomentIndex K c Z T) : Prop :=
  (∀ j ∈ i.selected,
    HeckeGeneral.ThetaSkeleton.TIP.slotLength c.geometry.slots (momentBlock i).shell ≤
      (momentMesh K c.family).val) ∧
  2 * (momentWitness i).plainLength +
    6 * (2 * c.family.B - 1) * selectedLength i ≤ 1

variable (K)

/-- One family, with a finite physical/witness height vector and independent
rowwise real/imaginary twists. The unmarked family has INDEPENDENT U,D.
Tests, backgrounds and masks are actual data; no energy is a field. -/
structure SourceMomentModels (c : TargetContext K) where
  dimension : ℕ
  inverse : ∀ Z T, SourceMomentIndex K c Z T →
    SixthUnitClasses K (places K c) → (Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) →
      MomentData K c.family.omega (targetCharacter K c)
  paired : ∀ Z T, SourceMomentIndex K c Z T →
    SixthUnitClasses K (places K c) → (Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) →
      MomentData K c.family.omega (targetCharacter K c)
  unmarked : ℝ → ℝ → SixthUnitClasses K (places K c) →
    (Fin dimension → ℝ) → (NonzeroIdeal K → Fin dimension → ℝ) →
    (NonzeroIdeal K → Fin dimension → ℝ) →
      MomentData K c.family.omega (targetCharacter K c)
  heights : ∀ Z T, SourceMomentIndex K c Z T → Fin dimension → ℝ
  realShifts : ∀ Z T, SourceMomentIndex K c Z T → NonzeroIdeal K → Fin dimension → ℝ
  imagShifts : ∀ Z T, SourceMomentIndex K c Z T → NonzeroIdeal K → Fin dimension → ℝ

-- OBLIGATION MI-M-ROW-CHARACTER | Prop3.1(iii),§4.1,§7.1,pp3–4,16–18,43–44.
-- MIGRATION: the audited default input arithmeticRowCharacterInput (ArithmeticInputs),
-- the same actual Kummer rows that the high-bin consumers require.
def momentRowCharacters (c : TargetContext K) : RowCharacterInput K (places K c) (probeData K c) :=
  arithmeticRowCharacterInput K (places K c) (probeData K c)

-- OBLIGATION MI-M-MODELS | §4.1–4.2,§7.1,pp16–20,43.
-- Construct actual finite ideal tests, sector slices, backgrounds and
-- row-independent slot coefficients, not arbitrary admissibility predicates.
def momentModels (c : TargetContext K) : SourceMomentModels K c := by
  sorry

variable {K}
abbrev inverseModel (M : SourceMomentModels K c) (i : SourceMomentIndex K c Z T)
    (s : SixthUnitClasses K (places K c)) :=
  M.inverse Z T i s (M.heights Z T i) (M.realShifts Z T i) (M.imagShifts Z T i)
abbrev pairedModel (M : SourceMomentModels K c) (i : SourceMomentIndex K c Z T)
    (s : SixthUnitClasses K (places K c)) :=
  M.paired Z T i s (M.heights Z T i) (M.realShifts Z T i) (M.imagShifts Z T i)
abbrev unmarkedModel (M : SourceMomentModels K c) (i : SourceMomentIndex K c Z T)
    (s : SixthUnitClasses K (places K c)) :=
  M.unmarked (momentBase i) ((momentBase i) ^ (momentWitness i).inverseLength)
    s (M.heights Z T i) (M.realShifts Z T i) (M.imagShifts Z T i)

/-- Original complete-ideal zeros, including redundant sixth powers. -/
def originalMomentMask (u : NonzeroIdeal K) (I : Ideal (𝓞 K)) : Bool :=
  if (∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I →
    p ∉ places K c ∧ (6 : 𝓞 K) ∉ p.asIdeal) ∧
    IsCoprime I u.val then true else false

/-- Literal polynomial calibration. Sector dependence is retained, and the
two plain factors are both matched, with their actual conjugated profiles. -/
structure SourcePolynomialCalibration (R : RowCharacterInput K (places K c) (probeData K c))
    (M : SourceMomentModels K c) : Prop where
  character : ∀ Z T (i : SourceMomentIndex K c Z T) u,
    u ∈ (momentWitness i).rows →
      (inverseModel M i u.sector).rowCharacter u.ideal.val = R.character u ∧
      (pairedModel M i u.sector).rowCharacter u.ideal.val = R.character u
  mask : ∀ Z T (i : SourceMomentIndex K c Z T) s u I,
    (inverseModel M i s).commonMask u I = originalMomentMask (c := c) u I ∧
    (pairedModel M i s).commonMask u I = originalMomentMask (c := c) u I
  inverse : ∀ Z T (i : SourceMomentIndex K c Z T) u,
    u ∈ (momentWitness i).rows →
      (momentWitness i).inverseValue u =
        inversePolynomial (inverseModel M i u.sector) u.ideal.val
          ((momentBase i) ^ (momentWitness i).inverseLength) 0
  plain₁ : ∀ Z T (i : SourceMomentIndex K c Z T) u,
    u ∈ (momentWitness i).rows →
      (momentWitness i).plainValue u =
        plainPolynomial (pairedModel M i u.sector)
          (pairedModel M i u.sector).plainTest₁ u.ideal.val
          ((momentBase i) ^ (momentWitness i).plainLength) 0
  plain₂ : ∀ Z T (i : SourceMomentIndex K c Z T) u,
    u ∈ (momentWitness i).rows →
      (momentWitness i).plainValue u =
        plainPolynomial (pairedModel M i u.sector)
          (pairedModel M i u.sector).plainTest₂ u.ideal.val
          ((momentBase i) ^ (momentWitness i).plainLength) 0
  inverse_slots : ∀ Z T (i : SourceMomentIndex K c Z T) u,
    u ∈ (momentWitness i).rows →
      (∏ j ∈ i.selected, (momentAmplitude i).slotValue j u) =
        slotProduct (inverseModel M i u.sector) u.ideal.val (momentBase i) 0
  paired_slots : ∀ Z T (i : SourceMomentIndex K c Z T) u,
    u ∈ (momentWitness i).rows →
      (∏ j ∈ i.selected, (momentAmplitude i).slotValue j u) =
        slotProduct (pairedModel M i u.sector) u.ideal.val (momentBase i) 0
  unmarked : ∀ Z T (i : SourceMomentIndex K c Z T) u,
    u ∈ (momentWitness i).rows →
      (momentWitness i).inverseValue u =
        inversePolynomial (unmarkedModel M i u.sector) u.ideal.val
          ((momentBase i) ^ (momentWitness i).inverseLength) 0

/-- The base ideal, original sector and complete common mask must survive
the true source reindex. Large complete norm alone cannot prove this. -/
structure SourceRowEligibility (M : SourceMomentModels K c) : Prop where
  /-- The actual strict widths r+2z<m and 2r+8z<3m, not the old ceiling. -/
  inverse_region : ∀ Z T (i : SourceMomentIndex K c Z T),
    inverseCapacity i → MIRegion (inverseParameters i)
  /-- Full kappa <= 1, retaining the unrestricted z=0 branch. -/
  paired_region : ∀ Z T (i : SourceMomentIndex K c Z T),
    pairedCapacity i → ExtendedPRegion (pairedParameters i)
  inverse_rows : ∀ Z T (i : SourceMomentIndex K c Z T) u,
    u ∈ (momentWitness i).rows →
      u.ideal.val ∈ (inverseModel M i u.sector).rows (momentBase i)
  paired_rows : ∀ Z T (i : SourceMomentIndex K c Z T) u,
    u ∈ (momentWitness i).rows →
      u.ideal.val ∈ pairedRows (pairedModel M i u.sector) (pairedParameters i) (momentBase i)
  unmarked_rows : ∀ Z T (i : SourceMomentIndex K c Z T) u,
    u ∈ (momentWitness i).rows →
      u.ideal.val ∈ (unmarkedModel M i u.sector).rows (2 * momentBase i) ∧
      SixthPowerFreeIdeal (K := K) u.ideal.val
  fiber : Function.Injective
    (fun u : FrequencyRow K (places K c) => (u.ideal.val, u.sector))
  geometry : ∀ Z T (i : SourceMomentIndex K c Z T) s,
    (inverseModel M i s).geometry.totalLength = selectedLength i ∧
    (pairedModel M i s).geometry.totalLength = selectedLength i
  paired_finite_slots : ∀ Z T (i : SourceMomentIndex K c Z T) s j,
    FiniteOrder ((pairedModel M i s).slotCoefficient j)

/-- Uniform control of each one-variable slice at every finite order.
This statement does NOT assert mixed parameter derivatives or locality.
Those requirements of the full profile family remain to be split out of
the coarse canonical-recursion obligations; slice bounds do not imply them. -/
def WholeMomentProfileControl (M : SourceMomentModels K c) : Prop :=
  ∀ J : ℕ, ∀ A : ℝ, 0 ≤ A →
    ∃ C H a b : ℝ, 0 < C ∧ 0 ≤ H ∧ 0 < a ∧ a < b ∧
      ∀ Z T (i : SourceMomentIndex K c Z T), 1 ≤ Z → 1 ≤ T →
      ∀ s (ξ : Fin M.dimension → ℝ) σ τ,
        ‖ξ‖ ≤ T → (∀ u, ‖σ u‖ ≤ 8) → (∀ u, ‖τ u‖ ≤ 1 + ‖ξ‖) →
        ∀ d ∈ [M.inverse Z T i s ξ σ τ, M.paired Z T i s ξ σ τ],
        ∀ W ∈ [d.inverseTest, d.plainTest₁, d.plainTest₂], ∀ u,
          ContDiff ℝ ∞ (W.profile u 0) ∧
          (∀ y, W.profile u 0 y ≠ 0 → a ≤ y ∧ y ≤ b) ∧
          testSeminorm (W.profile u 0) J A ≤ C * (1 + T) ^ H

variable (K) (c : TargetContext K)

-- OBLIGATION MI-M-POLYNOMIAL-CALIBRATION | §4.2,§6.2,§7.1,pp18–20,38,43.
theorem moment_polynomial_calibration :
    SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c) := by
  sorry

-- OBLIGATION MI-M-FIBER-ELIGIBILITY | §4.9,§7.1,pp35,43–44.
-- MIGRATION: ArithmeticFrequencyRowCharacterFibers/EventualExclusion.
-- Their cutoff is on the sixth-free BASE, not a complete ideal A^6.
-- Coarse remaining consumer: original row map, finite theta family and
-- both actual pairedRows branches, with all zero masks unchanged.
theorem moment_row_eligibility
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c)) :
    SourceRowEligibility (momentModels K c) := by
  sorry

-- OBLIGATION MI-M-PROFILE-UNIFORMITY | Lemma4.12,Prop4.14,pp33–35.
-- COARSE: must further split mixed Sobolev derivatives/locality/backward
-- finite-order propagation; this endpoint does not claim that pointwise
-- testSeminorm control alone establishes those stronger properties.
theorem moment_profile_control
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c)) :
    WholeMomentProfileControl (momentModels K c) := by
  sorry

/-- Actual allowed-symbol quadratic sieve, with arbitrary independent
column coefficients and common-prime zeros. -/
def QuadraticSieveBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y →
    ∀ A B : Finset (ExteriorIdeal K (places K c)),
      (∀ I ∈ A, Squarefree I.val.val ∧ exteriorNorm K (places K c) I ≤ X) →
      (∀ J ∈ B, Squarefree J.val.val ∧ exteriorNorm K (places K c) J ≤ Y) →
      ∀ z : ExteriorIdeal K (places K c) → ℂ,
        ∑ I ∈ A, ‖∑ J ∈ B, z J *
          idealSymbol K (places K c) (probeData K c).arithmetic J
            ((probeData K c).arithmetic.generator I) ^ 3‖ ^ 2 ≤
          C * (X * Y) ^ ε * (X + Y) * ∑ J ∈ B, ‖z J‖ ^ 2

def CubicSieveBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ X Y : ℝ, 1 ≤ X → 1 ≤ Y →
    ∀ A B : Finset (ExteriorIdeal K (places K c)),
      (∀ I ∈ A, Squarefree I.val.val ∧ exteriorNorm K (places K c) I ≤ X) →
      (∀ J ∈ B, Squarefree J.val.val ∧ exteriorNorm K (places K c) J ≤ Y) →
      ∀ e : ℤ, (e = 2 ∨ e = -2) → ∀ z : ExteriorIdeal K (places K c) → ℂ,
        ∑ I ∈ A, ‖∑ J ∈ B, z J *
          idealSymbol K (places K c) (probeData K c).arithmetic J
            ((probeData K c).arithmetic.generator I) ^ e‖ ^ 2 ≤
          C * (X * Y) ^ ε * (X + Y + (X * Y) ^ (2 / 3 : ℝ)) *
            ∑ J ∈ B, ‖z J‖ ^ 2

-- MI-M-QUADRATIC-SIEVE | §4.3,(4.12),pp20–21.
-- Axiom's Goldmakher–Louvel sieve for the actual Kummer quadratic family of the
-- same arithmetic context (HeckeAxiom.QuadraticSieve).
theorem moment_quadratic_sieve : QuadraticSieveBound K c :=
  HeckeAxiom.quadratic_sieve_bound (axiomChoice K c)

-- MI-M-CUBIC-SIEVE | Lemma4.5,(4.13),p21. Proved by Codex in CubicSieve/ (BGL n = 3).
-- Includes exact BGL/ray-class comparison, not an unspecified cubic family.
theorem moment_cubic_sieve : CubicSieveBound K c := by
  change CubicSieve.ExteriorSieve.TargetBound K (places K c)
    (probeData K c).arithmetic
  exact CubicSieve.Complete.targetBound (axiomChoice K c).A
    (probeData K c).arithmetic (allowedGenerators K c)

variable {K c}
def markedModelEnergy (M : SourceMomentModels K c) {Z T}
    (i : SourceMomentIndex K c Z T) : ℝ :=
  ∑ s : SixthUnitClasses K (places K c),
    inverseEnergy (inverseModel M i s) (inverseParameters i) (momentBase i) 0
def pairedModelEnergy (M : SourceMomentModels K c) {Z T}
    (i : SourceMomentIndex K c Z T) : ℝ :=
  ∑ s : SixthUnitClasses K (places K c),
    pairedEnergy (pairedModel M i s) (pairedParameters i) (momentBase i) 0

def unmarkedBallEnergy (d : MomentData K c.family.omega (targetCharacter K c))
    (U D : ℝ) : ℝ :=
  ∑ u ∈ (d.rows (2 * U)).filter (SixthPowerFreeIdeal (K := K)),
    ‖inversePolynomial d u D 0‖ ^ 2
def amplifiedModelEnergy (M : SourceMomentModels K c) {Z T}
    (i : SourceMomentIndex K c Z T) : ℝ :=
  ∑ s : SixthUnitClasses K (places K c),
    unmarkedBallEnergy (unmarkedModel M i s)
      (momentBase i) ((momentBase i) ^ (momentWitness i).inverseLength)

/-- Constants are for the ENTIRE actual index/profile family. Height order
and ceiling precede tau; threshold and scalar may depend on that fixed tau. -/
def UniformMomentBound
    (E : ∀ Z T, SourceMomentIndex K c Z T → ℝ)
    (power : ∀ Z T, SourceMomentIndex K c Z T → ℝ)
    (eligible : ∀ Z T, SourceMomentIndex K c Z T → Prop) : Prop :=
  ∃ A ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
    ∀ τ : ℝ, 0 < τ → τ ≤ ceiling → ∃ Z₀ k : ℝ, 1 ≤ Z₀ ∧ 0 ≤ k ∧
      ∀ Z : ℝ, Z₀ ≤ Z → ∀ i : SourceMomentIndex K c Z (Z ^ τ),
        51 / 100 < (momentBlock i).bin → eligible Z (Z ^ τ) i →
          E Z (Z ^ τ) i ≤
            k * (momentBase i) ^ (power Z (Z ^ τ) i + c.family.lamA) * (1 + Z ^ τ) ^ A

def StrictUnmarkedMomentBound (M : SourceMomentModels K c) : Prop :=
  ∀ a ε : ℝ, 0 < a → 0 < ε →
    ∃ C A h : ℝ, 0 < C ∧ 0 ≤ A ∧ 0 < h ∧
      ∀ U D : ℝ, 1 ≤ U → 1 ≤ D → D ≤ U ^ (1 / (1 + a)) →
      ∀ (ξ : Fin M.dimension → ℝ) σ τ,
        ‖ξ‖ ≤ (U * D) ^ h → (∀ u, ‖σ u‖ ≤ 8) →
        (∀ u, ‖τ u‖ ≤ 1 + ‖ξ‖) →
        (∑ s : SixthUnitClasses K (places K c),
          unmarkedBallEnergy (M.unmarked U D s ξ σ τ) U D) ≤
          C * U ^ (1 + ε) * (1 + ‖ξ‖) ^ A

structure CanonicalInverseModelBounds (M : SourceMomentModels K c) : Prop where
  marked : UniformMomentBound
    (fun _ _ i => markedModelEnergy M i) (fun _ _ _ => 1)
    (fun _ _ i => inverseCapacity i)
  unmarked_strict : StrictUnmarkedMomentBound M

def SixthPowerMaskIdentity (M : SourceMomentModels K c) : Prop :=
  ∀ U D s ξ σ τ (u : NonzeroIdeal K) (a : ExteriorIdeal K (places K c)),
    (M.unmarked U D s ξ σ τ).allowedRow u →
      (M.unmarked U D s ξ σ τ).allowedRow (u * a.val ^ 6) ∧
      (M.unmarked U D s ξ σ τ).rowCharacter (u * a.val ^ 6) =
        (M.unmarked U D s ξ σ τ).rowCharacter u ∧
      ∀ I : Ideal (𝓞 K),
        maskValue (M.unmarked U D s ξ σ τ) (u * a.val ^ 6) I =
          maskValue (M.unmarked U D s ξ σ τ) u I *
            (if IsCoprime I a.val.val then 1 else 0)

def AmplifiedIndependentMomentBound (M : SourceMomentModels K c) : Prop :=
  ∀ a ε : ℝ, 0 < a → 0 < ε →
    ∃ C A h : ℝ, 0 < C ∧ 0 ≤ A ∧ 0 < h ∧
      ∀ U D : ℝ, 1 ≤ U → 1 ≤ D →
      ∀ (ξ : Fin M.dimension → ℝ) σ τ,
        ‖ξ‖ ≤ (U * D) ^ h → (∀ u, ‖σ u‖ ≤ 8) →
        (∀ u, ‖τ u‖ ≤ 1 + ‖ξ‖) →
        (∑ s : SixthUnitClasses K (places K c),
          unmarkedBallEnergy (M.unmarked U D s ξ σ τ) U D) ≤
          C * max U (U ^ (1 / 6 : ℝ) * D ^ (5 * (1 + a) / 6)) *
            (U * D) ^ ε * (1 + ‖ξ‖) ^ A

variable (K c)
-- OBLIGATION MI-I-CANONICAL-RECURSION | Lemma4.8,Prop4.10,Thm4.1,pp23–28.
-- COARSE analytic/arithmetic proof: two true Poisson transforms, child
-- masks/labels/fixed-triple fibers, prefactor and strict margins, finite
-- termination; must not be replaced by an assumed MIInput or row bound.
theorem canonical_inverse_models (L : LocalHighKMellinInput K c)
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c))
    (hrows : SourceRowEligibility (momentModels K c))
    (hprofiles : WholeMomentProfileControl (momentModels K c))
    (hquadratic : QuadraticSieveBound K c) (hcubic : CubicSieveBound K c)
    (hreflection : MarkedCoefficientReflectionInput K (places K c)
      (probeData K c).arithmetic (finiteMellinData K c L)
      (thetaPeriod K (places K c) (probeData K c) (targetCharacter K c))) :
    CanonicalInverseModelBounds (momentModels K c) := by
  sorry

-- OBLIGATION MI-I-SIXTH-POWER-ZEROS | Lemma5.1,(5.2),(5.3),pp35–36.
theorem inverse_sixth_power_masks
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c)) :
    SixthPowerMaskIdentity (momentModels K c) := by
  sorry

-- OBLIGATION MI-I-INDEPENDENT-AMPLIFICATION | Lemma5.1,pp35–36.
-- Includes multiplier ideal count and injective(u,a)->u*a^6. U,D and the
-- physical/plain/inverse height vector remain independent after constants.
theorem inverse_independent_amplification
    (hmi : CanonicalInverseModelBounds (momentModels K c))
    (hmask : SixthPowerMaskIdentity (momentModels K c))
    (hprofiles : WholeMomentProfileControl (momentModels K c)) :
    AmplifiedIndependentMomentBound (momentModels K c) := by
  sorry

-- OBLIGATION MI-I-AMPLIFIED-WITNESS-CALIBRATION | (5.4),(7.6),pp36,43.
-- COARSE scale/height bridge: choose a and preliminary epsilon from the
-- fixed bounded witness lengths/loss; retain the true row-local profiles.
theorem inverse_amplified_witness_models
    (hamp : AmplifiedIndependentMomentBound (momentModels K c))
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c))
    (hrows : SourceRowEligibility (momentModels K c))
    (hprofiles : WholeMomentProfileControl (momentModels K c)) :
    UniformMomentBound
      (fun _ _ i => amplifiedModelEnergy (momentModels K c) i)
      (fun _ _ i => amplifiedInverseExponent (momentWitness i).inverseLength)
      (fun _ _ _ => True) := by
  sorry

/-- These are inequalities for the ACTUAL selected finite prime products,
not arbitrary sublists in P. At kappa1 no zero-free premise is supplied. -/
def PairedPrimeProductBound (M : SourceMomentModels K c) (κ : ℝ) : Prop :=
  UniformMomentBound
    (fun _ _ i => ∑ s : SixthUnitClasses K (places K c),
      ∑ u ∈ pairedRows (pairedModel M i s) (pairedParameters i) (momentBase i),
        ‖slotProduct (pairedModel M i s) u (momentBase i) 0‖ ^ 2)
    (fun _ _ i => 1 + κ * selectedLength i)
    (fun _ _ i => pairedCapacity i)

-- OBLIGATION MI-P-PRIME-CANCELLATION-BELOW-ONE | §4.6,(4.38),p29.
-- Actual finite-character log derivative and smooth prime Mellin estimate.
theorem paired_primes_below_one
    (hB : c.family.B < 1)
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c))
    (hrows : SourceRowEligibility (momentModels K c))
    (hprofiles : WholeMomentProfileControl (momentModels K c)) :
    PairedPrimeProductBound K c (momentModels K c) (2 * c.family.B - 1) := by
  sorry

-- OBLIGATION MI-P-PRIME-ABSOLUTE-ENDPOINT | §4.6,p29.
-- Existing partial migration: ActualPrimeGeometryAbsoluteBound and
-- ActualPairedSlotRemoval; those do not prove the fourth-moment recursion.
theorem paired_primes_endpoint
    (hB : c.family.B = 1)
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c))
    (hrows : SourceRowEligibility (momentModels K c))
    (hprofiles : WholeMomentProfileControl (momentModels K c)) :
    PairedPrimeProductBound K c (momentModels K c) 1 := by
  sorry

-- OBLIGATION MI-P-ZERO-SLOT | Thm4.2 z=0,Lemma4.11,pp17–18,29–33.
-- Unrestricted bounded plain lengths; only actual nonprincipal character
-- excluded. Same-mask equal-product residues cancel before absolute values.
theorem paired_zero_slot_models
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c))
    (hrows : SourceRowEligibility (momentModels K c))
    (hprofiles : WholeMomentProfileControl (momentModels K c))
    (hquadratic : QuadraticSieveBound K c) :
    UniformMomentBound
      (fun _ _ i => pairedModelEnergy (momentModels K c) i.noSlots)
      (fun _ _ _ => 1) (fun _ _ _ => True) := by
  sorry

-- OBLIGATION MI-P-POSITIVE-SLOTS-BELOW-ONE | Thm4.2,§4.8,pp17–18,30–33.
-- COARSE full recursive proof: whole centered coefficient, complete
-- nonprimitive correlations, amplifier pool and valuations1/6/7, child
-- support/capacity ledger, exceptional new rows, strict width termination.
theorem paired_positive_below_one
    (hB : c.family.B < 1)
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c))
    (hrows : SourceRowEligibility (momentModels K c))
    (hprofiles : WholeMomentProfileControl (momentModels K c))
    (hquadratic : QuadraticSieveBound K c)
    (hprime : PairedPrimeProductBound K c (momentModels K c) (2 * c.family.B - 1)) :
    UniformMomentBound
      (fun _ _ i => pairedModelEnergy (momentModels K c) i)
      (fun _ _ _ => 1) (fun _ _ i => pairedCapacity i ∧ i.selected.Nonempty) := by
  sorry

-- OBLIGATION MI-P-POSITIVE-SLOTS-ENDPOINT | Thm4.2,§4.8,pp17–18,30–33.
-- Exact kappa1 capacity; no hidden finite-order seven-eighths theorem.
theorem paired_positive_endpoint
    (hB : c.family.B = 1)
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c))
    (hrows : SourceRowEligibility (momentModels K c))
    (hprofiles : WholeMomentProfileControl (momentModels K c))
    (hquadratic : QuadraticSieveBound K c)
    (hprime : PairedPrimeProductBound K c (momentModels K c) 1) :
    UniformMomentBound
      (fun _ _ i => pairedModelEnergy (momentModels K c) i)
      (fun _ _ _ => 1) (fun _ _ i => pairedCapacity i ∧ i.selected.Nonempty) := by
  sorry

variable {K c}
def physicalInverseEnergy {Z T} (i : SourceMomentIndex K c Z T) : ℝ :=
  ∑ u ∈ (momentWitness i).rows,
    ‖(momentWitness i).inverseValue u *
      ∏ j ∈ i.selected, (momentAmplitude i).slotValue j u‖ ^ 2
def physicalPlainEnergy {Z T} (i : SourceMomentIndex K c Z T) : ℝ :=
  ∑ u ∈ (momentWitness i).rows,
    ‖(momentWitness i).plainValue u ^ 2 *
      ∏ j ∈ i.selected, (momentAmplitude i).slotValue j u‖ ^ 2
def physicalUnmarkedEnergy {Z T} (i : SourceMomentIndex K c Z T) : ℝ :=
  ∑ u ∈ (momentWitness i).rows, ‖(momentWitness i).inverseValue u‖ ^ 2

variable (K c)
-- OBLIGATION MI-M-FINITE-SECTOR-REINDEX | §4.1,§7.1,pp16–18,43.
-- COARSE finite-sum plumbing only. Uses actual pointwise calibration,
-- original pairedRows eligibility and injective(ideal,sector), no final
-- energy estimate. All sectors are summed rather than discarded.
theorem moment_finite_sector_reindex
    (hcal : SourcePolynomialCalibration (momentRowCharacters K c) (momentModels K c))
    (hrows : SourceRowEligibility (momentModels K c)) :
    ∀ Z T (i : SourceMomentIndex K c Z T),
      physicalInverseEnergy i ≤ markedModelEnergy (momentModels K c) i ∧
      physicalPlainEnergy i ≤ pairedModelEnergy (momentModels K c) i ∧
      physicalUnmarkedEnergy i ≤ amplifiedModelEnergy (momentModels K c) i := by
  sorry

variable {K c}

/-- Elementary common-constant plumbing for two actual energy families. -/
theorem uniformMomentBound_join
    (E F p q : ∀ Z T, SourceMomentIndex K c Z T → ℝ)
    (P Q : ∀ Z T, SourceMomentIndex K c Z T → Prop)
    (hE : UniformMomentBound E p P) (hF : UniformMomentBound F q Q) :
    ∃ A ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ ceiling → ∃ Z₀ k : ℝ, 1 ≤ Z₀ ∧ 0 ≤ k ∧
        ∀ Z : ℝ, Z₀ ≤ Z → ∀ i : SourceMomentIndex K c Z (Z ^ τ),
          51 / 100 < (momentBlock i).bin →
          (P Z (Z ^ τ) i → E Z (Z ^ τ) i ≤
            k * momentBase i ^ (p Z (Z ^ τ) i + c.family.lamA) * (1 + Z ^ τ) ^ A) ∧
          (Q Z (Z ^ τ) i → F Z (Z ^ τ) i ≤
            k * momentBase i ^ (q Z (Z ^ τ) i + c.family.lamA) * (1 + Z ^ τ) ^ A) := by
  obtain ⟨A₁, H₁, hA₁, hH₁, hb₁⟩ := hE
  obtain ⟨A₂, H₂, hA₂, hH₂, hb₂⟩ := hF
  refine ⟨max A₁ A₂, min H₁ H₂, hA₁.trans (le_max_left _ _), lt_min hH₁ hH₂, ?_⟩
  intro τ hτ hτH
  obtain ⟨Z₁, k₁, hZ₁, hk₁, he⟩ := hb₁ τ hτ (hτH.trans (min_le_left _ _))
  obtain ⟨Z₂, k₂, hZ₂, hk₂, hf⟩ := hb₂ τ hτ (hτH.trans (min_le_right _ _))
  refine ⟨max Z₁ Z₂, max k₁ k₂, hZ₁.trans (le_max_left _ _),
    hk₁.trans (le_max_left _ _), ?_⟩
  intro Z hZ i hbin
  have hZ₁' : Z₁ ≤ Z := (le_max_left _ _).trans hZ
  have hZ₂' : Z₂ ≤ Z := (le_max_right _ _).trans hZ
  have hZn : 0 ≤ Z := zero_le_one.trans (hZ₁.trans hZ₁')
  have hT : 1 ≤ 1 + Z ^ τ := by linarith [Real.rpow_nonneg hZn τ]
  have hU : 0 ≤ momentBase i := Real.rpow_nonneg hZn _
  have raise (k A r x : ℝ) (hk : 0 ≤ k) (hkk : k ≤ max k₁ k₂)
      (hAA : A ≤ max A₁ A₂)
      (hx : x ≤ k * momentBase i ^ r * (1 + Z ^ τ) ^ A) :
      x ≤ max k₁ k₂ * momentBase i ^ r * (1 + Z ^ τ) ^ max A₁ A₂ := by
    apply hx.trans
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hkk (Real.rpow_nonneg hU _)
    · exact Real.rpow_le_rpow_of_exponent_le hT hAA
    · exact Real.rpow_nonneg (zero_le_one.trans hT) _
    · exact mul_nonneg (hk₁.trans (le_max_left _ _)) (Real.rpow_nonneg hU _)
  constructor
  · intro hi
    exact raise k₁ A₁ _ _ hk₁ (le_max_left _ _) (le_max_left _ _) (he Z hZ₁' i hbin hi)
  · intro hi
    exact raise k₂ A₂ _ _ hk₂ (le_max_right _ _) (le_max_right _ _) (hf Z hZ₂' i hbin hi)

variable (K c)

/-- Actual ISource assembled from literal marked and amplified ideal energies. -/
theorem inverseSource (L : LocalHighKMellinInput K c)
    (H : LocalExteriorDigitInput K c) :
    ISource c.geometry (targetData K c) c.family.lamA := by
  have hcal := moment_polynomial_calibration K c
  have hrows := moment_row_eligibility K c hcal
  have hprofiles := moment_profile_control K c hcal
  have hmi := canonical_inverse_models K c L hcal hrows hprofiles
    (moment_quadratic_sieve K c) (moment_cubic_sieve K c) (markedReflection K c L H)
  have hamp := inverse_independent_amplification K c hmi
    (inverse_sixth_power_masks K c hcal) hprofiles
  have hw := inverse_amplified_witness_models K c hamp hcal hrows hprofiles
  have hreindex := moment_finite_sector_reindex K c hcal hrows
  obtain ⟨A, H, hA, hH, hb⟩ := uniformMomentBound_join
    (fun _ _ i => markedModelEnergy (momentModels K c) i)
    (fun _ _ i => amplifiedModelEnergy (momentModels K c) i)
    (fun _ _ _ => 1)
    (fun _ _ i => amplifiedInverseExponent (momentWitness i).inverseLength)
    (fun _ _ i => inverseCapacity i) (fun _ _ _ => True) hmi.marked hw
  refine ⟨A, H, hA, hH, ?_⟩
  intro τ hτ hτH
  obtain ⟨Z₀, k, hZ₀, hk, hbound⟩ := hb τ hτ hτH
  refine ⟨Z₀, k, hZ₀, hk, ?_⟩
  intro Z hZ b hbin ℓ t ht ht' j
  constructor
  · intro I h₁ h₂
    let i : SourceMomentIndex K c Z (Z ^ τ) := ⟨b, ℓ, t, ht, ht', j, I⟩
    exact (hreindex Z (Z ^ τ) i).1.trans
      ((hbound Z hZ i hbin).1 ⟨h₁, h₂⟩)
  · let i : SourceMomentIndex K c Z (Z ^ τ) := ⟨b, ℓ, t, ht, ht', j, ∅⟩
    exact (hreindex Z (Z ^ τ) i).2.2.trans
      ((hbound Z hZ i hbin).2 trivial)

/-- Actual PSource assembled with an explicit B<1 / B=1 split and the
unrestricted zero-slot energy. The old capped PRegion is absent. -/
theorem plainSource :
    PSource c.geometry (targetData K c) c.family.B c.family.lamA
      (momentMesh K c.family).val := by
  have hcal := moment_polynomial_calibration K c
  have hrows := moment_row_eligibility K c hcal
  have hprofiles := moment_profile_control K c hcal
  have hquad := moment_quadratic_sieve K c
  have hpositive : UniformMomentBound
      (fun _ _ i => pairedModelEnergy (momentModels K c) i)
      (fun _ _ _ => 1) (fun _ _ i => pairedCapacity i ∧ i.selected.Nonempty) := by
    rcases lt_or_eq_of_le c.family.B_upper with hB | hB
    · exact paired_positive_below_one K c hB hcal hrows hprofiles hquad
        (paired_primes_below_one K c hB hcal hrows hprofiles)
    · exact paired_positive_endpoint K c hB hcal hrows hprofiles hquad
        (paired_primes_endpoint K c hB hcal hrows hprofiles)
  have hzero := paired_zero_slot_models K c hcal hrows hprofiles hquad
  have hreindex := moment_finite_sector_reindex K c hcal hrows
  obtain ⟨A, H, hA, hH, hb⟩ := uniformMomentBound_join
    (fun _ _ i => pairedModelEnergy (momentModels K c) i)
    (fun _ _ i => pairedModelEnergy (momentModels K c) i.noSlots)
    (fun _ _ _ => 1) (fun _ _ _ => 1)
    (fun _ _ i => pairedCapacity i ∧ i.selected.Nonempty)
    (fun _ _ _ => True) hpositive hzero
  refine ⟨A, H, hA, hH, ?_⟩
  intro τ hτ hτH
  obtain ⟨Z₀, k, hZ₀, hk, hbound⟩ := hb τ hτ hτH
  refine ⟨Z₀, k, hZ₀, hk, ?_⟩
  intro Z hZ b hbin ℓ t ht ht' j
  constructor
  · intro I hmesh hcap
    let i : SourceMomentIndex K c Z (Z ^ τ) := ⟨b, ℓ, t, ht, ht', j, I⟩
    by_cases hI : I.Nonempty
    · exact (hreindex Z (Z ^ τ) i).2.1.trans
        ((hbound Z hZ i hbin).1 ⟨⟨hmesh, hcap⟩, hI⟩)
    · have hIempty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
      subst I
      exact (hreindex Z (Z ^ τ) i).2.1.trans
        ((hbound Z hZ i hbin).2 trivial)
  · let i : SourceMomentIndex K c Z (Z ^ τ) := ⟨b, ℓ, t, ht, ht', j, ∅⟩
    have hh := (hreindex Z (Z ^ τ) i).2.1.trans ((hbound Z hZ i hbin).2 trivial)
    simpa only [i, physicalPlainEnergy, SourceMomentIndex.noSlots,
      momentWitness, momentAmplitude, momentBlock, momentBase,
      Finset.prod_empty, mul_one] using hh

end HeckeSkeleton
