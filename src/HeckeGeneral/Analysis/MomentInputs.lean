import HeckeGeneral.Analysis.HeckeSeries
import HeckeGeneral.Analysis.HeckeContinuation
import HeckeGeneral.Analysis.EndpointClosure
import HeckeGeneral.Characters.IdeleNormContinuity
import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius

/-!
# Candidate MI / paired-fourth-moment interfaces

This file is a conditional interface, not an implementation of the canonical
construction. It uses actual nonzero integral ideals, their absolute norms,
the ideal Moebius function, and coefficients of actual Hecke characters.
`CanonicalAdmissibility` below is a separate, still-uninstantiated obligation:
in particular arbitrary finite row families do not become canonical merely
by satisfying the displayed numerical inequalities.

Source: M, sources/hecke_seven_eighths_all_characters.tex, 834--858 (MI),
878--886 (independent scales), 952--986 (P), 1454--1525 (choice order).
There is no axiom, seed bound, strict improvement, or zero-free conclusion here.
-/

noncomputable section

namespace HeckeGeneral.Analysis.ConditionalMoments

open NumberField IsDedekindDomain HeckeGeneral.Characters
open scoped BigOperators Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- Compact pretarget bounds. The positive margin is used for MI's two
strict inequalities, not to replace P's non-strict capacity inequality. -/
structure RealBox where
  upper : ℝ
  upper_pos : 0 < upper
  margin : ℝ
  margin_pos : 0 < margin

structure RealParameters where
  m : ℝ
  r : ℝ
  z : ℝ
  q : ℝ
  n₁ : ℝ
  n₂ : ℝ
  κ : ℝ

def InBox (b : RealBox) (a : RealParameters) : Prop :=
  0 ≤ a.m ∧ a.m ≤ b.upper ∧ 0 ≤ a.r ∧ a.r ≤ b.upper ∧
  0 ≤ a.z ∧ a.z ≤ b.upper ∧ 0 ≤ a.q ∧ a.q ≤ b.upper ∧
  0 ≤ a.n₁ ∧ a.n₁ ≤ b.upper ∧ 0 ≤ a.n₂ ∧ a.n₂ ≤ b.upper

def MIRegion (a : RealParameters) : Prop :=
  0 ≤ a.m ∧ 0 ≤ a.r ∧ 0 ≤ a.z ∧
  a.r + 2 * a.z < a.m ∧ 2 * a.r + 8 * a.z < 3 * a.m

def MIUniformMargins (b : RealBox) (a : RealParameters) : Prop :=
  a.r + 2 * a.z + b.margin ≤ a.m ∧
  2 * a.r + 8 * a.z + b.margin ≤ 3 * a.m

/-- Zero slots have no n₁+n₂ capacity restriction. Their lengths are still
bounded by the independently quantified pretarget `RealBox`. -/
def PRegion (a : RealParameters) : Prop :=
  3 / 4 ≤ a.κ ∧ a.κ ≤ 5 / 6 ∧
  (a.z = 0 ∨ (0 < a.z ∧ a.n₁ + a.n₂ + 6 * a.κ * a.z ≤ a.m + a.q))

/-- An actual ideal-indexed rowwise test with an exact finite support.
Smoothness, annular support, and permitted rowwise dependence belong to the
canonical-admissibility interface, not to this bare data structure. -/
structure IdealTest where
  profile : NonzeroIdeal K → ℝ → ℝ → ℂ
  support : NonzeroIdeal K → ℝ → ℝ → Finset (NonzeroIdeal K)
  support_spec : ∀ u t D I,
    I ∈ support u t D ↔ profile u t (idealNorm K I / D) ≠ 0

structure PrimeWindow where
  length : ℝ
  length_pos : 0 < length
  profile : ℝ → ℝ → ℂ
  support : ℝ → ℝ → Finset (HeightOneSpectrum (𝓞 K))
  support_spec : ∀ t P p,
    p ∈ support t P ↔ profile t ((Ideal.absNorm p.asIdeal : ℝ) / P) ≠ 0

/-- All slot lengths, tests and their analytic supports are pretarget data.
Only the arithmetic coefficient characters will be selected later. -/
structure SlotGeometry where
  slotCount : ℕ
  slots : Fin slotCount → PrimeWindow K

variable {K}

def SlotGeometry.totalLength (g : SlotGeometry K) : ℝ := ∑ i, (g.slots i).length

def SlotGeometry.fitsMesh (g : SlotGeometry K) (mesh : ℝ) : Prop :=
  ∀ i, (g.slots i).length ≤ mesh

variable (K)

/-- Concrete polynomial data with actual Hecke coefficients. The source's
finite-ray reciprocity identification of `rowCharacter u` with the moving
sextic presentation, and the source's row multiplicities/sectors, are NOT
constructed here. They must be supplied by `CanonicalAdmissibility`.

The row enumeration is exhaustive for its explicitly supplied arithmetic
predicate; it is not an unconstrained finite set selected after an estimate.
One common ideal mask is used in every polynomial and slot. -/
structure MomentData (ω ψ : HeckeCharacter K) where
  theta : Finset (HeckeCharacter K)
  theta_finite : ∀ θ ∈ theta, FiniteOrder θ
  inverseBackground : HeckeCharacter K
  direction : ℤ
  direction_spec : direction = -1 ∨ direction = 1
  directed_background :
    inverseBackground ^ (-direction) ∈ theta ∨
      ∃ θ ∈ theta, inverseBackground ^ (-direction) = ψ * θ
  plainBackground : HeckeCharacter K
  plain_background_spec :
    plainBackground = 1 ∨ plainBackground = ψ ∨ plainBackground = ψ⁻¹
  rowCharacter : NonzeroIdeal K → HeckeCharacter K
  rowCharacter_finite : ∀ u, FiniteOrder (rowCharacter u)
  allowedRow : NonzeroIdeal K → Prop
  rows : ℝ → Finset (NonzeroIdeal K)
  rows_spec : ∀ U u, u ∈ rows U ↔ allowedRow u ∧ idealNorm K u ≤ U
  commonMask : NonzeroIdeal K → Ideal (𝓞 K) → Bool
  inverseTest : IdealTest K
  plainTest₁ : IdealTest K
  plainTest₂ : IdealTest K
  geometry : SlotGeometry K
  slotCoefficient : Fin geometry.slotCount → HeckeCharacter K

variable {K}
variable {ω ψ : HeckeCharacter K}

def maskValue (d : MomentData K ω ψ) (u : NonzeroIdeal K)
    (I : Ideal (𝓞 K)) : ℂ := if d.commonMask u I then 1 else 0

/-- Inverting a zero-extended ramified coefficient does not make it one. -/
theorem zero_direction (d : MomentData K ω ψ) : (0 : ℂ) ^ d.direction = 0 := by
  rcases d.direction_spec with h | h <;> simp [h]

/-- The inverse finite sum, with the true ideal Moebius and character values.
The common mask is retained; ramified character values have their existing
zero extension. Negative direction uses the integer power of that value. -/
def inversePolynomial (d : MomentData K ω ψ) (u : NonzeroIdeal K)
    (D t : ℝ) : ℂ :=
  (Real.sqrt D : ℂ)⁻¹ *
    ∑ I ∈ d.inverseTest.support u t D,
      (UniqueFactorizationMonoid.moebius I.val : ℂ) *
        heckeIdealCoefficient K d.inverseBackground I *
        heckeIdealCoefficient K (d.rowCharacter u) I ^ d.direction *
        d.inverseTest.profile u t (idealNorm K I / D) * maskValue d u I.val

def plainPolynomial (d : MomentData K ω ψ) (W : IdealTest K)
    (u : NonzeroIdeal K) (N t : ℝ) : ℂ :=
  (Real.sqrt N : ℂ)⁻¹ * ∑ I ∈ W.support u t N,
    heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I *
      W.profile u t (idealNorm K I / N) * maskValue d u I.val

def primePolynomial (d : MomentData K ω ψ) (i : Fin d.geometry.slotCount)
    (u : NonzeroIdeal K) (Z t : ℝ) : ℂ :=
  let P := Z ^ (d.geometry.slots i).length
  (Real.sqrt P : ℂ)⁻¹ * ∑ p ∈ (d.geometry.slots i).support t P,
    primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p *
      (d.geometry.slots i).profile t ((Ideal.absNorm p.asIdeal : ℝ) / P) *
      maskValue d u p.asIdeal

def slotProduct (d : MomentData K ω ψ) (u : NonzeroIdeal K) (Z t : ℝ) : ℂ :=
  ∏ i, primePolynomial d i u Z t

def slotLength (d : MomentData K ω ψ) : ℝ := d.geometry.totalLength

/-- Positive-slot exclusion is finite inducing character in Θ; the zero-slot
branch excludes only the principal ACTUAL character. For actual Hecke
characters, inducing extensions and their deleted Euler factors still need
the source-calibration proof recorded below. -/
def pairedRows (d : MomentData K ω ψ) (a : RealParameters) (Z : ℝ) :
    Finset (NonzeroIdeal K) :=
  (d.rows (Z ^ (a.m + a.q))).filter fun u =>
    if a.z = 0 then d.plainBackground * d.rowCharacter u ≠ 1
    else d.rowCharacter u ∉ d.theta

def inverseEnergy (d : MomentData K ω ψ) (a : RealParameters) (Z t : ℝ) : ℝ :=
  ∑ u ∈ d.rows (Z ^ a.m),
    ‖inversePolynomial d u (Z ^ a.r) t * slotProduct d u Z t‖ ^ 2

def pairedEnergy (d : MomentData K ω ψ) (a : RealParameters) (Z t : ℝ) : ℝ :=
  ∑ u ∈ pairedRows d a Z,
    ‖plainPolynomial d d.plainTest₁ u (Z ^ a.n₁) t *
      plainPolynomial d d.plainTest₂ u (Z ^ a.n₂) t * slotProduct d u Z t‖ ^ 2

/-- Still-unimplemented source-compatibility interfaces. Implementers must
identify actual canonical row enumeration and sextic reciprocity; fixed-S
and presentation-zero masks; permitted Q4.5 rowwise profiles; disjoint
prime annuli BEFORE masks; bounded row-independent coefficients; strict
width/slot mesh; and every recursively generated moving puncture with its
Q17.2 capacity. Arbitrary extra moving masks are forbidden.

`paired` must additionally identify the primitive inducing characters and
exceptional rows, and source reflection/finite-seminorm compatibility.
Admissibility is imposed on a WHOLE SCALE FAMILY: profile seminorm bounds
and moving-puncture budgets must hold uniformly across Z (and across the
independent U,D for `unmarked`). Fixed backgrounds, finite-ray corrections,
and source indexing must remain calibrated throughout that family. A set of
unrelated per-scale certificates with per-scale constants does not suffice.
These predicates contain NO moment inequalities or zero-free assertions.
No instance is supplied, so this is not a claimed calibration theorem. -/
structure CanonicalAdmissibility (ω : HeckeCharacter K) where
  inverse : RealBox → RealParameters → ℝ →
    (ψ : HeckeCharacter K) → (ℝ → MomentData K ω ψ) → Prop
  paired : RealBox → RealParameters → ℝ →
    (ψ : HeckeCharacter K) → (ℝ → MomentData K ω ψ) → Prop
  unmarked : RealBox → (ψ : HeckeCharacter K) →
    (ℝ → ℝ → MomentData K ω ψ) → Prop

/-- A posttarget polynomial-height estimate. Its degree and allowed height
exponent may depend on the target and calibrated data. The real exponent
`power` and loss `ε` have already been chosen before that target. -/
def PolynomialHeightBound (E : ℝ → ℝ → ℝ) (power ε : ℝ) : Prop :=
  ∃ C Z₀ A h : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧ 0 ≤ A ∧ 0 < h ∧
    ∀ Z t : ℝ, Z₀ ≤ Z → |t| ≤ Z ^ h →
      E Z t ≤ C * Z ^ (power + ε) * (1 + |t|) ^ A

/-- MI: compact real ranges, strict margins and the mesh precede the target.
Constants/seminorm and height data are inside `PolynomialHeightBound`, after
the entire scale family, and hence are uniform in its external scale Z.
The zero-slot case is part of MI itself. -/
def MIInput (ω : HeckeCharacter K) (cal : CanonicalAdmissibility ω) : Prop :=
  ∀ b : RealBox, ∀ ε : ℝ, 0 < ε →
    ∃ mesh : ℝ, 0 < mesh ∧ ∀ a : RealParameters,
      InBox b a → MIRegion a → MIUniformMargins b a →
      ∀ g : SlotGeometry K, g.fitsMesh mesh → g.totalLength = a.z →
      ∀ ψ : HeckeCharacter K, ψ ∈ HeckePacket K ω →
      ∀ d : ℝ → MomentData K ω ψ,
        (∀ Z, (d Z).geometry = g) → cal.inverse b a mesh ψ d →
        PolynomialHeightBound (fun Z t => inverseEnergy (d Z) a Z t) a.m ε

/-- The actual finite-order common meromorphic zero boundary. This is a
premise of P at the current B, not a finite-order 7/8 theorem. -/
def FiniteOrderBoundary (B : ℝ) : Prop :=
  ∀ χ : HeckeCharacter K, FiniteOrder χ → ∀ s : ℂ, B < s.re →
    meromorphicOrderAt (heckeContinuation K χ) s ≤ 0

/-- P: the mesh is uniform in κ∈[3/4,5/6] on the pretarget compact box.
Paired slots have θ∈Θ, so their actual prime character χ_u θ is finite
order. The finite-order common-boundary/prime-cancellation premise is
explicit and precedes the estimate; it is not a 7/8 input.

The bridge from this actual zero boundary to the source's quantitative
reciprocal and prime bounds is still required. -/
def PInput (ω : HeckeCharacter K) (cal : CanonicalAdmissibility ω) : Prop :=
  ∀ b : RealBox, ∀ ε : ℝ, 0 < ε →
    ∃ mesh : ℝ, 0 < mesh ∧ ∀ a : RealParameters,
      InBox b a → PRegion a → FiniteOrderBoundary (K := K) ((1 + a.κ) / 2) →
      ∀ g : SlotGeometry K, g.fitsMesh mesh → g.totalLength = a.z →
      ∀ ψ : HeckeCharacter K, ψ ∈ HeckePacket K ω →
      ∀ d : ℝ → MomentData K ω ψ,
        (∀ Z, (d Z).geometry = g) → cal.paired b a mesh ψ d →
        (∀ Z i, (d Z).slotCoefficient i ∈ (d Z).theta) →
        PolynomialHeightBound (fun Z t => pairedEnergy (d Z) a Z t) (a.m + a.q) ε

def SixthPowerFreeIdeal (I : NonzeroIdeal K) : Prop :=
  ∀ p : HeightOneSpectrum (𝓞 K), ¬p.asIdeal ^ 6 ∣ I.val

def independentEnergy (d : MomentData K ω ψ) (U D t : ℝ) : ℝ :=
  ∑ u ∈ (d.rows (2 * U)).filter
      (fun u => U ≤ idealNorm K u ∧ SixthPowerFreeIdeal u),
    ‖inversePolynomial d u D t‖ ^ 2

/-- A SEPARATE candidate consequence of MI plus sixth-power amplification,
ideal counting, exact masks and scale-supremum control. No implication from
MI is proved here. U and D vary independently, including fixed U and D→∞.
The central exponent is exactly 5(1+c)/6, not 5/6 with an implicit loss.
The constants are selected after the ENTIRE two-scale data family, so they
remain uniform when its permitted profiles/masks depend on both U and D. -/
def IndependentTwoScaleInput (ω : HeckeCharacter K)
    (cal : CanonicalAdmissibility ω) : Prop :=
  ∀ b : RealBox, ∀ c ε : ℝ, 0 < c → 0 < ε →
    ∀ ψ : HeckeCharacter K, ψ ∈ HeckePacket K ω →
    ∀ d : ℝ → ℝ → MomentData K ω ψ, cal.unmarked b ψ d →
      ∃ C A h : ℝ,
        0 < C ∧ 0 ≤ A ∧ 0 < h ∧
        ∀ U D t : ℝ, 1 ≤ U → 1 ≤ D → |t| ≤ (U * D) ^ h →
          independentEnergy (d U D) U D t ≤
            C * max U (U ^ (1 / 6 : ℝ) * D ^ (5 * (1 + c) / 6)) *
              (U * D) ^ ε * (1 + |t|) ^ A

/-- Existing arithmetic certificate supplies the dynamic fourth-moment κ. -/
theorem dynamic_kappa {B : ℝ} (hlo : 7 / 8 < B) (hhi : B ≤ 11 / 12) :
    3 / 4 ≤ 2 * B - 1 ∧ 2 * B - 1 ≤ 5 / 6 ∧
      (1 + (2 * B - 1)) / 2 = B := by
  have h := dynamic_parameter_bounds hlo hhi
  constructor
  · exact h.2.2.1.le
  constructor
  · exact h.2.2.2.1
  · ring

theorem dynamic_capacity_denominator (B : ℝ) :
    6 * (2 * B - 1) = 9 / 2 + 12 * (B - 7 / 8) := by ring

theorem zero_slot_region {a : RealParameters}
    (hκlo : 3 / 4 ≤ a.κ) (hκhi : a.κ ≤ 5 / 6) (hz : a.z = 0) :
    PRegion a := ⟨hκlo, hκhi, Or.inl hz⟩

theorem pairedRows_zero (d : MomentData K ω ψ) (a : RealParameters)
    (Z : ℝ) (hz : a.z = 0) :
    pairedRows d a Z = (d.rows (Z ^ (a.m + a.q))).filter
      (fun u => d.plainBackground * d.rowCharacter u ≠ 1) := by
  simp [pairedRows, hz]

def capacityChoice (M n₁ n₂ κ : ℝ) : ℝ := (M - n₁ - n₂) / (6 * κ)

theorem positive_capacity_choice {M n₁ n₂ κ : ℝ}
    (hκ : 0 < κ) (hroom : n₁ + n₂ < M) :
    0 < capacityChoice M n₁ n₂ κ ∧
      n₁ + n₂ + 6 * κ * capacityChoice M n₁ n₂ κ = M := by
  have hden : 0 < 6 * κ := by positivity
  constructor
  · exact div_pos (by linarith) hden
  · unfold capacityChoice
    field_simp [ne_of_gt hden]
    ring

/-- M §7's plain capacity, with the actual dynamic κ, not κ=3/4. -/
def plainCapacity (m B : ℝ) : ℝ := (1 - 2 * m) / (6 * (2 * B - 1))

theorem dynamic_plain_capacity {m B : ℝ}
    (hB : 7 / 8 < B) (hm : m < 1 / 2) :
    0 < plainCapacity m B ∧
      2 * m + 6 * (2 * B - 1) * plainCapacity m B = 1 := by
  have hκ : 0 < 2 * B - 1 := by linarith
  have h := positive_capacity_choice (M := 1) (n₁ := m) (n₂ := m) hκ (by linarith)
  simpa [plainCapacity, capacityChoice, sub_sub, add_sub_assoc, two_mul] using h

theorem dynamic_capacity_loss {m q B : ℝ}
    (hmlo : 1 / 3 ≤ m) (hmhi : m ≤ 1 / 2)
    (hqlo : 0 ≤ q) (hqhi : q ≤ 1 / 2) (hB : 7 / 8 ≤ B) :
    2 * q * (1 - 2 * m) *
      (2 / 9 - 1 / (9 / 2 + 12 * (B - 7 / 8))) ≤ (B - 7 / 8) / 4 :=
  dynamic_capacity_cost hmlo hmhi hqlo hqhi (by linarith)

/-!
Unfinished bridges (none are hidden in a definition above):
1. Construct/calibrate actual canonical row/sector data and the admissibility
   predicates; identify χ_n(u)^direction with the actual coefficient used in
   inversePolynomial, preserving reciprocity phases and every zero/mask.
2. Prove MIInput and PInput from the transferred theta construction, canonical
   Q17/Q18 recursions and finite-seminorm propagation. In P, derive the actual
   quantitative prime bounds from the actual finite-order common zero boundary.
3. Derive IndependentTwoScaleInput from MI by sixth-power amplification and
   ideal counting, including exact mask averaging and fixed row shell.
4. Derive the actual inverse reciprocal/seed continuation from that independent
   estimate. No SeedBound is included in these inputs.
5. Feed MI/P with the dynamic capacities into zero detection and physical
   probe row estimates; choose real geometry, losses and slots before ψ;
   only then choose target-dependent seminorm/height data and external N.
   The parent skeleton supplies Mellin continuation and family closure.

The ideal-only row model needs an explicit equivalence to the source's
S-unit/sector indexing before it can be instantiated. The current definitions
do not claim that omitting those multiplicities preserves the moment bound.
-/

end HeckeGeneral.Analysis.ConditionalMoments
