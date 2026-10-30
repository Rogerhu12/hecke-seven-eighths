import HeckeGeneral.Analysis.ActualPacketClosure
import HeckeGeneral.Analysis.PrincipalProbeBounded
import HeckeGeneral.Analysis.TInputPrincipal
import HeckeGeneral.Analysis.PhysicalProbeRows
import HeckeGeneral.Analysis.FrequencyRowCounting
import HeckeGeneral.Analysis.PretargetPrimeWindows
import HeckeGeneral.Analysis.PhysicalComparisonAssembly
import HeckeGeneral.Analysis.EndpointRangeSavings
import HeckeGeneral.Analysis.WitnessRowCount

/-!
# The sources T, I and P for one fixed infinity type

The current route is the user-selected 11 October revised manuscript, Sections 4--8.
References to M below identify the legacy tex source of this interface. The small-row
margin is now 1/50, matching revised (7.31); all actual source estimates remain to be proved.

M Proposition 3.1 names three source consequences T, I and P.  This module
states them for the actual packet `HeckePacket K ω`, the actual normalized
compensated probe `normalizedProbe` and the actual height-free principal
signal `principalLineProbe`.  The closure (`TIPAccounting`, `TIPClosure`)
derives the row counts by Markov counting of saturated witnesses, the
short/long crossing with the dynamic capacity, the certificate and range
margins, the pretarget saving, height removal and the Mellin family closure.

Direct route.  The closure starts from the Euler-product bound: the common
boundary ranges over `7/8 < B ≤ 1`, and no separate `11/12` theorem is used.
Q's closure (Section 20) runs inside Part II, where `0 < B - 7/8 ≤ 1/24` and
every retained bin has `δ ≤ κ ≤ 5/6`.  T, I and P are required here for every
`7/8 < B ≤ 1` and for bins up to `δ ≤ 1`.  Several ingredients have source
statements without the Part II ceiling:
* Q Proposition 8.3 (`prop:detector-witness`) needs only `a > 51/100`;
* Q Lemma 18.1 (`lem:plain`, the paired fourth moment) holds for
  `3/4 ≤ κ ≤ 1`, and so does its transfer M Proposition A.1;
* Q Remark 19.3 allows the unselected inverse count for `1/50 < δ ≤ 1`.

The actual extended-range expansion and high-bin transfer remain obligations;
Q's high-bin application itself still uses the Part II ceiling.

What T, I and P contain.

* T (`TSource`): the primitive principal inputs (`TPrincipalInput`, including
  the low estimate (6.9) for the actual probe; analyticity, convergence and
  non-vanishing of the principal correction are theorems of
  `PrincipalEulerFactor`, not inputs); at every analysis height `T₁ = Z^τ`
  the exact decomposition of `probe - signal` into the principal remainder,
  small rows, large rows, finitely many moderate dyadic/bin blocks and an
  external tail, with the source exponents of M Table 7.3; the detector output
  of Q `prop:detector-witness` (saturated inverse and plain witnesses on a
  covering by witness subdivisions); the amplitude lower bounds of Q 19.1; and
  the single-bin estimate of Q Lemma 20.1 (`lem:high-bin`), stated
  CONDITIONALLY on row counts with exponents in a fixed bounded range.  T
  contains no improved or derived row count: the floor-bin count
  is derived from `TargetData.rows_in_norm_envelope` and actual ideal counting.
  Its remaining count inputs are multiplicities: the numbers of moderate
  blocks and of witness subdivisions.
* I (`ISource`): the marked inverse moment with selected slots at strict widths
  and the amplified no-slot inverse moment, for the SAME witness and slot values.
* P (`PSource`): the paired fourth moment at the dynamic capacity
  `κ = 2B - 1 ≤ 1`, with its slot mesh, and its zero-slot case.

The sources are required for one REPRESENTATIVE of each packet member with the
same zero real parts (M 7.5: remove the global norm twist and choose the
conjugate satisfying the angular condition).

Analysis heights.  Q's detector, witness and single-bin estimates hold at
`T₁ = Z^τ` for fixed `τ > 0`, with thresholds depending on `τ`; the height
degree and the ceiling precede `τ`.

Scope.  `ProbeData` contains `ThetaArithmeticData`, which needs a primitive
twelfth root of unity in `K`; the theorems are therefore informative only for
`μ₁₂ ⊆ K`.  General fields go through `K = F(ζ₁₂)` and abelian descent; that
descent is not constructed here (`HeckeFactorizationDescentData` states the
data it needs).

The pretarget saving uses the fixed certificate margin `49/440640`.
Instantiating these sources by the actual Poisson expansion, contour moves and
canonical moments is the remaining source transfer.
-/

noncomputable section
namespace HeckeGeneral.ThetaSkeleton.TIP

open NumberField IsDedekindDomain MeasureTheory Filter Asymptotics
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open scoped BigOperators Topology Classical

/-- The fixed margin of the endpoint certificate, M (7.6) and Q `lem:balanced-endpoint`. -/
def certificateMargin : ℝ := 49 / 440640

/-- Rows with one presentation label and one dyadic witness pair. -/
structure WitnessSubdivision (Row : Type) where
  rows : Finset Row
  inverseLength : ℝ
  plainLength : ℝ
  inverseValue : Row → ℂ
  plainValue : Row → ℂ

/-- One amplitude set of a moderate block at one retained tuple (Q 15064--15092).
For every witness parameter `t` it carries a finite witness subdivision. -/
structure AmplitudeSet (Row : Type) (J₀ : ℕ) where
  rows : Finset Row
  amplitude : Fin J₀ → ℝ
  slotValue : Fin J₀ → Row → ℂ
  subdivisionCount : ℝ → ℕ
  subdivision : (t : ℝ) → Fin (subdivisionCount t) → WitnessSubdivision Row

/-- The length-weighted mean amplitude for the uniform pretarget slot system. -/
def AmplitudeSet.mean {Row : Type} {J₀ : ℕ} (A : AmplitudeSet Row J₀) : ℝ :=
  (∑ i, A.amplitude i) / J₀

/-- One dyadic row shell `U = Z^shell` and one buffered bin `a = bin`.
The labels are the pointwise amplitude sets occurring in the block. -/
structure ModerateBlock (Row : Type) (J₀ : ℕ) : Type 1 where
  shell : ℝ
  bin : ℝ
  value : ℂ
  Label : Type
  amplitudeSet : Label → AmplitudeSet Row J₀

/-- The retained high expansion at one scale and one analysis height. -/
structure HighExpansion (Row : Type) (J₀ : ℕ) : Type 1 where
  principal : ℂ
  small : ℂ
  large : ℂ
  tail : ℂ
  blockCount : ℕ
  block : Fin blockCount → ModerateBlock Row J₀

/-- Slot length at base `Z^d` for slots of length `(1/6)/J₀` at base `Z`. -/
def slotLength (J₀ : ℕ) (d : ℝ) : ℝ := (1 / 6) / (J₀ * d)

variable (K : Type) [Field K] [NumberField K]

/-- Borel structures and additive Haar measures used by the actual probe. -/
structure ProbeMeasures (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S] where
  normOneSpace : MeasurableSpace (sLocalNormOneGroup K S)
  normOneBorel : @BorelSpace (sLocalNormOneGroup K S) inferInstance normOneSpace
  localSpace : (p : S) → MeasurableSpace (p.val.adicCompletion K)
  localBorel : ∀ p : S, @BorelSpace (p.val.adicCompletion K) inferInstance (localSpace p)
  haar : (p : S) → @Measure (p.val.adicCompletion K) (localSpace p)
  haar_isAddHaar : ∀ p : S, letI := localSpace p; (haar p).IsAddHaarMeasure

namespace ProbeMeasures

variable {K} {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]

/-- The actual normalized compensated probe for these measure data. -/
def probe (M : ProbeMeasures K S) (P : ProbeData K S) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) : ℝ → ℂ :=
  letI := M.normOneSpace
  haveI := M.normOneBorel
  letI := M.localSpace
  normalizedProbe K S M.haar P ψ g T

/-- The primitive principal/low part of T for these measure data. -/
def principalInput (M : ProbeMeasures K S) (P : ProbeData K S) (ψ : HeckeCharacter K)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K)) : Prop :=
  letI := M.normOneSpace
  haveI := M.normOneBorel
  letI := M.localSpace
  TPrincipalInput K S M.haar P ψ g T

end ProbeMeasures

/-- Posttarget arithmetic and analytic data supplied by the source for one
target: the final excluded set, probe data, measures, ray filter and the
retained high expansion at every scale and analysis height. -/
structure TargetData (g : PrimeWindowGeometry) : Type 1 where
  S : Finset (HeightOneSpectrum (𝓞 K))
  probe : ProbeData K (S : Set (HeightOneSpectrum (𝓞 K)))
  measures : ProbeMeasures K (S : Set (HeightOneSpectrum (𝓞 K)))
  rayFilter : Finset (HeckeCharacter K)
  expansion : ℝ → ℝ → HighExpansion (FrequencyRow K (S : Set (HeightOneSpectrum (𝓞 K)))) g.slots
  /-- Actual amplitude rows satisfy the displayed norm upper bound. This is a
  support property, not a supplied cardinality estimate. -/
  rows_in_norm_envelope : ∀ Z T₁ : ℝ, 1 ≤ Z → 1 ≤ T₁ →
    ∀ b : Fin (expansion Z T₁).blockCount, ∀ ℓ : ((expansion Z T₁).block b).Label,
      (((expansion Z T₁).block b).amplitudeSet ℓ).rows ⊆
        frequencyRows K (S : Set (HeightOneSpectrum (𝓞 K)))
          (2 * Z ^ ((expansion Z T₁).block b).shell)

namespace TargetData

variable {K} {g : PrimeWindowGeometry}

/-- The actual normalized physical probe `J_ψ` of M (6.8). -/
def probeFunction (D : TargetData K g) (ψ : HeckeCharacter K) : ℝ → ℂ :=
  D.measures.probe D.probe ψ g D.rayFilter

/-- The actual height-free principal signal `f_ψ` of M (6.8). -/
def signal (D : TargetData K g) (ψ : HeckeCharacter K) : ℝ → ℂ :=
  principalLineProbe K (D.S : Set (HeightOneSpectrum (𝓞 K))) D.probe ψ

end TargetData

variable {K}

/-- Q Proposition 8.3 at witness parameter `t`: a finite covering of the
amplitude set by subdivisions with saturated inverse and plain witnesses. -/
def WitnessCover {Row : Type} {J₀ : ℕ} (A : AmplitudeSet Row J₀)
    (t δ U lam k : ℝ) : Prop :=
  ((A.subdivisionCount t : ℝ) ≤ k * U ^ lam) ∧
  (∀ u ∈ A.rows, ∃ j, u ∈ (A.subdivision t j).rows) ∧
  ∀ j, (A.subdivision t j).rows ⊆ A.rows ∧
    0 ≤ (A.subdivision t j).inverseLength ∧ 0 ≤ (A.subdivision t j).plainLength ∧
    (A.subdivision t j).inverseLength ≤ t + lam ∧
    t - lam ≤ (A.subdivision t j).inverseLength + (A.subdivision t j).plainLength ∧
    (∀ u ∈ (A.subdivision t j).rows,
      U ^ (δ * (A.subdivision t j).inverseLength - lam) ≤
        ‖(A.subdivision t j).inverseValue u‖ ^ 2) ∧
    (∀ u ∈ (A.subdivision t j).rows,
      U ^ (δ * (A.subdivision t j).plainLength - lam) ≤
        ‖(A.subdivision t j).plainValue u‖ ^ 2)

/-- Structural part of T for one moderate block at scale `Z`: shell and bin
ranges, amplitude bounds (Q 15064--15092), and the
witness covers of Q Proposition 8.3 above the floor. -/
def BlockSource {Row : Type} (g : PrimeWindowGeometry) (b : ModerateBlock Row g.slots)
    (B lam k Z : ℝ) : Prop :=
  1 / 100 ≤ b.shell ∧ b.shell ≤ 13 / 16 + lam ∧ 51 / 100 ≤ b.bin ∧ b.bin ≤ B ∧
  ∀ ℓ : b.Label,
    (∀ i, 0 ≤ (b.amplitudeSet ℓ).amplitude i ∧
      (b.amplitudeSet ℓ).amplitude i ≤ (2 * b.bin - 1) / 2) ∧
    (∀ i, 0 < (b.amplitudeSet ℓ).amplitude i → ∀ u ∈ (b.amplitudeSet ℓ).rows,
      Z ^ ((1 / 6) / g.slots * (b.amplitudeSet ℓ).amplitude i) ≤
        ‖(b.amplitudeSet ℓ).slotValue i u‖) ∧
    (51 / 100 < b.bin → ∀ t : ℝ, 1 ≤ t → t ≤ 3 / 2 →
      WitnessCover (b.amplitudeSet ℓ) t (2 * b.bin - 1) (Z ^ b.shell) lam k)

/-- Increasing a witness-cover constant preserves the same subdivisions. -/
theorem WitnessCover.mono {Row : Type} {J₀ : ℕ} {A : AmplitudeSet Row J₀}
    {t δ U lam k k' : ℝ} (h : WitnessCover A t δ U lam k)
    (hU : 0 ≤ U) (hkk : k ≤ k') : WitnessCover A t δ U lam k' := by
  exact ⟨h.1.trans (mul_le_mul_of_nonneg_right hkk (Real.rpow_nonneg hU _)), h.2⟩

/-- Only the subdivision-count constant grows; the actual values and rows stay fixed. -/
theorem BlockSource.mono {Row : Type} {g : PrimeWindowGeometry}
    {b : ModerateBlock Row g.slots} {B lam k k' Z : ℝ}
    (h : BlockSource g b B lam k Z) (hZ : 0 ≤ Z) (hkk : k ≤ k') :
    BlockSource g b B lam k' Z := by
  obtain ⟨hd, hd', hb, hb', hl⟩ := h
  refine ⟨hd, hd', hb, hb', fun ℓ => ⟨(hl ℓ).1, (hl ℓ).2.1, ?_⟩⟩
  intro hbin t ht ht'
  exact ((hl ℓ).2.2 hbin t ht ht').mono (Real.rpow_nonneg hZ _) hkk

/-- T at one scale and analysis height: the exact high decomposition and the
source exponents of M Table 7.3 relative to `C(B) = B - 11/16`. -/
def ExpansionSource (g : PrimeWindowGeometry) (ψ : HeckeCharacter K) (D : TargetData K g)
    (B lamA lamB k A Z T₁ : ℝ) : Prop :=
  D.probeFunction ψ Z - D.signal ψ Z =
      (D.expansion Z T₁).principal + (D.expansion Z T₁).small + (D.expansion Z T₁).large +
        (∑ b, ((D.expansion Z T₁).block b).value) + (D.expansion Z T₁).tail ∧
  ‖(D.expansion Z T₁).principal‖ ≤
      k * (Z ^ (B - 11 / 16 - 23 / 960 + lamB) + Z ^ (B - 11 / 16 - 13 / 9600 + lamB) +
        Z ^ (B - 11 / 16 - principalSlotSaving g + lamB)) * (1 + T₁) ^ A ∧
  ‖(D.expansion Z T₁).small‖ ≤ k * Z ^ (B - 11 / 16 - 1 / 50 + lamB) * (1 + T₁) ^ A ∧
  ‖(D.expansion Z T₁).large‖ ≤ k * Z ^ (B - 11 / 16 - 63 / 800 + lamB) * (1 + T₁) ^ A ∧
  ((D.expansion Z T₁).blockCount : ℝ) ≤ k * Z ^ lamB ∧
  ∀ b, BlockSource g ((D.expansion Z T₁).block b) B lamA k Z

/-- A common larger source constant can also absorb the proved arithmetic
row-count constant. No exponent, height degree, or threshold changes. -/
theorem ExpansionSource.mono {g : PrimeWindowGeometry} {ψ : HeckeCharacter K}
    {D : TargetData K g} {B lamA lamB k k' A Z T₁ : ℝ}
    (h : ExpansionSource g ψ D B lamA lamB k A Z T₁)
    (hZ : 0 ≤ Z) (hT : 0 ≤ 1 + T₁) (hkk : k ≤ k') :
    ExpansionSource g ψ D B lamA lamB k' A Z T₁ := by
  obtain ⟨heq, hp, hs, hl, hn, hb⟩ := h
  refine ⟨heq, hp.trans ?_, hs.trans ?_, hl.trans ?_, hn.trans ?_, fun b => ?_⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hkk (by positivity)) (Real.rpow_nonneg hT _)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hkk (Real.rpow_nonneg hZ _)) (Real.rpow_nonneg hT _)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hkk (Real.rpow_nonneg hZ _)) (Real.rpow_nonneg hT _)
  · exact mul_le_mul_of_nonneg_right hkk (Real.rpow_nonneg hZ _)
  · exact (hb b).mono hZ hkk

/-- The source T of M Proposition 3.1 for one target and common boundary B. -/
structure TSource (g : PrimeWindowGeometry) (ψ : HeckeCharacter K) (D : TargetData K g)
    (B lamA lamB : ℝ) : Prop where
  principal : D.measures.principalInput D.probe ψ g D.rayFilter
  /-- The high expansion at analysis heights `T₁ = Z^τ`: the height degree and
  ceiling precede `τ`; the constant and threshold may depend on `τ`. -/
  expansion : ∃ A ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
    ∀ τ : ℝ, 0 < τ → τ ≤ ceiling → ∃ Z₀ k : ℝ, 2 ≤ Z₀ ∧ 0 ≤ k ∧
      ∀ Z : ℝ, Z₀ ≤ Z → ExpansionSource g ψ D B lamA lamB k A Z (Z ^ τ)
  tail : PowerHeightTailBound (fun Z T₁ => (D.expansion Z T₁).tail)
  /-- Q Lemma 20.1 (`lem:high-bin`), conditional on counts for every amplitude set of the
  block, for count exponents in the fixed pretarget range `0 ≤ R ≤ 2`.  The
  count height order `Ac` precedes `τ`; the count constant `kc` may depend on
  `τ`. -/
  highBin : ∀ Ac : ℝ, 0 ≤ Ac → ∃ A' ceiling : ℝ, 0 ≤ A' ∧ 0 < ceiling ∧
    ∀ τ : ℝ, 0 < τ → τ ≤ ceiling → ∀ kc : ℝ, 0 ≤ kc → ∃ k' Z₀ : ℝ, 0 ≤ k' ∧ 1 ≤ Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ b : Fin (D.expansion Z (Z ^ τ)).blockCount,
      ∀ R : ((D.expansion Z (Z ^ τ)).block b).Label → ℝ, ∀ Ebar : ℝ,
        (∀ ℓ, 0 ≤ R ℓ ∧ R ℓ ≤ 2) →
        (∀ ℓ, ((((D.expansion Z (Z ^ τ)).block b).amplitudeSet ℓ).rows.card : ℝ) ≤
          kc * (Z ^ ((D.expansion Z (Z ^ τ)).block b).shell) ^ (R ℓ + lamA) *
            (1 + Z ^ τ) ^ Ac) →
        (∀ ℓ, moderateExponent ((D.expansion Z (Z ^ τ)).block b).shell
          (2 * ((D.expansion Z (Z ^ τ)).block b).bin - 1)
          (((D.expansion Z (Z ^ τ)).block b).amplitudeSet ℓ).mean (R ℓ) ≤ Ebar) →
        ‖((D.expansion Z (Z ^ τ)).block b).value‖ ≤
          k' * Z ^ (3 / 16 + Ebar + lamA + lamB) * (1 + Z ^ τ) ^ A'

/-- I for one block: the marked inverse moment with selected slots at strict
widths and the amplified no-slot inverse moment, for the witness values. -/
def InverseBlockSource {Row : Type} (g : PrimeWindowGeometry) (b : ModerateBlock Row g.slots)
    (lam k A Z T₁ : ℝ) : Prop :=
  51 / 100 < b.bin → ∀ ℓ : b.Label, ∀ t : ℝ, 1 ≤ t → t ≤ 3 / 2 →
    ∀ j : Fin ((b.amplitudeSet ℓ).subdivisionCount t),
      (∀ I : Finset (Fin g.slots),
        ((b.amplitudeSet ℓ).subdivision t j).inverseLength +
            2 * ∑ _i ∈ I, slotLength g.slots b.shell ≤ 1 - 2 * lam →
        2 * ((b.amplitudeSet ℓ).subdivision t j).inverseLength +
            8 * ∑ _i ∈ I, slotLength g.slots b.shell ≤ 3 - 2 * lam →
        ∑ u ∈ ((b.amplitudeSet ℓ).subdivision t j).rows,
            ‖((b.amplitudeSet ℓ).subdivision t j).inverseValue u *
              ∏ i ∈ I, (b.amplitudeSet ℓ).slotValue i u‖ ^ 2 ≤
          k * (Z ^ b.shell) ^ (1 + lam) * (1 + T₁) ^ A) ∧
      ∑ u ∈ ((b.amplitudeSet ℓ).subdivision t j).rows,
          ‖((b.amplitudeSet ℓ).subdivision t j).inverseValue u‖ ^ 2 ≤
        k * (Z ^ b.shell) ^
          (amplifiedInverseExponent ((b.amplitudeSet ℓ).subdivision t j).inverseLength + lam) *
          (1 + T₁) ^ A

/-- P for one block: the paired fourth moment at the dynamic capacity
`κ = 2B - 1` on mesh-fine selected slots, and its zero-slot case. -/
def PlainBlockSource {Row : Type} (g : PrimeWindowGeometry) (b : ModerateBlock Row g.slots)
    (B lam mesh k A Z T₁ : ℝ) : Prop :=
  51 / 100 < b.bin → ∀ ℓ : b.Label, ∀ t : ℝ, 1 ≤ t → t ≤ 3 / 2 →
    ∀ j : Fin ((b.amplitudeSet ℓ).subdivisionCount t),
      (∀ I : Finset (Fin g.slots), (∀ _i ∈ I, slotLength g.slots b.shell ≤ mesh) →
        2 * ((b.amplitudeSet ℓ).subdivision t j).plainLength +
            6 * (2 * B - 1) * ∑ _i ∈ I, slotLength g.slots b.shell ≤ 1 →
        ∑ u ∈ ((b.amplitudeSet ℓ).subdivision t j).rows,
            ‖((b.amplitudeSet ℓ).subdivision t j).plainValue u ^ 2 *
              ∏ i ∈ I, (b.amplitudeSet ℓ).slotValue i u‖ ^ 2 ≤
          k * (Z ^ b.shell) ^ (1 + lam) * (1 + T₁) ^ A) ∧
      ∑ u ∈ ((b.amplitudeSet ℓ).subdivision t j).rows,
          ‖((b.amplitudeSet ℓ).subdivision t j).plainValue u ^ 2‖ ^ 2 ≤
        k * (Z ^ b.shell) ^ (1 + lam) * (1 + T₁) ^ A

/-- The source I of M Proposition 3.1 on the witness families of `D`. -/
def ISource (g : PrimeWindowGeometry) (D : TargetData K g) (lam : ℝ) : Prop :=
  ∃ A ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
    ∀ τ : ℝ, 0 < τ → τ ≤ ceiling → ∃ Z₀ k : ℝ, 1 ≤ Z₀ ∧ 0 ≤ k ∧
      ∀ Z : ℝ, Z₀ ≤ Z →
        ∀ b, InverseBlockSource g ((D.expansion Z (Z ^ τ)).block b) lam k A Z (Z ^ τ)

/-- The source P of M Proposition 3.1 on the witness families of `D`. -/
def PSource (g : PrimeWindowGeometry) (D : TargetData K g) (B lam mesh : ℝ) : Prop :=
  ∃ A ceiling : ℝ, 0 ≤ A ∧ 0 < ceiling ∧
    ∀ τ : ℝ, 0 < τ → τ ≤ ceiling → ∃ Z₀ k : ℝ, 1 ≤ Z₀ ∧ 0 ≤ k ∧
      ∀ Z : ℝ, Z₀ ≤ Z →
        ∀ b, PlainBlockSource g ((D.expansion Z (Z ^ τ)).block b) B lam mesh k A Z (Z ^ τ)

variable (K)

/-- T, I and P for the fixed family at every common boundary `7/8 < B ≤ 1`, with
the source order of choices: losses, then P's mesh, then the slot system, then
the remaining losses, and only then the target, a representative with the same
zero real parts, and its data. -/
def TIPInput (ω : HeckeCharacter K) : Prop :=
  ∀ B : ℝ, 7 / 8 < B → B ≤ 1 →
    (∀ χ : HeckePacketIndex K ω, ∀ r ∈ heckePacketZeros K ω χ, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) →
    ∀ lamA : ℝ, 0 < lamA → lamA ≤ 1 / 1000 →
    ∃ mesh : ℝ, 0 < mesh ∧
    ∀ g : PrimeWindowGeometry, (1 / 3 : ℝ) / g.slots ≤ mesh →
    ∀ lamB : ℝ, 0 < lamB →
    ∀ χ : HeckePacketIndex K ω, ∃ χ' : HeckePacketIndex K ω,
      heckePacketZeros K ω χ' = heckePacketZeros K ω χ ∧
      ∃ D : TargetData K g,
        TSource g χ'.val D B lamA lamB ∧ ISource g D lamA ∧ PSource g D B lamA mesh

variable {K}

/-- The pretarget saving: a fixed fraction of the certificate margin and of
the principal slot margin. It does not depend on the target or on `B`. -/
def tipSaving (g : PrimeWindowGeometry) : ℝ :=
  (1 / 8) * min certificateMargin (principalSlotSaving g)

/-- The saving used against a common boundary `B`, capped by `(B - 7/8)/4`. -/
def tipFinalSaving (g : PrimeWindowGeometry) (B : ℝ) : ℝ :=
  min (tipSaving g) ((B - 7 / 8) / 4)

/-- The floor bin, including the fixed extension above `h = 13/16`. -/
theorem floor_bin_saving_extended {d q R ζ : ℝ} (hd : 0 ≤ d) (hdhi : d ≤ 13 / 16 + ζ)
    (hζ : 0 ≤ ζ) (hq : q ≤ 1 / 100) (hR : R ≤ 1) :
    moderateExponent d (1 / 50) q R ≤ -(7 / 1200) + ζ := by
  -- Raise the count to `R = 1`; the remaining slope in `d` is `67/100 ≤ 1`.
  have hc := moderateExponent_mono_count hd hR (δ := 1 / 50) (q := q)
  unfold moderateExponent at *
  nlinarith only [hc, hdhi, hq, hζ]

/-- Zeros of the actual continuation have real part at most one. -/
theorem heckePacketZeros_le_one (ω : HeckeCharacter K) (χ : HeckePacketIndex K ω) {r : ℝ}
    (hr : r ∈ heckePacketZeros K ω χ) : r ≤ 1 := by
  -- On `Re s > 1` the continuation is the convergent Euler product: order zero.
  obtain ⟨z, hzr, hzero⟩ := hr
  apply le_of_not_gt
  intro hgt
  have hre : 1 < z.re := by rw [hzr]; exact hgt
  rw [meromorphicOrderAt_heckeContinuation K χ.val hre] at hzero
  exact lt_irrefl _ hzero

/-- The packet closure from the Euler-product bound, for representatives with the
same zero real parts, a common saving chosen before the target, power-height
comparisons, and NO hypothesis on the principal correction. -/
theorem heckePacket_sevenEighths_of_representativeComparisons (ω : HeckeCharacter K)
    (hcompare : ∀ B : ℝ, 7 / 8 < B → B ≤ 1 →
      (∀ χ : HeckePacketIndex K ω, ∀ r ∈ heckePacketZeros K ω χ, 1 / 2 ≤ r → r ≤ 1 → r ≤ B) →
      ∃ σ : ℝ, 0 < σ ∧ σ < (B - 7 / 8) / 2 ∧ ∀ χ : HeckePacketIndex K ω,
        ∃ χ' : HeckePacketIndex K ω, heckePacketZeros K ω χ' = heckePacketZeros K ω χ ∧
        ∃ (S : Finset (HeightOneSpectrum (𝓞 K)))
          (P : ProbeData K (S : Set (HeightOneSpectrum (𝓞 K)))) (J : ℝ → ℂ),
          (∀ ε : ℝ, 0 < ε → J =O[atTop] (fun Z : ℝ => Z ^ (3 / 16 + ε))) ∧
          PowerHeightComparison J (principalLineProbe K S P χ'.val) (B - 11 / 16) σ)
    (χ : HeckePacketIndex K ω) :
    MeromorphicZeroFreeOn (heckeContinuation K χ.val) (rightHalfPlane (7 / 8)) := by
  -- The common boundary `B` is at most one: zeros have real part `≤ 1`.
  have hB1 : familySupremum (heckePacketZeros K ω) ≤ 1 :=
    familySupremum_le_of_common_bound _ (by norm_num) (fun _ _ _ _ hhi => hhi)
  -- A boundary above `7/8` would be strictly improved at a common saving.
  have hB : familySupremum (heckePacketZeros K ω) ≤ 7 / 8 := by
    by_contra hnot
    have hlo : 7 / 8 < familySupremum (heckePacketZeros K ω) := lt_of_not_ge hnot
    obtain ⟨σ, hσ, hσsmall, htarget⟩ := hcompare (familySupremum (heckePacketZeros K ω)) hlo hB1
      (fun _ _ hr hrlo hrhi => zero_le_familySupremum _ hr hrlo hrhi)
    have hbaseline : 1 / 2 ≤ familySupremum (heckePacketZeros K ω) - σ / 2 := by linarith
    have hwitness : familySupremum (heckePacketZeros K ω) - σ / 2 <
        familySupremum (heckePacketZeros K ω) := by linarith
    obtain ⟨ψ, r, hr, _hrlo, _hrhi, hnear⟩ :=
      exists_family_zero_above _ hbaseline hwitness
    -- The representative has the same zero real parts and is zero-free past `B - σ`.
    obtain ⟨ψ', hψ', S, P, J, hlow, hhigh⟩ := htarget ψ
    have hfree := principal_zeroFree_of_powerHeightComparison_closedForm K S P ψ'.val J
      hB1 hσ hσsmall hlow hhigh
    have hr' : r ∈ heckePacketZeros K ω ψ' := by rw [hψ']; exact hr
    obtain ⟨z, hzr, hzero⟩ := hr'
    have hz : z ∈ rightHalfPlane (familySupremum (heckePacketZeros K ω) - σ) := by
      change familySupremum (heckePacketZeros K ω) - σ < z.re
      rw [hzr]
      linarith
    exact (not_lt_of_ge (hfree.2 z hz)) hzero
  -- Every zero with real part in `(7/8, 1]` lies below the boundary.
  refine ⟨fun z _ => meromorphicOn_heckeContinuation K χ.val z (Set.mem_univ _), ?_⟩
  intro z hz
  apply le_of_not_gt
  intro hzero
  have hz' : 7 / 8 < z.re := hz
  have hmem : z.re ∈ heckePacketZeros K ω χ := ⟨z, rfl, hzero⟩
  have hcommon := zero_le_familySupremum _ hmem (by linarith)
    (heckePacketZeros_le_one ω χ hmem)
  linarith

end HeckeGeneral.ThetaSkeleton.TIP
