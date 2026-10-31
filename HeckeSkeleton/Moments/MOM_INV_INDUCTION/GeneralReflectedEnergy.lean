import HeckeSkeleton.LowEnergy.ActualSeparatedBlock
import HeckeSkeleton.LowEnergy.ActualFrozenCharges
import HeckePort.Moments.Inversion.TerminalWidths

/-!
# The permitted general marked reflected-energy input

This is the fixed-frozen-state form of Lemma 4.8, manuscript lines
2120--2155.  Lines 2144--2148 supply the reflected-block estimate and
the arbitrary-power total tail.  The formula below uses the actual
`reflectedTerm`, its full cube `b=x n'`, and the original fixed completed
scale X.  In particular its kernel has P^2 in the denominator.

The pinned PR #3 source modules provide the exact frozen coordinates,
their masks, minimum-valuation charges, and full-cube reindexing.  Its
`ActualBlockEnergy.actual_block_energy` is the physical normalization
X=Z q_marks; it does not by itself prove this general canonical input.

No canonical margin, short cube-completion assumption, final terminal
power, or source reconstruction identity is a field of the input.
The powerful-row count O/2 and every canonical conductor comparison
are performed by the consumer.  The source equality at the end of
this file is proved from the original coefficient reflection.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.GeneralReflectedEnergy

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.ActualReflection
  HeckeSkeleton.LowEnergy.ActualReflectionReindex
  HeckeSkeleton.LowEnergy.ActualFrozenCharges
  HeckeSkeleton.LowEnergy.ActualFrozenIndependence
  HeckeSkeleton.LowEnergy.ActualHybridEntry
  HeckeSkeleton.LowEnergy.ActualSeparatedBlock
open HeckeSkeleton.LowEnergy.ClassSlices HeckeSkeleton.LowEnergy.ActualClassSlices
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

local notation "Ext" => ExteriorIdeal K S

/-- The actual complete dual cube is retained inside the same row
vector. Every failed original coprimality condition remains a zero. -/
def atom (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (V : ℝ → ℂ) (X : ℝ) (k P c b : Ext) : ℂ :=
  if hk : RowAdmissible K S f k then
    if hP : MarkAdmissible K S f P then
      if hkP : IsCoprime k.val.val P.val.val then
        if hcb : ColumnCondition K S s c b then
          if hPb : IsCoprime P.val.val b.val.val then
            reflectedTerm K S D (sourceDatum K S f k P hk hP hkP)
              (sourceIndex K S f s k P hk hP hkP ⟨(c, b), hcb⟩ hPb) F θ V X
          else 0
        else 0
      else 0
    else 0
  else 0

/-- The block consists of literal reflected terms with one common
completed scale and a row-independent active-mark coefficient. -/
def block (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (a : Ext → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (ps cs bs : Finset Ext) (k : Ext) : ℂ :=
  ∑ P ∈ ps, a P * ∑ c ∈ cs, ∑ b ∈ bs, atom K S D f s F θ V X k P c b

theorem atom_on_source (f : FixedData K S)
    (s : FrozenState K S f.frozen f.puncture)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (V : ℝ → ℂ) (X : ℝ) (k P c b : Ext)
    (hk : RowAdmissible K S f k) (hP : MarkAdmissible K S f P)
    (hkP : IsCoprime k.val.val P.val.val) (hcb : ColumnCondition K S s c b)
    (hPb : IsCoprime P.val.val b.val.val) :
    atom K S D f s F θ V X k P c b =
      reflectedTerm K S D (sourceDatum K S f k P hk hP hkP)
        (sourceIndex K S f s k P hk hP hkP ⟨(c, b), hcb⟩ hPb) F θ V X := by
  simp only [atom, dif_pos hk, dif_pos hP, dif_pos hkP, dif_pos hcb, dif_pos hPb]

/-- A fixed-X canonical atom, before the physical marked-scale
cancellation used by PR #3. This exact identity distinguishes the two
normalizations and preserves both pair-dependent hybrid masks. -/
theorem atom_eq_hybrid (hD : AllowedGeneratorInput K S D)
    (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (V : ℝ → ℂ) (X : ℝ) (k P c b : Ext)
    (hk : RowAdmissible K S f k) (hP : MarkAdmissible K S f P)
    (hkP : IsCoprime k.val.val P.val.val) (hcb : ColumnCondition K S s c b)
    (hPb : IsCoprime P.val.val b.val.val) :
    atom K S D f s F θ V X k P c b =
      inactiveWeight K S f * rowCoefficient K S D θ f s k *
        hybridAtom K S D (markCoefficient K S D θ f s P)
          (commonDualCoefficient K S D θ (baseDatum K S f) s ⟨(c, b), hcb⟩)
          k.val.val P.val.val c.val.val b.val.val *
        mellinReflectionKernel K S F θ (QuotientGroup.mk f.rowUnit)
          (blockFrequency (frozenClass K S D f s) (generatorLocalClass K S D k)
            (generatorLocalClass K S D P) (generatorLocalClass K S D c)
            (generatorLocalClass K S D b)) V 0
          (X * exteriorNorm K S s.minimum * exteriorNorm K S c *
            exteriorNorm K S b ^ 3 /
            (exteriorNorm K S k * exteriorNorm K S (primeSetIdeal K S s.active) *
              exteriorNorm K S P) ^ 2) := by
  rw [atom_on_source K S D f s F θ V X k P c b hk hP hkP hcb hPb,
    reflectedTerm_eq_hybridAtom K S D hD]
  rw [source_inactive K S f s k P hk hP hkP ⟨(c, b), hcb⟩ hPb,
    source_minimum K S f s k P hk hP hkP ⟨(c, b), hcb⟩ hPb,
    source_markedIdeal K S f s k P hk hP hkP ⟨(c, b), hcb⟩ hPb,
    source_fullCube K S f s k P hk hP hkP ⟨(c, b), hcb⟩ hPb,
    ← fullCubeCoefficient_frozenOnly,
    source_coefficient K S D f s k P hk hP hkP ⟨(c, b), hcb⟩ hPb θ,
    source_frequency K S D f s k P hk hP hkP ⟨(c, b), hcb⟩ hPb hD]
  rfl

def logNorm (Z : ℝ) (I : Ext) : ℝ := Real.log (exteriorNorm K S I) / Real.log Z

/-- Every frozen charge is determined by the actual minimum-valuation
ideals of the original reflection index. -/
def threshold (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    (Z Nstar H za : ℝ) : ℝ :=
  2 * H + 2 * logNorm K S Z (primeSetIdeal K S s.active) + 2 * za - Nstar -
    logNorm K S Z (minimumLinearIdeal K S s) -
    3 * logNorm K S Z (minimumCubeIdeal K S s)

/-- E_ref before the positive count of powerful rows is inserted.
It has no canonical deficit or induction margin as an argument. -/
def exponent (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    (Z Nstar H za v ell : ℝ) : ℝ :=
  HeckePort.Moments.reflectedExponent 0 H
    (logNorm K S Z (minimumSmallIdeal K S s))
    (logNorm K S Z (minimumCubeIdeal K S s)) za v ell 0
    (threshold K S f s Z Nstar H za)

def InAnnulus (Z length : ℝ) (I : Ext) : Prop :=
  Z ^ length ≤ exteriorNorm K S I ∧ exteriorNorm K S I ≤ 2 * Z ^ length

/-- Only fixed bounded-length data enter the uniform constants. -/
def BoundedSource (f : FixedData K S) (Z L Nstar H za : ℝ) : Prop :=
  |Nstar| ≤ L ∧ 0 ≤ H ∧ H ≤ L ∧ 0 ≤ za ∧ za ≤ L ∧
    exteriorNorm K S f.frozen ≤ Z ^ L ∧ exteriorNorm K S f.puncture ≤ Z ^ L ∧
    exteriorNorm K S (primeSetIdeal K S f.inactive) ≤ Z ^ L

/-- This is the actual off-threshold full-cube series, rather than a
tail bound attached to an unspecified source. -/
def tail (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (a : Ext → ℂ) (V : ℝ → ℂ) (Z Nstar H za tau : ℝ)
    (ps : Finset Ext) (k : Ext) : ℂ :=
  ∑ P ∈ ps, a P * ∑' cb : Ext × Ext,
    if Z ^ (threshold K S f s Z Nstar H za + tau) <
        exteriorNorm K S cb.1 * exteriorNorm K S cb.2 ^ 3 then
      atom K S D f s F θ V (Z ^ Nstar) k P cb.1 cb.2
    else 0

/-- Lemma 4.8 in its general fixed completed-scale form.

Constants and the finite seminorm order precede all moving rows,
frozen ideals, original coefficients, annular tests, and dyads.
The two fields are only the actual reflected block estimate and its
arbitrary-power tail; there is no canonical moment conclusion. -/
structure Input (F : FiniteMellinData K S)
    (backgrounds : Finset (HeckeCharacter K)) : Prop where
  block_energy : ∀ L lo hi eps : ℝ, 0 < L → 0 < lo → lo ≤ hi → 0 < eps →
    ∃ C Z₀ A : ℝ, ∃ J : ℕ,
      0 < C ∧ 1 < Z₀ ∧ 0 ≤ A ∧
      ∀ (θ : HeckeCharacter K), θ ∈ backgrounds →
      MarkedCoefficientReflectionInput K S D F θ →
      ∀ (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
        (V : SmoothAnnularTest) (Z Nstar H za v ell amp : ℝ),
      Z₀ ≤ Z → BoundedSource K S f Z L Nstar H za →
      0 ≤ v → v ≤ L → 0 ≤ ell → ell ≤ L → 0 ≤ amp →
      Function.support V.toFun ⊆ Set.Icc lo hi →
      ∀ (rows ps cs bs : Finset Ext) (a : Ext → ℂ),
      (∀ k ∈ rows, InAnnulus K S Z H k) →
      (∀ P ∈ ps, InAnnulus K S Z za P) →
      (∀ c ∈ cs, InAnnulus K S Z v c) →
      (∀ b ∈ bs, InAnnulus K S Z ell b) →
      (∀ P ∈ ps, ‖a P‖ ≤ amp) →
      (∑ k ∈ rows, ‖block K S D f s F θ a V.toFun (Z ^ Nstar) ps cs bs k‖ ^ 2) ≤
        C * amp ^ 2 * testSeminorm V.toFun J A ^ 2 * ‖inactiveWeight K S f‖ ^ 2 *
          Z ^ (exponent K S f s Z Nstar H za v ell + eps)
  tail_energy : ∀ L lo hi tau saving : ℝ,
    0 < L → 0 < lo → lo ≤ hi → 0 < tau → 0 < saving →
    ∃ C Z₀ A : ℝ, ∃ J : ℕ,
      0 < C ∧ 1 < Z₀ ∧ 0 ≤ A ∧
      ∀ (θ : HeckeCharacter K), θ ∈ backgrounds →
      MarkedCoefficientReflectionInput K S D F θ →
      ∀ (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
        (V : SmoothAnnularTest) (Z Nstar H za amp : ℝ),
      Z₀ ≤ Z → BoundedSource K S f Z L Nstar H za → 0 ≤ amp →
      Function.support V.toFun ⊆ Set.Icc lo hi →
      ∀ (rows ps : Finset Ext) (a : Ext → ℂ),
      (∀ k ∈ rows, InAnnulus K S Z H k) →
      (∀ P ∈ ps, InAnnulus K S Z za P) →
      (∀ P ∈ ps, ‖a P‖ ≤ amp) →
      (∑ k ∈ rows, ‖tail K S D f s F θ a V.toFun Z Nstar H za tau ps k‖ ^ 2) ≤
        C * amp ^ 2 * testSeminorm V.toFun J A ^ 2 * ‖inactiveWeight K S f‖ ^ 2 *
          Z ^ (-saving)

/-- The source expansion is a theorem, separate from the analytic
energy input. It retains every original active subset and full cube. -/
theorem completed_source_expansion (F : FiniteMellinData K S)
    (θ : HeckeCharacter K) (hreflection : MarkedCoefficientReflectionInput K S D F θ)
    (d : MarkedDatum K S) (V : SmoothAnnularTest) (X : ℝ) (hX : 0 < X) :
    completedThetaSum K S D θ (rowElement K S D d) d.puncture d.marks V.toFun X =
      ∑' s : FrozenState K S d.frozen d.puncture, ∑' A : MarkChoice K S d,
        ∑' cb : FrozenColumn K S s, extendMarkedColumn K S s A.val
          (fun z => reflectedTerm K S D d
            ((reflectionSigmaEquiv K S d).symm ⟨s, A, z⟩) F θ V.toFun X) cb :=
  completedThetaSum_reindexed K S D F θ hreflection d V X hX

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.GeneralReflectedEnergy

end
