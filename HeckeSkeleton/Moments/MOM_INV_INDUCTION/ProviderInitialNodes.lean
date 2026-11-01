import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialBoxes
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialInverse
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderNodes
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalChildClosure

/-!
# Actual initial packets enter the canonical induction class

The packet, rows, labels, frozen puncture and centered column family
below are constructed from the literal first inverse Poisson source.
Their bounds are consequences of membership in its actual three norm
boxes. The original strict source inequalities imply both canonical
margins, including all fixed smooth partition shifts. No initial energy
bound is included in the source conditions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

universe u

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialNodes

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep HeckeSkeleton.Moments.MOM_INV_STEP
open FixedTripleFibers FixedTripleEnergy CanonicalChildren CanonicalNormPools
open ProviderNodes
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable {σ : Type u} [DecidableEq σ]
variable (C : CanonicalBlock.ColumnData K S σ)
variable (Θ : Subgroup (HeckeCharacter K)) (ψ : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ C.background)
variable (W : SchwartzMap ℝ ℂ) (G : HeckeCharacter K) (hG : G ∈ Θ)
variable (hbase : 1 < C.base)
variable (H : ProviderInitialSource.Cutoff K S)
variable (J : Finset σ)
variable (hprime : ∀ i ∈ J, ∀ p ∈ C.primeLists i, Prime p)
variable (slotCap : ℕ) (hcap : J.card ≤ slotCap)
local notation "X" => C.base ^ C.length
local notation "Idx" => ProviderInitialSource.Index K S D Γ X H
variable (P : Finset (ProviderInitialSource.Index K S D Γ (C.base ^ C.length) H))
  (b : SecondMobiusGeometry.Index (C.base ^ C.length))
variable (A : ℝ) (j : ProviderInitialBoxes.BoxIndex C.base A)
local notation "Pbox" => ProviderInitialBoxes.boxed K S D Γ X H P b C.base A j
local notation "packet" => ProviderInitialSource.packet K S D Γ X H J C.primeLists
  hprime slotCap hcap Pbox
local notation "glen" => ProviderInitialBoxes.length C.base j 0
local notation "dlen" => ProviderInitialBoxes.length C.base j 1
local notation "vlen" => ProviderInitialBoxes.length C.base j 2
local notation "U" => SecondMobiusGeometry.childScale X b

/-- The common final Mellin profile is attached to the actual first
inverse production family. All original arithmetic metadata survive. -/
def wideFamily (t : ℝ) : ColumnFamily K Sset σ Θ ψ :=
  SecondCenteredFamily.family K S (ProviderInitialInverse.family K S C Θ ψ hν W)
    (ProviderInitialInverse.unitTriple K) G hG J U t

def pieceFamily (t : ℝ) (a : CanonicalChildClosure.Index) : ColumnFamily K Sset σ Θ ψ :=
  CanonicalChildClosure.pieceFamily K Sset (wideFamily K S C Θ ψ hν W G hG J b t)
    hbase a

def nodeAt (m h tau : ℝ) (markLengths : σ → ℝ) (t : ℝ)
    (gamma : OuterTriple K) (a : CanonicalChildClosure.Index) : Node K S Γ Θ ψ σ where
  family := pieceFamily K S C Θ ψ hν W G hG hbase J b t a
  triple := gamma
  labels := packet.labels
  rows := packet.rows
  rowLength := ProviderInitialGeometry.rowLength m C.length glen dlen h tau
  labelLength := ProviderInitialGeometry.labelLength dlen vlen h
  markLengths := markLengths

theorem wide_length (t : ℝ) (gamma : OuterTriple K) :
    (wideFamily K S C Θ ψ hν W G hG J b t).columnLength gamma = Real.logb C.base U := rfl

include hbase in
theorem wide_complete (t : ℝ) (gamma : OuterTriple K) :
    (wideFamily K S C Θ ψ hν W G hG J b t).columns gamma =
      squarefreePool K Sset
        (2 * C.base ^ (wideFamily K S C Θ ψ hν W G hG J b t).columnLength gamma) := by
  dsimp only [wideFamily, SecondCenteredFamily.family, ProviderInitialInverse.family]
  rw [FirstCompleteFamily.norm_scale C.base U hbase
    (SecondMobiusGeometry.childScale_pos X (Real.rpow_pos_of_pos (zero_lt_one.trans hbase) _) b)]

theorem wide_support (t : ℝ) (gamma : OuterTriple K) :
    tsupport ((wideFamily K S C Θ ψ hν W G hG J b t).cutoff gamma) ⊆
      Set.Icc (1 / 128 : ℝ) 4 := by
  intro y hy
  have hb := FinalMellinTests.weightedTest_support 0 t hy
  exact ⟨hb.1, by linarith [hb.2]⟩

theorem live_of_member (i : Idx) (hi : i ∈ Pbox) : 1 ≤ 4 * U := by
  have hbin : ProviderInitialBoxes.binIndex K S D Γ X H i = b :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
  have hb := (SecondMobiusGeometry.centerIndex_bounds K S X i.1.val i.2.2.2).1
  change DyadicSourcePartition.center (ProviderInitialBoxes.binIndex K S D Γ X H i).val ≤ _ at hb
  rw [hbin] at hb
  have hp := (SecondMobiusGeometry.product_bounds K S X i.1.val i.2.2.2).2
  unfold SecondMobiusGeometry.childScale
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (DyadicSourcePartition.center_pos b.val)).mpr
  linarith

variable (h : ℝ) (hh : 0 ≤ h) (hwidth : 2 ≤ C.base ^ h)
variable (hboxCap : 4 * C.base ^ C.length ≤ C.base ^ A)

include hbase hh hwidth hboxCap in
theorem packet_label_bound (f : Ideal (𝓞 K)) (hf : f ∈ packet.labels) :
    (f.absNorm : ℝ) ≤ C.base ^ ProviderInitialGeometry.labelLength dlen vlen h := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hf
  exact ProviderInitialBoxes.label_norm K S D Γ X H P b C.base A h hbase hh hwidth
    hboxCap j i (Finset.mem_filter.mp hi).1

include hbase hh hwidth hboxCap in
theorem packet_row_bound (rho : {r : ℝ // 0 < r}) (m tau : ℝ)
    (hrho : rho.val ≤ C.base ^ (-m))
    (hcutoff : H = SecondAdaptiveCutoff.fineCutoff K S rho X C.base tau)
    (r : Ideal (𝓞 K) × Sector) (hr : r ∈ packet.rows) :
    (r.1.absNorm : ℝ) ≤ C.base ^ ProviderInitialGeometry.rowLength m C.length glen dlen h tau := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
  exact ProviderInitialBoxes.row_norm K S D Γ X H P b C.base A h hbase hh hwidth
    hboxCap j rho m C.length tau rfl hrho hcutoff i (Finset.mem_filter.mp hi).1

include hbase hh hwidth hboxCap in
/-- The actual frozen puncture costs the one common residual only. -/
theorem puncture_length (Q : ℝ) (hRho : C.puncture ≠ 0)
    (hRhoNorm : (C.puncture.radical.absNorm : ℝ) ≤ C.base ^ Q)
    (i : Idx) (hi : i ∈ Pbox) :
    Real.logb C.base
      ((childPuncture C.puncture (ProviderInitialSource.outer K S D Γ X H i)).radical.absNorm : ℝ) ≤
        Q + glen - dlen + 2 * h := by
  let gamma := ProviderInitialSource.outer K S D Γ X H i
  have hres := ProviderInitialBoxes.residual_norm K S D Γ X H P b C.base A h
    hbase hh hwidth hboxCap j i hi
  have hr0 : gamma.residual ≠ 0 :=
    nonZeroDivisors.coe_ne_zero (ProviderInitialSource.residual K S D Γ X H i).val
  have hp : childPuncture C.puncture gamma ≠ 0 := by
    exact mul_ne_zero hRho (SourceLengths.radical_ne_zero _
      (mul_ne_zero (mul_ne_zero one_ne_zero one_ne_zero) hr0))
  have hn : 0 < ((childPuncture C.puncture gamma).radical.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (fun he => SourceLengths.radical_ne_zero _ hp (Ideal.absNorm_eq_zero_iff.mp he))
  apply (Real.logb_le_iff_le_rpow hbase hn).mpr
  calc
    _ ≤ (C.puncture.radical.absNorm : ℝ) *
        (gamma.q0.absNorm : ℝ) * (gamma.quotient.absNorm : ℝ) *
          (gamma.residual.absNorm : ℝ) := by
      exact_mod_cast childPuncture_radical_norm_le C.puncture gamma hRho
        one_ne_zero one_ne_zero hr0
    _ = (C.puncture.radical.absNorm : ℝ) *
        height K Sset (ProviderInitialSource.residual K S D Γ X H i) := by
      simp only [gamma, ProviderInitialSource.outer, map_one, Nat.cast_one, mul_one, height]
    _ ≤ C.base ^ Q * C.base ^ (glen - dlen + 2 * h) :=
      mul_le_mul hRhoNorm hres (height_pos K Sset _).le
        (Real.rpow_nonneg (zero_lt_one.trans hbase).le _)
    _ = _ := by rw [← Real.rpow_add (zero_lt_one.trans hbase)]; congr 1; ring

include hbase hh hwidth hboxCap in
/-- Each nonnegative actual smooth piece is an admissible canonical
node with capacity and row rank at most the original moment exponent. -/
theorem nodeAt_admissible
    (Lambda : HeckeCharacter K) (rho : {r : ℝ // 0 < r})
    (m Q z c tau lo hi : ℝ) (markLengths : σ → ℝ)
    (hA : 0 ≤ A) (hQ : 0 ≤ Q) (hz : 0 ≤ z) (htau : 0 ≤ tau)
    (hsource₁ : C.length + Q + z ≤ m - c)
    (hsource₂ : 2 * C.length + 6 * z ≤ 3 * m - c)
    (hloss : 100 * h + 3 * tau ≤ c / 4)
    (hrho : rho.val ≤ C.base ^ (-m))
    (hcutoff : H = SecondAdaptiveCutoff.fineCutoff K S rho X C.base tau)
    (hLambda : C.lambda = Lambda)
    (hcal : ThetaCalibrationInput K Sset D C.lambda G)
    (hbg : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K C.background p)
    (hRho : C.puncture ≠ 0)
    (hRhoNorm : (C.puncture.radical.absNorm : ℝ) ≤ C.base ^ Q)
    (hmarks : MarkConditions K S slotCap C.base z lo hi C.slots C.primeLists
      C.primeWeights markLengths)
    (t : ℝ) (gamma : OuterTriple K) (hgamma : gamma ∈ packet.triples)
    (hM : 0 ≤ ProviderInitialGeometry.rowLength m C.length glen dlen h tau)
    (a : CanonicalChildClosure.Index)
    (ha : 0 ≤ (pieceFamily K S C Θ ψ hν W G hG hbase J b t a).columnLength gamma) :
    (nodeAt K S D Γ C Θ ψ hν W G hG hbase H J hprime slotCap hcap P b A j
      m h tau markLengths t gamma a).Admissible D Lambda G slotCap C.base m
        (3 * c / 4) z lo hi := by
  obtain ⟨i, hiP, hiγ⟩ := ProviderInitialSource.packet_triple_member K S D Γ X H J
    C.primeLists hprime slotCap hcap Pbox gamma hgamma
  have hiBox : i ∈ Pbox := (Finset.mem_filter.mp hiP).1
  have hgap := ProviderInitialBoxes.common_gap K S D Γ X H P b C.base A h hbase hh hwidth
    hboxCap j i hiBox
  have hlen := ProviderInitialBoxes.child_length K S D Γ X H P b C.base A h hbase hh hwidth
    hboxCap j C.length rfl i hiBox
  have hpuncture := puncture_length K S D Γ C hbase H P b A j h hh hwidth hboxCap
    Q hRho hRhoNorm i hiBox
  rw [hiγ] at hpuncture
  have hcaps := ProviderInitialGeometry.initial_capacities C.base m C.length Q z c
    glen dlen vlen h tau (Real.logb C.base U) hbase hh hwidth hsource₁ hQ hz
    hgap hlen.1 hlen.2.1 hlen.2.2 (by linarith) htau a
  have hlive : 1 ≤ 4 * (wideFamily K S C Θ ψ hν W G hG J b t).base ^
      (wideFamily K S C Θ ψ hν W G hG J b t).columnLength gamma := by
    change 1 ≤ 4 * C.base ^ (Real.log U / Real.log C.base)
    rw [FirstCompleteFamily.norm_scale C.base U hbase
      (SecondMobiusGeometry.childScale_pos X (Real.rpow_pos_of_pos (zero_lt_one.trans hbase) _) b)]
    exact live_of_member K S D Γ C H P b A j i hiBox
  have hRho' : childPuncture C.puncture gamma ≠ 0 := by
    obtain ⟨hq0, ht0, hr0⟩ := packet.outer_nonzero gamma hgamma
    exact mul_ne_zero hRho (SourceLengths.radical_ne_zero _ (mul_ne_zero (mul_ne_zero hq0 ht0) hr0))
  refine {
    base_eq := rfl
    row_nonneg := hM
    column_nonneg := ha
    label_nonneg := ?_
    total_le := hcaps.1
    complete_pool := CanonicalChildClosure.pieceFamily_complete_pool K Sset
      (wideFamily K S C Θ ψ hν W G hG J b t) hbase a gamma
    test_support := CanonicalChildClosure.pieceFamily_support K Sset
      (wideFamily K S C Θ ψ hν W G hG J b t) hbase a gamma hlive
      (wide_support K S C Θ ψ hν W G hG J b t gamma)
    label_squarefree := packet.label_squarefree
    label_bound := packet_label_bound K S D Γ C hbase H J hprime slotCap hcap P b A j h
      hh hwidth hboxCap
    row_bound := packet_row_bound K S D Γ C hbase H J hprime slotCap hcap P b A j h
      hh hwidth hboxCap rho m tau hrho hcutoff
    puncture_nonzero := hRho'
    lambda_eq := hLambda
    calibration := hcal
    background_unramified := ?_
    marks := hmarks.restrict Finset.sdiff_subset
    margins := ?_ }
  · have hd := (ProviderInitialBoxes.length_bounds C.base A hbase hA j 1).1
    have hv := (ProviderInitialBoxes.length_bounds C.base A hbase hA j 2).1
    change 0 ≤ ProviderInitialGeometry.labelLength dlen vlen h
    unfold ProviderInitialGeometry.labelLength
    linarith
  · intro p hp
    exact (hbg p hp).mul K ((hcal.G_unramified p hp).inv K)
  · exact ProviderInitialGeometry.piece_margins C.base m C.length Q z c glen dlen vlen h tau
      (Real.logb C.base U)
      (Real.logb C.base ((childPuncture C.puncture gamma).radical.absNorm : ℝ))
      hbase hh hwidth hsource₁ hsource₂ hgap hpuncture hlen.1 hlen.2.1 hlen.2.2 hloss htau a

/-- The raw initial packet energy is the literal weighted row and
label energy of its actual common centered family. -/
def rawEnergy (t : ℝ) (gamma : OuterTriple K) : ℝ :=
  packet.energy (childValue K Sset D (wideFamily K S C Θ ψ hν W G hG J b t)
    (CanonicalSectors.sectorUnit K Sset Γ)) gamma

/-- The class-conversion seminorm is selected before every original
family, actual packet, source profile, frequency, scale and frozen
triple. Its sole recursive premise is the genuine canonical node bound.
Negative rows vanish exactly, and negative column pieces use the proved
unit-column bound in `CanonicalChildClosure`. -/
theorem exists_uniform_raw_bound (slotCap₀ : ℕ) (A₀ pi : ℝ)
    (hA₀ : 0 ≤ A₀) (hpi : 0 < pi) (q : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ B : ℝ, 0 < B ∧
      ∀ {σ₀ : Type u} [DecidableEq σ₀]
        (C₀ : CanonicalBlock.ColumnData K S σ₀)
        (Θ₀ : Subgroup (HeckeCharacter K)) (ψ₀ : HeckeCharacter K)
        (hν₀ : BackgroundCycle.Admissible K Θ₀ ψ₀ C₀.background)
        (W₀ : SchwartzMap ℝ ℂ) (G₀ : HeckeCharacter K) (hG₀ : G₀ ∈ Θ₀)
        (hbase₀ : 1 < C₀.base) (H₀ : ProviderInitialSource.Cutoff K S)
        (J₀ : Finset σ₀)
        (hprime₀ : ∀ i ∈ J₀, ∀ p ∈ C₀.primeLists i, Prime p)
        (hcap₀ : J₀.card ≤ slotCap₀)
        (P₀ : Finset (ProviderInitialSource.Index K S D Γ (C₀.base ^ C₀.length) H₀))
        (b₀ : SecondMobiusGeometry.Index (C₀.base ^ C₀.length))
        (j₀ : ProviderInitialBoxes.BoxIndex C₀.base A₀)
        (Lambda : HeckeCharacter K) (rho : {r : ℝ // 0 < r})
        (m Q z c h tau lo hi eps Cih : ℝ) (markLengths : σ₀ → ℝ),
      0 ≤ Q → 0 ≤ z → h ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ tau →
      2 ≤ C₀.base ^ h → 4 * C₀.base ^ C₀.length ≤ C₀.base ^ A₀ →
      C₀.length + Q + z ≤ m - c → 2 * C₀.length + 6 * z ≤ 3 * m - c →
      100 * h + 3 * tau ≤ c / 4 →
      rho.val ≤ C₀.base ^ (-m) →
      H₀ = SecondAdaptiveCutoff.fineCutoff K S rho (C₀.base ^ C₀.length) C₀.base tau →
      C₀.lambda = Lambda → ThetaCalibrationInput K Sset D C₀.lambda G₀ →
      (∀ p : HeightOneSpectrum (𝓞 K), p ∉ Sset → UnramifiedAt K C₀.background p) →
      C₀.puncture ≠ 0 → (C₀.puncture.radical.absNorm : ℝ) ≤ C₀.base ^ Q →
      MarkConditions K S slotCap₀ C₀.base z lo hi C₀.slots C₀.primeLists
        C₀.primeWeights markLengths →
      0 ≤ eps → 0 ≤ Cih →
      UniformBound.{u} (Γ := Γ) (Θ := Θ₀) (ψ := ψ₀) D Lambda G₀ slotCap₀ C₀.base m
        (3 * c / 4) z lo hi eps m Cih q →
      ∀ t : ℝ, ∀ gamma ∈
        (ProviderInitialSource.packet K S D Γ (C₀.base ^ C₀.length) H₀ J₀ C₀.primeLists
          hprime₀ slotCap₀ hcap₀
          (ProviderInitialBoxes.boxed K S D Γ (C₀.base ^ C₀.length) H₀ P₀ b₀ C₀.base A₀ j₀)).triples,
      rawEnergy K S D Γ C₀ Θ₀ ψ₀ hν₀ W₀ G₀ hG₀ H₀ J₀ hprime₀ slotCap₀ hcap₀
        P₀ b₀ A₀ j₀ t gamma ≤
        B * (Cih + (Fintype.card Sector : ℝ)) *
          (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (FinalMellinTests.weightedTest 0 t)) ^ 2 *
          C₀.base ^ (2 * (max 0 (Real.logb C₀.base (SecondMobiusGeometry.childScale
            (C₀.base ^ C₀.length) b₀)) + ProviderInitialGeometry.labelLength
            (ProviderInitialBoxes.length C₀.base j₀ 1) (ProviderInitialBoxes.length C₀.base j₀ 2) h) +
            28 * h + eps + pi) := by
  obtain ⟨s, B, hB, hb⟩ := CanonicalChildClosure.exists_closed_raw_bound K Sset D
    slotCap₀ (2 * A₀ + 2) pi (by positivity) hpi q
  refine ⟨s, B, hB, ?_⟩
  intro σ₀ _ C₀ Θ₀ ψ₀ hν₀ W₀ G₀ hG₀ hbase₀ H₀ J₀ hprime₀ hcap₀
    P₀ b₀ j₀ Lambda rho m Q z c h tau lo hi eps Cih markLengths
    hQ hz hh htau hwidth hbox hsource₁ hsource₂ hloss hrho hcutoff
    hLambda hcal hbg hRho hRhoNorm hmarks heps hCih hih t gamma hgamma
  let Pg := ProviderInitialBoxes.boxed K S D Γ (C₀.base ^ C₀.length) H₀ P₀ b₀ C₀.base A₀ j₀
  let Qp := ProviderInitialSource.packet K S D Γ (C₀.base ^ C₀.length) H₀ J₀ C₀.primeLists
    hprime₀ slotCap₀ hcap₀ Pg
  let Cw := wideFamily K S C₀ Θ₀ ψ₀ hν₀ W₀ G₀ hG₀ J₀ b₀ t
  let g := ProviderInitialBoxes.length C₀.base j₀ 0
  let theta := ProviderInitialBoxes.length C₀.base j₀ 1
  let v := ProviderInitialBoxes.length C₀.base j₀ 2
  let Mc := ProviderInitialGeometry.rowLength m C₀.length g theta h tau
  let Vc := ProviderInitialGeometry.labelLength theta v h
  obtain ⟨i, hiP, hiγ⟩ := ProviderInitialSource.packet_triple_member K S D Γ
    (C₀.base ^ C₀.length) H₀ J₀ C₀.primeLists hprime₀ slotCap₀ hcap₀ Pg gamma hgamma
  have hiBox : i ∈ Pg := (Finset.mem_filter.mp hiP).1
  have hlen := ProviderInitialBoxes.child_length K S D Γ (C₀.base ^ C₀.length) H₀
    P₀ b₀ C₀.base A₀ h hbase₀ hh.1 hwidth hbox j₀ C₀.length rfl i hiBox
  have hgap := ProviderInitialBoxes.common_gap K S D Γ (C₀.base ^ C₀.length) H₀
    P₀ b₀ C₀.base A₀ h hbase₀ hh.1 hwidth hbox j₀ i hiBox
  have hpuncture := puncture_length K S D Γ C₀ hbase₀ H₀ P₀ b₀ A₀ j₀ h
    hh.1 hwidth hbox Q hRho hRhoNorm i hiBox
  rw [hiγ] at hpuncture
  have hrows : ∀ r ∈ Qp.rows, (r.1.absNorm : ℝ) ≤ C₀.base ^ Mc :=
    packet_row_bound K S D Γ C₀ hbase₀ H₀ J₀ hprime₀ slotCap₀ hcap₀ P₀ b₀ A₀ j₀ h
      hh.1 hwidth hbox rho m tau hrho hcutoff
  have hlabels : ∀ f ∈ Qp.labels, (f.absNorm : ℝ) ≤ C₀.base ^ Vc :=
    packet_label_bound K S D Γ C₀ hbase₀ H₀ J₀ hprime₀ slotCap₀ hcap₀ P₀ b₀ A₀ j₀ h
      hh.1 hwidth hbox
  by_cases hM : 0 ≤ Mc
  · have hV : 0 ≤ Vc := by
      have hd := (ProviderInitialBoxes.length_bounds C₀.base A₀ hbase₀ hA₀ j₀ 1).1
      have hv := (ProviderInitialBoxes.length_bounds C₀.base A₀ hbase₀ hA₀ j₀ 2).1
      dsimp only [Vc, theta, v, ProviderInitialGeometry.labelLength]
      linarith [hh.1]
    have hVc : Vc ≤ 2 * A₀ + 2 := by
      have hd := (ProviderInitialBoxes.length_bounds C₀.base A₀ hbase₀ hA₀ j₀ 1).2
      have hv := (ProviderInitialBoxes.length_bounds C₀.base A₀ hbase₀ hA₀ j₀ 2).2
      dsimp only [Vc, theta, v, ProviderInitialGeometry.labelLength]
      linarith [hh.2]
    have hlive : 1 ≤ 4 * Cw.base ^ Cw.columnLength gamma := by
      change 1 ≤ 4 * C₀.base ^ (Real.log (SecondMobiusGeometry.childScale
        (C₀.base ^ C₀.length) b₀) / Real.log C₀.base)
      rw [FirstCompleteFamily.norm_scale C₀.base _ hbase₀
        (SecondMobiusGeometry.childScale_pos _ (Real.rpow_pos_of_pos (zero_lt_one.trans hbase₀) _) b₀)]
      exact live_of_member K S D Γ C₀ H₀ P₀ b₀ A₀ j₀ i hiBox
    have hQnew : 0 ≤ Real.logb C₀.base
        ((childPuncture C₀.puncture gamma).radical.absNorm : ℝ) := by
      have hp : childPuncture C₀.puncture gamma ≠ 0 := by
        obtain ⟨hq0, ht0, hr0⟩ := Qp.outer_nonzero gamma hgamma
        exact mul_ne_zero hRho (SourceLengths.radical_ne_zero _
          (mul_ne_zero (mul_ne_zero hq0 ht0) hr0))
      apply Real.logb_nonneg hbase₀
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (fun he => SourceLengths.radical_ne_zero _ hp (Ideal.absNorm_eq_zero_iff.mp he))
    have hsmall : ∀ a : CanonicalChildClosure.Index,
        (CanonicalChildClosure.pieceFamily K Sset Cw hbase₀ a).columnLength gamma < 0 →
          Mc ≤ Vc + 28 * h := by
      intro a ha
      exact ProviderInitialGeometry.small_piece_row C₀.base m C₀.length Q z c g theta v h tau
        (Real.logb C₀.base (SecondMobiusGeometry.childScale (C₀.base ^ C₀.length) b₀))
        (Real.logb C₀.base ((childPuncture C₀.puncture gamma).radical.absNorm : ℝ))
        hbase₀ hh.1 hwidth hsource₁ hQnew hz hpuncture hlen.1 hlen.2.1 hlen.2.2
        (by linarith [hh.1]) a ha
    have hrecursive : ∀ a : CanonicalChildClosure.Index,
        0 ≤ (CanonicalChildClosure.pieceFamily K Sset Cw hbase₀ a).columnLength gamma →
        normalizedChildEnergy C₀.base
          ((CanonicalChildClosure.pieceFamily K Sset Cw hbase₀ a).columnLength gamma) Vc
          slotCap₀ Qp.labels Qp.rows
          (childValue K Sset D (CanonicalChildClosure.pieceFamily K Sset Cw hbase₀ a)
            (CanonicalSectors.sectorUnit K Sset Γ)) gamma ≤
        Cih * (q.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          ((CanonicalChildClosure.pieceFamily K Sset Cw hbase₀ a).cutoff gamma)) ^ 2 *
          C₀.base ^ ((CanonicalChildClosure.pieceFamily K Sset Cw hbase₀ a).columnLength gamma +
            Vc + eps) := by
      intro a ha
      let x := nodeAt K S D Γ C₀ Θ₀ ψ₀ hν₀ W₀ G₀ hG₀ hbase₀ H₀ J₀ hprime₀
        slotCap₀ hcap₀ P₀ b₀ A₀ j₀ m h tau markLengths t gamma a
      have hx := nodeAt_admissible K S D Γ C₀ Θ₀ ψ₀ hν₀ W₀ G₀ hG₀ hbase₀ H₀ J₀
        hprime₀ slotCap₀ hcap₀ P₀ b₀ A₀ j₀ h hh.1 hwidth hbox Lambda rho
        m Q z c tau lo hi markLengths hA₀ hQ hz htau hsource₁ hsource₂ hloss
        hrho hcutoff hLambda hcal hbg hRho hRhoNorm hmarks t gamma hgamma hM a ha
      have hcaps := ProviderInitialGeometry.initial_capacities C₀.base m C₀.length Q z c
        g theta v h tau (Real.logb C₀.base (SecondMobiusGeometry.childScale
          (C₀.base ^ C₀.length) b₀)) hbase₀ hh.1 hwidth hsource₁ hQ hz hgap
        hlen.1 hlen.2.1 hlen.2.2 (by linarith [hh.1]) htau a
      exact hih x hx hcaps.2
    exact hb Cw hbase₀ G₀ hcal (CanonicalSectors.sectorUnit K Sset Γ) gamma Qp.labels Qp.rows
      Mc Vc h eps Cih (wide_complete K S C₀ Θ₀ ψ₀ hν₀ W₀ G₀ hG₀ hbase₀ J₀ b₀ t gamma)
      hlive (wide_support K S C₀ Θ₀ ψ₀ hν₀ W₀ G₀ hG₀ J₀ b₀ t gamma)
      hV hVc hh.1 hwidth heps hCih hrows hlabels
      (fun i hi p hp => hmarks.prime i (Finset.mem_sdiff.mp hi).1 p hp) hsmall hrecursive
  · have hz := CanonicalChildClosure.raw_energy_eq_zero_of_negative_row_length K Sset D
      (CanonicalSectors.sectorUnit K Sset Γ) Cw hbase₀ gamma slotCap₀ Qp.labels Qp.rows
      Mc (lt_of_not_ge hM) hrows
    change childEnergy slotCap₀ Qp.labels Qp.rows
      (childValue K Sset D Cw (CanonicalSectors.sectorUnit K Sset Γ)) gamma ≤ _
    rw [hz]
    positivity

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderInitialNodes

end
