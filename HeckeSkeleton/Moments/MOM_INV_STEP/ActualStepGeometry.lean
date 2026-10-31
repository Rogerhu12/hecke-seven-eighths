import HeckeSkeleton.Moments.MOM_INV_STEP.ActualUniformProduction

/-!
# Geometry of exactly the canonical children consumed by production

The quantifiers below are the quantifiers of
`ActualUniformProduction.AllSmallerPieces`: the actual first and second
marked subsets, both Cauchy branches, both spectral frequencies, the
predetermined first center, the actual second bin and norm box, and the
frozen triples in that literal packet. Every recursive piece has its
complete norm pool and a test supported in [1,2], and satisfies the four
public descent conclusions. Negative row and column pieces are excluded
from this induction class by the proved terminal estimates.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualStepGeometry

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalNormPools FirstParentRows
  FirstOuterCenters FirstToSecondData CommonKernel ActualProductionBoxes ActualBoxGeometry
  ActualUniformProduction
open HeckePort.Moments
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
local notation "OS" => Set.integer Sset K
variable {σ : Type*} [DecidableEq σ]
variable (T : FirstParentEnergy.Data K S (σ := σ))
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
variable (hbase : 1 < T.columns.base)

section Box

variable (R : OuterIndex K S D T → {r : ℝ // 0 < r})
variable (U : {r : ℝ // 0 < r}) (J₁ : Finset σ) (s : ℝ)
variable (H₂ : ∀ o : OuterIndex K S D T, (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K)))) → Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)) → ℝ)
variable (hmask : T.mask = ∅)
local notation "X" => sourceScale K S T U
local notation "Idx" => ProductionIndex K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂
local notation "Eidx" => indexEquiv K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂
local notation "Hraw" => actualCutoff K S D T U H₂
variable {ι : Type*} [Fintype ι]
variable (grid : ι → {r : ℝ // 0 < r})
variable (centers : FirstOuterCenters.Centering K S D T grid)
variable (alive : OuterIndex K S D T → Prop) (k : ι) (side₁ : Bool)
variable (P : Finset (ProductionIndex K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂)) (b : SecondMobiusGeometry.Index (sourceScale K S T U))
variable (Z L : ℝ) (j : BoxIndex Z L)
local notation "Pbox" => ActualSingleBoxBudget.boxedSource K S D Γ T Θ ψ G hν hG hbase
  R U J₁ s H₂ hmask grid centers alive k side₁ P b Z L j
variable (hprime : ∀ q ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists q, Prime p)
variable (hweights : ∀ q ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists q,
  ‖T.columns.primeWeights q p‖ ≤ 1)
variable (hJ₁ : J₁ ⊆ T.columns.slots) (J₂ : Finset σ) (hJ₂ : J₂ ⊆ T.columns.slots)
variable (slotCap : ℕ) (hcap : T.columns.slots.card ≤ slotCap)
local notation "packet" => SecondProductionPacket.packet K S D Γ T Θ ψ G hν hG hbase
  R U J₁ s H₂ hmask hprime hweights hJ₁ J₂ hJ₂ Pbox side₁ slotCap hcap
local notation "piece" side₂ p a => ActualClosedBoxBudget.pieceAt K S T Θ ψ hν hbase
  U J₁ J₂ b side₂ p a

/-- The actual canonical test class and the precise margins of every
piece on which the recursive hypothesis is invoked. -/
def PieceClassGeometry (M r ell V z c d eta h : ℝ) (side₂ : Bool) : Prop :=
  ∀ p : LogPlane × ℝ,
    let Mc := childM M ell (extractedLength Z j side₁) (length Z j .firstOverlap)
      (length Z j .secondCommon) (length Z j .secondDivisor) V (length Z j .cubeLabel) (5 * h)
    let Vc := secondFormalLabel (length Z j .firstCommon) (length Z j .secondDivisor)
      (length Z j .secondOverlap) (length Z j .cubeLabel) + 4 * h
    0 ≤ Mc → ∀ γ ∈ (packet).triples, ∀ a : CanonicalChildClosure.Index,
    0 ≤ (piece side₂ p a).columnLength γ →
      (piece side₂ p a).columns γ = squarefreePool K Sset
        (2 * Z ^ (piece side₂ p a).columnLength γ) ∧
      tsupport ((piece side₂ p a).cutoff γ) ⊆ Set.Icc (1 : ℝ) 2 ∧
      let Fc := (piece side₂ p a).columnLength γ + Vc
      let Qc := Real.logb Z (Ideal.absNorm (childPuncture T.columns.puncture γ).radical : ℝ)
      c - 5 * eta ≤ Fc - Mc - Qc - z ∧
        c - 7 * eta ≤ 4 * Fc - 3 * Mc - 6 * z ∧
        3 * d / 2 ≤ M - Mc ∧ Fc ≤ r + 3 * ell + V + 11 * eta

theorem piece_class_geometry (M r ell V Q z c d eta h : ℝ)
    (hZ : 1 < Z) (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
    (hb : ∀ q ∈ T.cubes, height K Sset q ≤ Z ^ L)
    (hfirst : 2 * T.scale.val ≤ Z ^ L) (hsecond : 4 * X ≤ Z ^ L)
    (hbase_eq : T.columns.base = Z) (hscale : U.val = Z ^ r / (grid k).val)
    (hcube : ∀ q ∈ T.cubes, height K Sset q ≤ Z ^ (ell + h))
    (hell : 0 ≤ ell) (hV : 0 ≤ V) (hL : 0 ≤ L)
    (hmesh : h ≤ eta / 16) (hstep : eta ≤ d / 16)
    (hparent : HeckePort.Moments.CanonicalMargins (r + 3 * ell + V) M Q z c)
    (hnonterminal : d ≤ ell + V)
    (hRho : T.columns.puncture ≠ 0)
    (hRhoNorm : (Ideal.absNorm T.columns.puncture.radical : ℝ) ≤ Z ^ Q)
    (side₂ : Bool) :
    PieceClassGeometry K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
      grid centers alive k side₁ P b Z L j hprime hweights hJ₁ J₂ hJ₂ slotCap hcap
      M r ell V z c d eta h side₂ := by
  intro p Mc Vc hMc γ hγ a ha
  let C := ActualClosedBoxBudget.familyAt K S T Θ ψ hν U J₁ J₂ b side₂ p
  have hCbase : C.base = Z := hbase_eq
  have hCz : 1 < C.base := hbase
  have hpool := CanonicalChildClosure.pieceFamily_complete_pool K Sset C hCz a γ
  have hpiecebase : (piece side₂ p a).base = Z := hbase_eq
  have hcomplete : (piece side₂ p a).columns γ =
      squarefreePool K Sset (2 * Z ^ (piece side₂ p a).columnLength γ) := by
    change (piece side₂ p a).columns γ = squarefreePool K Sset
      (2 * (piece side₂ p a).base ^ (piece side₂ p a).columnLength γ) at hpool
    rwa [hpiecebase] at hpool
  obtain ⟨B,hB,hγB⟩ := ActualPacketProvenance.triple_member K S T.columns D Γ
    hprime hweights J₁ J₂ hJ₁ hJ₂
    (FirstProductionChildren.sourceOn K S D Γ T Θ ψ G hν hG hbase
      R U J₁ s H₂ hmask Pbox) side₁ slotCap hcap γ hγ
  rw [ActualSingleBoxBudget.sourceOn_eq_bare_image K S D Γ T Θ ψ G hν hG hbase
    R U J₁ s H₂ hmask grid centers alive k side₁ P b Z L j] at hB
  obtain ⟨i,hi,hBi⟩ := Finset.mem_image.mp hB
  have hm := ActualSingleBoxBudget.source_membership K S D Γ T Θ ψ G hν hG hbase
    R U J₁ s H₂ hmask grid centers alive k side₁ P b Z L j i hi
  have hbin : ActualCenteredGeometry.secondBin K S D Γ T X Hraw (Eidx i) = b := hm.2.2.2.1
  have hquarter := ActualCenteredGeometry.childScale_one_quarter_le K S D Γ T X Hraw (Eidx i)
  rw [hbin] at hquarter
  have hU : 0 < SecondMobiusGeometry.childScale X b :=
    SecondMobiusGeometry.childScale_pos X
      (by rw [sourceScale_eq K S T hbase U]; exact U.property) b
  have hlive : 1 ≤ 4 * C.base ^ C.columnLength γ := by
    change 1 ≤ 4 * T.columns.base ^
      (Real.log (SecondMobiusGeometry.childScale X b) / Real.log T.columns.base)
    rw [FirstCompleteFamily.norm_scale T.columns.base _ hbase hU]
    linarith
  have hsupport : tsupport (C.cutoff γ) ⊆ Set.Icc (1 / 128 : ℝ) 4 := by
    intro x hx
    have hh := FinalMellinTests.weightedTest_support 0
      (p.2 + SecondParentProduction.coordinate side₂ p.1) hx
    exact ⟨hh.1, by linarith [hh.2]⟩
  have hs := CanonicalChildClosure.pieceFamily_support K Sset C hCz a γ hlive hsupport
  have hg := ActualClosedBoxBudget.piece_child_geometry K S D Γ T Θ ψ G hν hG hbase
    R U J₁ s H₂ hmask grid centers alive k side₁ P b Z L j
    hprime hweights hJ₁ J₂ hJ₂ slotCap hcap h hZ hh hwidth hb hfirst hsecond
    M r ell V Q z c d eta hbase_eq hscale hcube hell hV hL hmesh hstep hparent
    hnonterminal hRho hRhoNorm side₂ p γ hγ a
  refine ⟨hcomplete, hs, ?_⟩
  simpa only [max_eq_right ha, add_assoc] using hg

end Box

variable (hmask : T.mask = ∅)
variable (A Z M r ell V h tau : ℝ) (hZ : 1 < Z)
local notation "Rcap" => FirstOuterPhysicalCap.radius K S D Γ T hmask
  Z (boxCap A) M r ell V h tau (zero_lt_one.trans hZ)
local notation "Grid" => FirstParentCentering.grid Z A 1
variable (H : OuterIndex K S D T → {r : ℝ // 0 < r}) (oldLabels : Finset (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K)))))
variable (centers : FirstOuterCenters.Centering K S D T (FirstParentCentering.grid Z A 1))
variable (hprime : ∀ q ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists q, Prime p)
variable (hweights : ∀ q ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists q,
  ‖T.columns.primeWeights q p‖ ≤ 1)
variable (slotCap : ℕ) (hcap : T.columns.slots.card ≤ slotCap)
local notation "Alive" => FirstLiveCappedFreeEnergy.alive K S D Γ T H oldLabels

/-- Geometry on exactly the actual generation set quantified by
`AllSmallerPieces`; it is proved independently of that energy premise. -/
def AllChildrenGeometry (z c d eta : ℝ) : Prop :=
  ∀ (side₁ : Bool) (k : FirstParentCentering.CenterIndex Z A 1)
    (J₁ : Finset σ) (hJ₁ : J₁ ⊆ T.columns.slots) (s : ℝ) (side₂ : Bool),
    ∀ (b : SecondMobiusGeometry.Index (sourceScale K S T
      (FirstCenteredPositiveEnergy.centerScale T.scale (Grid k))))
      (J₂ : Finset σ) (hJ₂ : J₂ ⊆ T.columns.slots),
      J₂ ∈ (T.columns.slots \ J₁).powerset → ∀ j : BoxIndex Z (boxCap A),
      PieceClassGeometry
        (K := K) (S := S) (D := D) (Γ := Γ) (T := T) (Θ := Θ) (ψ := ψ) (G := G)
        (hν := hν) (hG := hG) (hbase := hbase) (R := Rcap)
        (U := FirstCenteredPositiveEnergy.centerScale T.scale (Grid k)) (J₁ := J₁) (s := s)
        (H₂ := FirstSecondErrorBridge.cutoff K S D T Rcap
          (FirstCenteredPositiveEnergy.centerScale T.scale (Grid k)) Z tau)
        (hmask := hmask) (grid := Grid) (centers := centers) (alive := Alive)
        (k := k) (side₁ := side₁) (P := Finset.univ) (b := b) (Z := Z) (L := boxCap A) (j := j)
        (hprime := hprime) (hweights := hweights) (hJ₁ := hJ₁) (J₂ := J₂) (hJ₂ := hJ₂)
        (slotCap := slotCap) (hcap := hcap) M r ell V z c d eta h side₂

theorem all_children_geometry (Q z c d eta : ℝ) (hA : 1 ≤ A)
    (hr : r ∈ Set.Icc (0 : ℝ) A) (hell : ell ∈ Set.Icc (0 : ℝ) A)
    (hV : 0 ≤ V) (hh : h ∈ Set.Icc (0 : ℝ) 1)
    (hwidth : 2 ≤ Z ^ h) (hmesh : h ≤ eta / 16) (hstep : eta ≤ d / 16)
    (hbase_eq : T.columns.base = Z) (hscale : T.scale.val = Z ^ r)
    (hcube : ∀ q ∈ T.cubes, height K Sset q ≤ Z ^ (ell + h))
    (hparent : HeckePort.Moments.CanonicalMargins (r + 3 * ell + V) M Q z c)
    (hnonterminal : d ≤ ell + V) (hRho : T.columns.puncture ≠ 0)
    (hRhoNorm : (Ideal.absNorm T.columns.puncture.radical : ℝ) ≤ Z ^ Q) :
    AllChildrenGeometry K S D Γ T Θ ψ G hν hG hbase hmask A Z M r ell V h tau hZ
      H oldLabels centers hprime hweights slotCap hcap z c d eta := by
  intro side₁ k J₁ hJ₁ s side₂ b J₂ hJ₂ hJ₂remaining j
  let U := FirstCenteredPositiveEnergy.centerScale T.scale (Grid k)
  have hz0 : 0 < Z := zero_lt_one.trans hZ
  have hZ2 : 2 ≤ Z := by
    have hp := Real.rpow_le_rpow_of_exponent_le hZ.le hh.2
    rw [Real.rpow_one] at hp
    exact hwidth.trans hp
  have hL : 0 ≤ boxCap A := by unfold boxCap; linarith
  have hUscale : U.val = Z ^ r / (Grid k).val := by
    change T.scale.val / (Grid k).val = _
    rw [hscale]
  have hU : U.val ≤ Z ^ A := by
    rw [hUscale]
    exact (div_le_self (Real.rpow_nonneg hz0.le _)
      (FirstParentCentering.grid_one_le Z A 1 k)).trans
      (Real.rpow_le_rpow_of_exponent_le hZ.le hr.2)
  have hX : sourceScale K S T U ≤ Z ^ A := by
    rwa [sourceScale_eq K S T hbase U]
  have hXpos : 0 < sourceScale K S T U := by
    rw [sourceScale_eq K S T hbase U]
    exact U.property
  have hb : ∀ q ∈ T.cubes, height K Sset q ≤ Z ^ boxCap A := by
    intro q hq
    exact (hcube q hq).trans (Real.rpow_le_rpow_of_exponent_le hZ.le
      (by unfold boxCap; linarith [hell.2, hh.2]))
  have hfirst : 2 * T.scale.val ≤ Z ^ boxCap A := by
    calc
      2 * T.scale.val ≤ Z * Z ^ r := mul_le_mul hZ2 hscale.le T.scale.property.le hz0.le
      _ = Z ^ (1 + r) := by rw [Real.rpow_add hz0, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by unfold boxCap; linarith [hr.2])
  have hsecond : 4 * sourceScale K S T U ≤ Z ^ boxCap A := by
    have h4 : (4 : ℝ) ≤ Z ^ (2 : ℝ) := by rw [Real.rpow_two]; nlinarith
    calc
      4 * sourceScale K S T U ≤ Z ^ (2 : ℝ) * Z ^ A :=
        mul_le_mul h4 hX hXpos.le (Real.rpow_nonneg hz0.le _)
      _ = Z ^ (2 + A) := (Real.rpow_add hz0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by unfold boxCap; linarith)
  exact piece_class_geometry K S D Γ T Θ ψ G hν hG hbase Rcap U J₁ s
    (FirstSecondErrorBridge.cutoff K S D T Rcap U Z tau) hmask Grid centers Alive
    k side₁ Finset.univ b Z (boxCap A) j hprime hweights hJ₁ J₂ hJ₂ slotCap hcap
    M r ell V Q z c d eta h hZ hh.1 hwidth hb hfirst hsecond hbase_eq hUscale
    hcube hell.1 hV hL hmesh hstep hparent hnonterminal hRho hRhoNorm side₂

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualStepGeometry

end
