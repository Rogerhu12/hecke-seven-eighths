import HeckeSkeleton.Moments.MOM_INV_STEP.ActualSingleBoxBudget
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalChildClosure
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondSpectralCost
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstOuterPhysicalCap

/-!
# Smooth canonical child closure inside the actual source integral

The child induction premise below concerns exactly the nonnegative-length
[1,2] pieces of the literal two-pass child. Negative pieces use the unit
column estimate. Their capacity comes from the actual parent margin and
the source-certified puncture, row and column windows.

The finite seminorm and its constant depend only on the fixed child
seminorm, slot cap and bounded label window. They precede all source
ideals, prime lists, rows, labels and Fourier/Mellin frequencies.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualClosedBoxBudget

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open HeckePort.Moments
open FixedTripleFibers FixedTripleEnergy CanonicalChildren CanonicalNormPools
  FirstParentRows FirstToSecondData CommonKernel ActualProductionBoxes ActualBoxGeometry
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

def closureSeminorm (slotCap : ℕ) (Vcap piTerm : ℝ)
    (hVcap : 0 ≤ Vcap) (hpiTerm : 0 < piTerm) (t : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  Classical.choose (CanonicalChildClosure.exists_closed_raw_bound
    K Sset D slotCap Vcap piTerm hVcap hpiTerm t)

def closureConstant (slotCap : ℕ) (Vcap piTerm : ℝ)
    (hVcap : 0 ≤ Vcap) (hpiTerm : 0 < piTerm) (t : Finset (ℕ × ℕ)) : ℝ :=
  Classical.choose (Classical.choose_spec (CanonicalChildClosure.exists_closed_raw_bound
    K Sset D slotCap Vcap piTerm hVcap hpiTerm t))

theorem closureConstant_pos (slotCap : ℕ) (Vcap piTerm : ℝ)
    (hVcap : 0 ≤ Vcap) (hpiTerm : 0 < piTerm) (t : Finset (ℕ × ℕ)) :
    0 < closureConstant K S D slotCap Vcap piTerm hVcap hpiTerm t :=
  (Classical.choose_spec (Classical.choose_spec (CanonicalChildClosure.exists_closed_raw_bound
    K Sset D slotCap Vcap piTerm hVcap hpiTerm t))).1

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
local notation "Ext" => ExteriorIdeal K Sset
local notation "OS" => Set.integer Sset K
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

def profile (slotCap : ℕ) (Vcap piTerm : ℝ)
    (hVcap : 0 ≤ Vcap) (hpiTerm : 0 < piTerm) (t : Finset (ℕ × ℕ))
    (Cih : ℝ) (side₂ : Bool) (p : LogPlane × ℝ) : ℝ :=
  closureConstant K S D slotCap Vcap piTerm hVcap hpiTerm t *
    (Cih + (Fintype.card Sector : ℝ)) *
    ((closureSeminorm K S D slotCap Vcap piTerm hVcap hpiTerm t).sup
      (schwartzSeminormFamily ℝ ℝ ℂ)
        (FinalMellinTests.weightedTest 0 (p.2 + SecondParentProduction.coordinate side₂ p.1))) ^ 2

theorem profile_nonneg (slotCap : ℕ) (Vcap piTerm : ℝ)
    (hVcap : 0 ≤ Vcap) (hpiTerm : 0 < piTerm) (t : Finset (ℕ × ℕ))
    (Cih : ℝ) (hCih : 0 ≤ Cih) (side₂ : Bool) (p : LogPlane × ℝ) :
    0 ≤ profile K S D Γ slotCap Vcap piTerm hVcap hpiTerm t Cih side₂ p := by
  unfold profile
  exact mul_nonneg
    (mul_nonneg (closureConstant_pos K S D slotCap Vcap piTerm hVcap hpiTerm t).le
      (add_nonneg hCih (Nat.cast_nonneg _))) (sq_nonneg _)

/-- The second decay order is selected solely from the fixed child
seminorm and the bounded label window. -/
def spectralDegree (slotCap : ℕ) (Vcap piTerm : ℝ)
    (hVcap : 0 ≤ Vcap) (hpiTerm : 0 < piTerm) (t : Finset (ℕ × ℕ)) : ℕ :=
  Classical.choose (SecondSpectralCost.exists_seminorm_majorant
    (closureSeminorm K S D slotCap Vcap piTerm hVcap hpiTerm t))

def spectralCoefficient (slotCap : ℕ) (Vcap piTerm : ℝ)
    (hVcap : 0 ≤ Vcap) (hpiTerm : 0 < piTerm) (t : Finset (ℕ × ℕ)) : ℝ :=
  Classical.choose (Classical.choose_spec (SecondSpectralCost.exists_seminorm_majorant
    (closureSeminorm K S D slotCap Vcap piTerm hVcap hpiTerm t)))

theorem spectralCoefficient_nonneg (slotCap : ℕ) (Vcap piTerm : ℝ)
    (hVcap : 0 ≤ Vcap) (hpiTerm : 0 < piTerm) (t : Finset (ℕ × ℕ)) :
    0 ≤ spectralCoefficient K S D slotCap Vcap piTerm hVcap hpiTerm t :=
  (Classical.choose_spec (Classical.choose_spec (SecondSpectralCost.exists_seminorm_majorant
    (closureSeminorm K S D slotCap Vcap piTerm hVcap hpiTerm t)))).1

/-- This explicit continuous cost replaces the child seminorm inside
the actual Fourier/Mellin integral. -/
def spectralCost (slotCap : ℕ) (Vcap piTerm : ℝ)
    (hVcap : 0 ≤ Vcap) (hpiTerm : 0 < piTerm) (t : Finset (ℕ × ℕ))
    (Cih : ℝ) (side₂ : Bool) (p : LogPlane × ℝ) : ℝ :=
  SecondSpectralCost.polynomialCost
    (spectralDegree K S D slotCap Vcap piTerm hVcap hpiTerm t)
    (closureConstant K S D slotCap Vcap piTerm hVcap hpiTerm t *
      (Cih + (Fintype.card Sector : ℝ)) *
      spectralCoefficient K S D slotCap Vcap piTerm hVcap hpiTerm t)
    (SecondParentProduction.coordinate side₂) p

theorem spectralCost_nonneg (slotCap : ℕ) (Vcap piTerm : ℝ)
    (hVcap : 0 ≤ Vcap) (hpiTerm : 0 < piTerm) (t : Finset (ℕ × ℕ))
    (Cih : ℝ) (hCih : 0 ≤ Cih) (side₂ : Bool) (p : LogPlane × ℝ) :
    0 ≤ spectralCost K S D Γ slotCap Vcap piTerm hVcap hpiTerm t Cih side₂ p := by
  apply SecondSpectralCost.polynomialCost_nonneg
  exact mul_nonneg
    (mul_nonneg (closureConstant_pos K S D slotCap Vcap piTerm hVcap hpiTerm t).le
      (add_nonneg hCih (Nat.cast_nonneg _)))
    (spectralCoefficient_nonneg K S D slotCap Vcap piTerm hVcap hpiTerm t)

theorem profile_le_spectralCost (slotCap : ℕ) (Vcap piTerm : ℝ)
    (hVcap : 0 ≤ Vcap) (hpiTerm : 0 < piTerm) (t : Finset (ℕ × ℕ))
    (Cih : ℝ) (hCih : 0 ≤ Cih) (side₂ : Bool) (p : LogPlane × ℝ) :
    profile K S D Γ slotCap Vcap piTerm hVcap hpiTerm t Cih side₂ p ≤
      spectralCost K S D Γ slotCap Vcap piTerm hVcap hpiTerm t Cih side₂ p := by
  have hb : ((closureSeminorm K S D slotCap Vcap piTerm hVcap hpiTerm t).sup
      (schwartzSeminormFamily ℝ ℝ ℂ)
        (FinalMellinTests.weightedTest 0 (p.2 + SecondParentProduction.coordinate side₂ p.1))) ^ 2 ≤
      SecondSpectralCost.polynomialCost
        (spectralDegree K S D slotCap Vcap piTerm hVcap hpiTerm t)
        (spectralCoefficient K S D slotCap Vcap piTerm hVcap hpiTerm t)
        (SecondParentProduction.coordinate side₂) p :=
    (Classical.choose_spec (Classical.choose_spec (SecondSpectralCost.exists_seminorm_majorant
      (closureSeminorm K S D slotCap Vcap piTerm hVcap hpiTerm t)))).2
        (SecondParentProduction.coordinate side₂) p
  have hp := mul_le_mul_of_nonneg_left hb
    (mul_nonneg (closureConstant_pos K S D slotCap Vcap piTerm hVcap hpiTerm t).le
      (add_nonneg hCih (Nat.cast_nonneg _)))
  exact hp.trans_eq (by unfold spectralCost SecondSpectralCost.polynomialCost; ring)

theorem spectralCost_integrable (slotCap : ℕ) (Vcap piTerm : ℝ)
    (hVcap : 0 ≤ Vcap) (hpiTerm : 0 < piTerm) (t : Finset (ℕ × ℕ))
    (Cih s : ℝ) (side₂ : Bool) :
    Integrable (fun p : LogPlane × ℝ =>
      SecondProductionIntegral.jointDensity s
        (spectralDegree K S D slotCap Vcap piTerm hVcap hpiTerm t) p *
        spectralCost K S D Γ slotCap Vcap piTerm hVcap hpiTerm t Cih side₂ p)
      ((volume : Measure LogPlane).prod (volume : Measure ℝ)) :=
  SecondSpectralCost.joint_polynomial_integrable s
    (spectralDegree K S D slotCap Vcap piTerm hVcap hpiTerm t) _
    (SecondParentProduction.coordinate side₂)

variable {σ : Type*} [DecidableEq σ]
variable (T : FirstParentEnergy.Data K S (σ := σ))
variable (Θ : Subgroup (HeckeCharacter K)) (ψ G : HeckeCharacter K)
variable (hν : BackgroundCycle.Admissible K Θ ψ T.columns.background) (hG : G ∈ Θ)
variable (hbase : 1 < T.columns.base)
variable (R : OuterIndex K S D T → {r : ℝ // 0 < r})
variable (U : {r : ℝ // 0 < r}) (J₁ : Finset σ) (s : ℝ)
variable (H₂ : ∀ o : OuterIndex K S D T,
  ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K))) →
    Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)) → ℝ)
variable (hmask : T.mask = ∅)
local notation "X" => sourceScale K S T U
local notation "Idx" => ProductionIndex K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂
local notation "Eidx" => indexEquiv K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂
local notation "Hraw" => actualCutoff K S D T U H₂
variable {ι : Type*} [Fintype ι]
variable (grid : ι → {r : ℝ // 0 < r})
variable (centers : FirstOuterCenters.Centering K S D T grid)
variable (alive : OuterIndex K S D T → Prop) (k : ι) (side₁ : Bool)
variable (P : Finset (ProductionIndex K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂))
variable (b : SecondMobiusGeometry.Index (sourceScale K S T U))
variable (Z L : ℝ) (j : BoxIndex Z L)
local notation "Pslice" => ActualSingleBoxBudget.slice K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
  grid centers alive k side₁ P b
local notation "Pbox" => ActualSingleBoxBudget.boxedSource K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
  grid centers alive k side₁ P b Z L j
variable (hprime : ∀ q ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists q, Prime p)
variable (hweights : ∀ q ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists q,
  ‖T.columns.primeWeights q p‖ ≤ 1)
variable (hJ₁ : J₁ ⊆ T.columns.slots) (J₂ : Finset σ) (hJ₂ : J₂ ⊆ T.columns.slots)
variable (slotCap : ℕ) (hcap : T.columns.slots.card ≤ slotCap)
local notation "packet" => SecondProductionPacket.packet K S D Γ T Θ ψ G hν hG hbase
  R U J₁ s H₂ hmask hprime hweights hJ₁ J₂ hJ₂ Pbox side₁ slotCap hcap
local notation "Nactual" => Real.logb Z (SecondMobiusGeometry.childScale X b)
local notation "ALen" => extractedLength Z j side₁
local notation "BLen" => length Z j .firstCommon
local notation "RLen" => length Z j .activeConductor
local notation "JLen" => length Z j .cubeLabel
local notation "deltaLen" => length Z j .firstDivisor
local notation "tLen" => length Z j .firstOverlap
local notation "gLen" => length Z j .secondCommon
local notation "thetaLen" => length Z j .secondDivisor
local notation "vLen" => length Z j .secondOverlap

def familyAt (J₂ : Finset σ) (b : SecondMobiusGeometry.Index X)
    (side₂ : Bool) (p : LogPlane × ℝ) : ColumnFamily K Sset σ Θ ψ :=
  ActualTwoPassChildren.family K S T.columns Θ ψ hν J₁ J₂
    (SecondMobiusGeometry.childScale X b) (p.2 + SecondParentProduction.coordinate side₂ p.1)

def pieceAt (J₂ : Finset σ) (b : SecondMobiusGeometry.Index X)
    (side₂ : Bool) (p : LogPlane × ℝ) (a : CanonicalChildClosure.Index) :
    ColumnFamily K Sset σ Θ ψ :=
  CanonicalChildClosure.pieceFamily K Sset
    (familyAt K S T Θ ψ hν U J₁ J₂ b side₂ p) hbase a

variable (h : ℝ) (hZ : 1 < Z) (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
variable (hb : ∀ q ∈ T.cubes,
  height K (S : Set (HeightOneSpectrum (𝓞 K))) q ≤ Z ^ L)
variable (hfirst : 2 * T.scale.val ≤ Z ^ L)
  (hsecond : 4 * sourceScale K S T U ≤ Z ^ L)

/-- The recursive premise lists only the actual canonical pieces with
nonnegative row and column length. All rows, labels and triples are
those reconstructed from the first slice and the second norm box. -/
def SmallerPieceBound (M ell V eps Cih : ℝ)
    (t : Finset (ℕ × ℕ)) (side₂ : Bool) : Prop :=
  ∀ p : LogPlane × ℝ,
    0 ≤ childM M ell ALen tLen gLen thetaLen V JLen (5 * h) →
    ∀ γ ∈ (packet).triples, ∀ a : CanonicalChildClosure.Index,
    0 ≤ (pieceAt K S T Θ ψ hν hbase U J₁ J₂ b side₂ p a).columnLength γ →
    normalizedChildEnergy Z
      ((pieceAt K S T Θ ψ hν hbase U J₁ J₂ b side₂ p a).columnLength γ)
      (secondFormalLabel BLen thetaLen vLen JLen + 4 * h)
      slotCap (packet).labels (packet).rows
      (childValue K Sset D (pieceAt K S T Θ ψ hν hbase U J₁ J₂ b side₂ p a)
        (CanonicalSectors.sectorUnit K Sset Γ)) γ ≤
    Cih * (t.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      ((pieceAt K S T Θ ψ hν hbase U J₁ J₂ b side₂ p a).cutoff γ)) ^ 2 *
      Z ^ ((pieceAt K S T Θ ψ hν hbase U J₁ J₂ b side₂ p a).columnLength γ +
        (secondFormalLabel BLen thetaLen vLen JLen + 4 * h) + eps)

include hZ in
/-- The row cap is chosen before the second transform from the original
outer source. Every actual box recovers those same three coordinates. -/
theorem prescribed_radius_eq (M r ell V tau : ℝ)
    (hR : R = FirstOuterPhysicalCap.radius K S D Γ T hmask Z L M r ell V h tau
      (zero_lt_one.trans hZ)) (i : Idx) (hi : i ∈ Pbox) :
    (R i.1).val =
      Z ^ (firstPhysicalHeight M r ell V deltaLen BLen JLen + 12 * h + tau) := by
  have hr := ActualSingleBoxBudget.source_raw_box K S D Γ T Θ ψ G hν hG hbase
    R U J₁ s H₂ hmask grid centers alive k side₁ P b Z L j i hi
  have he := FirstOuterPhysicalCap.radius_eq_of_box K S D Γ T hmask X Hraw
    ((Pslice).image Eidx) Z L M r ell V h tau (zero_lt_one.trans hZ) j (Eidx i) hr
  calc
    (R i.1).val =
        (FirstOuterPhysicalCap.radius K S D Γ T hmask Z L M r ell V h tau
          (zero_lt_one.trans hZ) i.1).val := by rw [hR]
    _ = _ := he

include hZ hh hwidth hb hfirst hsecond in
/-- Every smooth piece in the recursive premise has its literal
logarithmic length and the certified descent margins. All windows and
the puncture estimate come from the same actual source box. -/
theorem piece_child_geometry (M r ell V Q z c d eta : ℝ)
    (hbase_eq : T.columns.base = Z)
    (hscale : U.val = Z ^ r / (grid k).val)
    (hcube : ∀ q ∈ T.cubes, height K Sset q ≤ Z ^ (ell + h))
    (hell : 0 ≤ ell) (hV : 0 ≤ V) (hL : 0 ≤ L)
    (hmesh : h ≤ eta / 16) (hstep : eta ≤ d / 16)
    (hparent : HeckePort.Moments.CanonicalMargins (r + 3 * ell + V) M Q z c)
    (hnonterminal : d ≤ ell + V)
    (hRho : T.columns.puncture ≠ 0)
    (hRhoNorm : (Ideal.absNorm T.columns.puncture.radical : ℝ) ≤ Z ^ Q)
    (side₂ : Bool) (p : LogPlane × ℝ) :
    ∀ γ ∈ (packet).triples, ∀ a : CanonicalChildClosure.Index,
      let Fc := max 0 ((pieceAt K S T Θ ψ hν hbase U J₁ J₂ b side₂ p a).columnLength γ) +
        secondFormalLabel BLen thetaLen vLen JLen + 4 * h
      let Mc := childM M ell ALen tLen gLen thetaLen V JLen (5 * h)
      let Qc := Real.logb Z (Ideal.absNorm (childPuncture T.columns.puncture γ).radical : ℝ)
      c - 5 * eta ≤ Fc - Mc - Qc - z ∧
        c - 7 * eta ≤ 4 * Fc - 3 * Mc - 6 * z ∧
        3 * d / 2 ≤ M - Mc ∧ Fc ≤ r + 3 * ell + V + 11 * eta := by
  intro γ hγ a
  have hpuncture := ActualSingleBoxBudget.packet_puncture_bound K S D Γ T Θ ψ G hν hG hbase
    R U J₁ s H₂ hmask grid centers alive k side₁ P b Z L j h hZ hh hwidth hb hfirst hsecond
    hprime hweights hJ₁ J₂ hJ₂ slotCap hcap ell Q V hcube hV hL
    T.columns.puncture hRho hRhoNorm γ hγ
  obtain ⟨B,hB,hγB⟩ := ActualPacketProvenance.triple_member K S T.columns D Γ
    hprime hweights J₁ J₂ hJ₁ hJ₂
    (FirstProductionChildren.sourceOn K S D Γ T Θ ψ G hν hG hbase
      R U J₁ s H₂ hmask Pbox) side₁ slotCap hcap γ hγ
  rw [ActualSingleBoxBudget.sourceOn_eq_bare_image K S D Γ T Θ ψ G hν hG hbase
    R U J₁ s H₂ hmask grid centers alive k side₁ P b Z L j] at hB
  obtain ⟨i,hi,hBi⟩ := Finset.mem_image.mp hB
  have hr := ActualSingleBoxBudget.source_raw_box K S D Γ T Θ ψ G hν hG hbase
    R U J₁ s H₂ hmask grid centers alive k side₁ P b Z L j i hi
  have hn := ActualSingleBoxBudget.source_length_bounds K S D Γ T Θ ψ G hν hG hbase
    R U J₁ s H₂ hmask grid centers alive k side₁ P b Z L j h hZ hh hwidth hb hfirst hsecond
    r hscale i hi
  have hcommon := ActualBoxGeometry.source_common_and_label K S D Γ T hmask X Hraw
    ((Pslice).image Eidx) Z L ell h hZ hh hwidth hb hfirst hsecond hcube j (Eidx i) hr
  have hlen : (pieceAt K S T Θ ψ hν hbase U J₁ J₂ b side₂ p a).columnLength γ =
      PartitionedChildGeometry.pieceLength Z Nactual a := by
    change PartitionedChildGeometry.pieceLength T.columns.base
      (Real.log (SecondMobiusGeometry.childScale X b) / Real.log T.columns.base) a = _
    rw [hbase_eq]
    rfl
  dsimp only
  rw [hlen]
  exact PartitionedChildGeometry.partitioned_step Z M r ell V Q
    (Real.logb Z (Ideal.absNorm (childPuncture T.columns.puncture γ).radical : ℝ)) z c d
    ALen BLen tLen gLen thetaLen vLen JLen h eta Nactual
    (childM M ell ALen tLen gLen thetaLen V JLen (5 * h)) hZ hwidth hparent hh hmesh hstep
    hell (extractedLength_nonneg Z L hZ hL j side₁)
    (length_bounds Z L hZ hL j .firstOverlap).1 hV
    (length_bounds Z L hZ hL j .cubeLabel).1 hcommon.1 hcommon.2 hpuncture
    hnonterminal hn.1 hn.2.1 hn.2.2 le_rfl a

include hZ hh hwidth hb hfirst hsecond in
/-- The actual child is controlled by the positive-length canonical
pieces. Unit-scale pieces are estimated internally, using the real
parent margin and the reconstructed puncture to supply their capacity. -/
theorem closed_child_bound
    (M r ell V Q z c tau eps Vcap piTerm Cih : ℝ)
    (hbase_eq : T.columns.base = Z) (hL : 0 ≤ L) (hV : 0 ≤ V)
    (hscale : U.val = Z ^ r / (grid k).val)
    (hcube : ∀ q ∈ T.cubes, height K Sset q ≤ Z ^ (ell + h))
    (hcutoff : H₂ = FirstToSecondData.fineCutoff K S D T R U Z tau)
    (hrow : ∀ i ∈ Pbox, (R i.1).val =
      Z ^ (firstPhysicalHeight M r ell V deltaLen BLen JLen + 12 * h + tau))
    (hparent : c ≤ r + 3 * ell + V - M - Q - z) (hc : 0 ≤ c) (hz : 0 ≤ z)
    (hRho : T.columns.puncture ≠ 0)
    (hRhoNorm : (Ideal.absNorm T.columns.puncture.radical : ℝ) ≤ Z ^ Q)
    (hVcap : 0 ≤ Vcap) (hpiTerm : 0 < piTerm)
    (hlabelCap : secondFormalLabel BLen thetaLen vLen JLen + 4 * h ≤ Vcap)
    (heps : 0 ≤ eps) (hCih : 0 ≤ Cih)
    (hcal : ThetaCalibrationInput K Sset D T.columns.lambda G)
    (t : Finset (ℕ × ℕ)) (side₂ : Bool) (p : LogPlane × ℝ)
    (hih : 0 ≤ childM M ell ALen tLen gLen thetaLen V JLen (5 * h) →
      ∀ γ ∈ (packet).triples, ∀ a : CanonicalChildClosure.Index,
      0 ≤ (pieceAt K S T Θ ψ hν hbase U J₁ J₂ b side₂ p a).columnLength γ →
      normalizedChildEnergy Z
        ((pieceAt K S T Θ ψ hν hbase U J₁ J₂ b side₂ p a).columnLength γ)
        (secondFormalLabel BLen thetaLen vLen JLen + 4 * h)
        slotCap (packet).labels (packet).rows
        (childValue K Sset D (pieceAt K S T Θ ψ hν hbase U J₁ J₂ b side₂ p a)
          (CanonicalSectors.sectorUnit K Sset Γ)) γ ≤
      Cih * (t.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        ((pieceAt K S T Θ ψ hν hbase U J₁ J₂ b side₂ p a).cutoff γ)) ^ 2 *
        Z ^ ((pieceAt K S T Θ ψ hν hbase U J₁ J₂ b side₂ p a).columnLength γ +
          (secondFormalLabel BLen thetaLen vLen JLen + 4 * h) + eps)) :
    ∀ γ ∈ (packet).triples,
      normalizedChildEnergy Z (max 0 Nactual)
        (secondFormalLabel BLen thetaLen vLen JLen + 4 * h)
        slotCap (packet).labels (packet).rows
        (SecondProductionPacket.childFunction K S D Γ T Θ ψ hν U J₁ J₂ side₂ b p) γ ≤
      profile K S D Γ slotCap Vcap piTerm hVcap hpiTerm t Cih side₂ p *
        Z ^ (max 0 Nactual + (secondFormalLabel BLen thetaLen vLen JLen + 4 * h) +
          (28 * h + eps + piTerm)) := by
  intro γ hγ
  let C := familyAt K S T Θ ψ hν U J₁ J₂ b side₂ p
  have hCb : C.base = Z := hbase_eq
  have hCZ : 1 < C.base := hbase
  have hlen : C.columnLength γ = Nactual := by
    change Real.log (SecondMobiusGeometry.childScale X b) / Real.log T.columns.base = _
    rw [hbase_eq]
    rfl
  have hU : 0 < SecondMobiusGeometry.childScale X b :=
    SecondMobiusGeometry.childScale_pos X
      (by rw [sourceScale_eq K S T hbase U]; exact U.property) b
  have hpool : C.columns γ = squarefreePool K Sset (2 * C.base ^ C.columnLength γ) := by
    change squarefreePool K Sset (2 * SecondMobiusGeometry.childScale X b) =
      squarefreePool K Sset (2 * T.columns.base ^
        (Real.log (SecondMobiusGeometry.childScale X b) / Real.log T.columns.base))
    rw [FirstCompleteFamily.norm_scale T.columns.base _ hbase hU]
  have hrows := ActualSingleBoxBudget.packet_rows_bound K S D Γ T Θ ψ G hν hG hbase
    R U J₁ s H₂ hmask grid centers alive k side₁ P b Z L j h hZ hh hwidth hb hfirst hsecond
    hprime hweights hJ₁ J₂ hJ₂ slotCap hcap M r ell V tau hscale hcutoff hrow
  by_cases hMc : childM M ell ALen tLen gLen thetaLen V JLen (5 * h) < 0
  · have hzero := CanonicalChildClosure.raw_energy_eq_zero_of_negative_row_length
      K Sset D (CanonicalSectors.sectorUnit K Sset Γ) C hCZ γ slotCap
      (packet).labels (packet).rows (childM M ell ALen tLen gLen thetaLen V JLen (5 * h))
      hMc (by simpa only [hCb] using hrows)
    rw [normalizedChildEnergy_eq Z (max 0 Nactual)
      (secondFormalLabel BLen thetaLen vLen JLen + 4 * h) (zero_lt_one.trans hZ)]
    change Z ^ (-(max 0 Nactual + (secondFormalLabel BLen thetaLen vLen JLen + 4 * h))) *
      childEnergy slotCap (packet).labels (packet).rows
        (childValue K Sset D C (CanonicalSectors.sectorUnit K Sset Γ)) γ ≤ _
    rw [hzero, mul_zero]
    exact mul_nonneg (profile_nonneg K S D Γ slotCap Vcap piTerm hVcap hpiTerm t Cih hCih side₂ p)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
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
  have hlive : 1 ≤ 4 * C.base ^ C.columnLength γ := by
    rw [hCb, hlen, Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) hU]
    linarith
  have hsupport : tsupport (C.cutoff γ) ⊆ Set.Icc (1 / 128 : ℝ) 4 := by
    intro x hx
    have hb := FinalMellinTests.weightedTest_support 0
      (p.2 + SecondParentProduction.coordinate side₂ p.1) hx
    exact ⟨hb.1, by linarith [hb.2]⟩
  have hchildV : 0 ≤ secondFormalLabel BLen thetaLen vLen JLen + 4 * h := by
    have hB := (length_bounds Z L hZ hL j .firstCommon).1
    have ht := (length_bounds Z L hZ hL j .secondDivisor).1
    have hv := (length_bounds Z L hZ hL j .secondOverlap).1
    have hj := (length_bounds Z L hZ hL j .cubeLabel).1
    unfold secondFormalLabel
    linarith
  have hlabels := SecondProductionBoxes.packet_labels_norm_bound K S D Γ T Θ ψ G
    hν hG hbase R U J₁ s H₂ hmask Pslice Z L h hZ hh hwidth hb hfirst hsecond j
    hprime hweights hJ₁ J₂ hJ₂ side₁ slotCap hcap
  have hlength := ActualSingleBoxBudget.source_length_bounds K S D Γ T Θ ψ G hν hG hbase
    R U J₁ s H₂ hmask grid centers alive k side₁ P b Z L j h hZ hh hwidth hb hfirst hsecond
    r hscale i hi
  have hpuncture := ActualSingleBoxBudget.packet_puncture_bound K S D Γ T Θ ψ G hν hG hbase
    R U J₁ s H₂ hmask grid centers alive k side₁ P b Z L j h hZ hh hwidth hb hfirst hsecond
    hprime hweights hJ₁ J₂ hJ₂ slotCap hcap ell Q V hcube hV hL
    T.columns.puncture hRho hRhoNorm γ hγ
  have hQnonneg := ActualSingleBoxBudget.packet_puncture_nonneg K S D Γ T Θ ψ G hν hG hbase
    R U J₁ s H₂ hmask grid centers alive k side₁ P b Z L j hZ
    hprime hweights hJ₁ J₂ hJ₂ slotCap hcap T.columns.puncture hRho γ hγ
  have hcapacity : ∀ a : CanonicalChildClosure.Index,
      (CanonicalChildClosure.pieceFamily K Sset C hCZ a).columnLength γ < 0 →
      childM M ell ALen tLen gLen thetaLen V JLen (5 * h) ≤
        (secondFormalLabel BLen thetaLen vLen JLen + 4 * h) + 28 * h := by
    intro a ha
    have hsmall : PartitionedChildGeometry.pieceLength Z Nactual a ≤ 0 := by
      simpa only [CanonicalChildClosure.pieceFamily_length, hCb, hlen] using ha.le
    exact PartitionedChildGeometry.small_piece_row_bound Z M r ell V Q
      (Real.logb Z (Ideal.absNorm (childPuncture T.columns.puncture γ).radical : ℝ))
      z c ALen BLen tLen gLen thetaLen vLen JLen h Nactual
      (childM M ell ALen tLen gLen thetaLen V JLen (5 * h))
      hZ hh hwidth hparent hc hQnonneg hz hpuncture
      hlength.1 hlength.2.1 hlength.2.2 le_rfl a hsmall
  have hclose := (Classical.choose_spec (Classical.choose_spec
    (CanonicalChildClosure.exists_closed_raw_bound K Sset D slotCap Vcap piTerm hVcap hpiTerm t))).2
  have hraw := hclose C hCZ G hcal (CanonicalSectors.sectorUnit K Sset Γ) γ
    (packet).labels (packet).rows (childM M ell ALen tLen gLen thetaLen V JLen (5 * h))
    (secondFormalLabel BLen thetaLen vLen JLen + 4 * h) h eps Cih
    hpool hlive hsupport hchildV hlabelCap hh (by simpa only [hCb] using hwidth) heps hCih
    (by simpa only [hCb] using hrows)
    (by simpa only [hCb, secondFormalLabel] using hlabels)
    (by
      intro q hq P hP
      exact hprime q (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hq).1).1 P hP)
    hcapacity (by
      intro a ha
      simpa only [hCb] using hih (le_of_not_gt hMc) γ hγ a ha)
  have hraw' : childEnergy slotCap (packet).labels (packet).rows
      (SecondProductionPacket.childFunction K S D Γ T Θ ψ hν U J₁ J₂ side₂ b p) γ ≤
      profile K S D Γ slotCap Vcap piTerm hVcap hpiTerm t Cih side₂ p *
        Z ^ (2 * (max 0 Nactual + (secondFormalLabel BLen thetaLen vLen JLen + 4 * h)) +
          (28 * h + eps + piTerm)) := by
    convert hraw using 1 <;> try rfl
    rw [hCb, hlen]
    congr 2
    ring
  exact CanonicalChildClosure.normalized_bound_of_raw K Z (max 0 Nactual)
    (secondFormalLabel BLen thetaLen vLen JLen + 4 * h) (28 * h + eps + piTerm)
    (profile K S D Γ slotCap Vcap piTerm hVcap hpiTerm t Cih side₂ p)
    (zero_lt_one.trans hZ) slotCap (packet).labels (packet).rows
    (SecondProductionPacket.childFunction K S D Γ T Θ ψ hν U J₁ J₂ side₂ b p) γ hraw'

variable (w : ∀ o : OuterIndex K S D T, FirstOuterCenters.Overlap K S D T o → ℝ)
variable (ε : ℝ)

include hZ hh hwidth hb hfirst hsecond in
/-- A real first slice and second box closes using only the smaller
canonical pieces. The continuous spectral majorant and its product
integrability are supplied internally, and all fixed-scale losses are
paid inside the public `40 eta` allowance. -/
theorem closed_sourceIntegral_le
    (M r ell V Q z c eta tau piMass eps Vcap piTerm Cih Cweight Cradial massEps : ℝ)
    (hbase_eq : T.columns.base = Z) (hL : 0 ≤ L) (hV : 0 ≤ V)
    (hscale : U.val = Z ^ r / (grid k).val)
    (hcube : ∀ q ∈ T.cubes, height K Sset q ≤ Z ^ (ell + h))
    (hcutoff : H₂ = FirstToSecondData.fineCutoff K S D T R U Z tau)
    (hrow : ∀ i ∈ Pbox, (R i.1).val =
      Z ^ (firstPhysicalHeight M r ell V deltaLen BLen JLen + 12 * h + tau))
    (hparent : c ≤ r + 3 * ell + V - M - Q - z) (hc : 0 ≤ c) (hz : 0 ≤ z)
    (hRho : T.columns.puncture ≠ 0)
    (hRhoNorm : (Ideal.absNorm T.columns.puncture.radical : ℝ) ≤ Z ^ Q)
    (hVcap : 0 ≤ Vcap) (hpiTerm : 0 < piTerm)
    (hlabelCap : secondFormalLabel BLen thetaLen vLen JLen + 4 * h ≤ Vcap)
    (heps : 0 ≤ eps) (hCih : 0 ≤ Cih)
    (hcal : ThetaCalibrationInput K Sset D T.columns.lambda G)
    (hmassEps : 0 < massEps) (hmesh : h ≤ eta / 32)
    (hCweight : 0 ≤ Cweight) (hCradial : 0 ≤ Cradial)
    (hloss : massEps * (secondCount ell RLen JLen tLen gLen thetaLen + 11 * h / 2) ≤ piMass)
    (hw : ∀ i ∈ Pbox, 0 ≤ w i.1 i.2.1)
    (hweight : ∀ i ∈ Pbox, w i.1 i.2.1 ≤
      Cweight * Z ^ (firstKappa M r ell V deltaLen ALen BLen RLen + (9 / 2 : ℝ) * h))
    (hradial : ∀ i ∈ Pbox,
      SecondProductionPacket.radialWeight K S D Γ T Θ ψ G hν hG hbase
        R U J₁ s H₂ ε i ≤ Cradial)
    (t : Finset (ℕ × ℕ)) (side₂ : Bool)
    (hih : ∀ p : LogPlane × ℝ,
      0 ≤ childM M ell ALen tLen gLen thetaLen V JLen (5 * h) →
      ∀ γ ∈ (packet).triples, ∀ a : CanonicalChildClosure.Index,
      0 ≤ (pieceAt K S T Θ ψ hν hbase U J₁ J₂ b side₂ p a).columnLength γ →
      normalizedChildEnergy Z
        ((pieceAt K S T Θ ψ hν hbase U J₁ J₂ b side₂ p a).columnLength γ)
        (secondFormalLabel BLen thetaLen vLen JLen + 4 * h)
        slotCap (packet).labels (packet).rows
        (childValue K Sset D (pieceAt K S T Θ ψ hν hbase U J₁ J₂ b side₂ p a)
          (CanonicalSectors.sectorUnit K Sset Γ)) γ ≤
      Cih * (t.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        ((pieceAt K S T Θ ψ hν hbase U J₁ J₂ b side₂ p a).cutoff γ)) ^ 2 *
        Z ^ ((pieceAt K S T Θ ψ hν hbase U J₁ J₂ b side₂ p a).columnLength γ +
          (secondFormalLabel BLen thetaLen vLen JLen + 4 * h) + eps)) :
    SecondProductionIntegral.sourceIntegral K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
      w ε side₁ (spectralDegree K S D slotCap Vcap piTerm hVcap hpiTerm t) side₂ Pbox b J₂ ≤
      ((Cweight * Cradial * ActualPoissonScale.fieldConstant K) *
        SecondProductionBudget.massConstant K S D Γ slotCap massEps hmassEps *
          Z ^ (r + 3 * ell + V + 40 * eta + tau + piMass + piTerm + eps)) *
        ∫ p : LogPlane × ℝ,
          SecondProductionIntegral.jointDensity s
            (spectralDegree K S D slotCap Vcap piTerm hVcap hpiTerm t) p *
            spectralCost K S D Γ slotCap Vcap piTerm hVcap hpiTerm t Cih side₂ p
          ∂((volume : Measure LogPlane).prod (volume : Measure ℝ)) := by
  have hclosed (p : LogPlane × ℝ) := closed_child_bound
    (K := K) (S := S) (D := D) (Γ := Γ) (T := T) (Θ := Θ) (ψ := ψ) (G := G)
    (hν := hν) (hG := hG) (hbase := hbase) (R := R) (U := U) (J₁ := J₁) (s := s)
    (H₂ := H₂) (hmask := hmask) (grid := grid) (centers := centers) (alive := alive)
    (k := k) (side₁ := side₁) (P := P) (b := b) (Z := Z) (L := L) (j := j)
    (hprime := hprime) (hweights := hweights) (hJ₁ := hJ₁) (J₂ := J₂) (hJ₂ := hJ₂)
    (slotCap := slotCap) (hcap := hcap) (h := h) (hZ := hZ) (hh := hh) (hwidth := hwidth)
    (hb := hb) (hfirst := hfirst) (hsecond := hsecond)
    M r ell V Q z c tau eps Vcap piTerm Cih hbase_eq hL hV hscale hcube hcutoff hrow
    hparent hc hz hRho hRhoNorm hVcap hpiTerm hlabelCap heps hCih hcal t side₂ p (hih p)
  have hbudget := ActualSingleBoxBudget.sourceIntegral_le_smaller_children
    (K := K) (S := S) (D := D) (Γ := Γ) (T := T) (Θ := Θ) (ψ := ψ) (G := G)
    (hν := hν) (hG := hG) (hbase := hbase) (R := R) (U := U) (J₁ := J₁) (s := s)
    (H₂ := H₂) (hmask := hmask) (grid := grid) (centers := centers) (alive := alive)
    (k := k) (side₁ := side₁) (P := P) (b := b) (Z := Z) (L := L) (j := j)
    (h := h) (hZ := hZ) (hh := hh) (hwidth := hwidth) (hb := hb)
    (hfirst := hfirst) (hsecond := hsecond) (w := w) (ε := ε)
    (hprime := hprime) (hweights := hweights) (hJ₁ := hJ₁) (J₂ := J₂) (hJ₂ := hJ₂)
    (slotCap := slotCap) (hcap := hcap)
    M r ell V (eta / 2) tau piMass (28 * h + eps + piTerm) Cweight Cradial massEps
    hmassEps (by linarith) hscale hcube hCweight hCradial hloss
    (fun i hi => (hrow i hi).le) hw hweight hradial
    (spectralDegree K S D slotCap Vcap piTerm hVcap hpiTerm t) side₂
    (spectralCost K S D Γ slotCap Vcap piTerm hVcap hpiTerm t Cih side₂)
    (spectralCost_nonneg K S D Γ slotCap Vcap piTerm hVcap hpiTerm t Cih hCih side₂)
    (spectralCost_integrable K S D Γ slotCap Vcap piTerm hVcap hpiTerm t Cih s side₂)
    (by
      intro p γ hγ
      have hc := (hclosed p γ hγ).trans
        (mul_le_mul_of_nonneg_right
          (profile_le_spectralCost K S D Γ slotCap Vcap piTerm hVcap hpiTerm t Cih hCih side₂ p)
          (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
      simpa only [add_assoc] using hc)
  apply hbudget.trans
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_left
    · apply Real.rpow_le_rpow_of_exponent_le hZ.le
      linarith
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg hCweight hCradial) (ActualPoissonScale.fieldConstant_nonneg K))
        (SecondProductionBudget.massConstant_pos K S D Γ slotCap massEps hmassEps).le
  · exact integral_nonneg fun p =>
      mul_nonneg (SecondProductionIntegral.jointDensity_nonneg s _ p)
        (spectralCost_nonneg K S D Γ slotCap Vcap piTerm hVcap hpiTerm t Cih hCih side₂ p)

include hcap in
/-- The actual second Cauchy mass and the proved continuous child cost
reduce to the fixed two-pass Mellin ledger. -/
theorem spectralCost_cauchy_le (Vcap piTerm : ℝ)
    (hVcap : 0 ≤ Vcap) (hpiTerm : 0 < piTerm) (t : Finset (ℕ × ℕ))
    (Cih : ℝ) (hCih : 0 ≤ Cih) (side₂ : Bool) :
    SecondProductionIntegral.cauchyMass K S T J₁ s *
      (∫ p : LogPlane × ℝ,
        SecondProductionIntegral.jointDensity s
          (spectralDegree K S D slotCap Vcap piTerm hVcap hpiTerm t) p *
          spectralCost K S D Γ slotCap Vcap piTerm hVcap hpiTerm t Cih side₂ p
        ∂((volume : Measure LogPlane).prod (volume : Measure ℝ))) ≤
      ((2 : ℝ) ^ slotCap *
        (closureConstant K S D slotCap Vcap piTerm hVcap hpiTerm t *
          (Cih + (Fintype.card Sector : ℝ)) *
          spectralCoefficient K S D slotCap Vcap piTerm hVcap hpiTerm t) *
        SecondSpectralCost.coordinateMoment
          (spectralDegree K S D slotCap Vcap piTerm hVcap hpiTerm t)
          (SecondParentProduction.coordinate side₂)) *
        NestedMellinBudget.cauchyCost (-(1 / 2 : ℝ)) s
          (spectralDegree K S D slotCap Vcap piTerm hVcap hpiTerm t) := by
  apply SecondSpectralCost.actual_cauchy_polynomial_bound K S T slotCap hcap J₁ s
    (spectralDegree K S D slotCap Vcap piTerm hVcap hpiTerm t) _ _
    (SecondParentProduction.coordinate side₂)
  exact mul_nonneg
    (mul_nonneg (closureConstant_pos K S D slotCap Vcap piTerm hVcap hpiTerm t).le
      (add_nonneg hCih (Nat.cast_nonneg _)))
    (spectralCoefficient_nonneg K S D slotCap Vcap piTerm hVcap hpiTerm t)

include hZ hh hwidth hb hfirst hsecond in
/-- Full actual production after all second bins, marks and arithmetic
norm boxes. The row cap is the previously selected original cap, the
first activity and center condition belong to each source, and the only
energy assumption is the smaller canonical piece induction hypothesis.
Both mask multiplicities are charged to the original slot cap. -/
theorem actualTotal_closed_le
    (M r ell V Q z c eta tau piMass eps Vcap piTerm Cih Cweight Cradial massEps : ℝ)
    (hbase_eq : T.columns.base = Z) (hL : 0 ≤ L) (hV : 0 ≤ V)
    (hscale : U.val = Z ^ r / (grid k).val)
    (hcube : ∀ q ∈ T.cubes, height K Sset q ≤ Z ^ (ell + h))
    (hR : R = FirstOuterPhysicalCap.radius K S D Γ T hmask Z L M r ell V h tau
      (zero_lt_one.trans hZ))
    (hcutoff : H₂ = FirstToSecondData.fineCutoff K S D T R U Z tau)
    (hparent : c ≤ r + 3 * ell + V - M - Q - z) (hc : 0 ≤ c) (hz : 0 ≤ z)
    (hRho : T.columns.puncture ≠ 0)
    (hRhoNorm : (Ideal.absNorm T.columns.puncture.radical : ℝ) ≤ Z ^ Q)
    (hVcap : 0 ≤ Vcap) (hpiTerm : 0 < piTerm)
    (hlabelCap : ∀ j : BoxIndex Z L,
      secondFormalLabel (length Z j .firstCommon) (length Z j .secondDivisor)
        (length Z j .secondOverlap) (length Z j .cubeLabel) + 4 * h ≤ Vcap)
    (heps : 0 ≤ eps) (hCih : 0 ≤ Cih)
    (hcal : ThetaCalibrationInput K Sset D T.columns.lambda G)
    (hmassEps : 0 < massEps) (hmesh : h ≤ eta / 32)
    (hCweight : 0 ≤ Cweight) (hCradial : 0 ≤ Cradial)
    (hloss : ∀ j : BoxIndex Z L,
      massEps * (secondCount ell (length Z j .activeConductor) (length Z j .cubeLabel)
        (length Z j .firstOverlap) (length Z j .secondCommon) (length Z j .secondDivisor) +
          11 * h / 2) ≤ piMass)
    (hw : ∀ i : Idx, 0 ≤ w i.1 i.2.1)
    (hweight : ∀ b : SecondMobiusGeometry.Index X, ∀ j : BoxIndex Z L,
      ∀ i ∈ ActualSingleBoxBudget.boxedSource K S D Γ T Θ ψ G hν hG hbase
        R U J₁ s H₂ hmask grid centers alive k side₁ Finset.univ b Z L j,
      w i.1 i.2.1 ≤ Cweight *
        Z ^ (firstKappa M r ell V (length Z j .firstDivisor) (extractedLength Z j side₁)
          (length Z j .firstCommon) (length Z j .activeConductor) + (9 / 2 : ℝ) * h))
    (hradial : ∀ i : Idx,
      SecondProductionPacket.radialWeight K S D Γ T Θ ψ G hν hG hbase
        R U J₁ s H₂ ε i ≤ Cradial)
    (t : Finset (ℕ × ℕ)) (side₂ : Bool)
    (hih : ∀ (b : SecondMobiusGeometry.Index X) (J₂ : Finset σ)
      (hJ₂ : J₂ ⊆ T.columns.slots), J₂ ∈ (T.columns.slots \ J₁).powerset →
      ∀ j : BoxIndex Z L,
      SmallerPieceBound
        (K := K) (S := S) (D := D) (Γ := Γ) (T := T) (Θ := Θ) (ψ := ψ) (G := G)
        (hν := hν) (hG := hG) (hbase := hbase) (R := R) (U := U) (J₁ := J₁) (s := s)
        (H₂ := H₂) (hmask := hmask) (grid := grid) (centers := centers) (alive := alive)
        (k := k) (side₁ := side₁) (P := Finset.univ) (b := b) (Z := Z) (L := L) (j := j)
        (hprime := hprime) (hweights := hweights) (hJ₁ := hJ₁) (J₂ := J₂) (hJ₂ := hJ₂)
        (slotCap := slotCap) (hcap := hcap) (h := h) M ell V eps Cih t side₂) :
    SecondProductionIntegral.actualTotal K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂
      (SecondProductionRestriction.weightOn K S D T w
        (fun o e => alive o ∧ centers.assignment side₁ o e = k))
      ε side₁ (spectralDegree K S D slotCap Vcap piTerm hVcap hpiTerm t) side₂ ≤
      ((Fintype.card (SecondMobiusGeometry.Index X) : ℝ) * (2 : ℝ) ^ slotCap *
        (Fintype.card (BoxIndex Z L) : ℝ) *
        ((Cweight * Cradial * ActualPoissonScale.fieldConstant K) *
          SecondProductionBudget.massConstant K S D Γ slotCap massEps hmassEps *
            Z ^ (r + 3 * ell + V + 40 * eta + tau + piMass + piTerm + eps))) *
        (((2 : ℝ) ^ slotCap *
          (closureConstant K S D slotCap Vcap piTerm hVcap hpiTerm t *
            (Cih + (Fintype.card Sector : ℝ)) *
            spectralCoefficient K S D slotCap Vcap piTerm hVcap hpiTerm t) *
          SecondSpectralCost.coordinateMoment
            (spectralDegree K S D slotCap Vcap piTerm hVcap hpiTerm t)
            (SecondParentProduction.coordinate side₂)) *
          NestedMellinBudget.cauchyCost (-(1 / 2 : ℝ)) s
            (spectralDegree K S D slotCap Vcap piTerm hVcap hpiTerm t)) := by
  let m₂ := spectralDegree K S D slotCap Vcap piTerm hVcap hpiTerm t
  let Cscalar := (Cweight * Cradial * ActualPoissonScale.fieldConstant K) *
    SecondProductionBudget.massConstant K S D Γ slotCap massEps hmassEps *
      Z ^ (r + 3 * ell + V + 40 * eta + tau + piMass + piTerm + eps)
  let I : ℝ := ∫ p : LogPlane × ℝ, SecondProductionIntegral.jointDensity s m₂ p *
    spectralCost K S D Γ slotCap Vcap piTerm hVcap hpiTerm t Cih side₂ p
    ∂((volume : Measure LogPlane).prod (volume : Measure ℝ))
  have hbox (b : SecondMobiusGeometry.Index X) (J₂ : Finset σ)
      (hmem : J₂ ∈ (T.columns.slots \ J₁).powerset) (j : BoxIndex Z L) :
      SecondProductionIntegral.sourceIntegral K S D Γ T Θ ψ G hν hG hbase
        R U J₁ s H₂ w ε side₁ m₂ side₂
        (ActualSingleBoxBudget.boxedSource K S D Γ T Θ ψ G hν hG hbase
          R U J₁ s H₂ hmask grid centers alive k side₁ Finset.univ b Z L j) b J₂ ≤ Cscalar * I := by
    have hJ₂ : J₂ ⊆ T.columns.slots := (Finset.mem_powerset.mp hmem).trans Finset.sdiff_subset
    apply closed_sourceIntegral_le
      (K := K) (S := S) (D := D) (Γ := Γ) (T := T) (Θ := Θ) (ψ := ψ) (G := G)
      (hν := hν) (hG := hG) (hbase := hbase) (R := R) (U := U) (J₁ := J₁) (s := s)
      (H₂ := H₂) (hmask := hmask) (grid := grid) (centers := centers) (alive := alive)
      (k := k) (side₁ := side₁) (P := Finset.univ) (b := b) (Z := Z) (L := L) (j := j)
      (hprime := hprime) (hweights := hweights) (hJ₁ := hJ₁) (J₂ := J₂) (hJ₂ := hJ₂)
      (slotCap := slotCap) (hcap := hcap) (h := h) (hZ := hZ) (hh := hh) (hwidth := hwidth)
      (hb := hb) (hfirst := hfirst) (hsecond := hsecond) (w := w) (ε := ε)
      M r ell V Q z c eta tau piMass eps Vcap piTerm Cih Cweight Cradial massEps
      hbase_eq hL hV hscale hcube hcutoff _ hparent hc hz hRho hRhoNorm
      hVcap hpiTerm (hlabelCap j) heps hCih hcal hmassEps hmesh hCweight hCradial
      (hloss j) (fun i _ => hw i) (hweight b j) (fun i _ => hradial i) t side₂
      (hih b J₂ hJ₂ hmem j)
    exact prescribed_radius_eq
      (K := K) (S := S) (D := D) (Γ := Γ) (T := T) (Θ := Θ) (ψ := ψ) (G := G)
      (hν := hν) (hG := hG) (hbase := hbase) (R := R) (U := U) (J₁ := J₁) (s := s)
      (H₂ := H₂) (hmask := hmask) (grid := grid) (centers := centers) (alive := alive)
      (k := k) (side₁ := side₁) (P := Finset.univ) (b := b) (Z := Z) (L := L) (j := j)
      (h := h) (hZ := hZ) M r ell V tau hR
  have hsum := ActualSingleBoxBudget.actualTotal_weightOn_le_uniform_box
    (K := K) (S := S) (D := D) (Γ := Γ) (T := T) (Θ := Θ) (ψ := ψ) (G := G)
    (hν := hν) (hG := hG) (hbase := hbase) (R := R) (U := U) (J₁ := J₁) (s := s)
    (H₂ := H₂) (hmask := hmask) (grid := grid) (centers := centers) (alive := alive)
    (k := k) (side₁ := side₁) (Z := Z) (L := L) (w := w) (ε := ε)
    m₂ side₂ Cscalar I hbox
  have hspec := spectralCost_cauchy_le K S D Γ T J₁ s slotCap hcap
    Vcap piTerm hVcap hpiTerm t Cih hCih side₂
  have hCscalar : 0 ≤ Cscalar :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg hCweight hCradial) (ActualPoissonScale.fieldConstant_nonneg K))
        (SecondProductionBudget.massConstant_pos K S D Γ slotCap massEps hmassEps).le)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  have hI : 0 ≤ I := integral_nonneg fun p =>
    mul_nonneg (SecondProductionIntegral.jointDensity_nonneg s m₂ p)
      (spectralCost_nonneg K S D Γ slotCap Vcap piTerm hVcap hpiTerm t Cih hCih side₂ p)
  have hmass : 0 ≤ SecondProductionIntegral.cauchyMass K S T J₁ s := by
    rw [SecondSpectralCost.cauchyMass_eq]
    exact mul_nonneg (Nat.cast_nonneg _) (NestedMellinBudget.moment_nonneg _ _ _)
  have hcount := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (SecondSpectralCost.remaining_masks_bound K S T slotCap hcap J₁)
      (Nat.cast_nonneg (Fintype.card (SecondMobiusGeometry.Index X))))
    (Nat.cast_nonneg (Fintype.card (BoxIndex Z L)))
  exact hsum.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right hcount hCscalar) hspec (mul_nonneg hmass hI)
    (mul_nonneg (by positivity) hCscalar))

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualClosedBoxBudget

end
