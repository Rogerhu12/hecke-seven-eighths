import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderNodes
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualStepGeometry

/-!
# Every actual generated piece belongs to the induction class

This file constructs the node from the provider's literal packet and
piece family. Its row and label norm bounds are the bounds proved from
the actual source box. The complete pool, support, margins and strict
row decrease are the independent geometric output of that same box.
All arithmetic fields and individual mark coefficients are inherited.

The resulting theorem converts a uniform bound on the actual induction
class into the provider's `SmallerPieceBound`, without a column identity
or a recursive energy inequality among its source hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderGeneratedNodes

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open HeckeSkeleton.Moments.MOM_INV_STEP
open HeckePort.Moments
open FixedTripleFibers FixedTripleEnergy CanonicalChildren CanonicalNormPools
  FirstParentRows FirstToSecondData CommonKernel ActualProductionBoxes ActualBoxGeometry
open HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderNodes
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
variable {σ : Type u} [DecidableEq σ]
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
variable {ι : Type*} [Fintype ι]
variable (grid : ι → {r : ℝ // 0 < r})
variable (centers : FirstOuterCenters.Centering K S D T grid)
variable (alive : OuterIndex K S D T → Prop) (k : ι) (side₁ : Bool)
variable (P : Finset (ProductionIndex K S D T Θ ψ G hν hG hbase R U J₁ s Γ H₂))
  (b : SecondMobiusGeometry.Index (sourceScale K S T U))
variable (Z L : ℝ) (j : BoxIndex Z L)
local notation "Pslice" => ActualSingleBoxBudget.slice K S D Γ T Θ ψ G hν hG hbase
  R U J₁ s H₂ grid centers alive k side₁ P b
local notation "Pbox" => ActualSingleBoxBudget.boxedSource K S D Γ T Θ ψ G hν hG hbase
  R U J₁ s H₂ hmask grid centers alive k side₁ P b Z L j
variable (hprime : ∀ q ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists q, Prime p)
variable (hweights : ∀ q ∈ T.columns.slots, ∀ p ∈ T.columns.primeLists q,
  ‖T.columns.primeWeights q p‖ ≤ 1)
variable (hJ₁ : J₁ ⊆ T.columns.slots) (J₂ : Finset σ) (hJ₂ : J₂ ⊆ T.columns.slots)
variable (slotCap : ℕ) (hcap : T.columns.slots.card ≤ slotCap)
local notation "packet" => SecondProductionPacket.packet K S D Γ T Θ ψ G hν hG hbase
  R U J₁ s H₂ hmask hprime hweights hJ₁ J₂ hJ₂ Pbox side₁ slotCap hcap
local notation "piece" side₂:max p:max a:max => ActualClosedBoxBudget.pieceAt K S T Θ ψ hν hbase
  U J₁ J₂ b side₂ p a
local notation "Mc" M:max ell:max V:max h:max => childM M ell (extractedLength Z j side₁)
  (length Z j Coordinate.firstOverlap) (length Z j Coordinate.secondCommon)
  (length Z j Coordinate.secondDivisor) V (length Z j Coordinate.cubeLabel) (5 * h)
local notation "Vc" h:max => secondFormalLabel (length Z j Coordinate.firstCommon)
  (length Z j Coordinate.secondDivisor) (length Z j Coordinate.secondOverlap)
  (length Z j Coordinate.cubeLabel) + 4 * h

/-- The genuine finite node from one actual two-pass packet. -/
def nodeAt (M ell V h : ℝ) (markLengths : σ → ℝ) (side₂ : Bool)
    (p : LogPlane × ℝ) (γ : OuterTriple K) (a : CanonicalChildClosure.Index) :
    Node K S Γ Θ ψ σ where
  family := piece side₂ p a
  triple := γ
  labels := (packet).labels
  rows := (packet).rows
  rowLength := Mc M ell V h
  labelLength := Vc h
  markLengths := markLengths

variable (h : ℝ) (hZ : 1 < Z) (hh : 0 ≤ h) (hwidth : 2 ≤ Z ^ h)
variable (hb : ∀ q ∈ T.cubes, height K (S : Set (HeightOneSpectrum (𝓞 K))) q ≤ Z ^ L)
variable (hfirst : 2 * T.scale.val ≤ Z ^ L)
  (hsecond : 4 * sourceScale K S T U ≤ Z ^ L)

include hZ hh in
/-- The packet labels have the nonnegative exponent appearing in the
literal normalized energy, including its four mesh losses. -/
theorem label_length_nonneg (hL : 0 ≤ L) : 0 ≤ Vc h := by
  have hB := (length_bounds Z L hZ hL j .firstCommon).1
  have ht := (length_bounds Z L hZ hL j .secondDivisor).1
  have hv := (length_bounds Z L hZ hL j .secondOverlap).1
  have hj := (length_bounds Z L hZ hL j .cubeLabel).1
  unfold secondFormalLabel
  linarith

include hZ hh hwidth hb hfirst hsecond in
/-- All source conditions of every nonnegative recursive piece are
proved from its actual arithmetic packet and inherited original marks. -/
theorem nodeAt_admissible
    (Λ : HeckeCharacter K) (M r ell V tau z c d eta A lo hi : ℝ) (markLengths : σ → ℝ)
    (hL : 0 ≤ L) (heta : 0 ≤ eta) (hbase_eq : T.columns.base = Z)
    (hscale : U.val = Z ^ r / (grid k).val)
    (hcutoff : H₂ = FirstToSecondData.fineCutoff K S D T R U Z tau)
    (hrow : ∀ i ∈ Pbox, (R i.1).val =
      Z ^ (firstPhysicalHeight M r ell V (length Z j .firstDivisor)
        (length Z j .firstCommon) (length Z j .cubeLabel) + 12 * h + tau))
    (hlambda : T.columns.lambda = Λ)
    (hcal : ThetaCalibrationInput K Sset D T.columns.lambda G)
    (hbg : ∀ q : HeightOneSpectrum (𝓞 K), q ∉ Sset →
      UnramifiedAt K T.columns.background q)
    (hRho : T.columns.puncture ≠ 0)
    (hmarks : MarkConditions K S slotCap Z z lo hi T.columns.slots
      T.columns.primeLists T.columns.primeWeights markLengths)
    (hF : r + 3 * ell + V ≤ A) (side₂ : Bool)
    (hgeometry : ActualStepGeometry.PieceClassGeometry K S D Γ T Θ ψ G hν hG hbase
      R U J₁ s H₂ hmask grid centers alive k side₁ P b Z L j
      hprime hweights hJ₁ J₂ hJ₂ slotCap hcap M r ell V z c d eta h side₂)
    (p : LogPlane × ℝ) (hMc : 0 ≤ Mc M ell V h)
    (γ : OuterTriple K) (hγ : γ ∈ packet.triples) (a : CanonicalChildClosure.Index)
    (ha : 0 ≤ (piece side₂ p a).columnLength γ) :
    (nodeAt K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
      grid centers alive k side₁ P b Z L j hprime hweights hJ₁ J₂ hJ₂ slotCap hcap
      M ell V h markLengths side₂ p γ a).Admissible D Λ G slotCap Z
        (A + 11 * eta) (c - 7 * eta) z lo hi := by
  obtain ⟨hpool, hsupp, hm₁, hm₂, hdrop, hFc⟩ := hgeometry p hMc γ hγ a ha
  have hrows := ActualSingleBoxBudget.packet_rows_bound K S D Γ T Θ ψ G hν hG hbase
    R U J₁ s H₂ hmask grid centers alive k side₁ P b Z L j
    h hZ hh hwidth hb hfirst hsecond hprime hweights hJ₁ J₂ hJ₂ slotCap hcap
    M r ell V tau hscale hcutoff hrow
  have hlabels := SecondProductionBoxes.packet_labels_norm_bound K S D Γ T Θ ψ G
    hν hG hbase R U J₁ s H₂ hmask Pslice Z L h hZ hh hwidth hb hfirst hsecond j
    hprime hweights hJ₁ J₂ hJ₂ side₁ slotCap hcap
  have hRho' : childPuncture T.columns.puncture γ ≠ 0 := by
    obtain ⟨hq, ht, hr⟩ := packet.outer_nonzero γ hγ
    exact mul_ne_zero hRho
      (SourceLengths.radical_ne_zero _ (mul_ne_zero (mul_ne_zero hq ht) hr))
  refine {
    base_eq := hbase_eq
    row_nonneg := hMc
    column_nonneg := ha
    label_nonneg := label_length_nonneg Z L j h hZ hh hL
    total_le := ?_
    complete_pool := hpool
    test_support := hsupp
    label_squarefree := packet.label_squarefree
    label_bound := ?_
    row_bound := hrows
    puncture_nonzero := hRho'
    lambda_eq := hlambda
    calibration := hcal
    background_unramified := hbg
    marks := ?_
    margins := ?_ }
  · change (piece side₂ p a).columnLength γ + Vc h ≤ A + 11 * eta
    exact hFc.trans (by linarith)
  · simpa only [secondFormalLabel, add_assoc] using hlabels
  · exact hmarks.restrict (Finset.sdiff_subset.trans Finset.sdiff_subset)
  · change HeckePort.Moments.CanonicalMargins
      ((piece side₂ p a).columnLength γ + Vc h) (Mc M ell V h)
      (Real.logb Z (Ideal.absNorm (childPuncture T.columns.puncture γ).radical : ℝ))
      z (c - 7 * eta)
    exact ⟨by linarith, hm₂⟩

include hZ hh hwidth hb hfirst hsecond in
/-- A uniform bound on the next actual node class supplies exactly the
recursive premise required by the authoritative step. Its row rank is
strictly smaller by the actual geometric drop. -/
theorem smaller_piece_bound_of_uniform
    (Λ : HeckeCharacter K) (M r ell V tau z c d eta A lo hi Rcap eps Cih : ℝ)
    (markLengths : σ → ℝ) (t : Finset (ℕ × ℕ))
    (hL : 0 ≤ L) (heta : 0 ≤ eta) (hd : 0 ≤ d) (hM : M ≤ Rcap)
    (hbase_eq : T.columns.base = Z) (hscale : U.val = Z ^ r / (grid k).val)
    (hcutoff : H₂ = FirstToSecondData.fineCutoff K S D T R U Z tau)
    (hrow : ∀ i ∈ Pbox, (R i.1).val =
      Z ^ (firstPhysicalHeight M r ell V (length Z j .firstDivisor)
        (length Z j .firstCommon) (length Z j .cubeLabel) + 12 * h + tau))
    (hlambda : T.columns.lambda = Λ)
    (hcal : ThetaCalibrationInput K Sset D T.columns.lambda G)
    (hbg : ∀ q : HeightOneSpectrum (𝓞 K), q ∉ Sset →
      UnramifiedAt K T.columns.background q)
    (hRho : T.columns.puncture ≠ 0)
    (hmarks : MarkConditions K S slotCap Z z lo hi T.columns.slots
      T.columns.primeLists T.columns.primeWeights markLengths)
    (hF : r + 3 * ell + V ≤ A) (side₂ : Bool)
    (hgeometry : ActualStepGeometry.PieceClassGeometry K S D Γ T Θ ψ G hν hG hbase
      R U J₁ s H₂ hmask grid centers alive k side₁ P b Z L j
      hprime hweights hJ₁ J₂ hJ₂ slotCap hcap M r ell V z c d eta h side₂)
    (hih : UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
      (A + 11 * eta) (c - 7 * eta) z lo hi eps (Rcap - d) Cih t) :
    ActualClosedBoxBudget.SmallerPieceBound K S D Γ T Θ ψ G hν hG hbase
      R U J₁ s H₂ hmask grid centers alive k side₁ P b Z L j
      hprime hweights hJ₁ J₂ hJ₂ slotCap hcap h M ell V eps Cih t side₂ := by
  intro p hMc γ hγ a ha
  let x := nodeAt K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    grid centers alive k side₁ P b Z L j hprime hweights hJ₁ J₂ hJ₂ slotCap hcap
    M ell V h markLengths side₂ p γ a
  have hx := nodeAt_admissible K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    grid centers alive k side₁ P b Z L j hprime hweights hJ₁ J₂ hJ₂ slotCap hcap
    h hZ hh hwidth hb hfirst hsecond Λ M r ell V tau z c d eta A lo hi markLengths
    hL heta hbase_eq hscale hcutoff hrow hlambda hcal hbg hRho hmarks hF side₂ hgeometry
    p hMc γ hγ a ha
  have hdrop := (hgeometry p hMc γ hγ a ha).2.2.2.2.1
  have hrank : x.rowLength ≤ Rcap - d := by
    change Mc M ell V h ≤ Rcap - d
    linarith
  have hb := hih x hx hrank
  change normalizedChildEnergy T.columns.base ((piece side₂ p a).columnLength γ)
    (Vc h) slotCap packet.labels packet.rows
    (childValue K Sset D (piece side₂ p a) (CanonicalSectors.sectorUnit K Sset Γ)) γ ≤
    Cih * (t.sup (schwartzSeminormFamily ℝ ℝ ℂ) ((piece side₂ p a).cutoff γ)) ^ 2 *
      Z ^ ((piece side₂ p a).columnLength γ + Vc h + eps) at hb
  simpa only [hbase_eq] using hb

include hZ hh hwidth hb hfirst hsecond in
/-- Preserve the full actual 3d/2 row drop. This is used for the
long-cube source, whose dyadic centers permit dStep=2dOriginal/3. -/
theorem smaller_piece_bound_of_uniform_sharp
    (Λ : HeckeCharacter K) (M r ell V tau z c d eta A lo hi Rcap eps Cih : ℝ)
    (markLengths : σ → ℝ) (t : Finset (ℕ × ℕ))
    (hL : 0 ≤ L) (heta : 0 ≤ eta) (hd : 0 ≤ d) (hM : M ≤ Rcap)
    (hbase_eq : T.columns.base = Z) (hscale : U.val = Z ^ r / (grid k).val)
    (hcutoff : H₂ = FirstToSecondData.fineCutoff K S D T R U Z tau)
    (hrow : ∀ i ∈ Pbox, (R i.1).val =
      Z ^ (firstPhysicalHeight M r ell V (length Z j .firstDivisor)
        (length Z j .firstCommon) (length Z j .cubeLabel) + 12 * h + tau))
    (hlambda : T.columns.lambda = Λ)
    (hcal : ThetaCalibrationInput K Sset D T.columns.lambda G)
    (hbg : ∀ q : HeightOneSpectrum (𝓞 K), q ∉ Sset →
      UnramifiedAt K T.columns.background q)
    (hRho : T.columns.puncture ≠ 0)
    (hmarks : MarkConditions K S slotCap Z z lo hi T.columns.slots
      T.columns.primeLists T.columns.primeWeights markLengths)
    (hF : r + 3 * ell + V ≤ A) (side₂ : Bool)
    (hgeometry : ActualStepGeometry.PieceClassGeometry K S D Γ T Θ ψ G hν hG hbase
      R U J₁ s H₂ hmask grid centers alive k side₁ P b Z L j
      hprime hweights hJ₁ J₂ hJ₂ slotCap hcap M r ell V z c d eta h side₂)
    (hih : UniformBound.{u} (Γ := Γ) (Θ := Θ) (ψ := ψ) D Λ G slotCap Z
      (A + 11 * eta) (c - 7 * eta) z lo hi eps (Rcap - 3 * d / 2) Cih t) :
    ActualClosedBoxBudget.SmallerPieceBound K S D Γ T Θ ψ G hν hG hbase
      R U J₁ s H₂ hmask grid centers alive k side₁ P b Z L j
      hprime hweights hJ₁ J₂ hJ₂ slotCap hcap h M ell V eps Cih t side₂ := by
  intro p hMc γ hγ a ha
  let x := nodeAt K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    grid centers alive k side₁ P b Z L j hprime hweights hJ₁ J₂ hJ₂ slotCap hcap
    M ell V h markLengths side₂ p γ a
  have hx := nodeAt_admissible K S D Γ T Θ ψ G hν hG hbase R U J₁ s H₂ hmask
    grid centers alive k side₁ P b Z L j hprime hweights hJ₁ J₂ hJ₂ slotCap hcap
    h hZ hh hwidth hb hfirst hsecond Λ M r ell V tau z c d eta A lo hi markLengths
    hL heta hbase_eq hscale hcutoff hrow hlambda hcal hbg hRho hmarks hF side₂ hgeometry
    p hMc γ hγ a ha
  have hdrop := (hgeometry p hMc γ hγ a ha).2.2.2.2.1
  have hrank : x.rowLength ≤ Rcap - 3 * d / 2 := by
    change Mc M ell V h ≤ Rcap - 3 * d / 2
    linarith
  have hb := hih x hx hrank
  change normalizedChildEnergy T.columns.base ((piece side₂ p a).columnLength γ)
    (Vc h) slotCap packet.labels packet.rows
    (childValue K Sset D (piece side₂ p a) (CanonicalSectors.sectorUnit K Sset Γ)) γ ≤
    Cih * (t.sup (schwartzSeminormFamily ℝ ℝ ℂ) ((piece side₂ p a).cutoff γ)) ^ 2 *
      Z ^ ((piece side₂ p a).columnLength γ + Vc h + eps) at hb
  simpa only [hbase_eq] using hb

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderGeneratedNodes

end
