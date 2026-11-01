import HeckeSkeleton.Moments.MOM_INV_STEP.FirstNormPoolEnergy

/-!
# Exact complete norm pools for the first residual source

The independent first residual domain is characterized in both
directions for a complete original squarefree dyadic pool. Its only
remaining restriction is avoidance of the actual frozen cube and
common-factor support. This permits a subsequent exact zero-term
restoration, without a moving indicator of an arbitrary original set.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstCompletePools

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open IdealMobiusMask FirstSourceDecomposition FirstSourceReindexing FirstSourceColumns
  CanonicalFirstEnergy CanonicalNormPools FirstNormPoolEnergy
open scoped Classical BigOperators nonZeroDivisors

section Supports
variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem mem_columnDomain_iff (N : Finset ((Ideal R)⁰))
    (hN : ∀ n ∈ N, Squarefree n.val) (B A C U : Finset (HeightOneSpectrum R)) :
    U ∈ columnDomain N B A C ↔ Disjoint U (B ∪ C) ∧
      nonzeroProduct (Supports.restore A C U) ∈ N := by
  constructor
  · intro hU
    exact ⟨(Finset.mem_filter.mp hU).2.1, columnDomain_reconstruct_mem hN hU⟩
  · rintro ⟨hd, hn⟩
    have hr : Supports.restore A C U ∈ supportFamily N := by
      exact Finset.mem_image.mpr ⟨nonzeroProduct (Supports.restore A C U), hn,
        primeSupport_nonzeroProduct _⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hd, hr⟩
    intro p hp
    exact Finset.mem_biUnion.mpr ⟨Supports.restore A C U, hr,
      Finset.mem_union_right _ hp⟩

end Supports

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "NI" => (Ideal (𝓞 K))⁰

def extractedSupportSide (r₁ r₂ b₁ b₂ : Ext) (side : Bool) :=
  if side then rightSupport K S r₂ b₁ b₂ else leftSupport K S r₁ b₁ b₂

def blockedSupport (r₁ r₂ b₁ b₂ : Ext) :=
  cubeSupport K S b₁ b₂ ∪ CanonicalFirstEnergy.commonSupport K S r₁ r₂ b₁ b₂

theorem extractedSupportSide_subset (r₁ r₂ b₁ b₂ : Ext) (side : Bool) :
    extractedSupportSide K S r₁ r₂ b₁ b₂ side ⊆ cubeSupport K S b₁ b₂ := by
  cases side
  · exact leftSupport_subset K S r₁ b₁ b₂
  · exact rightSupport_subset K S r₂ b₁ b₂

include D in
theorem extractedFactor_support_product (r₁ r₂ b₁ b₂ : Ext) (side : Bool) :
    (extractedFactor K S r₁ r₂ b₁ b₂ side).val.val =
      primeProduct (extractedSupportSide K S r₁ r₂ b₁ b₂ side) *
        primeProduct (CanonicalFirstEnergy.commonSupport K S r₁ r₂ b₁ b₂) := by
  rw [extractedFactor_val K S D, CanonicalConductor.commonResidualIdeal_eq_C]
  cases side <;> rfl

include D in
theorem restore_product (r₁ r₂ b₁ b₂ : Ext) (side : Bool)
    (U : Finset (HeightOneSpectrum (𝓞 K)))
    (hU : Disjoint U (blockedSupport K S r₁ r₂ b₁ b₂)) :
    primeProduct (Supports.restore (extractedSupportSide K S r₁ r₂ b₁ b₂ side)
      (CanonicalFirstEnergy.commonSupport K S r₁ r₂ b₁ b₂) U) =
      (extractedFactor K S r₁ r₂ b₁ b₂ side).val.val * primeProduct U := by
  let A := extractedSupportSide K S r₁ r₂ b₁ b₂ side
  let C := CanonicalFirstEnergy.commonSupport K S r₁ r₂ b₁ b₂
  have hAC : Disjoint A C := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact Finset.disjoint_left.mp (commonSupport_disjoint K S r₁ r₂ b₁ b₂)
      hq (extractedSupportSide_subset K S r₁ r₂ b₁ b₂ side hp)
  have hACU : Disjoint (A ∪ C) U := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    apply Finset.disjoint_left.mp hU hq
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Finset.mem_union_left _ (extractedSupportSide_subset K S r₁ r₂ b₁ b₂ side hp)
    · exact Finset.mem_union_right _ hp
  rw [extractedFactor_support_product K S D]
  change primeProduct (A ∪ C ∪ U) = _
  rw [show primeProduct (A ∪ C ∪ U) = primeProduct (A ∪ C) * primeProduct U from
    Finset.prod_union hACU,
    show primeProduct (A ∪ C) = primeProduct A * primeProduct C from Finset.prod_union hAC]

include D in
theorem sideDomain_exterior (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext)
    (side : Bool) (U : Finset (HeightOneSpectrum (𝓞 K)))
    (hU : U ∈ sideDomain K S (dyadicPool K Sset X.val) r₁ r₂ b₁ b₂ side) :
    ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ primeProduct U → p ∉ Sset := by
  obtain ⟨n, hn, he⟩ := domain_reconstruct K S D (dyadicPool K Sset X.val)
    (fun n hn => dyadicPool_squarefree K Sset hn) r₁ r₂ b₁ b₂ side U hU
  intro p hp
  apply n.property p
  rw [he]
  exact dvd_mul_of_dvd_right hp _

/-- Every finite-support source maps to its actual exterior ideal. -/
def domainIdeal (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext)
    (side : Bool) (U : Finset (HeightOneSpectrum (𝓞 K)))
    (hU : U ∈ sideDomain K S (dyadicPool K Sset X.val) r₁ r₂ b₁ b₂ side) : Ext :=
  ⟨nonzeroProduct U, sideDomain_exterior K S D X r₁ r₂ b₁ b₂ side U hU⟩

include D in
/-- Both directions use the original complete dyadic source pool. -/
theorem sideDomain_primeSupport_iff (X : {r : ℝ // 0 < r})
    (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (u : Ext) (hu : Squarefree u.val.val) :
    primeSupport u.val ∈ sideDomain K S (dyadicPool K Sset X.val) r₁ r₂ b₁ b₂ side ↔
      u ∈ dyadicPool K Sset (residualScale K S X r₁ r₂ b₁ b₂ side).val ∧
        Disjoint (primeSupport u.val) (blockedSupport K S r₁ r₂ b₁ b₂) := by
  constructor
  · intro hU
    have hh := domain_height_window K S D X r₁ r₂ b₁ b₂ side _ hU
    rw [primeProduct_support u.val hu] at hh
    refine ⟨(mem_dyadicPool K Sset _ u).mpr ⟨hu, hh⟩, ?_⟩
    cases side <;> exact (Finset.mem_filter.mp hU).2.1
  · rintro ⟨huN, hd⟩
    let A := extractedSupportSide K S r₁ r₂ b₁ b₂ side
    let C := CanonicalFirstEnergy.commonSupport K S r₁ r₂ b₁ b₂
    let n := exteriorMul K Sset
      (CanonicalIdealRow.toExterior K S (extractedFactor K S r₁ r₂ b₁ b₂ side)) u
    have hr : (nonzeroProduct (Supports.restore A C (primeSupport u.val))).val =
        n.val.val := by
      rw [show (nonzeroProduct (Supports.restore A C (primeSupport u.val))).val =
        primeProduct (Supports.restore A C (primeSupport u.val)) from rfl,
        restore_product K S D r₁ r₂ b₁ b₂ side _ hd, primeProduct_support u.val hu]
      rfl
    have hn : n ∈ dyadicPool K Sset X.val := by
      obtain ⟨_, hlo, hhi⟩ := (mem_dyadicPool K Sset _ u).mp huN
      have hE : 0 < ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ) := by
        exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors
          (extractedFactor K S r₁ r₂ b₁ b₂ side).val
      have hnheight : height K Sset n =
          ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ) * height K Sset u :=
        height_mul K Sset _ u
      refine (mem_dyadicPool K Sset X.val n).mpr ⟨?_, ?_, ?_⟩
      · rw [← hr]
        exact squarefree_primeProduct _
      · rw [hnheight]
        exact (div_le_iff₀ hE).mp hlo |>.trans_eq (mul_comm _ _)
      · rw [hnheight]
        have hb := (le_div_iff₀ hE).mp
          (show height K Sset u ≤ (2 * X.val) /
            ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ) by
              convert hhi using 1 <;> dsimp only [residualScale] <;> ring)
        simpa only [mul_comm] using hb
    have hm : nonzeroProduct (Supports.restore A C (primeSupport u.val)) ∈
        nonzeroRange K S (dyadicPool K Sset X.val) :=
      Finset.mem_image.mpr ⟨n, hn, (Subtype.ext hr).symm⟩
    have hh := (mem_columnDomain_iff (nonzeroRange K S (dyadicPool K Sset X.val))
      (nonzeroRange_squarefree K S _ (fun n hn => dyadicPool_squarefree K Sset hn))
      (cubeSupport K S b₁ b₂) A C (primeSupport u.val)).mpr ⟨hd, hm⟩
    cases side <;> exact hh

def residualPool (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext) (side : Bool) : Finset Ext :=
  (dyadicPool K Sset (residualScale K S X r₁ r₂ b₁ b₂ side).val).filter
    (fun u => Disjoint (primeSupport u.val) (blockedSupport K S r₁ r₂ b₁ b₂))

include D in
/-- Exact finite reindexing from support columns to complete exterior
norm pools, retaining the sole frozen avoidance condition explicitly. -/
theorem sum_sideDomain (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext)
    (side : Bool) (F : NI → ℂ) :
    (∑ U ∈ sideDomain K S (dyadicPool K Sset X.val) r₁ r₂ b₁ b₂ side,
      F (nonzeroProduct U)) = ∑ u ∈ residualPool K S X r₁ r₂ b₁ b₂ side, F u.val := by
  apply Finset.sum_bij (fun U hU => domainIdeal K S D X r₁ r₂ b₁ b₂ side U hU)
  · intro U hU
    have hs : Squarefree (domainIdeal K S D X r₁ r₂ b₁ b₂ side U hU).val.val :=
      squarefree_primeProduct U
    apply Finset.mem_filter.mpr
    apply (sideDomain_primeSupport_iff K S D X r₁ r₂ b₁ b₂ side _ hs).mp
    simpa only [domainIdeal, primeSupport_nonzeroProduct] using hU
  · intro U hU V hV he
    have hp := congrArg (fun u : Ext => primeSupport u.val) he
    simpa only [domainIdeal, primeSupport_nonzeroProduct] using hp
  · intro u huN
    have hs := dyadicPool_squarefree K Sset (Finset.mem_filter.mp huN).1
    have hU := (sideDomain_primeSupport_iff K S D X r₁ r₂ b₁ b₂ side u hs).mpr
      (Finset.mem_filter.mp huN)
    refine ⟨primeSupport u.val, hU, ?_⟩
    apply Subtype.ext
    exact nonzeroProduct_support u.val hs
  · intro U hU
    rfl

/-- Actual squarefree division preserves both ends of the source
annulus, with the exact quotient norm and no extra range indicator. -/
theorem dyadic_multiples_eq (X : ℝ) (e : Ext) (he : Squarefree e.val.val) :
    (dyadicPool K Sset X).filter (fun n => e.val.val ∣ n.val.val) =
      ((dyadicPool K Sset (X / height K Sset e)).filter
        (fun u => IsCoprime e.val.val u.val.val)).image (exteriorMul K Sset e) := by
  ext n
  constructor
  · intro hn
    obtain ⟨hn, hdiv⟩ := Finset.mem_filter.mp hn
    let u := squarefreeQuotient K Sset n e hdiv
    have hm : exteriorMul K Sset e u = n := squarefreeQuotient_spec K Sset n e hdiv
    have hu := (exteriorMul_mem_dyadicPool K Sset X e u he).mp (hm.symm ▸ hn)
    exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr hu, hm⟩
  · intro hn
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_filter.mpr
      ⟨(exteriorMul_mem_dyadicPool K Sset X e u he).mpr (Finset.mem_filter.mp hu),
        dvd_mul_right _ _⟩

theorem sum_dyadic_multiples (X : ℝ) (e : Ext) (he : Squarefree e.val.val)
    (F : Ext → ℂ) :
    (∑ n ∈ dyadicPool K Sset X with e.val.val ∣ n.val.val, F n) =
      ∑ u ∈ dyadicPool K Sset (X / height K Sset e) with IsCoprime e.val.val u.val.val,
        F (exteriorMul K Sset e u) := by
  rw [dyadic_multiples_eq K S X e he]
  exact Finset.sum_image (fun _ _ _ _ h => exteriorMul_injective K Sset e h)

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstCompletePools

end
