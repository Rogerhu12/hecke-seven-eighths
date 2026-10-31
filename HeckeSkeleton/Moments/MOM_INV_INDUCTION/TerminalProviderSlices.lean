import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderBlockEnergy
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.GeneralReflectedEnergy

/-!
# Literal canonical atoms and the four component-class slices

Every zero from the original reflection remains in the ordinary hybrid
kernel or in the independently extended column coefficient. The active
mark weight has no row or dual-column argument. Class expansion is an
exact finite equality before any norm or large-sieve estimate is taken.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalSlices

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy
open HeckeSkeleton.LowEnergy.ActualReflection
  HeckeSkeleton.LowEnergy.ActualReflectionReindex
  HeckeSkeleton.LowEnergy.ActualFrozenIndependence
  HeckeSkeleton.LowEnergy.ActualHybridEntry
  HeckeSkeleton.LowEnergy.ActualSeparatedBlock
  HeckeSkeleton.LowEnergy.ActualSymbols
  HeckeSkeleton.LowEnergy.ClassSlices
  HeckeSkeleton.LowEnergy.ActualClassSlices
open TerminalMellin
open scoped Classical BigOperators nonZeroDivisors NumberField

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

local notation "Ext" => ExteriorIdeal K S

variable (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)

def entry (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : ℝ → ℂ)
    (X : ℝ) (k P c b : Ext) : ℂ :=
  inactiveWeight K S f * rowCoefficient K S D θ f s k *
    markCoefficient K S D θ f s P * columnCoefficient K S D θ f s c b *
    FiniteHybridIntegral.hybridKernel (cubicKernel K S D) (quadraticKernel K S D)
      k.val.val P.val.val c.val.val b.val.val *
    mellinReflectionKernel K S F θ (QuotientGroup.mk f.rowUnit)
      (blockFrequency (frozenClass K S D f s) (generatorLocalClass K S D k)
        (generatorLocalClass K S D P) (generatorLocalClass K S D c)
        (generatorLocalClass K S D b)) V 0
      (CommonMellin.argument (canonicalBase K S f s X)
        (exteriorNorm K S k) (exteriorNorm K S P)
        (exteriorNorm K S c) (exteriorNorm K S b))

theorem atom_eq_entry (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : ℝ → ℂ)
    (X : ℝ) (k P c b : Ext)
    (hk : RowAdmissible K S f k) (hP : MarkAdmissible K S f P) :
    GeneralReflectedEnergy.atom K S D f s F θ V X k P c b =
      entry K S D f s F θ V X k P c b := by
  have harg : X * exteriorNorm K S s.minimum * exteriorNorm K S c *
      exteriorNorm K S b ^ 3 /
      (exteriorNorm K S k * exteriorNorm K S (primeSetIdeal K S s.active) *
        exteriorNorm K S P) ^ 2 =
      CommonMellin.argument (canonicalBase K S f s X)
        (exteriorNorm K S k) (exteriorNorm K S P)
        (exteriorNorm K S c) (exteriorNorm K S b) := by
    unfold CommonMellin.argument canonicalBase
    field_simp [(exteriorNorm_pos K S k).ne', (exteriorNorm_pos K S P).ne',
      (exteriorNorm_pos K S (primeSetIdeal K S s.active)).ne']
    <;> ring
  by_cases hkP : IsCoprime k.val.val P.val.val
  · by_cases hcb : ColumnCondition K S s c b
    · by_cases hPb : IsCoprime P.val.val b.val.val
      · rw [GeneralReflectedEnergy.atom_eq_hybrid K S D hD f s F θ V X
          k P c b hk hP hkP hcb hPb, harg]
        simp only [entry, columnCoefficient, extendColumn, dif_pos hcb,
          hybridAtom, FiniteHybridIntegral.hybridKernel, KeepOriginalRow.mask,
          if_pos hkP, if_pos hPb, div_eq_mul_inv]
        ring
      · simp [GeneralReflectedEnergy.atom, hk, hP, hkP, hcb, hPb, entry,
          FiniteHybridIntegral.hybridKernel, KeepOriginalRow.mask]
    · simp [GeneralReflectedEnergy.atom, hk, hP, hkP, hcb, entry,
        columnCoefficient, extendColumn]
  · simp [GeneralReflectedEnergy.atom, hk, hP, hkP, entry,
      FiniteHybridIntegral.hybridKernel, KeepOriginalRow.mask]

def slicedEntry (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (q : FourClasses (SixthLocalClasses K S)) (V : ℝ → ℂ)
    (X : ℝ) (k P c b : Ext) : ℂ :=
  inactiveWeight K S f * ActualSeparatedBlock.slicedRow K S D f s θ q k *
    slicedMark K S D f s θ q P * slicedColumn K S D f s θ q c b *
    FiniteHybridIntegral.hybridKernel (cubicKernel K S D) (quadraticKernel K S D)
      k.val.val P.val.val c.val.val b.val.val *
    mellinReflectionKernel K S F θ (QuotientGroup.mk f.rowUnit)
      (blockFrequency (frozenClass K S D f s) q.1.1 q.1.2 q.2.1 q.2.2) V 0
      (CommonMellin.argument (canonicalBase K S f s X)
        (exteriorNorm K S k) (exteriorNorm K S P)
        (exteriorNorm K S c) (exteriorNorm K S b))

theorem entry_eq_slices [Fintype (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (θ : HeckeCharacter K) (V : ℝ → ℂ)
    (X : ℝ) (k P c b : Ext) :
    entry K S D f s F θ V X k P c b =
      ∑ q : FourClasses (SixthLocalClasses K S),
        slicedEntry K S D f s F θ q V X k P c b := by
  unfold entry
  rw [class_expansion
    (fun r m c' b' => mellinReflectionKernel K S F θ (QuotientGroup.mk f.rowUnit)
      (blockFrequency (frozenClass K S D f s) r m c' b') V 0
      (CommonMellin.argument (canonicalBase K S f s X)
        (exteriorNorm K S k) (exteriorNorm K S P)
        (exteriorNorm K S c) (exteriorNorm K S b)))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  unfold slicedEntry ActualSeparatedBlock.slicedRow slicedMark slicedColumn
  ring

def exteriorSlicedBlock (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (q : FourClasses (SixthLocalClasses K S)) (a : Ext → ℂ) (V : ℝ → ℂ)
    (X : ℝ) (ps cs bs : Finset Ext) (k : Ext) : ℂ :=
  ∑ P ∈ ps, ∑ c ∈ cs, ∑ b ∈ bs,
    a P * slicedEntry K S D f s F θ q V X k P c b

/-- Exact class decomposition of the original finite canonical block. -/
theorem block_eq_slices [Fintype (SixthLocalClasses K S)]
    (hD : AllowedGeneratorInput K S D)
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (a : Ext → ℂ) (V : ℝ → ℂ) (X : ℝ) (ps cs bs : Finset Ext) (k : Ext)
    (hk : RowAdmissible K S f k) (hps : ∀ P ∈ ps, MarkAdmissible K S f P) :
    GeneralReflectedEnergy.block K S D f s F θ a V X ps cs bs k =
      ∑ q : FourClasses (SixthLocalClasses K S),
        exteriorSlicedBlock K S D f s F θ q a V X ps cs bs k := by
  unfold GeneralReflectedEnergy.block exteriorSlicedBlock
  simp only [Finset.mul_sum]
  calc
    _ = ∑ P ∈ ps, ∑ c ∈ cs, ∑ b ∈ bs,
        ∑ q : FourClasses (SixthLocalClasses K S),
          a P * slicedEntry K S D f s F θ q V X k P c b := by
      apply Finset.sum_congr rfl
      intro P hP
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro b hb
      rw [atom_eq_entry K S D f s hD F θ V X k P c b hk (hps P hP),
        entry_eq_slices, Finset.mul_sum]
    _ = ∑ P ∈ ps, ∑ c ∈ cs, ∑ q : FourClasses (SixthLocalClasses K S),
        ∑ b ∈ bs, a P * slicedEntry K S D f s F θ q V X k P c b := by
      apply Finset.sum_congr rfl
      intro P hP
      apply Finset.sum_congr rfl
      intro c hc
      exact Finset.sum_comm
    _ = ∑ P ∈ ps, ∑ q : FourClasses (SixthLocalClasses K S),
        ∑ c ∈ cs, ∑ b ∈ bs, a P * slicedEntry K S D f s F θ q V X k P c b := by
      apply Finset.sum_congr rfl
      intro P hP
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Extension of the actual mark weight to ordinary ideals. -/
def ordinaryWeight (a : Ext → ℂ) (I : Ideal (𝓞 K)) : ℂ :=
  if h : IsExterior K S I then a (toExterior K S I h) else 0

theorem ordinaryWeight_on_exterior (a : Ext → ℂ) (I : Ext) :
    ordinaryWeight K S a I.val.val = a I := by
  rw [ordinaryWeight, dif_pos ⟨nonZeroDivisors.coe_ne_zero I.val, I.property⟩]
  rfl

theorem exteriorSlicedBlock_eq_ordinary
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (q : FourClasses (SixthLocalClasses K S)) (a : Ext → ℂ) (V : ℝ → ℂ)
    (X : ℝ) (ps cs bs : Finset Ext) (k : Ext) :
    exteriorSlicedBlock K S D f s F θ q a V X ps cs bs k =
      slicedCanonicalBlock K S D f s F θ q (ordinaryWeight K S a) V X
        (ps.image (fun I => I.val.val)) (cs.image (fun I => I.val.val))
        (bs.image (fun I => I.val.val)) k.val.val := by
  have hinj : Function.Injective (fun I : Ext => I.val.val) :=
    fun _ _ h => Subtype.ext (Subtype.ext h)
  unfold exteriorSlicedBlock slicedCanonicalBlock
  simp only [Finset.sum_image, hinj.injOn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro b hb
  rw [ordinaryWeight_on_exterior]
  simp only [ordinaryRow, ordinaryMark, ordinaryColumn,
    dif_pos (show IsExterior K S k.val.val from
      ⟨nonZeroDivisors.coe_ne_zero k.val, k.property⟩),
    dif_pos (show IsExterior K S P.val.val from
      ⟨nonZeroDivisors.coe_ne_zero P.val, P.property⟩),
    dif_pos (show IsExterior K S c.val.val from
      ⟨nonZeroDivisors.coe_ne_zero c.val, c.property⟩),
    dif_pos (show IsExterior K S b.val.val from
      ⟨nonZeroDivisors.coe_ne_zero b.val, b.property⟩),
    safeNorm_exterior, slicedEntry]
  ring

theorem block_eq_zero_of_row
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (a : Ext → ℂ) (V : ℝ → ℂ) (X : ℝ) (ps cs bs : Finset Ext) (k : Ext)
    (hk : ¬RowAdmissible K S f k) :
    GeneralReflectedEnergy.block K S D f s F θ a V X ps cs bs k = 0 := by
  simp [GeneralReflectedEnergy.block, GeneralReflectedEnergy.atom, hk]

/-- The original zero extensions justify all support filters used by
the two sieves. No nonzero term is added or deleted. -/
theorem block_eq_filter
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (a : Ext → ℂ) (V : ℝ → ℂ) (X : ℝ) (ps cs bs : Finset Ext) (k : Ext) :
    GeneralReflectedEnergy.block K S D f s F θ a V X ps cs bs k =
      GeneralReflectedEnergy.block K S D f s F θ a V X
        (ps.filter (MarkAdmissible K S f)) (cs.filter (fun c => Squarefree c.val.val)) bs k := by
  unfold GeneralReflectedEnergy.block
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hp : MarkAdmissible K S f P
  · rw [if_pos hp, Finset.sum_filter]
    congr 1
    apply Finset.sum_congr rfl
    intro c hc
    by_cases hsf : Squarefree c.val.val
    · simp only [if_pos hsf]
    · have hcb (b : Ext) : ¬ColumnCondition K S s c b := fun h => hsf h.1
      simp [if_neg hsf, GeneralReflectedEnergy.atom, hcb]
  · simp [if_neg hp, GeneralReflectedEnergy.atom, hp]

theorem block_energy_eq_filter
    (F : FiniteMellinData K S) (θ : HeckeCharacter K)
    (a : Ext → ℂ) (V : ℝ → ℂ) (X : ℝ) (rows ps cs bs : Finset Ext) :
    (∑ k ∈ rows,
      ‖GeneralReflectedEnergy.block K S D f s F θ a V X ps cs bs k‖ ^ 2) =
      ∑ k ∈ rows.filter (RowAdmissible K S f),
        ‖GeneralReflectedEnergy.block K S D f s F θ a V X
          (ps.filter (MarkAdmissible K S f)) (cs.filter (fun c => Squarefree c.val.val)) bs k‖ ^ 2 := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hr : RowAdmissible K S f k
  · rw [if_pos hr, block_eq_filter]
  · rw [if_neg hr, block_eq_zero_of_row K S D f s F θ a V X ps cs bs k hr]
    simp


/-- The original atom block inherits the actual canonical hybrid bound.
All finite supports are mapped injectively to their literal ordinary
ideals. The only class loss is the fixed fourth-power count twice. -/
theorem block_energy [Finite (SixthLocalClasses K S)]
    (F : FiniteMellinData K S) (hF : FiniteMellinAdmissible K S F)
    (θ : HeckeCharacter K) (hKernel : MellinKernelInput K S F θ)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (hD : AllowedGeneratorInput K S D)
    (hquadratic : ActualSieveDictionary.ExteriorQuadraticBound K S D)
    (hcubic : ActualSieveDictionary.ExteriorCubicBound K S D)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : FixedData K S) (s : FrozenState K S f.frozen f.puncture)
        (V : SmoothAnnularTest) (X Klo Plo Clo Blo Kup Pup Cup Bup : ℝ),
      0 < X → 0 < Klo → 0 < Plo → 0 < Clo → 0 < Blo →
      1 ≤ Kup → 1 ≤ Pup → 1 ≤ Cup → 1 ≤ Bup →
      ∀ rows ps cs bs : Finset Ext,
      (∀ k ∈ rows, RowAdmissible K S f k ∧ exteriorNorm K S k ≤ Kup) →
      (∀ P ∈ ps, MarkAdmissible K S f P ∧ exteriorNorm K S P ≤ Pup) →
      (∀ c ∈ cs, Squarefree c.val.val ∧ exteriorNorm K S c ≤ Cup) →
      (∀ b ∈ bs, exteriorNorm K S b ≤ Bup) →
      (∀ k ∈ rows, 1 ≤ exteriorNorm K S k / Klo ∧ exteriorNorm K S k / Klo ≤ 2) →
      (∀ P ∈ ps, 1 ≤ exteriorNorm K S P / Plo ∧ exteriorNorm K S P / Plo ≤ 2) →
      (∀ c ∈ cs, 1 ≤ exteriorNorm K S c / Clo ∧ exteriorNorm K S c / Clo ≤ 2) →
      (∀ b ∈ bs, 1 ≤ exteriorNorm K S b / Blo ∧ exteriorNorm K S b / Blo ≤ 2) →
      ∀ (a : Ext → ℂ) (amp : ℝ), 0 < amp →
      (∀ P ∈ ps, ‖a P‖ ≤ amp) →
      (∑ k ∈ rows, ‖GeneralReflectedEnergy.block K S D f s F θ a V.toFun X ps cs bs k‖ ^ 2) ≤
        C * amp ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
        ‖inactiveWeight K S f‖ ^ 2 *
        CommonMellinTail.scalar (canonicalScale K S f s X Klo Plo Clo Blo) ^ 2 *
        (stateMajorant K S s ^ 2 / (Clo * Blo ^ 2)) *
        (Kup * Cup * Bup * Pup) ^ eps * (Kup + Cup * Bup) * Bup *
        (Cup + Pup + (Cup * Pup) ^ (2 / 3 : ℝ)) := by
  classical
  letI : Fintype (SixthLocalClasses K S) := Fintype.ofFinite _
  obtain ⟨C, hC, hb⟩ := TerminalBlockEnergy.canonical_block_energy
    K S D F hF θ hKernel hθ hD hquadratic hcubic eps heps
  let nc : ℝ := Fintype.card (SixthLocalClasses K S)
  have hnc : 0 < nc := by
    dsimp [nc]
    exact_mod_cast Fintype.card_pos
  refine ⟨nc ^ 8 * C, mul_pos (pow_pos hnc _) hC, ?_⟩
  intro f s V X Klo Plo Clo Blo Kup Pup Cup Bup hX hK hP hCf hB
    hKu hPu hCu hBu rows ps cs bs hr hp hc hd hkr hpr hcr hbr a amp hamp ha
  have hext (I : Ext) : IsExterior K S I.val.val :=
    ⟨nonZeroDivisors.coe_ne_zero I.val, I.property⟩
  have hinj : Function.Injective (fun I : Ext => I.val.val) :=
    fun _ _ h => Subtype.ext (Subtype.ext h)
  let R := C * amp ^ 2 * testSeminorm V.toFun (ActualCommonMellinTail.order K 0) 2 ^ 2 *
    ‖inactiveWeight K S f‖ ^ 2 *
    CommonMellinTail.scalar (canonicalScale K S f s X Klo Plo Clo Blo) ^ 2 *
    (stateMajorant K S s ^ 2 / (Clo * Blo ^ 2)) *
    (Kup * Cup * Bup * Pup) ^ eps * (Kup + Cup * Bup) * Bup *
    (Cup + Pup + (Cup * Pup) ^ (2 / 3 : ℝ))
  have hs (q : FourClasses (SixthLocalClasses K S)) :
      (∑ k ∈ rows, ‖exteriorSlicedBlock K S D f s F θ q a V.toFun X ps cs bs k‖ ^ 2) ≤ R := by
    have hh := hb f s q V X Klo Plo Clo Blo Kup Pup Cup Bup
      hX hK hP hCf hB hKu hPu hCu hBu
      (rows.image (fun I => I.val.val)) (ps.image (fun I => I.val.val))
      (cs.image (fun I => I.val.val)) (bs.image (fun I => I.val.val))
      (by
        intro I hI
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hI
        exact ⟨hext k, (hr k hk).1.squarefree, (hr k hk).2⟩)
      (by
        intro I hI
        obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hI
        exact ⟨hext P, (hp P hP).1.squarefree, (hp P hP).2⟩)
      (by
        intro I hI
        obtain ⟨c, hc', rfl⟩ := Finset.mem_image.mp hI
        exact ⟨hext c, (hc c hc').1, (hc c hc').2⟩)
      (by
        intro I hI
        obtain ⟨b, hb', rfl⟩ := Finset.mem_image.mp hI
        exact ⟨hext b, hd b hb'⟩)
      (by
        intro I hI
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hI
        simpa only [safeNorm_exterior] using hkr k hk)
      (by
        intro I hI
        obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hI
        simpa only [safeNorm_exterior] using hpr P hP)
      (by
        intro I hI
        obtain ⟨c, hc', rfl⟩ := Finset.mem_image.mp hI
        simpa only [safeNorm_exterior] using hcr c hc')
      (by
        intro I hI
        obtain ⟨b, hb', rfl⟩ := Finset.mem_image.mp hI
        simpa only [safeNorm_exterior] using hbr b hb')
      (ordinaryWeight K S a) amp hamp
      (by
        intro I hI
        obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hI
        simpa only [ordinaryWeight_on_exterior] using ha P hP)
    simpa only [Finset.sum_image, hinj.injOn, ← exteriorSlicedBlock_eq_ordinary]
      using hh
  have he : ∀ k ∈ rows,
      GeneralReflectedEnergy.block K S D f s F θ a V.toFun X ps cs bs k =
        ∑ q : FourClasses (SixthLocalClasses K S),
          exteriorSlicedBlock K S D f s F θ q a V.toFun X ps cs bs k :=
    fun k hk => block_eq_slices K S D f s hD F θ a V.toFun X ps cs bs k
      (hr k hk).1 (fun P hP => (hp P hP).1)
  calc
    _ = ∑ k ∈ rows, ‖∑ q : FourClasses (SixthLocalClasses K S),
        exteriorSlicedBlock K S D f s F θ q a V.toFun X ps cs bs k‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [he k hk]
    _ ≤ nc ^ 4 * ∑ q : FourClasses (SixthLocalClasses K S),
        ∑ k ∈ rows, ‖exteriorSlicedBlock K S D f s F θ q a V.toFun X ps cs bs k‖ ^ 2 :=
      four_class_energy rows _
    _ ≤ nc ^ 4 * ∑ _q : FourClasses (SixthLocalClasses K S), R :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q _ => hs q)) (pow_nonneg hnc.le _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_fourClasses]
      push_cast
      dsimp [R, nc]
      ring

end HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalSlices

end
