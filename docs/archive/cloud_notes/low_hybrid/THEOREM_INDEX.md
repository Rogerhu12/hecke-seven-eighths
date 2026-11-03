# LOW-HYBRID / LOW-FROZEN-CUBE：全部源码定理签名索引

本索引逐字摘录新模块的全部 `theorem` / `lemma` 声明，包含明确标注的私有辅助定理。

每个代码块保留完整的源码级签名，并止于原有的 `:= by`；直接用证明项定义的定理止于 `:=`，不会伪造 `by` 或填入占位证明。源码级签名沿用对应文件的命名空间、类型变量和 section 假设；所有继承的 section 参数和类型类假设另由 Lean 直接展开导出至 `ELABORATED_TYPES.md`。

生成时间：2026-10-31T02:47:09+08:00。

共扫描 **80 个模块**，收录 **570 条公开定理/引理**；同时收录 **3 条私有辅助定理/引理**。

重跑命令：`python3 generate_theorem_index.py --final`。该脚本只读 Lean 源码，不调用编译器。

## 按模块计数

| 模块 | 公开定理/引理 | 私有辅助 |
|---|---:|---:|
| `HeckeSkeleton/LowHybrid.lean` | 0 | 0 |
| `HeckeSkeleton/LowHybrid/ArithmeticLosses.lean` | 10 | 0 |
| `HeckeSkeleton/LowHybrid/Assembly.lean` | 10 | 0 |
| `HeckeSkeleton/LowHybrid/BlockAdmissible.lean` | 12 | 0 |
| `HeckeSkeleton/LowHybrid/CanonicalInputs.lean` | 4 | 0 |
| `HeckeSkeleton/LowHybrid/CanonicalSupport.lean` | 9 | 0 |
| `HeckeSkeleton/LowHybrid/ColumnMass.lean` | 2 | 0 |
| `HeckeSkeleton/LowHybrid/CommonTactics.lean` | 0 | 0 |
| `HeckeSkeleton/LowHybrid/CompletedQuadratic.lean` | 10 | 0 |
| `HeckeSkeleton/LowHybrid/CompletedQuadraticBound.lean` | 4 | 0 |
| `HeckeSkeleton/LowHybrid/Corollaries.lean` | 2 | 0 |
| `HeckeSkeleton/LowHybrid/Counting.lean` | 6 | 0 |
| `HeckeSkeleton/LowHybrid/CountingBridge.lean` | 3 | 0 |
| `HeckeSkeleton/LowHybrid/CountingPositivity.lean` | 3 | 0 |
| `HeckeSkeleton/LowHybrid/DivisorEnvelope.lean` | 4 | 0 |
| `HeckeSkeleton/LowHybrid/Factorization.lean` | 34 | 0 |
| `HeckeSkeleton/LowHybrid/Global.lean` | 7 | 0 |
| `HeckeSkeleton/LowHybrid/Homogeneity.lean` | 11 | 0 |
| `HeckeSkeleton/LowHybrid/HybridEnergy.lean` | 1 | 0 |
| `HeckeSkeleton/LowHybrid/Losses.lean` | 5 | 0 |
| `HeckeSkeleton/LowHybrid/Masks.lean` | 9 | 0 |
| `HeckeSkeleton/LowHybrid/NaturalLosses.lean` | 2 | 0 |
| `HeckeSkeleton/LowHybrid/NormalForm.lean` | 8 | 1 |
| `HeckeSkeleton/LowHybrid/NormalFormAlgebra.lean` | 16 | 0 |
| `HeckeSkeleton/LowHybrid/NormalFormBound.lean` | 1 | 0 |
| `HeckeSkeleton/LowHybrid/NormalFormFinite.lean` | 8 | 0 |
| `HeckeSkeleton/LowHybrid/NormalFormKernels.lean` | 7 | 0 |
| `HeckeSkeleton/LowHybrid/NormalFormSupport.lean` | 8 | 0 |
| `HeckeSkeleton/LowHybrid/NormalFormUniform.lean` | 2 | 0 |
| `HeckeSkeleton/LowHybrid/Normalization.lean` | 7 | 0 |
| `HeckeSkeleton/LowHybrid/Parameters.lean` | 8 | 0 |
| `HeckeSkeleton/LowHybrid/PrimeArithmetic.lean` | 16 | 0 |
| `HeckeSkeleton/LowHybrid/PrimeDivisorBounds.lean` | 16 | 0 |
| `HeckeSkeleton/LowHybrid/ProductBounds.lean` | 14 | 0 |
| `HeckeSkeleton/LowHybrid/Rows.lean` | 1 | 0 |
| `HeckeSkeleton/LowHybrid/SieveBounds.lean` | 1 | 0 |
| `HeckeSkeleton/LowHybrid/SieveComposition.lean` | 8 | 0 |
| `HeckeSkeleton/LowHybrid/SquarefreeDivisors.lean` | 5 | 0 |
| `HeckeSkeleton/LowHybrid/SupportPower.lean` | 4 | 0 |
| `HeckeSkeleton/LowHybrid/Transpose.lean` | 3 | 0 |
| `HeckeSkeleton/LowHybrid/Weighted.lean` | 5 | 1 |
| `HeckeSkeleton/LowHybrid/WeightedSieveBounds.lean` | 3 | 1 |
| `HeckeSkeleton/LowFrozenCube.lean` | 0 | 0 |
| `HeckeSkeleton/LowFrozenCube/AggregateSource.lean` | 3 | 0 |
| `HeckeSkeleton/LowFrozenCube/Assembly.lean` | 6 | 0 |
| `HeckeSkeleton/LowFrozenCube/CoefficientSeparation.lean` | 5 | 0 |
| `HeckeSkeleton/LowFrozenCube/ColumnNormalization.lean` | 6 | 0 |
| `HeckeSkeleton/LowFrozenCube/FrozenBounds.lean` | 17 | 0 |
| `HeckeSkeleton/LowFrozenCube/FrozenCounts.lean` | 3 | 0 |
| `HeckeSkeleton/LowFrozenCube/FrozenPartition.lean` | 2 | 0 |
| `HeckeSkeleton/LowFrozenCube/FrozenReduction.lean` | 15 | 0 |
| `HeckeSkeleton/LowFrozenCube/FrozenSupportExtension.lean` | 4 | 0 |
| `HeckeSkeleton/LowFrozenCube/FullHybridBound.lean` | 2 | 0 |
| `HeckeSkeleton/LowFrozenCube/HybridExit.lean` | 2 | 0 |
| `HeckeSkeleton/LowFrozenCube/Ledger.lean` | 11 | 0 |
| `HeckeSkeleton/LowFrozenCube/LocalBudget.lean` | 7 | 0 |
| `HeckeSkeleton/LowFrozenCube/LocalCoefficients.lean` | 4 | 0 |
| `HeckeSkeleton/LowFrozenCube/LocalTable.lean` | 16 | 0 |
| `HeckeSkeleton/LowFrozenCube/Overlap.lean` | 10 | 0 |
| `HeckeSkeleton/LowFrozenCube/Phases.lean` | 14 | 0 |
| `HeckeSkeleton/LowFrozenCube/PowerfulCounting.lean` | 7 | 0 |
| `HeckeSkeleton/LowFrozenCube/PrimeCoordinates.lean` | 23 | 0 |
| `HeckeSkeleton/LowFrozenCube/PrimeProducts.lean` | 7 | 0 |
| `HeckeSkeleton/LowFrozenCube/Products.lean` | 6 | 0 |
| `HeckeSkeleton/LowFrozenCube/RawInput.lean` | 7 | 0 |
| `HeckeSkeleton/LowFrozenCube/RawRowBlockExit.lean` | 2 | 0 |
| `HeckeSkeleton/LowFrozenCube/RawSource.lean` | 6 | 0 |
| `HeckeSkeleton/LowFrozenCube/RowCoordinates.lean` | 23 | 0 |
| `HeckeSkeleton/LowFrozenCube/RowTableExit.lean` | 4 | 0 |
| `HeckeSkeleton/LowFrozenCube/Scale.lean` | 5 | 0 |
| `HeckeSkeleton/LowFrozenCube/SourceLedger.lean` | 5 | 0 |
| `HeckeSkeleton/LowFrozenCube/TableExit.lean` | 8 | 0 |
| `HeckeSkeleton/LowFrozenCube/TerminalSource.lean` | 2 | 0 |
| `HeckeSkeleton/LowFrozenCube/UniformAggregateSource.lean` | 3 | 0 |
| `HeckeSkeleton/LowFrozenCube/UniformAggregateTerminal.lean` | 3 | 0 |
| `HeckeSkeleton/LowFrozenCube/UniformSourceLedger.lean` | 2 | 0 |
| `HeckeSkeleton/LowFrozenCube/UniformTerminalSource.lean` | 2 | 0 |
| `HeckeSkeleton/LowFrozenCube/UniformWeightedHybridBound.lean` | 1 | 0 |
| `HeckeSkeleton/LowFrozenCube/Valuations.lean` | 37 | 0 |
| `HeckeSkeleton/LowFrozenCube/WeightedHybridBound.lean` | 1 | 0 |
| **总计** | **570** | **3** |

## HeckeSkeleton/LowHybrid.lean

源码 SHA-256：`68f23703df12859337888610f4b44b2eb0c42169d55866bb378c990fdd8c8b1f`。

此模块为入口或组织模块，没有新增公开定理声明。

## HeckeSkeleton/LowHybrid/ArithmeticLosses.lean

源码 SHA-256：`d679f7b7ab6eb4ef2bfd09ae2c5898251ed283bf6d0269a45afcdafe97fd557f`。

### finite_nat_norms_of_linear_counting

源码起始行：22。

```lean
theorem finite_nat_norms_of_linear_counting
    {I : Type*} (q : I → ℕ) (C : ℝ) (hcount : LinearNormCounting q C)
    (N : ℕ) : Set.Finite {i : I | q i ≤ N} := by
```

### finite_real_norms_of_linear_counting

源码起始行：35。

```lean
theorem finite_real_norms_of_linear_counting
    {I : Type*} (q : I → ℕ) (normI : I → ℝ)
    (hnorm : ∀ i, normI i = (q i : ℝ)) (C : ℝ)
    (hcount : LinearNormCounting q C) (X : ℝ) :
    Set.Finite {i : I | normI i ≤ X} := by
```

### one_le_real_norm_of_natural

源码起始行：47。

```lean
theorem one_le_real_norm_of_natural
    {I : Type*} (q : I → ℕ) (normI : I → ℝ)
    (hnorm : ∀ i, normI i = (q i : ℝ)) (hq : ∀ i, 1 ≤ q i) :
    ∀ i, 1 ≤ normI i := by
```

### harmonicEnvelope_nonneg

源码起始行：59。

```lean
theorem harmonicEnvelope_nonneg (C : ℝ) (hC : 0 ≤ C) (X : ℝ) (hX : 1 ≤ X) :
    0 ≤ harmonicEnvelope C X := by
```

### harmonicEnvelope_subpower

源码起始行：64。

```lean
theorem harmonicEnvelope_subpower (C : ℝ) (hC : 0 < C) :
    SubpowerBound (harmonicEnvelope C) := by
```

### reciprocal_sum_le_harmonicEnvelope

源码起始行：70。

```lean
theorem reciprocal_sum_le_harmonicEnvelope
    {I : Type*} (q : I → ℕ) (normI : I → ℝ)
    (hnorm : ∀ i, normI i = (q i : ℝ)) (C : ℝ) (hC : 0 ≤ C)
    (hq : ∀ i : I, 1 ≤ q i) (hcount : LinearNormCounting q C)
    (X : ℝ) (hX : 1 ≤ X) (s : Finset I)
    (hs : ∀ i ∈ s, normI i ≤ X) :
    (∑ i ∈ s, 1 / normI i) ≤ harmonicEnvelope C X := by
```

### divisorEnvelopeOfCounting_nonneg

源码起始行：97。

```lean
theorem divisorEnvelopeOfCounting_nonneg (X : ℝ) :
    0 ≤ divisorEnvelopeOfCounting coords normI q hnorm Ccount hcount X :=
```

### divisor_count_le_envelopeOfCounting

源码起始行：101。

```lean
theorem divisor_count_le_envelopeOfCounting (X : ℝ) (a : A) (ha : normI a ≤ X) :
    ((PrimeArithmetic.divisors coords a).card : ℝ) ≤
      divisorEnvelopeOfCounting coords normI q hnorm Ccount hcount X :=
```

### divisorEnvelopeOfCounting_subpower

源码起始行：106。

```lean
theorem divisorEnvelopeOfCounting_subpower (hq : ∀ a : A, 1 ≤ q a) :
    SubpowerBound (divisorEnvelopeOfCounting coords normI q hnorm Ccount hcount) := by
```

### natural_arithmetic_loss_subpower_of_counting

源码起始行：116。

```lean
theorem natural_arithmetic_loss_subpower_of_counting
    (hCcount : 0 < Ccount) (hq : ∀ a : A, 1 ≤ q a)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ eta C : ℝ, 0 < eta ∧ 0 < C ∧
      ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
        naturalHybridArithmeticLoss
          (divisorEnvelopeOfCounting coords normI q hnorm Ccount hcount)
          (harmonicEnvelope Ccount) eta K N B L ≤ C * (K * N * B * L) ^ eps := by
```

## HeckeSkeleton/LowHybrid/Assembly.lean

源码 SHA-256：`bfbc0a1cb47dbde64240f318bcc9cfacdc12d43336b42ace31b6717a18cdb456`。

### row_local_cauchy

源码起始行：28。

```lean
theorem row_local_cauchy {K D : Type*}
    (rows : Finset K) (localBlocks : K → Finset D)
    (mu value : K → D → ℂ) (Delta : ℝ)
    (hmu : ∀ k ∈ rows, ∀ d ∈ localBlocks k, ‖mu k d‖ ≤ 1)
    (hcard : ∀ k ∈ rows, ((localBlocks k).card : ℝ) ≤ Delta) :
    (∑ k ∈ rows, ‖∑ d ∈ localBlocks k, mu k d * value k d‖ ^ 2) ≤
      Delta * ∑ k ∈ rows, ∑ d ∈ localBlocks k, ‖value k d‖ ^ 2 := by
```

### row_local_positive_transpose

源码起始行：45。

```lean
theorem row_local_positive_transpose {K D : Type*}
    [DecidableEq K] [DecidableEq D]
    (rows : Finset K) (localBlocks : K → Finset D) (blocks : Finset D)
    (E : K → D → ℝ)
    (hmap : ∀ k ∈ rows, ∀ d ∈ localBlocks k, d ∈ blocks) :
    (∑ k ∈ rows, ∑ d ∈ localBlocks k, E k d) =
      ∑ d ∈ blocks, ∑ k ∈ rows with d ∈ localBlocks k, E k d := by
```

### row_local_weighted_cauchy

源码起始行：71。

```lean
theorem row_local_weighted_cauchy {K D : Type*}
    [DecidableEq K] [DecidableEq D]
    (rows : Finset K) (localBlocks : K → Finset D) (blocks : Finset D)
    (mu : K → D → ℂ) (weight : D → ℂ) (value : K → D → ℂ)
    (Delta : ℝ)
    (hmu : ∀ k ∈ rows, ∀ d ∈ localBlocks k, ‖mu k d‖ ≤ 1)
    (hcard : ∀ k ∈ rows, ((localBlocks k).card : ℝ) ≤ Delta)
    (hmap : ∀ k ∈ rows, ∀ d ∈ localBlocks k, d ∈ blocks) :
    (∑ k ∈ rows,
      ‖∑ d ∈ localBlocks k, mu k d * (weight d * value k d)‖ ^ 2) ≤
      Delta * ∑ d ∈ blocks,
        ‖weight d‖ ^ 2 * ∑ k ∈ rows with d ∈ localBlocks k, ‖value k d‖ ^ 2 := by
```

### row_local_weighted_cauchy_of_block_bounds

源码起始行：102。

```lean
theorem row_local_weighted_cauchy_of_block_bounds {K D : Type*}
    [DecidableEq K] [DecidableEq D]
    (rows : Finset K) (localBlocks : K → Finset D) (blocks : Finset D)
    (mu : K → D → ℂ) (weight : D → ℂ) (value : K → D → ℂ)
    (Delta : ℝ) (bound : D → ℝ) (hDelta : 0 ≤ Delta)
    (hmu : ∀ k ∈ rows, ∀ d ∈ localBlocks k, ‖mu k d‖ ≤ 1)
    (hcard : ∀ k ∈ rows, ((localBlocks k).card : ℝ) ≤ Delta)
    (hmap : ∀ k ∈ rows, ∀ d ∈ localBlocks k, d ∈ blocks)
    (hblock : ∀ d ∈ blocks,
      (∑ k ∈ rows with d ∈ localBlocks k, ‖value k d‖ ^ 2) ≤ bound d) :
    (∑ k ∈ rows,
      ‖∑ d ∈ localBlocks k, mu k d * (weight d * value k d)‖ ^ 2) ≤
      Delta * ∑ d ∈ blocks, ‖weight d‖ ^ 2 * bound d := by
```

### two_row_local_cauchy

源码起始行：124。

```lean
theorem two_row_local_cauchy {K D R : Type*}
    (rows : Finset K) (outer : K → Finset D) (inner : K → D → Finset R)
    (mu : K → D → ℂ) (nu value : K → D → R → ℂ)
    (DeltaD DeltaR : ℝ) (hDeltaD : 0 ≤ DeltaD)
    (hmu : ∀ k ∈ rows, ∀ d ∈ outer k, ‖mu k d‖ ≤ 1)
    (hnu : ∀ k ∈ rows, ∀ d ∈ outer k, ∀ r ∈ inner k d, ‖nu k d r‖ ≤ 1)
    (hcardD : ∀ k ∈ rows, ((outer k).card : ℝ) ≤ DeltaD)
    (hcardR : ∀ k ∈ rows, ∀ d ∈ outer k, ((inner k d).card : ℝ) ≤ DeltaR) :
    (∑ k ∈ rows, ‖∑ d ∈ outer k, mu k d *
      (∑ r ∈ inner k d, nu k d r * value k d r)‖ ^ 2) ≤
      DeltaD * DeltaR *
        ∑ k ∈ rows, ∑ d ∈ outer k, ∑ r ∈ inner k d, ‖value k d r‖ ^ 2 := by
```

### weighted_positive_fiber_sum_le

源码起始行：163。

```lean
theorem weighted_positive_fiber_sum_le {X Y : Type*} [DecidableEq Y]
    (source : Finset X) (target : Finset Y) (phi : X → Y)
    (weight : X → ℝ) (E : Y → ℝ) (W : ℝ)
    (hmap : ∀ x ∈ source, phi x ∈ target)
    (hE : ∀ y ∈ target, 0 ≤ E y)
    (hfiber : ∀ y ∈ target, (∑ x ∈ source with phi x = y, weight x) ≤ W) :
    (∑ x ∈ source, weight x * E (phi x)) ≤ W * ∑ y ∈ target, E y := by
```

### weighted_column_mass_mono

源码起始行：189。

```lean
theorem weighted_column_mass_mono {D Q : Type*}
    (blocks : Finset D) (columns : D → Finset Q)
    (weight : D → ℝ) (normQ : Q → ℝ) (a b : D → Q → ℂ)
    (hw : ∀ d ∈ blocks, 0 ≤ weight d)
    (hn : ∀ d ∈ blocks, ∀ q ∈ columns d, 0 ≤ normQ q)
    (hab : ∀ d ∈ blocks, ∀ q ∈ columns d, ‖a d q‖ ≤ ‖b d q‖) :
    (∑ d ∈ blocks, weight d * ∑ q ∈ columns d, ‖a d q‖ ^ 2 / normQ q) ≤
      ∑ d ∈ blocks, weight d * ∑ q ∈ columns d, ‖b d q‖ ^ 2 / normQ q := by
```

### factorized_column_mass_le

源码起始行：209。

```lean
theorem factorized_column_mass_le {D Q P : Type*}
    [DecidableEq D] [DecidableEq Q] [DecidableEq P]
    (blocks : Finset D) (columns : D → Finset Q) (target : Finset P)
    (product : D → Q → P) (normD : D → ℝ) (normQ : Q → ℝ) (normP : P → ℝ)
    (a : P → ℂ) (multiplicity : ℝ)
    (hD : ∀ d ∈ blocks, 0 < normD d)
    (hQ : ∀ d ∈ blocks, ∀ q ∈ columns d, 0 < normQ q)
    (hP : ∀ p ∈ target, 0 < normP p)
    (hmap : ∀ d ∈ blocks, ∀ q ∈ columns d, product d q ∈ target)
    (hnorm : ∀ d ∈ blocks, ∀ q ∈ columns d,
      normP (product d q) = normD d * normQ q)
    (hfiber : ∀ p ∈ target,
      (((blocks.sigma columns).filter fun dq => product dq.1 dq.2 = p).card : ℝ) ≤
        multiplicity) :
    (∑ d ∈ blocks, (1 / normD d) *
      ∑ q ∈ columns d, ‖a (product d q)‖ ^ 2 / normQ q) ≤
      multiplicity * ∑ p ∈ target, ‖a p‖ ^ 2 / normP p := by
```

### weighted_row_fiber_sieve

源码起始行：249。

```lean
theorem weighted_row_fiber_sieve {X Y P : Type*} [DecidableEq Y]
    (source : Finset X) (target : Finset Y) (columns : Finset P)
    (phi : X → Y) (chi : P → Y → ℂ) (a : P → ℂ) (beta : X → ℂ)
    (W S : ℝ) (hW : 0 ≤ W)
    (hmap : ∀ x ∈ source, phi x ∈ target)
    (hfiber : ∀ y ∈ target, (∑ x ∈ source with phi x = y, ‖beta x‖ ^ 2) ≤ W)
    (hsieve : ∀ u : P → ℂ,
      (∑ y ∈ target, ‖∑ p ∈ columns, u p * chi p y‖ ^ 2) ≤
        S * ∑ p ∈ columns, ‖u p‖ ^ 2) :
    (∑ x ∈ source,
      ‖beta x * (∑ p ∈ columns, a p * chi p (phi x))‖ ^ 2) ≤
      W * S * ∑ p ∈ columns, ‖a p‖ ^ 2 := by
```

### assembled_blocks_energy_of_two_sieves

源码起始行：279。

```lean
theorem assembled_blocks_energy_of_two_sieves
    {K D M H C J P : Type*}
    [DecidableEq K] [DecidableEq D] [DecidableEq M]
    [DecidableEq H] [DecidableEq C] [DecidableEq J]
    (rows : Finset K) (localBlocks : K → Finset D) (blocks : Finset D)
    (pairs : D → Finset (M × H)) (cset : D → M → Finset C)
    (hset : D → Finset H) (mc : D → Finset (M × C))
    (jset : D → Finset J) (pset : D → Finset P)
    (q : D → K → M × H → ℂ) (phi : D → M × C → J)
    (chi : D → P → J → ℂ)
    (a : D → H → P → ℂ) (beta : D → C → M → H → ℂ)
    (mu : K → D → ℂ) (weight : D → ℂ)
    (Q S Cbound Fbound Ebound : D → ℝ) (Delta : ℝ)
    (hDelta : 0 ≤ Delta)
    (hmu : ∀ k ∈ rows, ∀ d ∈ localBlocks k, ‖mu k d‖ ≤ 1)
    (hcard : ∀ k ∈ rows, ((localBlocks k).card : ℝ) ≤ Delta)
    (hblockMap : ∀ k ∈ rows, ∀ d ∈ localBlocks k, d ∈ blocks)
    (hQ : ∀ d ∈ blocks, 0 ≤ Q d)
    (hS : ∀ d ∈ blocks, 0 ≤ S d)
    (hC : ∀ d ∈ blocks, 0 ≤ Cbound d)
    (hF : ∀ d ∈ blocks, 0 ≤ Fbound d)
    (hcount : ∀ d ∈ blocks, ∀ u ∈ pairs d,
      ((cset d u.1).card : ℝ) ≤ Cbound d)
    (hbeta : ∀ d ∈ blocks, ∀ u ∈ pairs d, ∀ c ∈ cset d u.1,
      ‖beta d c u.1 u.2‖ ≤ 1)
    (hh : ∀ d ∈ blocks, ∀ u ∈ pairs d, u.2 ∈ hset d)
    (hmc : ∀ d ∈ blocks, ∀ u ∈ pairs d, ∀ c ∈ cset d u.1,
      (u.1, c) ∈ mc d)
    (hmap : ∀ d ∈ blocks, ∀ u ∈ mc d, phi d u ∈ jset d)
    (hfiber : ∀ d ∈ blocks, ∀ j ∈ jset d,
      (((mc d).filter fun u => phi d u = j).card : ℝ) ≤ Fbound d)
    (hcoef : ∀ d ∈ blocks, ∀ h ∈ hset d,
      (∑ p ∈ pset d, ‖a d h p‖ ^ 2) ≤ Ebound d)
    (hquadratic : ∀ d ∈ blocks, ∀ f : M × H → ℂ,
      (∑ k ∈ rows with d ∈ localBlocks k,
        ‖∑ u ∈ pairs d, q d k u * f u‖ ^ 2) ≤
        Q d * ∑ u ∈ pairs d, ‖f u‖ ^ 2)
    (hcubic : ∀ d ∈ blocks, ∀ u : P → ℂ,
      (∑ j ∈ jset d, ‖∑ p ∈ pset d, u p * chi d p j‖ ^ 2) ≤
        S d * ∑ p ∈ pset d, ‖u p‖ ^ 2) :
    (∑ k ∈ rows, ‖∑ d ∈ localBlocks k, mu k d * (weight d *
      (∑ u ∈ pairs d, q d k u *
        (∑ c ∈ cset d u.1, beta d c u.1 u.2 *
          (∑ p ∈ pset d, a d u.2 p * chi d p (phi d (u.1, c))))))‖ ^ 2) ≤
      Delta * ∑ d ∈ blocks, ‖weight d‖ ^ 2 *
        (Q d * Cbound d * ((hset d).card : ℝ) * Fbound d * S d * Ebound d) := by
```

## HeckeSkeleton/LowHybrid/BlockAdmissible.lean

源码 SHA-256：`74d0bb1e94acc9ab3777444f50eca4672ff49ecb42f78abb2d9b45ae231091e7`。

### norm_quadratic_le_one

源码起始行：24。

```lean
theorem norm_quadratic_le_one (x y : I) : ‖S.quadratic x y‖ ≤ 1 := by
```

### norm_cubic_le_one

源码起始行：30。

```lean
theorem norm_cubic_le_one (x y : I) : ‖S.cubic x y‖ ≤ 1 :=
```

### norm_mask_le_one

源码起始行：33。

```lean
theorem norm_mask_le_one (x y : I) : ‖S.mask x y‖ ≤ 1 :=
```

### norm_firstBeta_le

源码起始行：36。

```lean
theorem norm_firstBeta_le (beta : I → I → ℂ) (d n b : I) :
    ‖S.firstBeta beta d n b‖ ≤ ‖beta n b‖ := by
```

### norm_blockBetaCore_le

源码起始行：42。

```lean
theorem norm_blockBetaCore_le (beta : I → I → ℂ) (d r t c m h : I) :
    ‖S.blockBetaCore beta d r t c m h‖ ≤ ‖beta (r * c * m) (r * c * h * t ^ 2)‖ :=
```

### norm_blockBeta_le_one

源码起始行：47。

```lean
theorem norm_blockBeta_le_one {columns cubes : Finset I}
    (C : Completion columns cubes) (beta : I → I → ℂ)
    (hbeta : ∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ 1) (d r t c m h : I) :
    ‖S.blockBeta beta C.support d r t c m h‖ ≤ 1 := by
```

### columnMass_nonneg

源码起始行：60。

```lean
theorem columnMass_nonneg (a : I → ℂ) (marks : Finset I) (d : I) :
    0 ≤ S.columnMass a marks d := by
```

### blockA_mass_le

源码起始行：64。

```lean
theorem blockA_mass_le (hnorm : ∀ x, 1 ≤ S.normI x)
    (a : I → ℂ) (marks : Finset I) (d r t h : I) :
    (∑ p ∈ S.markQuotients marks d, ‖S.blockA a d r t h p‖ ^ 2) ≤
      S.columnMass a marks d := by
```

### blockBeta_budget

源码起始行：75。

```lean
theorem blockBeta_budget {columns cubes : Finset I}
    (C : Completion columns cubes) (hnorm : ∀ x, 1 ≤ S.normI x)
    (beta : I → I → ℂ)
    (hbeta : ∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ 1)
    (B : ℝ) (hB : 0 ≤ B) (hcubes : ∀ b ∈ cubes, S.normI b ≤ B)
    (d r t c m h : I) :
    S.normI t * S.normI c * ‖S.blockBeta beta C.support d r t c m h‖ ^ 2 ≤
      (B / S.normI r) / (S.normI t * S.normI h) := by
```

### quotientTwice_reconstruct

源码起始行：96。

```lean
theorem quotientTwice_reconstruct (d r k : I)
    (hd : d ∈ S.divisors k) (hr : r ∈ S.divisors (S.quotient d k)) :
    (d * r) * S.quotientTwice d r k = k := by
```

### quotientTwice_injOn

源码起始行：103。

```lean
theorem quotientTwice_injOn (rows : Finset I) (d r : I)
    (hdiv : ∀ k ∈ rows, d ∈ S.divisors k ∧ r ∈ S.divisors (S.quotient d k)) :
    Set.InjOn (S.quotientTwice d r) (rows : Set I) := by
```

### weightedBlock_admissible_from_sieves

源码起始行：115。

```lean
theorem weightedBlock_admissible_from_sieves (sf : I → Prop)
    (hnorm : ∀ x, 1 ≤ S.normI x)
    (hq : QuadraticSieveInput S.normI sf S.symbol)
    (hc : CubicSieveInput S.normI sf S.symbol)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ Cq Cc : ℝ, 0 < Cq ∧ 0 < Cc ∧
    ∀ K Y N L : ℝ, 1 ≤ K → 1 ≤ Y → 1 ≤ N → 1 ≤ L →
    ∀ (rows marks columns cubes ts cs ms hs qset jset : Finset I)
      (C : Completion columns cubes)
      (goodPairs goodMC : Finset (I × I)) (a : I → ℂ) (beta : I → I → ℂ)
      (d r : I) (B Dq Dc : ℝ),
      0 ≤ B → 0 ≤ Dq → 0 ≤ Dc →
      (∀ k ∈ rows, d ∈ S.divisors k ∧ r ∈ S.divisors (S.quotient d k)) →
      (∀ k ∈ rows, sf (S.quotientTwice d r k) ∧ S.normI (S.quotientTwice d r k) ≤ K) →
      (∀ j ∈ qset, sf j ∧ S.normI j ≤ Y) →
      (∀ j ∈ jset, sf j ∧ S.normI j ≤ N) →
      (∀ p ∈ S.markQuotients marks d, sf p ∧ S.normI p ≤ L) →
      goodPairs ⊆ ms ×ˢ hs → goodMC ⊆ ms ×ˢ cs →
      (∀ u ∈ goodPairs, u.1 * u.2 ∈ qset) →
      (∀ j ∈ qset, ((goodPairs.filter fun u => u.1 * u.2 = j).card : ℝ) ≤ Dq) →
      (∀ u ∈ goodMC, u.2 * u.1 ∈ jset) →
      (∀ j ∈ jset, ((goodMC.filter fun u => u.2 * u.1 = j).card : ℝ) ≤ Dc) →
      (∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ 1) →
      (∀ b ∈ cubes, S.normI b ≤ B) →
      (S.weightedBlock a beta marks C.support ts cs ms hs goodPairs goodMC d r).Admissible
        rows (Cq * (K * Y) ^ eta * (K + Y) * Dq)
        (Cc * (N * L) ^ eta * (N + L + (N * L) ^ (2 / 3 : ℝ)) * Dc)
        (B / S.normI r) (S.columnMass a marks d) := by
```

## HeckeSkeleton/LowHybrid/CanonicalInputs.lean

源码 SHA-256：`5779041c1ae73dacce59cc1237657d7f84f72c96e8ab1cf697780d3e6ca09ad2`。

### arithmetic_quotient_dvd

源码起始行：40。

```lean
theorem arithmetic_quotient_dvd (S : Arithmetic A) (d k : A) (hd : d ∣ k) :
    S.quotient d k ∣ k := by
```

### divisor_pair_norms

源码起始行：46。

```lean
theorem divisor_pair_norms (S : Arithmetic A) (hnorm : ∀ x, 1 ≤ S.normI x)
    {d r k : A} (h : (d, r) ∈ S.divisorPairs k) :
    S.normI d ≤ S.normI k ∧ S.normI r ≤ S.normI k := by
```

### divisor_pair_count_le

源码起始行：55。

```lean
theorem divisor_pair_count_le (S : Arithmetic A)
    (hnorm : ∀ x, 1 ≤ S.normI x) (hdiv : S.divisors = divisors coords)
    (cutoff : ℝ → Finset A)
    (hmem : ∀ X a, a ∈ cutoff X ↔ S.normI a ≤ X)
    (K : ℝ) (k : A) (hk : S.normI k ≤ K) :
    ((S.divisorPairs k).card : ℝ) ≤
      divisorCountEnvelope cutoff (divisors coords) K ^ 2 := by
```

### canonical_finite_inputs

源码起始行：79。

```lean
theorem canonical_finite_inputs
    (S : Arithmetic A) (hnorm : ∀ x, 1 ≤ S.normI x)
    (hdiv : S.divisors = divisors coords)
    (cutoff : ℝ → Finset A)
    (hmem : ∀ X a, a ∈ cutoff X ↔ S.normI a ≤ X)
    (K N B L : ℝ) (rows marks columns cubes : Finset A)
    (hrows : ∀ k ∈ rows, Squarefree coords k ∧ S.normI k ≤ K)
    (hmarks : ∀ p ∈ marks, Squarefree coords p ∧ S.normI p ≤ L)
    (hcolumns : ∀ n ∈ columns, Squarefree coords n ∧ S.normI n ≤ N)
    (hcubes : ∀ b ∈ cubes, S.normI b ≤ B) :
    S.FiniteInputs (Squarefree coords) rows marks columns cubes
      (cutoff K) (cutoff K) (completion coords columns cubes)
      (fun _ _ => cutoff B) (fun _ _ => cutoff N)
      (fun _ _ => cutoff N) (fun _ _ => cutoff B)
      (fun _ _ => quadraticPairs coords S cutoff N B)
      (fun _ _ => cubicPairs coords S cutoff N)
      (squarefreeCutoff coords cutoff (N * B)) (squarefreeCutoff coords cutoff N)
      K (N * B) N L
      (divisorCountEnvelope cutoff (divisors coords) K ^ 2)
      (divisorCountEnvelope cutoff (divisors coords) (N * B))
      (divisorCountEnvelope cutoff (divisors coords) N)
      (cutoffHarmonic S cutoff B) (cutoffHarmonic S cutoff N)
      (cutoffHarmonic S cutoff B) := by
```

## HeckeSkeleton/LowHybrid/CanonicalSupport.lean

源码 SHA-256：`8dd3196ae28103d4439ae6e9f028419cab62c653f75a601a617c06be58190510`。

### fromSupport_support_of_squarefree

源码起始行：24。

```lean
theorem fromSupport_support_of_squarefree {a : A} (ha : Squarefree coords a) :
    fromSupport coords (support coords a) = a := by
```

### support_subset_of_dvd

源码起始行：37。

```lean
theorem support_subset_of_dvd {a b : A} (h : a ∣ b) :
    support coords a ⊆ support coords b := by
```

### mem_divisors_of_squarefree_dvd

源码起始行：44。

```lean
theorem mem_divisors_of_squarefree_dvd {a d : A}
    (hsf : Squarefree coords d) (hd : d ∣ a) : d ∈ divisors coords a := by
```

### canonical_support_residual_squarefree

源码起始行：50。

```lean
theorem canonical_support_residual_squarefree
    {columns cubes : Finset A} (hcolumns : ∀ n ∈ columns, Squarefree coords n)
    {v : CompletedIndex A} (hv : v ∈ (completion coords columns cubes).support) :
    Squarefree coords (v.2.2.1 * v.2.2.2) := by
```

### canonical_block_residual_squarefree

源码起始行：58。

```lean
theorem canonical_block_residual_squarefree (S : Arithmetic A)
    {columns cubes : Finset A} (hcolumns : ∀ n ∈ columns, Squarefree coords n)
    {r : A} {v : CompletedIndex A}
    (hv : v ∈ S.blockSupport (completion coords columns cubes).support r) :
    Squarefree coords (v.2.2.1 * v.2.2.2) := by
```

### arithmetic_norm_le_of_dvd

源码起始行：67。

```lean
theorem arithmetic_norm_le_of_dvd (S : Arithmetic A)
    (hnorm : ∀ x, 1 ≤ S.normI x) {a b : A} (h : a ∣ b) :
    S.normI a ≤ S.normI b := by
```

### canonical_block_bounds

源码起始行：77。

```lean
theorem canonical_block_bounds (S : Arithmetic A)
    (hnorm : ∀ x, 1 ≤ S.normI x)
    {columns cubes : Finset A} (N B : ℝ)
    (hcolumns : ∀ n ∈ columns, Squarefree coords n ∧ S.normI n ≤ N)
    (hcubes : ∀ b ∈ cubes, S.normI b ≤ B)
    {r : A} {v : CompletedIndex A}
    (hv : v ∈ S.blockSupport (completion coords columns cubes).support r) :
    S.normI v.1 ≤ B ∧ S.normI v.2.1 ≤ N ∧
      S.normI v.2.2.1 ≤ N ∧ S.normI v.2.2.2 ≤ B ∧
      Squarefree coords (v.2.2.1 * v.2.2.2) ∧
      S.normI (v.2.2.1 * v.2.2.2) ≤ N * B ∧
      Squarefree coords (v.2.1 * v.2.2.1) ∧
      S.normI (v.2.1 * v.2.2.1) ≤ N := by
```

### product_fiber_card_le_squarefree_divisors

源码起始行：113。

```lean
theorem product_fiber_card_le_squarefree_divisors
    (pairs : Finset (A × A)) (j : A) (hj : Squarefree coords j) :
    ((pairs.filter fun u => u.1 * u.2 = j).card : ℝ) ≤
      ((divisors coords j).card : ℝ) := by
```

### swapped_product_fiber_card_le_squarefree_divisors

源码起始行：135。

```lean
theorem swapped_product_fiber_card_le_squarefree_divisors
    (pairs : Finset (A × A)) (j : A) (hj : Squarefree coords j) :
    ((pairs.filter fun u => u.2 * u.1 = j).card : ℝ) ≤
      ((divisors coords j).card : ℝ) := by
```

## HeckeSkeleton/LowHybrid/ColumnMass.lean

源码 SHA-256：`7efb313b7d48702290266ef45ef7e7af23f63ae5e108516f3027bc45c6eb8e72`。

### columnMass_div_eq

源码起始行：27。

```lean
theorem columnMass_div_eq (a : I → ℂ) (marks : Finset I) (d : I) :
    S.columnMass a marks d / S.normI d =
      ∑ p ∈ marks with d ∣ p, ‖a p‖ ^ 2 / S.normI p := by
```

### columnMass_sum_le_divisors

源码起始行：44。

```lean
theorem columnMass_sum_le_divisors
    (a : I → ℂ) (marks ds : Finset I) (D : ℝ)
    (hcomplete : ∀ p ∈ marks, ∀ d : I, d ∣ p → d ∈ S.divisors p)
    (hcount : ∀ p ∈ marks, ((S.divisors p).card : ℝ) ≤ D) :
    (∑ d ∈ ds, S.columnMass a marks d / S.normI d) ≤
      D * ∑ p ∈ marks, ‖a p‖ ^ 2 / S.normI p := by
```

## HeckeSkeleton/LowHybrid/CommonTactics.lean

源码 SHA-256：`59bea2789e1639f7ac3cf9b2dd4ca0dc45ac81b83aa1f856fa1712dcf13a8989`。

此模块为入口或组织模块，没有新增公开定理声明。

## HeckeSkeleton/LowHybrid/CompletedQuadratic.lean

源码 SHA-256：`473b9d332958b716ebb6c51e5b77a52649aee4ad5460c87692e5526a121da60d`。

### square_decomposition

源码起始行：29。

```lean
theorem square_decomposition (y : A) :
    squarefreePart coords y * squarePart coords y ^ 2 = y := by
```

### squarefreePart_squarefree

源码起始行：38。

```lean
theorem squarefreePart_squarefree (y : A) :
    PrimeArithmetic.Squarefree coords (squarefreePart coords y) := by
```

### squarefreeColumns_mem

源码起始行：49。

```lean
theorem squarefreeColumns_mem {ys : Finset A} {t s : A}
    (hs : s ∈ squarefreeColumns coords ys t) :
    s * t ^ 2 ∈ ys ∧ PrimeArithmetic.Squarefree coords s := by
```

### squarefreeColumn_injective

源码起始行：59。

```lean
theorem squarefreeColumn_injective (ys : Finset A) (t : A) :
    Set.InjOn (squarefreePart coords) (ys.filter fun y => squarePart coords y = t) := by
```

### sum_square_parts

源码起始行：68。

```lean
theorem sum_square_parts {R : Type*} [AddCommMonoid R]
    (ys : Finset A) (F : A → R) :
    (∑ y ∈ ys, F y) =
      ∑ t ∈ squareRoots coords ys, ∑ s ∈ squarefreeColumns coords ys t, F (s * t ^ 2) := by
```

### square_symbol

源码起始行：83。

```lean
theorem square_symbol (symbol : A → A → ℂ)
    (hright : ∀ a b c, symbol a (b * c) = symbol a b * symbol a c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then 1 else 0)
    (k s t : A) :
    symbol k (s * t ^ 2) ^ 3 =
      (if Coprime coords k t then (1 : ℂ) else 0) * symbol k s ^ 3 := by
```

### sum_square_symbols

源码起始行：94。

```lean
theorem sum_square_symbols (symbol : A → A → ℂ)
    (hright : ∀ a b c, symbol a (b * c) = symbol a b * symbol a c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then 1 else 0)
    (ys : Finset A) (gamma : A → ℂ) (k : A) :
    (∑ y ∈ ys, gamma y * symbol k y ^ 3) =
      ∑ t ∈ squareRoots coords ys,
        (if Coprime coords k t then (1 : ℂ) else 0) *
          ∑ s ∈ squarefreeColumns coords ys t, gamma (s * t ^ 2) * symbol k s ^ 3 := by
```

### completed_quadratic_positive

源码起始行：113。

```lean
theorem completed_quadratic_positive
    (normI : A → ℝ) (hn : ∀ a, 0 < normI a)
    (symbol : A → A → ℂ)
    (hright : ∀ a b c, symbol a (b * c) = symbol a b * symbol a c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then 1 else 0)
    (rows ys : Finset A) (gamma : A → ℂ) (Q : ℝ)
    (hquadratic : ∀ t ∈ squareRoots coords ys, ∀ f : A → ℂ,
      (∑ k ∈ rows, ‖∑ s ∈ squarefreeColumns coords ys t, f s * symbol k s ^ 3‖ ^ 2) ≤
        Q * ∑ s ∈ squarefreeColumns coords ys t, ‖f s‖ ^ 2) :
    (∑ k ∈ rows, ‖∑ y ∈ ys, gamma y * symbol k y ^ 3‖ ^ 2) ≤
      (∑ t ∈ squareRoots coords ys, 1 / normI t) *
        ∑ t ∈ squareRoots coords ys,
          normI t * (Q * ∑ s ∈ squarefreeColumns coords ys t, ‖gamma (s * t ^ 2)‖ ^ 2) := by
```

### card_le_real_scale

源码起始行：140。

```lean
theorem card_le_real_scale
    (normI : A → ℝ) (q : A → ℕ) (hnatural : ∀ a, normI a = (q a : ℝ))
    (C : ℝ) (hC : 0 ≤ C) (hcount : LinearNormCounting q C)
    (X : ℝ) (hX : 0 ≤ X) (s : Finset A) (hs : ∀ a ∈ s, normI a ≤ X) :
    (s.card : ℝ) ≤ C * X := by
```

### completed_energy_le

源码起始行：154。

```lean
theorem completed_energy_le
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount) (hcount : LinearNormCounting q Ccount)
    (symbol : A → A → ℂ)
    (hright : ∀ a b c, symbol a (b * c) = symbol a b * symbol a c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then 1 else 0)
    (hq : QuadraticSieveInput normI (PrimeArithmetic.Squarefree coords) symbol)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ Cq : ℝ, 0 < Cq ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
      ∀ (rows ys : Finset A) (gamma : A → ℂ) (G : ℝ), 0 ≤ G →
        (∀ k ∈ rows, PrimeArithmetic.Squarefree coords k ∧ normI k ≤ K) →
        (∀ y ∈ ys, normI y ≤ X) → (∀ y ∈ ys, ‖gamma y‖ ≤ G) →
        (∑ k ∈ rows, ‖∑ y ∈ ys, gamma y * symbol k y ^ 3‖ ^ 2) ≤
          (Cq * (K * X) ^ eta * (K + X)) * G ^ 2 * Ccount * X *
            harmonicEnvelope Ccount X ^ 2 := by
```

## HeckeSkeleton/LowHybrid/CompletedQuadraticBound.lean

源码 SHA-256：`abf7f2a5f32988d6c312b52bdc44f1ea2088a3a52ee0d8403babfaf365ef43b9`。

### product_row

源码起始行：31。

```lean
theorem product_row (symbol : A → A → ℂ)
    (columns cubes : Finset A) (beta : A → A → ℂ) (k : A) :
    (∑ n ∈ columns, ∑ b ∈ cubes, beta n b * symbol k (n * b) ^ 3) =
      ∑ y ∈ products columns cubes, productCoefficient columns cubes beta y * symbol k y ^ 3 := by
```

### product_fiber_card

源码起始行：53。

```lean
theorem product_fiber_card (columns cubes : Finset A)
    (hcolumns : ∀ n ∈ columns, PrimeArithmetic.Squarefree coords n) (y : A) :
    (((columns ×ˢ cubes).filter fun u => u.1 * u.2 = y).card : ℝ) ≤
      ((PrimeArithmetic.divisors coords y).card : ℝ) := by
```

### productCoefficient_norm

源码起始行：75。

```lean
theorem productCoefficient_norm (columns cubes : Finset A)
    (hcolumns : ∀ n ∈ columns, PrimeArithmetic.Squarefree coords n)
    (beta : A → A → ℂ) (hbeta : ∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ 1)
    (y : A) :
    ‖productCoefficient columns cubes beta y‖ ≤
      ((PrimeArithmetic.divisors coords y).card : ℝ) := by
```

### completed_quadratic_energy_bounded

源码起始行：95。

```lean
theorem completed_quadratic_energy_bounded
    (coords : A ≃* Multiplicative (ι →₀ ℕ))
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount) (hcount : LinearNormCounting q Ccount)
    (symbol : A → A → ℂ)
    (hright : ∀ a b c, symbol a (b * c) = symbol a b * symbol a c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then 1 else 0)
    (hq : QuadraticSieveInput normI (PrimeArithmetic.Squarefree coords) symbol)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ K N B : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
      ∀ (rows columns cubes : Finset A) (beta : A → A → ℂ),
        (∀ k ∈ rows, PrimeArithmetic.Squarefree coords k ∧ normI k ≤ K) →
        (∀ n ∈ columns, PrimeArithmetic.Squarefree coords n ∧ normI n ≤ N) →
        (∀ b ∈ cubes, normI b ≤ B) →
        (∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ 1) →
        (∑ k ∈ rows, ‖∑ n ∈ columns, ∑ b ∈ cubes,
          beta n b * symbol k (n * b) ^ 3‖ ^ 2) ≤
          C0 * (K * N * B) ^ eps * (K + N * B) * (N * B) := by
```

## HeckeSkeleton/LowHybrid/Corollaries.lean

源码 SHA-256：`6076de63bd551113f5b4cc1a595101ef969e35eb9cfc23c484512823d52fbb1b`。

### hybrid_energy_with_beta_mass

源码起始行：25。

```lean
theorem hybrid_energy_with_beta_mass
    (coords : A ≃* Multiplicative (ι →₀ ℕ))
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount) (hcount : LinearNormCounting q Ccount)
    (symbol : A → A → ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (hright : ∀ a b c, symbol a (b * c) = symbol a b * symbol a c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then 1 else 0)
    (hq : QuadraticSieveInput normI (PrimeArithmetic.Squarefree coords) symbol)
    (hc : CubicSieveInput normI (PrimeArithmetic.Squarefree coords) symbol)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
      ∀ (rows marks columns cubes : Finset A) (a : A → ℂ) (beta : A → A → ℂ),
        (∀ k ∈ rows, PrimeArithmetic.Squarefree coords k ∧ normI k ≤ K) →
        (∀ p ∈ marks, PrimeArithmetic.Squarefree coords p ∧ normI p ≤ L) →
        (∀ n ∈ columns, PrimeArithmetic.Squarefree coords n ∧ normI n ≤ N) →
        (∀ b ∈ cubes, normI b ≤ B) →
        hybridEnergy symbol (Coprime coords) normI a beta rows marks columns cubes ≤
          C0 * (K * N * B * L) ^ eps * (K + N * B) * B *
            (N + L + (N * L) ^ (2 / 3 : ℝ)) *
            (∑ p ∈ marks, ‖a p‖ ^ 2 / normI p) * betaSquaredMass beta columns cubes := by
```

### hybrid_energy_bounded

源码起始行：63。

```lean
theorem hybrid_energy_bounded
    (coords : A ≃* Multiplicative (ι →₀ ℕ))
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount) (hcount : LinearNormCounting q Ccount)
    (symbol : A → A → ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (hright : ∀ a b c, symbol a (b * c) = symbol a b * symbol a c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then 1 else 0)
    (hq : QuadraticSieveInput normI (PrimeArithmetic.Squarefree coords) symbol)
    (hc : CubicSieveInput normI (PrimeArithmetic.Squarefree coords) symbol)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
      ∀ (rows marks columns cubes : Finset A) (a : A → ℂ) (beta : A → A → ℂ),
        (∀ k ∈ rows, PrimeArithmetic.Squarefree coords k ∧ normI k ≤ K) →
        (∀ p ∈ marks, PrimeArithmetic.Squarefree coords p ∧ normI p ≤ L) →
        (∀ n ∈ columns, PrimeArithmetic.Squarefree coords n ∧ normI n ≤ N) →
        (∀ b ∈ cubes, normI b ≤ B) →
        (∀ p ∈ marks, ‖a p‖ ≤ 1) →
        (∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ 1) →
        hybridEnergy symbol (Coprime coords) normI a beta rows marks columns cubes ≤
          C0 * (K * N * B * L) ^ eps * (K + N * B) * B *
            (N + L + (N * L) ^ (2 / 3 : ℝ)) := by
```

## HeckeSkeleton/LowHybrid/Counting.lean

源码 SHA-256：`1d2f151634708bad54994910059584c2e57937a6f9d6500d8a67cec1dfe91f3d`。

### sum_mul_le_of_prefix_bound

源码起始行：19。

```lean
theorem sum_mul_le_of_prefix_bound (a w : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (hw0 : ∀ n : ℕ, 0 ≤ w n) (hw : Antitone w)
    (ha : ∀ n : ℕ, n ≤ N → (∑ j ∈ Finset.range n, a j) ≤ C * n) :
    (∑ n ∈ Finset.range N, a n * w n) ≤
      C * ∑ n ∈ Finset.range N, w n := by
```

### harmonicPartial_le_log

源码起始行：61。

```lean
theorem harmonicPartial_le_log (N : ℕ) :
    harmonicPartial N ≤ 1 + Real.log N := by
```

### reciprocal_sum_le_harmonic_of_prefix_count

源码起始行：88。

```lean
theorem reciprocal_sum_le_harmonic_of_prefix_count
    {I : Type*} (s : Finset I) (q : I → ℕ) (N : ℕ) (C : ℝ)
    (hq : ∀ i ∈ s, 1 ≤ q i) (hupper : ∀ i ∈ s, q i ≤ N)
    (hcount : ∀ n : ℕ, n ≤ N →
      ((s.filter fun i => q i ≤ n).card : ℝ) ≤ C * n) :
    (∑ i ∈ s, 1 / (q i : ℝ)) ≤ C * harmonicPartial N := by
```

### reciprocal_sum_le_log_of_linear_counting

源码起始行：154。

```lean
theorem reciprocal_sum_le_log_of_linear_counting
    {I : Type*} (q : I → ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hq : ∀ i : I, 1 ≤ q i) (hcount : LinearNormCounting q C)
    (X : ℝ) (hX : 1 ≤ X) (s : Finset I)
    (hs : ∀ i ∈ s, (q i : ℝ) ≤ X) :
    (∑ i ∈ s, 1 / (q i : ℝ)) ≤ C * (1 + Real.log X) := by
```

### reciprocal_sum_subpower_of_linear_counting

源码起始行：181。

```lean
theorem reciprocal_sum_subpower_of_linear_counting
    {I : Type*} (q : I → ℕ) (C : ℝ) (hC : 0 < C)
    (hq : ∀ i : I, 1 ≤ q i) (hcount : LinearNormCounting q C)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ CH : ℝ, 0 < CH ∧ ∀ X : ℝ, 1 ≤ X → ∀ s : Finset I,
      (∀ i ∈ s, (q i : ℝ) ≤ X) →
        (∑ i ∈ s, 1 / (q i : ℝ)) ≤ CH * X ^ eps := by
```

### harmonic_cutoff_subpower_of_linear_counting

源码起始行：198。

```lean
theorem harmonic_cutoff_subpower_of_linear_counting
    {I : Type*} (q : I → ℕ) (C : ℝ) (hC : 0 < C)
    (hq : ∀ i : I, 1 ≤ q i) (hcount : LinearNormCounting q C)
    (cutoff : ℝ → Finset I)
    (hcutoff : ∀ X : ℝ, 1 ≤ X → ∀ i ∈ cutoff X, (q i : ℝ) ≤ X) :
    SubpowerBound (fun X => ∑ i ∈ cutoff X, 1 / (q i : ℝ)) := by
```

## HeckeSkeleton/LowHybrid/CountingBridge.lean

源码 SHA-256：`409c43c3e08c26869af782f1bd660a53781ed891e389cce35ebd9f6467c55984`。

### linear_norm_counting_of_cutoffs

源码起始行：18。

```lean
theorem linear_norm_counting_of_cutoffs
    {I : Type*} (q : I → ℕ) (C : ℝ) (cutoff : ℕ → Finset I)
    (hmem : ∀ N : ℕ, ∀ i : I, q i ≤ N → i ∈ cutoff N)
    (hcard : ∀ N : ℕ, ((cutoff N).card : ℝ) ≤ C * N) :
    LinearNormCounting q C := by
```

### real_norm_reciprocal_sum_subpower

源码起始行：30。

```lean
theorem real_norm_reciprocal_sum_subpower
    {I : Type*} (q : I → ℕ) (normI : I → ℝ) (hnorm : ∀ i, normI i = (q i : ℝ))
    (C : ℝ) (hC : 0 < C) (hq : ∀ i : I, 1 ≤ q i)
    (hcount : LinearNormCounting q C) (eps : ℝ) (heps : 0 < eps) :
    ∃ CH : ℝ, 0 < CH ∧ ∀ X : ℝ, 1 ≤ X → ∀ s : Finset I,
      (∀ i ∈ s, normI i ≤ X) →
        (∑ i ∈ s, 1 / normI i) ≤ CH * X ^ eps := by
```

### cube_support_weight_budget_mass

源码起始行：48。

```lean
theorem cube_support_weight_budget_mass
    (wt wc wh r B betaMass : ℝ) (beta : ℂ)
    (hwt : 0 < wt) (hwc : 0 ≤ wc) (hwh : 0 < wh) (hr : 0 < r)
    (hB : 0 ≤ B) (hmass : 0 ≤ betaMass)
    (hbeta : ‖beta‖ ^ 2 ≤ betaMass)
    (hsupport : beta ≠ 0 → r * wc * wh * wt ^ 2 ≤ B) :
    wt * wc * ‖beta‖ ^ 2 ≤ (betaMass * B / r) / (wt * wh) := by
```

## HeckeSkeleton/LowHybrid/CountingPositivity.lean

源码 SHA-256：`845ab3680d2ad0cc9efc033d470b8c694e2b73f15c823efab4c65eb949faeb32`。

### linear_norm_counting_norm_one_le

源码起始行：15。

```lean
theorem linear_norm_counting_norm_one_le
    {I : Type*} (q : I → ℕ) (C : ℝ) (hcount : LinearNormCounting q C) :
    ∀ i : I, 1 ≤ q i := by
```

### linear_norm_counting_constant_pos_of_element

源码起始行：28。

```lean
theorem linear_norm_counting_constant_pos_of_element
    {I : Type*} (q : I → ℕ) (C : ℝ) (hcount : LinearNormCounting q C) (i : I) :
    0 < C := by
```

### linear_norm_counting_constant_pos

源码起始行：43。

```lean
theorem linear_norm_counting_constant_pos
    {I : Type*} [Nonempty I] (q : I → ℕ) (C : ℝ) (hcount : LinearNormCounting q C) :
    0 < C :=
```

## HeckeSkeleton/LowHybrid/DivisorEnvelope.lean

源码 SHA-256：`340340dc00adf7a049fd19e4e34a16e988b770825b14826d0a37a16161c4519f`。

### divisorCountEnvelope_nonneg

源码起始行：21。

```lean
theorem divisorCountEnvelope_nonneg {I : Type*} (cutoff : ℝ → Finset I)
    (divisors : I → Finset I) (X : ℝ) :
    0 ≤ divisorCountEnvelope cutoff divisors X := by
```

### divisor_count_le_envelope

源码起始行：28。

```lean
theorem divisor_count_le_envelope {I : Type*} (cutoff : ℝ → Finset I)
    (divisors : I → Finset I) (X : ℝ) (i : I) (hi : i ∈ cutoff X) :
    ((divisors i).card : ℝ) ≤ divisorCountEnvelope cutoff divisors X := by
```

### divisorCountEnvelope_subpower

源码起始行：35。

```lean
theorem divisorCountEnvelope_subpower
    {I : Type*} (cutoff : ℝ → Finset I) (divisors : I → Finset I) (normI : I → ℝ)
    (hnorm : ∀ i : I, 0 ≤ normI i)
    (hcutoff : ∀ X : ℝ, 1 ≤ X → ∀ i ∈ cutoff X, normI i ≤ X)
    (hdiv : ∀ eta : ℝ, 0 < eta → ∃ C : ℝ, 0 < C ∧
      ∀ i : I, ((divisors i).card : ℝ) ≤ C * normI i ^ eta) :
    SubpowerBound (divisorCountEnvelope cutoff divisors) := by
```

### divisor_envelope_subpower_from_prime_norms

源码起始行：59。

```lean
theorem divisor_envelope_subpower_from_prime_norms
    {I P : Type*} (support : I → Finset P) (divisors : I → Finset I)
    (primeNorm : P → ℝ) (normI : I → ℝ) (cutoff : ℝ → Finset I)
    (hp : ∀ p : P, 1 ≤ primeNorm p)
    (hfinite : ∀ X : ℝ, Set.Finite {p : P | primeNorm p ≤ X})
    (hcard : ∀ i : I, ((divisors i).card : ℝ) ≤ (2 : ℝ) ^ (support i).card)
    (hnorm : ∀ i : I, (∏ p ∈ support i, primeNorm p) ≤ normI i)
    (hcutoff : ∀ X : ℝ, 1 ≤ X → ∀ i ∈ cutoff X, normI i ≤ X) :
    SubpowerBound (divisorCountEnvelope cutoff divisors) := by
```

## HeckeSkeleton/LowHybrid/Factorization.lean

源码 SHA-256：`8189b8901e88dc3d7f2f33b74731253a485d9f5761a17e673e0e9b64b7ee3ba0`。

### square_extraction

源码起始行：25。

```lean
theorem square_extraction (b : ℕ) : b = squarefreeExp b + 2 * squareExp b := by
```

### squarefreeExp_le_one

源码起始行：29。

```lean
theorem squarefreeExp_le_one (b : ℕ) : squarefreeExp b ≤ 1 := by
```

### split_left

源码起始行：33。

```lean
theorem split_left (n b : ℕ) : n = commonExp n b + leftExp n b := by
```

### split_right

源码起始行：38。

```lean
theorem split_right (n b : ℕ) : squarefreeExp b = commonExp n b + rightExp n b := by
```

### commonExp_le_one

源码起始行：43。

```lean
theorem commonExp_le_one (n b : ℕ) (hn : n ≤ 1) : commonExp n b ≤ 1 :=
```

### leftExp_le_one

源码起始行：46。

```lean
theorem leftExp_le_one (n b : ℕ) (hn : n ≤ 1) : leftExp n b ≤ 1 := by
```

### rightExp_le_one

源码起始行：50。

```lean
theorem rightExp_le_one (n b : ℕ) : rightExp n b ≤ 1 := by
```

### common_left_disjoint

源码起始行：55。

```lean
theorem common_left_disjoint (n b : ℕ) (hn : n ≤ 1) :
    commonExp n b = 0 ∨ leftExp n b = 0 := by
```

### common_right_disjoint

源码起始行：60。

```lean
theorem common_right_disjoint (n b : ℕ) :
    commonExp n b = 0 ∨ rightExp n b = 0 := by
```

### left_right_disjoint

源码起始行：66。

```lean
theorem left_right_disjoint (n b : ℕ) : leftExp n b = 0 ∨ rightExp n b = 0 := by
```

### completed_square_exponent

源码起始行：73。

```lean
theorem completed_square_exponent (n b : ℕ) :
    n + b = leftExp n b + rightExp n b + 2 * (commonExp n b + squareExp b) := by
```

### residual_exponent_le_one

源码起始行：80。

```lean
theorem residual_exponent_le_one (n b : ℕ) (hn : n ≤ 1) :
    leftExp n b + rightExp n b ≤ 1 := by
```

### local_factorization_unique

源码起始行：90。

```lean
theorem local_factorization_unique (n b g t c m h : ℕ)
    (hg : g ≤ 1) (hb : b = g + 2 * t)
    (hn : n = c + m) (hgc : g = c + h) (hmh : m = 0 ∨ h = 0) :
    g = squarefreeExp b ∧ t = squareExp b ∧ c = commonExp n b ∧
      m = leftExp n b ∧ h = rightExp n b := by
```

### squarePart_decomposition

源码起始行：116。

```lean
theorem squarePart_decomposition (b : ι → ℕ) :
    b = fun p => squarefreePart b p + 2 * squarePart b p := by
```

### leftPart_decomposition

源码起始行：121。

```lean
theorem leftPart_decomposition (n b : ι → ℕ) :
    n = fun p => commonPart n b p + leftPart n b p := by
```

### rightPart_decomposition

源码起始行：126。

```lean
theorem rightPart_decomposition (n b : ι → ℕ) :
    squarefreePart b = fun p => commonPart n b p + rightPart n b p := by
```

### squarefreePart_squarefree

源码起始行：131。

```lean
theorem squarefreePart_squarefree (b : ι → ℕ) : SquarefreeVector (squarefreePart b) := by
```

### commonPart_squarefree

源码起始行：135。

```lean
theorem commonPart_squarefree (n b : ι → ℕ) (hn : SquarefreeVector n) :
    SquarefreeVector (commonPart n b) := by
```

### leftPart_squarefree

源码起始行：140。

```lean
theorem leftPart_squarefree (n b : ι → ℕ) (hn : SquarefreeVector n) :
    SquarefreeVector (leftPart n b) := by
```

### rightPart_squarefree

源码起始行：145。

```lean
theorem rightPart_squarefree (n b : ι → ℕ) : SquarefreeVector (rightPart n b) := by
```

### commonPart_leftPart_coprime

源码起始行：149。

```lean
theorem commonPart_leftPart_coprime (n b : ι → ℕ) (hn : SquarefreeVector n) :
    CoprimeVector (commonPart n b) (leftPart n b) := by
```

### commonPart_rightPart_coprime

源码起始行：154。

```lean
theorem commonPart_rightPart_coprime (n b : ι → ℕ) :
    CoprimeVector (commonPart n b) (rightPart n b) := by
```

### leftPart_rightPart_coprime

源码起始行：159。

```lean
theorem leftPart_rightPart_coprime (n b : ι → ℕ) :
    CoprimeVector (leftPart n b) (rightPart n b) := by
```

### residualProduct_squarefree

源码起始行：165。

```lean
theorem residualProduct_squarefree (n b : ι → ℕ) (hn : SquarefreeVector n) :
    SquarefreeVector (residualProduct n b) := by
```

### completed_square_decomposition

源码起始行：170。

```lean
theorem completed_square_decomposition (n b : ι → ℕ) :
    (fun p => n p + b p) = fun p => residualProduct n b p + 2 * maskPart n b p := by
```

### vector_factorization_unique

源码起始行：175。

```lean
theorem vector_factorization_unique (n b g t c m h : ι → ℕ)
    (hg : SquarefreeVector g) (hb : ∀ p, b p = g p + 2 * t p)
    (hn : ∀ p, n p = c p + m p) (hgc : ∀ p, g p = c p + h p)
    (hmh : CoprimeVector m h) :
    g = squarefreePart b ∧ t = squarePart b ∧ c = commonPart n b ∧
      m = leftPart n b ∧ h = rightPart n b := by
```

### cubicColumn_decomposition

源码起始行：190。

```lean
theorem cubicColumn_decomposition (n b r c' : ι → ℕ)
    (hc : ∀ p, commonPart n b p = r p + c' p) :
    n = fun p => r p + (c' p + leftPart n b p) := by
```

### cubicColumn_squarefree

源码起始行：202。

```lean
theorem cubicColumn_squarefree (n b r c' : ι → ℕ)
    (hn : SquarefreeVector n)
    (hc : ∀ p, commonPart n b p = r p + c' p) :
    SquarefreeVector (fun p => c' p + leftPart n b p) := by
```

### cubicColumn_factors_coprime

源码起始行：215。

```lean
theorem cubicColumn_factors_coprime (n b r c' : ι → ℕ)
    (hn : SquarefreeVector n)
    (hc : ∀ p, commonPart n b p = r p + c' p) :
    CoprimeVector c' (leftPart n b) := by
```

### coprimeVector_add_right

源码起始行：228。

```lean
theorem coprimeVector_add_right (P a b : ι → ℕ) :
    CoprimeVector P (fun p => a p + b p) ↔
      CoprimeVector P a ∧ CoprimeVector P b := by
```

### completed_quadratic_symbol

源码起始行：254。

```lean
theorem completed_quadratic_symbol (row n b : ι → ℕ)
    (chi : (ι → ℕ) → ℂ)
    (hadd : ∀ a b, chi (fun p => a p + b p) = chi a * chi b)
    (hsix : ∀ a, chi a ^ 6 = if CoprimeVector row a then 1 else 0) :
    chi (fun p => n p + b p) ^ 3 =
      if CoprimeVector row (maskPart n b) then chi (residualProduct n b) ^ 3 else 0 := by
```

### completed_row_mask

源码起始行：278。

```lean
theorem completed_row_mask (row n b : ι → ℕ) :
    CoprimeVector row (maskPart n b) ↔
      CoprimeVector row (commonPart n b) ∧ CoprimeVector row (squarePart b) :=
```

### cubic_mask_equivalence

源码起始行：286。

```lean
theorem cubic_mask_equivalence (P r c m h t : ι → ℕ)
    (hn : CoprimeVector P (fun p => r p + c p + m p)) :
    CoprimeVector P (fun p => r p + c p + h p + 2 * t p) ↔
      CoprimeVector P (fun p => h p + t p) := by
```

### completed_cubic_mask

源码起始行：307。

```lean
theorem completed_cubic_mask (P r c m h t : ι → ℕ)
    (psi : (ι → ℕ) → ℂ)
    (hadd : ∀ a b, psi (fun p => a p + b p) = psi a * psi b)
    (hzero : ∀ a, ¬ CoprimeVector P a → psi a = 0) :
    (if CoprimeVector P (fun p => r p + c p + h p + 2 * t p)
      then psi (fun p => r p + c p + m p) else 0) =
    if CoprimeVector P (fun p => h p + t p)
      then psi r * psi (fun p => c p + m p) else 0 := by
```

## HeckeSkeleton/LowHybrid/Global.lean

源码 SHA-256：`4fee86656221c1abf7dfac6b151edff0d2fc0e342b58b4ecbaa8dc4d3d67b4d7`。

### tHarmonic_nonneg

源码起始行：79。

```lean
theorem tHarmonic_nonneg (rows : Finset I) (Q S Rbudget A : ℝ)
    (hb : b.Admissible rows Q S Rbudget A) : 0 ≤ b.tHarmonic := by
```

### cHarmonic_nonneg

源码起始行：86。

```lean
theorem cHarmonic_nonneg (rows : Finset I) (Q S Rbudget A : ℝ)
    (hb : b.Admissible rows Q S Rbudget A) : 0 ≤ b.cHarmonic := by
```

### hHarmonic_nonneg

源码起始行：93。

```lean
theorem hHarmonic_nonneg (rows : Finset I) (Q S Rbudget A : ℝ)
    (hb : b.Admissible rows Q S Rbudget A) : 0 ≤ b.hHarmonic := by
```

### energy_le

源码起始行：101。

```lean
theorem energy_le (rows : Finset I) (Q S Rbudget A : ℝ)
    (hQ : 0 ≤ Q) (hS : 0 ≤ S) (hR : 0 ≤ Rbudget) (hA : 0 ≤ A)
    (hb : b.Admissible rows Q S Rbudget A) :
    (∑ i ∈ rows, ‖b.row i‖ ^ 2) ≤
      Q * S * Rbudget * A * b.tHarmonic ^ 2 * b.cHarmonic * b.hHarmonic := by
```

### energy_le_uniform_harmonics

源码起始行：113。

```lean
theorem energy_le_uniform_harmonics (rows : Finset I) (Q S Rbudget A Ht Hc Hh : ℝ)
    (hQ : 0 ≤ Q) (hS : 0 ≤ S) (hR : 0 ≤ Rbudget) (hA : 0 ≤ A)
    (hHt : 0 ≤ Ht) (hHc : 0 ≤ Hc) (hHh : 0 ≤ Hh)
    (hb : b.Admissible rows Q S Rbudget A)
    (ht : b.tHarmonic ≤ Ht) (hc : b.cHarmonic ≤ Hc) (hh : b.hHarmonic ≤ Hh) :
    (∑ i ∈ rows, ‖b.row i‖ ^ 2) ≤
      Q * S * Rbudget * A * Ht ^ 2 * Hc * Hh := by
```

### inverse_sqrt_norm_sq

源码起始行：142。

```lean
theorem inverse_sqrt_norm_sq (x : ℝ) (hx : 0 < x) :
    ‖(1 : ℂ) / (Real.sqrt x : ℂ)‖ ^ 2 = 1 / x := by
```

### hybrid_energy_of_weighted_blocks

源码起始行：154。

```lean
theorem hybrid_energy_of_weighted_blocks
    {I : Type u} {D : Type uD} {R : Type uR}
    [DecidableEq I] [DecidableEq D] [DecidableEq R]
    (rows : Finset I) (ds : Finset D) (rs : Finset R)
    (localBlocks : I → Finset (D × R))
    (block : D → R → WeightedBlock.{u, v} I)
    (mu : I → D × R → ℂ)
    (ND : D → ℝ) (NR : R → ℝ) (AD : D → ℝ)
    (Delta Q S B Ht Hc Hh : ℝ)
    (hDelta : 0 ≤ Delta) (hQ : 0 ≤ Q) (hS : 0 ≤ S) (hB : 0 ≤ B)
    (hHt : 0 ≤ Ht) (hHc : 0 ≤ Hc) (hHh : 0 ≤ Hh)
    (hND : ∀ d ∈ ds, 0 < ND d) (hNR : ∀ r ∈ rs, 0 < NR r)
    (hAD : ∀ d ∈ ds, 0 ≤ AD d)
    (hlocal : ∀ i ∈ rows, localBlocks i ⊆ ds ×ˢ rs)
    (hmu : ∀ i ∈ rows, ∀ dr ∈ localBlocks i, ‖mu i dr‖ ≤ 1)
    (hcard : ∀ i ∈ rows, ((localBlocks i).card : ℝ) ≤ Delta)
    (hadmissible : ∀ d ∈ ds, ∀ r ∈ rs,
      (block d r).Admissible (rows.filter fun i => (d, r) ∈ localBlocks i)
        Q S (B / NR r) (AD d))
    (ht : ∀ d ∈ ds, ∀ r ∈ rs, (block d r).tHarmonic ≤ Ht)
    (hc : ∀ d ∈ ds, ∀ r ∈ rs, (block d r).cHarmonic ≤ Hc)
    (hh : ∀ d ∈ ds, ∀ r ∈ rs, (block d r).hHarmonic ≤ Hh) :
    (∑ i ∈ rows, ‖∑ dr ∈ localBlocks i, mu i dr *
      (((1 : ℂ) / (Real.sqrt (ND dr.1) : ℂ)) * (block dr.1 dr.2).row i)‖ ^ 2) ≤
      Delta * Q * S * B * Ht ^ 2 * Hc * Hh *
        (∑ d ∈ ds, AD d / ND d) * (∑ r ∈ rs, 1 / NR r) := by
```

## HeckeSkeleton/LowHybrid/Homogeneity.lean

源码 SHA-256：`0f35d33c04b85816f19e0a0dd25d9ae9cc77c68b856a68e5b6ecf076a50974e0`。

### hybridRow_beta_congr

源码起始行：21。

```lean
theorem hybridRow_beta_congr
    (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ)
    (a : I → ℂ) (beta gamma : I → I → ℂ)
    (marks columns cubes : Finset I) (k : I)
    (hbeta : ∀ n ∈ columns, ∀ b ∈ cubes, beta n b = gamma n b) :
    hybridRow symbol cop normI a beta marks columns cubes k =
      hybridRow symbol cop normI a gamma marks columns cubes k := by
```

### hybridRow_beta_mul

源码起始行：38。

```lean
theorem hybridRow_beta_mul
    (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ)
    (a : I → ℂ) (beta : I → I → ℂ) (z : ℂ)
    (marks columns cubes : Finset I) (k : I) :
    hybridRow symbol cop normI a (fun n b => z * beta n b) marks columns cubes k =
      z * hybridRow symbol cop normI a beta marks columns cubes k := by
```

### hybridEnergy_beta_mul

源码起始行：59。

```lean
theorem hybridEnergy_beta_mul
    (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ)
    (a : I → ℂ) (beta : I → I → ℂ) (z : ℂ)
    (rows marks columns cubes : Finset I) :
    hybridEnergy symbol cop normI a (fun n b => z * beta n b) rows marks columns cubes =
      ‖z‖ ^ 2 * hybridEnergy symbol cop normI a beta rows marks columns cubes := by
```

### hybridEnergy_eq_zero_of_beta_zero

源码起始行：68。

```lean
theorem hybridEnergy_eq_zero_of_beta_zero
    (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ)
    (a : I → ℂ) (beta : I → I → ℂ)
    (rows marks columns cubes : Finset I)
    (hbeta : ∀ n ∈ columns, ∀ b ∈ cubes, beta n b = 0) :
    hybridEnergy symbol cop normI a beta rows marks columns cubes = 0 := by
```

### hybridEnergy_beta_bound_of_unit

源码起始行：83。

```lean
theorem hybridEnergy_beta_bound_of_unit
    (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ)
    (a : I → ℂ) (beta : I → I → ℂ)
    (rows marks columns cubes : Finset I) (U R : ℝ) (hU : 0 ≤ U)
    (hbeta : ∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ U)
    (hunit : ∀ gamma : I → I → ℂ,
      (∀ n ∈ columns, ∀ b ∈ cubes, ‖gamma n b‖ ≤ 1) →
      hybridEnergy symbol cop normI a gamma rows marks columns cubes ≤ R) :
    hybridEnergy symbol cop normI a beta rows marks columns cubes ≤ U ^ 2 * R := by
```

### hybridEnergy_beta_squared_bound_of_unit

源码起始行：124。

```lean
theorem hybridEnergy_beta_squared_bound_of_unit
    (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ)
    (a : I → ℂ) (beta : I → I → ℂ)
    (rows marks columns cubes : Finset I) (V R : ℝ) (hV : 0 ≤ V)
    (hbeta : ∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ^ 2 ≤ V)
    (hunit : ∀ gamma : I → I → ℂ,
      (∀ n ∈ columns, ∀ b ∈ cubes, ‖gamma n b‖ ≤ 1) →
      hybridEnergy symbol cop normI a gamma rows marks columns cubes ≤ R) :
    hybridEnergy symbol cop normI a beta rows marks columns cubes ≤ V * R := by
```

### betaSquaredMass_nonneg

源码起始行：148。

```lean
theorem betaSquaredMass_nonneg (beta : I → I → ℂ) (columns cubes : Finset I) :
    0 ≤ betaSquaredMass beta columns cubes :=
```

### norm_sq_le_betaSquaredMass

源码起始行：152。

```lean
theorem norm_sq_le_betaSquaredMass (beta : I → I → ℂ) (columns cubes : Finset I)
    (n : I) (hn : n ∈ columns) (b : I) (hb : b ∈ cubes) :
    ‖beta n b‖ ^ 2 ≤ betaSquaredMass beta columns cubes := by
```

### betaSquaredMass_empty_columns

源码起始行：161。

```lean
@[simp] theorem betaSquaredMass_empty_columns (beta : I → I → ℂ) (cubes : Finset I) :
    betaSquaredMass beta ∅ cubes = 0 := by
```

### betaSquaredMass_empty_cubes

源码起始行：164。

```lean
@[simp] theorem betaSquaredMass_empty_cubes (beta : I → I → ℂ) (columns : Finset I) :
    betaSquaredMass beta columns ∅ = 0 := by
```

### hybridEnergy_beta_mass_of_unit

源码起始行：169。

```lean
theorem hybridEnergy_beta_mass_of_unit
    (symbol : I → I → ℂ) (cop : I → I → Prop) (normI : I → ℝ)
    (a : I → ℂ) (beta : I → I → ℂ)
    (rows marks columns cubes : Finset I) (R : ℝ)
    (hunit : ∀ gamma : I → I → ℂ,
      (∀ n ∈ columns, ∀ b ∈ cubes, ‖gamma n b‖ ≤ 1) →
      hybridEnergy symbol cop normI a gamma rows marks columns cubes ≤ R) :
    hybridEnergy symbol cop normI a beta rows marks columns cubes ≤
      betaSquaredMass beta columns cubes * R :=
```

## HeckeSkeleton/LowHybrid/HybridEnergy.lean

源码 SHA-256：`cfde452b6ae969ffcf8ef26c17f834fa0c89c4c8dea0eef1177daaf45e7a695a`。

### hybrid_energy

源码起始行：36。

```lean
theorem hybrid_energy
    (coords : A ≃* Multiplicative (ι →₀ ℕ))
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount) (hcount : LinearNormCounting q Ccount)
    (symbol : A → A → ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (hright : ∀ a b c, symbol a (b * c) = symbol a b * symbol a c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then 1 else 0)
    (hq : QuadraticSieveInput normI (PrimeArithmetic.Squarefree coords) symbol)
    (hc : CubicSieveInput normI (PrimeArithmetic.Squarefree coords) symbol)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
      ∀ (rows marks columns cubes : Finset A) (a : A → ℂ) (beta : A → A → ℂ),
        (∀ k ∈ rows, PrimeArithmetic.Squarefree coords k ∧ normI k ≤ K) →
        (∀ p ∈ marks, PrimeArithmetic.Squarefree coords p ∧ normI p ≤ L) →
        (∀ n ∈ columns, PrimeArithmetic.Squarefree coords n ∧ normI n ≤ N) →
        (∀ b ∈ cubes, normI b ≤ B) →
        (∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ 1) →
        hybridEnergy symbol (Coprime coords) normI a beta rows marks columns cubes ≤
          C0 * (K * N * B * L) ^ eps * (K + N * B) * B *
            (N + L + (N * L) ^ (2 / 3 : ℝ)) *
            (∑ p ∈ marks, ‖a p‖ ^ 2 / normI p) := by
```

## HeckeSkeleton/LowHybrid/Losses.lean

源码 SHA-256：`67e206863dae07c4d3db016e947c58a7c1ddd4be87df3a8959be27c4cb847dab`。

### one_add_log_le_small_power

源码起始行：22。

```lean
theorem one_add_log_le_small_power (X eps : ℝ) (hX : 1 ≤ X) (heps : 0 < eps) :
    1 + Real.log X ≤ (1 + 1 / eps) * X ^ eps := by
```

### subpower_of_logarithmic_bound

源码起始行：31。

```lean
theorem subpower_of_logarithmic_bound (f : ℝ → ℝ) (C : ℝ) (hC : 0 < C)
    (hf : ∀ X : ℝ, 1 ≤ X → f X ≤ C * (1 + Real.log X)) :
    SubpowerBound f := by
```

### hybrid_total_scale_bounds

源码起始行：45。

```lean
theorem hybrid_total_scale_bounds (K N B L : ℝ)
    (hK : 1 ≤ K) (hN : 1 ≤ N) (hB : 1 ≤ B) (hL : 1 ≤ L) :
    1 ≤ K * N * B * L ∧ K ≤ K * N * B * L ∧ N ≤ K * N * B * L ∧
      B ≤ K * N * B * L ∧ L ≤ K * N * B * L ∧
      N * B ≤ K * N * B * L ∧ K * N * B ≤ K * N * B * L ∧
      N * L ≤ K * N * B * L := by
```

### hybrid_arithmetic_loss_le

源码起始行：95。

```lean
theorem hybrid_arithmetic_loss_le
    (divisor harmonic : ℝ → ℝ) (CD CH eta K N B L : ℝ)
    (hCD : 0 ≤ CD) (hCH : 0 ≤ CH) (heta : 0 ≤ eta)
    (hK : 1 ≤ K) (hN : 1 ≤ N) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hd0 : ∀ X : ℝ, 1 ≤ X → 0 ≤ divisor X)
    (hh0 : ∀ X : ℝ, 1 ≤ X → 0 ≤ harmonic X)
    (hd : ∀ X : ℝ, 1 ≤ X → divisor X ≤ CD * X ^ eta)
    (hh : ∀ X : ℝ, 1 ≤ X → harmonic X ≤ CH * X ^ eta) :
    hybridArithmeticLoss divisor harmonic eta K N B L ≤
      (CD ^ 5 * CH ^ 5) * (K * N * B * L) ^ (12 * eta) := by
```

### hybrid_arithmetic_loss_subpower

源码起始行：152。

```lean
theorem hybrid_arithmetic_loss_subpower
    (divisor harmonic : ℝ → ℝ)
    (hd0 : ∀ X : ℝ, 1 ≤ X → 0 ≤ divisor X)
    (hh0 : ∀ X : ℝ, 1 ≤ X → 0 ≤ harmonic X)
    (hd : SubpowerBound divisor) (hh : SubpowerBound harmonic)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ eta C : ℝ, 0 < eta ∧ 0 < C ∧
      ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
        hybridArithmeticLoss divisor harmonic eta K N B L ≤
          C * (K * N * B * L) ^ eps := by
```

## HeckeSkeleton/LowHybrid/Masks.lean

源码 SHA-256：`350318bf58d031ebc7832a176d1decf7346be75eb5e182d6ae705c0ccf6a3fea`。

### complex_support_mobius_sum

源码起始行：25。

```lean
theorem complex_support_mobius_sum {Prime : Type*} [DecidableEq Prime]
    (support : Finset Prime) :
    (∑ d ∈ support.powerset, (-1 : ℂ) ^ d.card) =
      if support = ∅ then 1 else 0 := by
```

### norm_support_mobius

源码起始行：37。

```lean
theorem norm_support_mobius {Prime : Type*} (d : Finset Prime) :
    ‖(-1 : ℂ) ^ d.card‖ = 1 := by
```

### support_coprime_mask_eq_mobius_sum

源码起始行：42。

```lean
theorem support_coprime_mask_eq_mobius_sum {Prime : Type*} [DecidableEq Prime]
    (columnSupport rowSupport : Finset Prime) :
    (if Disjoint columnSupport rowSupport then (1 : ℂ) else 0) =
      ∑ d ∈ (columnSupport ∩ rowSupport).powerset, (-1 : ℂ) ^ d.card := by
```

### row_powerset_filter_eq_common_powerset

源码起始行：50。

```lean
theorem row_powerset_filter_eq_common_powerset
    {Prime : Type*} [DecidableEq Prime]
    (columnSupport rowSupport : Finset Prime) :
    rowSupport.powerset.filter (fun d => d ⊆ columnSupport) =
      (columnSupport ∩ rowSupport).powerset := by
```

### support_coprime_mask_eq_row_divisor_sum

源码起始行：61。

```lean
theorem support_coprime_mask_eq_row_divisor_sum
    {Prime : Type*} [DecidableEq Prime]
    (columnSupport rowSupport : Finset Prime) :
    (if Disjoint columnSupport rowSupport then (1 : ℂ) else 0) =
      ∑ d ∈ rowSupport.powerset,
        if d ⊆ columnSupport then (-1 : ℂ) ^ d.card else 0 := by
```

### support_mask_column_expansion

源码起始行：72。

```lean
theorem support_mask_column_expansion
    {Prime P : Type*} [DecidableEq Prime]
    (columns : Finset P) (columnSupport : P → Finset Prime)
    (rowSupport : Finset Prime) (F : P → ℂ) :
    (∑ p ∈ columns,
      (if Disjoint (columnSupport p) rowSupport then (1 : ℂ) else 0) * F p) =
      ∑ d ∈ rowSupport.powerset, (-1 : ℂ) ^ d.card *
        ∑ p ∈ columns with d ⊆ columnSupport p, F p := by
```

### support_mask_row_expansion

源码起始行：100。

```lean
theorem support_mask_row_expansion
    {Prime K P : Type*} [DecidableEq Prime]
    (columns : Finset P) (rowSupport : K → Finset Prime)
    (columnSupport : P → Finset Prime) (F : K → P → ℂ) (k : K) :
    (∑ p ∈ columns,
      (if Disjoint (columnSupport p) (rowSupport k) then (1 : ℂ) else 0) * F k p) =
      ∑ d ∈ (rowSupport k).powerset, (-1 : ℂ) ^ d.card *
        ∑ p ∈ columns with d ⊆ columnSupport p, F k p :=
```

### support_mask_row_energy_local_count

源码起始行：111。

```lean
theorem support_mask_row_energy_local_count
    {Prime K P : Type*} [DecidableEq Prime]
    (rows : Finset K) (columns : Finset P)
    (rowSupport : K → Finset Prime) (columnSupport : P → Finset Prime)
    (F : K → P → ℂ) :
    (∑ k ∈ rows, ‖∑ p ∈ columns,
      (if Disjoint (columnSupport p) (rowSupport k) then (1 : ℂ) else 0) * F k p‖ ^ 2) ≤
      ∑ k ∈ rows, (((rowSupport k).powerset).card : ℝ) *
        ∑ d ∈ (rowSupport k).powerset,
          ‖∑ p ∈ columns with d ⊆ columnSupport p, F k p‖ ^ 2 := by
```

### support_mask_row_energy

源码起始行：131。

```lean
theorem support_mask_row_energy
    {Prime K P : Type*} [DecidableEq Prime]
    (rows : Finset K) (columns : Finset P)
    (rowSupport : K → Finset Prime) (columnSupport : P → Finset Prime)
    (F : K → P → ℂ) (Delta : ℝ)
    (hcard : ∀ k ∈ rows, (((rowSupport k).powerset).card : ℝ) ≤ Delta) :
    (∑ k ∈ rows, ‖∑ p ∈ columns,
      (if Disjoint (columnSupport p) (rowSupport k) then (1 : ℂ) else 0) * F k p‖ ^ 2) ≤
      Delta * ∑ k ∈ rows, ∑ d ∈ (rowSupport k).powerset,
        ‖∑ p ∈ columns with d ⊆ columnSupport p, F k p‖ ^ 2 := by
```

## HeckeSkeleton/LowHybrid/NaturalLosses.lean

源码 SHA-256：`3d0f29b936c86de66780797560bb18b868e45327f6862f0d29cd1366d48c5957`。

### natural_hybrid_arithmetic_loss_le

源码起始行：21。

```lean
theorem natural_hybrid_arithmetic_loss_le
    (divisor harmonic : ℝ → ℝ) (CD CH eta K N B L : ℝ)
    (hCD : 0 ≤ CD) (hCH : 0 ≤ CH) (heta : 0 ≤ eta)
    (hK : 1 ≤ K) (hN : 1 ≤ N) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hd0 : ∀ X : ℝ, 1 ≤ X → 0 ≤ divisor X)
    (hh0 : ∀ X : ℝ, 1 ≤ X → 0 ≤ harmonic X)
    (hd : ∀ X : ℝ, 1 ≤ X → divisor X ≤ CD * X ^ eta)
    (hh : ∀ X : ℝ, 1 ≤ X → harmonic X ≤ CH * X ^ eta) :
    naturalHybridArithmeticLoss divisor harmonic eta K N B L ≤
      (CD ^ 5 * CH ^ 5) * (K * N * B * L) ^ (12 * eta) := by
```

### natural_hybrid_arithmetic_loss_subpower

源码起始行：79。

```lean
theorem natural_hybrid_arithmetic_loss_subpower
    (divisor harmonic : ℝ → ℝ)
    (hd0 : ∀ X : ℝ, 1 ≤ X → 0 ≤ divisor X)
    (hh0 : ∀ X : ℝ, 1 ≤ X → 0 ≤ harmonic X)
    (hd : SubpowerBound divisor) (hh : SubpowerBound harmonic)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ eta C : ℝ, 0 < eta ∧ 0 < C ∧
      ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
        naturalHybridArithmeticLoss divisor harmonic eta K N B L ≤
          C * (K * N * B * L) ^ eps := by
```

## HeckeSkeleton/LowHybrid/NormalForm.lean

源码 SHA-256：`8a824e50a35c8f8daec4e5a6a12e9da61436a2c295664781d14e8cfc1f3bae4c`。

### rotate_three_sums（私有辅助）

源码起始行：19。

```lean
private theorem rotate_three_sums {A B C : Type*}
    (as : Finset A) (bs : Finset B) (cs : Finset C) (F : A → B → C → ℂ) :
    (∑ a ∈ as, ∑ b ∈ bs, ∑ c ∈ cs, F a b c) =
      ∑ b ∈ bs, ∑ c ∈ cs, ∑ a ∈ as, F a b c := by
```

### first_divisor_summand

源码起始行：44。

```lean
theorem first_divisor_summand (a : I → ℂ) (beta : I → I → ℂ)
    (d k p n b : I) :
    (a (d * p) / (Real.sqrt (S.normI (d * p)) : ℂ)) *
      (beta n b * (S.quadratic (d * k) (n * b) *
        S.cubic (d * p) n * S.mask (d * p) b)) =
    S.weight d * (S.firstBeta beta d n b * S.quadratic k (n * b) *
      ((a (d * p) / (Real.sqrt (S.normI p) : ℂ)) * S.cubic p n * S.mask p b)) := by
```

### first_divisor_column_sum

源码起始行：55。

```lean
theorem first_divisor_column_sum (a : I → ℂ) (beta : I → I → ℂ)
    (marks columns cubes : Finset I) (d k : I) :
    (∑ p ∈ S.markQuotients marks d,
      (a (d * p) / (Real.sqrt (S.normI (d * p)) : ℂ)) *
        ∑ n ∈ columns, ∑ b ∈ cubes, beta n b *
          (S.quadratic (d * k) (n * b) * S.cubic (d * p) n * S.mask (d * p) b)) =
      S.weight d * S.firstRow a beta marks columns cubes d k := by
```

### hybridRow_first_expansion

源码起始行：75。

```lean
theorem hybridRow_first_expansion (a : I → ℂ) (beta : I → I → ℂ)
    (marks columns cubes : Finset I) (k : I) :
    hybridRow S.symbol S.cop S.normI a beta marks columns cubes k =
      ∑ d ∈ S.divisors k, S.mu d *
        (S.weight d * S.firstRow a beta marks columns cubes d (S.quotient d k)) := by
```

### firstColumn_completed

源码起始行：118。

```lean
theorem firstColumn_completed (a : I → ℂ) (marks : Finset I) (d r t c m h : I) :
    S.firstColumn a marks d (r * c * m) (r * c * h * t ^ 2) =
      S.blockColumn a marks d r t c m h := by
```

### firstRow_completed

源码起始行：136。

```lean
theorem firstRow_completed (a : I → ℂ) (beta : I → I → ℂ)
    (marks columns cubes : Finset I) (C : Completion columns cubes) (d k : I) :
    S.firstRow a beta marks columns cubes d k =
      ∑ v ∈ C.support, S.mask k v.2.1 *
        (S.mask k v.1 * S.quadratic k (v.2.2.1 * v.2.2.2) *
          (S.firstBeta beta d (recombine v).1 (recombine v).2 *
            S.firstColumn a marks d (recombine v).1 (recombine v).2)) := by
```

### firstRow_second_expansion

源码起始行：153。

```lean
theorem firstRow_second_expansion (a : I → ℂ) (beta : I → I → ℂ)
    (marks columns cubes : Finset I) (C : Completion columns cubes) (d k : I) :
    S.firstRow a beta marks columns cubes d k =
      ∑ r ∈ S.divisors k, S.mu r * S.blockRowSupport a beta marks C.support d r k := by
```

### hybridRow_normal_form

源码起始行：180。

```lean
theorem hybridRow_normal_form (a : I → ℂ) (beta : I → I → ℂ)
    (marks columns cubes : Finset I) (C : Completion columns cubes) (k : I) :
    hybridRow S.symbol S.cop S.normI a beta marks columns cubes k =
      ∑ d ∈ S.divisors k, ∑ r ∈ S.divisors (S.quotient d k),
        (S.mu d * S.mu r) * (S.weight d *
          S.blockRowSupport a beta marks C.support d r (S.quotient d k)) := by
```

### blockRowSupport_eq_box

源码起始行：208。

```lean
theorem blockRowSupport_eq_box (a : I → ℂ) (beta : I → I → ℂ)
    (marks : Finset I) (support : Finset (CompletedIndex I))
    (ts cs ms hs : Finset I) (d r k : I)
    (hbox : S.blockSupport support r ⊆ completedBox ts cs ms hs) :
    S.blockRowSupport a beta marks support d r k =
      S.blockRowBox a beta marks support ts cs ms hs d r k := by
```

## HeckeSkeleton/LowHybrid/NormalFormAlgebra.lean

源码 SHA-256：`7d70034bb4ef2e75387da82f3dee900bf9f0a0cedef4863a73a014a7f331fbb7`。

### mask_symm

源码起始行：50。

```lean
theorem mask_symm (x y : I) : S.mask x y = S.mask y x := by
```

### mask_mul_left

源码起始行：53。

```lean
theorem mask_mul_left (x y z : I) : S.mask (x * y) z = S.mask x z * S.mask y z := by
```

### mask_mul_right

源码起始行：57。

```lean
theorem mask_mul_right (x y z : I) : S.mask x (y * z) = S.mask x y * S.mask x z := by
```

### mask_square

源码起始行：61。

```lean
theorem mask_square (x y : I) : S.mask x (y ^ 2) = S.mask x y := by
```

### symbol_zero

源码起始行：64。

```lean
theorem symbol_zero (x y : I) (h : ¬ S.cop x y) : S.symbol x y = 0 := by
```

### quadratic_mul_left

源码起始行：68。

```lean
theorem quadratic_mul_left (x y z : I) :
    S.quadratic (x * y) z = S.quadratic x z * S.quadratic y z := by
```

### quadratic_mul_right

源码起始行：72。

```lean
theorem quadratic_mul_right (x y z : I) :
    S.quadratic x (y * z) = S.quadratic x y * S.quadratic x z := by
```

### cubic_mul_left

源码起始行：76。

```lean
theorem cubic_mul_left (x y z : I) :
    S.cubic (x * y) z = S.cubic x z * S.cubic y z := by
```

### cubic_mul_right

源码起始行：80。

```lean
theorem cubic_mul_right (x y z : I) :
    S.cubic x (y * z) = S.cubic x y * S.cubic x z := by
```

### cubic_mask

源码起始行：84。

```lean
theorem cubic_mask (x y : I) : S.cubic x y * S.mask x y = S.cubic x y := by
```

### quadratic_square

源码起始行：89。

```lean
theorem quadratic_square (x y : I) : S.quadratic x (y ^ 2) = S.mask x y := by
```

### completed_quadratic

源码起始行：97。

```lean
theorem completed_quadratic (k t c m h : I) :
    S.quadratic k ((c * m) * (c * h * t ^ 2)) =
      S.quadratic k (m * h) * S.mask k c * S.mask k t := by
```

### completed_cubic

源码起始行：107。

```lean
theorem completed_cubic (p r t c m h : I) :
    S.cubic p (r * c * m) * S.mask p (r * c * h * t ^ 2) =
      S.cubic p r * S.cubic p (c * m) * S.mask p (h * t) := by
```

### normalization_mul

源码起始行：116。

```lean
theorem normalization_mul (d p : I) (a : ℂ) :
    a / (Real.sqrt (S.normI (d * p)) : ℂ) =
      S.weight d * (a / (Real.sqrt (S.normI p) : ℂ)) := by
```

### sum_divisor_reindex

源码起始行：129。

```lean
theorem sum_divisor_reindex (marks : Finset I) (d : I) (F : I → ℂ) :
    (∑ p ∈ marks with d ∣ p, F p) =
      ∑ p ∈ S.markQuotients marks d, F (d * p) := by
```

### mask_sum_expansion

源码起始行：142。

```lean
theorem mask_sum_expansion (marks : Finset I) (k : I) (F : I → ℂ) :
    (∑ p ∈ marks, S.mask p k * F p) =
      ∑ d ∈ S.divisors k, S.mu d * ∑ p ∈ marks with d ∣ p, F p := by
```

## HeckeSkeleton/LowHybrid/NormalFormBound.lean

源码 SHA-256：`a9bd69f4cb99d2c002b846ec603e28bda50d66bc8503e5aa3e82c5358dc14088`。

### hybridEnergy_finite_bound

源码起始行：60。

```lean
theorem hybridEnergy_finite_bound (sf : I → Prop)
    (hnorm : ∀ x, 1 ≤ S.normI x) (hmu : ∀ x, ‖S.mu x‖ ≤ 1)
    (hq : QuadraticSieveInput S.normI sf S.symbol)
    (hc : CubicSieveInput S.normI sf S.symbol) (eta : ℝ) (heta : 0 < eta) :
    ∃ C0 : ℝ, 0 < C0 ∧
    ∀ K Y N L : ℝ, 1 ≤ K → 1 ≤ Y → 1 ≤ N → 1 ≤ L →
    ∀ (rows marks columns cubes ds rs : Finset I) (C : Completion columns cubes)
      (ts cs ms hs : I → I → Finset I)
      (goodPairs goodMC : I → I → Finset (I × I)) (qset jset : Finset I)
      (a : I → ℂ) (beta : I → I → ℂ) (B Delta Dq Dc Ht Hc Hh : ℝ),
      0 ≤ B → 0 ≤ Delta → 0 ≤ Dq → 0 ≤ Dc → 0 ≤ Ht → 0 ≤ Hc → 0 ≤ Hh →
      (∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ 1) →
      (∀ b ∈ cubes, S.normI b ≤ B) →
      S.FiniteInputs sf rows marks columns cubes ds rs C ts cs ms hs goodPairs goodMC
        qset jset K Y N L Delta Dq Dc Ht Hc Hh →
      hybridEnergy S.symbol S.cop S.normI a beta rows marks columns cubes ≤
        C0 * Delta * Dq * Dc * (K * Y * N * L) ^ eta * (K + Y) * B *
          (N + L + (N * L) ^ (2 / 3 : ℝ)) * Ht ^ 2 * Hc * Hh *
          (∑ d ∈ ds, S.columnMass a marks d / S.normI d) *
          (∑ r ∈ rs, 1 / S.normI r) := by
```

## HeckeSkeleton/LowHybrid/NormalFormFinite.lean

源码 SHA-256：`ac89af86ed6a268f5793c30d958faa0d9b690f1da0ec267ab231ae5f325355c7`。

### split_injective_on

源码起始行：37。

```lean
theorem split_injective_on : Set.InjOn C.split ↑(columns ×ˢ cubes) := by
```

### sum_reindex

源码起始行：44。

```lean
theorem sum_reindex (F : I → I → ℂ) :
    (∑ n ∈ columns, ∑ b ∈ cubes, F n b) =
      ∑ v ∈ C.support, F (recombine v).1 (recombine v).2 := by
```

### mem_support_recombine

源码起始行：56。

```lean
theorem mem_support_recombine {v : CompletedIndex I} (hv : v ∈ C.support) :
    recombine v ∈ columns ×ˢ cubes := by
```

### restore_quotient_common

源码起始行：73。

```lean
theorem restore_quotient_common (r : I) (v : CompletedIndex I)
    (h : r ∣ v.2.1) : S.restoreCommon r (S.quotientCommon r v) = v := by
```

### sum_common_reindex

源码起始行：83。

```lean
theorem sum_common_reindex (support : Finset (CompletedIndex I)) (r : I)
    (F : CompletedIndex I → ℂ) :
    (∑ v ∈ support with r ∣ v.2.1, F v) =
      ∑ v ∈ S.blockSupport support r, F (S.restoreCommon r v) := by
```

### blockSupport_restore_mem

源码起始行：99。

```lean
theorem blockSupport_restore_mem {support : Finset (CompletedIndex I)}
    {r : I} {v : CompletedIndex I} (hv : v ∈ S.blockSupport support r) :
    S.restoreCommon r v ∈ support := by
```

### mask_common_expansion

源码起始行：107。

```lean
theorem mask_common_expansion (support : Finset (CompletedIndex I)) (k : I)
    (F : CompletedIndex I → ℂ) :
    (∑ v ∈ support, S.mask k v.2.1 * F v) =
      ∑ r ∈ S.divisors k, S.mu r * ∑ v ∈ support with r ∣ v.2.1, F v := by
```

### sum_zero_extend_box

源码起始行：134。

```lean
theorem sum_zero_extend_box (support : Finset (CompletedIndex I))
    (ts cs ms hs : Finset I) (hsub : support ⊆ completedBox ts cs ms hs)
    (F : CompletedIndex I → ℂ) :
    (∑ v ∈ support, F v) =
      ∑ t ∈ ts, ∑ c ∈ cs, ∑ m ∈ ms, ∑ h ∈ hs,
        if (t, c, m, h) ∈ support then F (t, c, m, h) else 0 := by
```

## HeckeSkeleton/LowHybrid/NormalFormKernels.lean

源码 SHA-256：`25642299e9ad6cfe5d5f844f8f11293693900150e0ec6838f76f60871a079db6`。

### blockRowBox_eq_zero

源码起始行：35。

```lean
theorem blockRowBox_eq_zero (a : I → ℂ) (beta : I → I → ℂ)
    (marks : Finset I) (support : Finset (CompletedIndex I))
    (ts cs ms hs : Finset I) (goodPairs goodMC : Finset (I × I)) (d r k : I)
    (hq : ∀ v ∈ S.blockSupport support r, (v.2.2.1, v.2.2.2) ∈ goodPairs)
    (hc : ∀ v ∈ S.blockSupport support r, (v.2.2.1, v.2.1) ∈ goodMC) :
    S.blockRowBox a beta marks support ts cs ms hs d r k =
      S.blockRowZero a beta marks support ts cs ms hs goodPairs goodMC d r k := by
```

### weightedBlock_row

源码起始行：85。

```lean
theorem weightedBlock_row (a : I → ℂ) (beta : I → I → ℂ)
    (marks : Finset I) (support : Finset (CompletedIndex I))
    (ts cs ms hs : Finset I) (goodPairs goodMC : Finset (I × I)) (d r k : I) :
    (S.weightedBlock a beta marks support ts cs ms hs goodPairs goodMC d r).row k =
      S.blockRowZero a beta marks support ts cs ms hs goodPairs goodMC
        d r (S.quotient d k) :=
```

### mem_divisorPairs

源码起始行：96。

```lean
theorem mem_divisorPairs (k d r : I) :
    (d, r) ∈ S.divisorPairs k ↔
      d ∈ S.divisors k ∧ r ∈ S.divisors (S.quotient d k) := by
```

### divisorPairs_disjoint

源码起始行：108。

```lean
theorem divisorPairs_disjoint (k : I) :
    Set.PairwiseDisjoint (↑(S.divisors k))
      (fun d => (S.divisors (S.quotient d k)).image fun r => (d, r)) := by
```

### sum_divisorPairs

源码起始行：119。

```lean
theorem sum_divisorPairs (k : I) (F : I × I → ℂ) :
    (∑ dr ∈ S.divisorPairs k, F dr) =
      ∑ d ∈ S.divisors k, ∑ r ∈ S.divisors (S.quotient d k), F (d, r) := by
```

### card_divisorPairs

源码起始行：130。

```lean
theorem card_divisorPairs (k : I) :
    (S.divisorPairs k).card =
      ∑ d ∈ S.divisors k, (S.divisors (S.quotient d k)).card := by
```

### hybridRow_eq_weightedBlocks

源码起始行：142。

```lean
theorem hybridRow_eq_weightedBlocks (a : I → ℂ) (beta : I → I → ℂ)
    (marks columns cubes : Finset I) (C : Completion columns cubes)
    (ts cs ms hs : I → I → Finset I)
    (goodPairs goodMC : I → I → Finset (I × I)) (k : I)
    (hbox : ∀ d ∈ S.divisors k, ∀ r ∈ S.divisors (S.quotient d k),
      S.blockSupport C.support r ⊆ completedBox (ts d r) (cs d r) (ms d r) (hs d r))
    (hq : ∀ d ∈ S.divisors k, ∀ r ∈ S.divisors (S.quotient d k),
      ∀ v ∈ S.blockSupport C.support r, (v.2.2.1, v.2.2.2) ∈ goodPairs d r)
    (hc : ∀ d ∈ S.divisors k, ∀ r ∈ S.divisors (S.quotient d k),
      ∀ v ∈ S.blockSupport C.support r, (v.2.2.1, v.2.1) ∈ goodMC d r) :
    hybridRow S.symbol S.cop S.normI a beta marks columns cubes k =
      ∑ dr ∈ S.divisorPairs k, (S.mu dr.1 * S.mu dr.2) *
        (((1 : ℂ) / (Real.sqrt (S.normI dr.1) : ℂ)) *
          (S.weightedBlock a beta marks C.support
            (ts dr.1 dr.2) (cs dr.1 dr.2) (ms dr.1 dr.2) (hs dr.1 dr.2)
            (goodPairs dr.1 dr.2) (goodMC dr.1 dr.2) dr.1 dr.2).row k) := by
```

## HeckeSkeleton/LowHybrid/NormalFormSupport.lean

源码 SHA-256：`1eb59ea8d53178afdf867546c60d7ee6e277a21926e1d19772062a00936d1c31`。

### markQuotients_mul_mem

源码起始行：21。

```lean
theorem markQuotients_mul_mem {marks : Finset I} {d p : I}
    (hp : p ∈ S.markQuotients marks d) : d * p ∈ marks := by
```

### blockSupport_original_mem

源码起始行：29。

```lean
theorem blockSupport_original_mem {columns cubes : Finset I}
    (C : Completion columns cubes) {r : I} {v : CompletedIndex I}
    (hv : v ∈ S.blockSupport C.support r) :
    r * v.2.1 * v.2.2.1 ∈ columns ∧
      r * v.2.1 * v.2.2.2 * v.1 ^ 2 ∈ cubes := by
```

### blockBeta_ne_zero_mem

源码起始行：37。

```lean
theorem blockBeta_ne_zero_mem (beta : I → I → ℂ)
    (support : Finset (CompletedIndex I)) (d r t c m h : I)
    (hb : S.blockBeta beta support d r t c m h ≠ 0) :
    (t, c, m, h) ∈ S.blockSupport support r := by
```

### blockBeta_ne_zero_original_mem

源码起始行：46。

```lean
theorem blockBeta_ne_zero_original_mem {columns cubes : Finset I}
    (C : Completion columns cubes) (beta : I → I → ℂ) (d r t c m h : I)
    (hb : S.blockBeta beta C.support d r t c m h ≠ 0) :
    r * c * m ∈ columns ∧ r * c * h * t ^ 2 ∈ cubes :=
```

### completed_cube_norm

源码起始行：53。

```lean
theorem completed_cube_norm (r t c h : I) :
    S.normI (r * c * h * t ^ 2) =
      S.normI r * S.normI c * S.normI h * S.normI t ^ 2 := by
```

### completed_column_norm

源码起始行：58。

```lean
theorem completed_column_norm (r c m : I) :
    S.normI (r * c * m) = S.normI r * S.normI c * S.normI m := by
```

### blockBeta_cube_support

源码起始行：62。

```lean
theorem blockBeta_cube_support {columns cubes : Finset I}
    (C : Completion columns cubes) (beta : I → I → ℂ) (B : ℝ)
    (hB : ∀ b ∈ cubes, S.normI b ≤ B) (d r t c m h : I)
    (hb : S.blockBeta beta C.support d r t c m h ≠ 0) :
    S.normI r * S.normI c * S.normI h * S.normI t ^ 2 ≤ B := by
```

### blockBeta_column_support

源码起始行：70。

```lean
theorem blockBeta_column_support {columns cubes : Finset I}
    (C : Completion columns cubes) (beta : I → I → ℂ) (N : ℝ)
    (hN : ∀ n ∈ columns, S.normI n ≤ N) (d r t c m h : I)
    (hb : S.blockBeta beta C.support d r t c m h ≠ 0) :
    S.normI r * S.normI c * S.normI m ≤ N := by
```

## HeckeSkeleton/LowHybrid/NormalFormUniform.lean

源码 SHA-256：`d9d503deb64e4ab4ac6efa7ab2a7defe99e13fd784666dfc3798f4e0414609ca`。

### originalColumnMass_nonneg

源码起始行：27。

```lean
theorem originalColumnMass_nonneg (a : I → ℂ) (marks : Finset I) :
    0 ≤ S.originalColumnMass a marks :=
```

### hybrid_energy_of_finite_inputs

源码起始行：34。

```lean
theorem hybrid_energy_of_finite_inputs (sf : I → Prop)
    (hnorm : ∀ x, 1 ≤ S.normI x) (hmu : ∀ x, ‖S.mu x‖ ≤ 1)
    (hq : QuadraticSieveInput S.normI sf S.symbol)
    (hc : CubicSieveInput S.normI sf S.symbol)
    (divisor harmonic : ℝ → ℝ)
    (hd0 : ∀ X : ℝ, 1 ≤ X → 0 ≤ divisor X)
    (hh0 : ∀ X : ℝ, 1 ≤ X → 0 ≤ harmonic X)
    (hd : SubpowerBound divisor) (hh : SubpowerBound harmonic)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C0 : ℝ, 0 < C0 ∧
    ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
    ∀ (rows marks columns cubes ds rs : Finset I) (C : Completion columns cubes)
      (ts cs ms hs : I → I → Finset I)
      (goodPairs goodMC : I → I → Finset (I × I)) (qset jset : Finset I)
      (a : I → ℂ) (beta : I → I → ℂ),
      (∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ 1) →
      (∀ b ∈ cubes, S.normI b ≤ B) →
      S.FiniteInputs sf rows marks columns cubes ds rs C ts cs ms hs goodPairs goodMC
        qset jset K (N * B) N L (divisor K ^ 2) (divisor (N * B)) (divisor N)
        (harmonic B) (harmonic N) (harmonic B) →
      (∑ d ∈ ds, S.columnMass a marks d / S.normI d) ≤
        divisor L * S.originalColumnMass a marks →
      (∑ r ∈ rs, 1 / S.normI r) ≤ harmonic K →
      hybridEnergy S.symbol S.cop S.normI a beta rows marks columns cubes ≤
        C0 * (K * N * B * L) ^ eps * (K + N * B) * B *
          (N + L + (N * L) ^ (2 / 3 : ℝ)) * S.originalColumnMass a marks := by
```

## HeckeSkeleton/LowHybrid/Normalization.lean

源码 SHA-256：`46a355aa59dee9d009aec213a0948592972f82f32678126f97c65d26ecda9a2a`。

### norm_div_sqrt_sq

源码起始行：17。

```lean
theorem norm_div_sqrt_sq (a : ℂ) (q : ℝ) (hq : 0 ≤ q) :
    ‖a / (Real.sqrt q : ℂ)‖ ^ 2 = ‖a‖ ^ 2 / q := by
```

### normalized_column_mass

源码起始行：22。

```lean
theorem normalized_column_mass {P : Type*} (columns : Finset P)
    (a : P → ℂ) (normP : P → ℝ) (hpos : ∀ p ∈ columns, 0 ≤ normP p) :
    (∑ p ∈ columns, ‖a p / (Real.sqrt (normP p) : ℂ)‖ ^ 2) =
      ∑ p ∈ columns, ‖a p‖ ^ 2 / normP p := by
```

### annular_normalized_mass_le

源码起始行：30。

```lean
theorem annular_normalized_mass_le {P : Type*} (columns : Finset P)
    (a : P → ℂ) (normP : P → ℝ) (L C : ℝ) (hL : 0 < L)
    (ha : ∀ p ∈ columns, ‖a p‖ ≤ 1)
    (hlower : ∀ p ∈ columns, L ≤ normP p)
    (hcount : (columns.card : ℝ) ≤ C * (2 * L)) :
    (∑ p ∈ columns, ‖a p / (Real.sqrt (normP p) : ℂ)‖ ^ 2) ≤ 2 * C := by
```

### divisor_column_normalization

源码起始行：50。

```lean
theorem divisor_column_normalization (D Q : ℝ) (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (a : ℂ) :
    a / (Real.sqrt (D * Q) : ℂ) =
      (Real.sqrt D : ℂ)⁻¹ * (a / (Real.sqrt Q : ℂ)) := by
```

### divisor_weight_sq

源码起始行：57。

```lean
theorem divisor_weight_sq (D : ℝ) (hD : 0 ≤ D) :
    ‖(Real.sqrt D : ℂ)⁻¹‖ ^ 2 = 1 / D := by
```

### scalar_row_energy

源码起始行：62。

```lean
theorem scalar_row_energy {K : Type*} (rows : Finset K) (f : K → ℂ) (a : ℂ) :
    (∑ k ∈ rows, ‖a * f k‖ ^ 2) = ‖a‖ ^ 2 * ∑ k ∈ rows, ‖f k‖ ^ 2 := by
```

### cube_support_weight_budget

源码起始行：71。

```lean
theorem cube_support_weight_budget (wt wc wh r B : ℝ) (beta : ℂ)
    (hwt : 0 < wt) (hwc : 0 ≤ wc) (hwh : 0 < wh) (hr : 0 < r)
    (hB : 0 ≤ B) (hbeta : ‖beta‖ ≤ 1)
    (hsupport : beta ≠ 0 → r * wc * wh * wt ^ 2 ≤ B) :
    wt * wc * ‖beta‖ ^ 2 ≤ (B / r) / (wt * wh) := by
```

## HeckeSkeleton/LowHybrid/Parameters.lean

源码 SHA-256：`6fef533e2f53bb523439d2e66a93d06faa01c7a782946a306795e5fd19ab03f7`。

### cube_block_squarefree_le

源码起始行：19。

```lean
theorem cube_block_squarefree_le (T G B : ℝ)
    (hT : 1 ≤ T) (hG : 0 ≤ G) (hB : T ^ 2 * G = B) : G ≤ B := by
```

### completed_quadratic_parameter_le

源码起始行：29。

```lean
theorem completed_quadratic_parameter_le (K N D r C T G B : ℝ)
    (hK : 1 ≤ K) (hN : 1 ≤ N) (hD : 1 ≤ D) (hr : 1 ≤ r)
    (hC : 1 ≤ C) (hT : 1 ≤ T) (hG : 0 ≤ G)
    (hB : T ^ 2 * G = B) :
    K / (D * r) + N * G / C ^ 2 ≤ K + N * B := by
```

### completed_cubic_parameter_le

源码起始行：48。

```lean
theorem completed_cubic_parameter_le (N L D r : ℝ)
    (hN : 1 ≤ N) (hL : 1 ≤ L) (hD : 1 ≤ D) (hr : 1 ≤ r) :
    N / r + L / D + (N * L / (r * D)) ^ (2 / 3 : ℝ) ≤
      N + L + (N * L) ^ (2 / 3 : ℝ) := by
```

### completed_cubic_parameter_nonneg

源码起始行：66。

```lean
theorem completed_cubic_parameter_nonneg (N L D r : ℝ)
    (hN : 1 ≤ N) (hL : 1 ≤ L) (hD : 1 ≤ D) (hr : 1 ≤ r) :
    0 ≤ N / r + L / D + (N * L / (r * D)) ^ (2 / 3 : ℝ) := by
```

### completed_cube_count

源码起始行：79。

```lean
theorem completed_cube_count (T G C r B : ℝ)
    (hC : 1 ≤ C) (hr : 1 ≤ r) (hB : T ^ 2 * G = B) :
    T ^ 2 * (C / r) * (G / C) = B / r := by
```

### block_envelope

源码起始行：94。

```lean
theorem block_envelope (K N L D r C T G B A : ℝ)
    (hK : 1 ≤ K) (hN : 1 ≤ N) (hL : 1 ≤ L)
    (hD : 1 ≤ D) (hr : 1 ≤ r) (hC : 1 ≤ C) (hT : 1 ≤ T)
    (hG : 0 ≤ G) (hA : 0 ≤ A) (hB : T ^ 2 * G = B) :
    completedBlock K N L D r C T G A ≤
      (K + N * B) * (B / r) * (N + L + (N * L) ^ (2 / 3 : ℝ)) * A := by
```

### normalized_block_envelope

源码起始行：126。

```lean
theorem normalized_block_envelope (K N L D r C T G B A : ℝ)
    (hK : 1 ≤ K) (hN : 1 ≤ N) (hL : 1 ≤ L)
    (hD : 1 ≤ D) (hr : 1 ≤ r) (hC : 1 ≤ C) (hT : 1 ≤ T)
    (hG : 0 ≤ G) (hA : 0 ≤ A) (hB : T ^ 2 * G = B) :
    (1 / D) * completedBlock K N L D r C T G A ≤
      (K + N * B) * B * (N + L + (N * L) ^ (2 / 3 : ℝ)) *
        (A / D) * (1 / r) := by
```

### normalized_blocks_sum_le

源码起始行：146。

```lean
theorem normalized_blocks_sum_le {DIndex RIndex : Type*}
    (ds : Finset DIndex) (rs : Finset RIndex)
    (dNorm : DIndex → ℝ) (rNorm : RIndex → ℝ)
    (C T G : DIndex → RIndex → ℝ) (A : DIndex → ℝ)
    (K N L B : ℝ) (hK : 1 ≤ K) (hN : 1 ≤ N) (hL : 1 ≤ L)
    (hD : ∀ d ∈ ds, 1 ≤ dNorm d)
    (hr : ∀ r ∈ rs, 1 ≤ rNorm r)
    (hC : ∀ d ∈ ds, ∀ r ∈ rs, 1 ≤ C d r)
    (hT : ∀ d ∈ ds, ∀ r ∈ rs, 1 ≤ T d r)
    (hG : ∀ d ∈ ds, ∀ r ∈ rs, 0 ≤ G d r)
    (hA : ∀ d ∈ ds, 0 ≤ A d)
    (hB : ∀ d ∈ ds, ∀ r ∈ rs, (T d r) ^ 2 * G d r = B) :
    (∑ d ∈ ds, ∑ r ∈ rs, (1 / dNorm d) *
      completedBlock K N L (dNorm d) (rNorm r) (C d r) (T d r) (G d r) (A d)) ≤
      (K + N * B) * B * (N + L + (N * L) ^ (2 / 3 : ℝ)) *
        (∑ d ∈ ds, A d / dNorm d) * (∑ r ∈ rs, 1 / rNorm r) := by
```

## HeckeSkeleton/LowHybrid/PrimeArithmetic.lean

源码 SHA-256：`8f4f60f04cfdb45812f457d1955295dd1640a363abafe66a4089fe7c98ec37ca`。

### valuation_mapTwo

源码起始行：32。

```lean
@[simp] theorem valuation_mapTwo (f : ℕ → ℕ → ℕ) (hf : f 0 0 = 0)
    (a b : A) (p : ι) :
    valuation coords (mapTwo coords f hf a b) p =
      f (valuation coords a p) (valuation coords b p) := by
```

### valuation_quotient

源码起始行：40。

```lean
@[simp] theorem valuation_quotient (d k : A) (p : ι) :
    valuation coords (quotient coords d k) p =
      valuation coords k p - valuation coords d p := by
```

### dvd_iff_coordinates_le

源码起始行：45。

```lean
theorem dvd_iff_coordinates_le (a b : A) :
    a ∣ b ↔ ∀ p, valuation coords a p ≤ valuation coords b p := by
```

### quotient_spec

源码起始行：59。

```lean
theorem quotient_spec (d k : A) (h : d ∣ k) : d * quotient coords d k = k := by
```

### valuation_fromSupport

源码起始行：72。

```lean
@[simp] theorem valuation_fromSupport (s : Finset ι) (p : ι) :
    valuation coords (fromSupport coords s) p = if p ∈ s then 1 else 0 := by
```

### support_fromSupport

源码起始行：76。

```lean
@[simp] theorem support_fromSupport (s : Finset ι) :
    support coords (fromSupport coords s) = s := by
```

### fromSupport_injective

源码起始行：81。

```lean
theorem fromSupport_injective : Function.Injective (fromSupport coords) := by
```

### fromSupport_dvd_iff

源码起始行：85。

```lean
theorem fromSupport_dvd_iff (s : Finset ι) (a : A) :
    fromSupport coords s ∣ a ↔ s ⊆ support coords a := by
```

### coprime_iff_disjoint_support

源码起始行：101。

```lean
theorem coprime_iff_disjoint_support (a b : A) :
    Coprime coords a b ↔ Disjoint (support coords a) (support coords b) := by
```

### divisor_dvd

源码起始行：123。

```lean
theorem divisor_dvd (a d : A) (hd : d ∈ divisors coords a) : d ∣ a := by
```

### mobius_norm

源码起始行：127。

```lean
theorem mobius_norm (a : A) : ‖mobius coords a‖ = 1 := by
```

### mobius_expansion

源码起始行：129。

```lean
theorem mobius_expansion (p k : A) :
    (if Coprime coords p k then (1 : ℂ) else 0) =
      ∑ d ∈ divisors coords k, if d ∣ p then mobius coords d else 0 := by
```

### completedSplit_reconstruct

源码起始行：191。

```lean
theorem completedSplit_reconstruct (x : A × A) :
    recombine (completedSplit coords x) = x := by
```

### squarefree_of_dvd

源码起始行：228。

```lean
theorem squarefree_of_dvd {a b : A} (ha : a ∣ b) (hb : Squarefree coords b) :
    Squarefree coords a := by
```

### completed_residual_squarefree

源码起始行：233。

```lean
theorem completed_residual_squarefree (n b : A) (hn : Squarefree coords n) :
    Squarefree coords (leftPart coords n b * rightPart coords n b) := by
```

### squarefree_mem_divisors

源码起始行：240。

```lean
theorem squarefree_mem_divisors (a d : A) (hd : d ∈ divisors coords a) :
    Squarefree coords d := by
```

## HeckeSkeleton/LowHybrid/PrimeDivisorBounds.lean

源码 SHA-256：`b1cc77a2ff4e26dcd70ede2bd3f6be1ff1e9de057acef3020852011ed85cde52`。

### card_divisors

源码起始行：25。

```lean
theorem card_divisors (a : A) :
    (divisors coords a).card = 2 ^ (support coords a).card := by
```

### card_divisors_real

源码起始行：31。

```lean
theorem card_divisors_real (a : A) :
    ((divisors coords a).card : ℝ) = (2 : ℝ) ^ (support coords a).card := by
```

### norm_le_of_dvd

源码起始行：37。

```lean
theorem norm_le_of_dvd (normI : A →* ℝ) (hn : ∀ a, 1 ≤ normI a)
    {a b : A} (hab : a ∣ b) : normI a ≤ normI b := by
```

### norm_fromSupport_le

源码起始行：44。

```lean
theorem norm_fromSupport_le (normI : A →* ℝ) (hn : ∀ a, 1 ≤ normI a)
    (a : A) : normI (fromSupport coords (support coords a)) ≤ normI a := by
```

### singleton_fromSupport_injective

源码起始行：49。

```lean
theorem singleton_fromSupport_injective :
    Function.Injective (fun p : ι => fromSupport coords {p}) := by
```

### finite_singleton_prime_norms

源码起始行：55。

```lean
theorem finite_singleton_prime_norms
    (normI : A → ℝ) (hfinite : ∀ X : ℝ, Set.Finite {a : A | normI a ≤ X})
    (X : ℝ) : Set.Finite {p : ι | normI (fromSupport coords {p}) ≤ X} := by
```

### finite_norms_of_cutoffs

源码起始行：62。

```lean
theorem finite_norms_of_cutoffs
    (normI : A → ℝ) (cutoff : ℝ → Finset A)
    (hcomplete : ∀ X : ℝ, ∀ a : A, normI a ≤ X → a ∈ cutoff X)
    (X : ℝ) : Set.Finite {a : A | normI a ≤ X} :=
```

### prime_product_le_norm

源码起始行：70。

```lean
theorem prime_product_le_norm
    (normI : A →* ℝ) (hn : ∀ a, 1 ≤ normI a) (a : A) :
    (∏ p ∈ support coords a, normI (primeElement coords p)) ≤ normI a := by
```

### finite_prime_norms

源码起始行：86。

```lean
theorem finite_prime_norms
    (normI : A → ℝ) (hfinite : ∀ X : ℝ, Set.Finite {a : A | normI a ≤ X})
    (X : ℝ) : Set.Finite {p : ι | normI (primeElement coords p) ≤ X} := by
```

### divisor_count_subpower

源码起始行：93。

```lean
theorem divisor_count_subpower
    (normI : A →* ℝ) (hn : ∀ a, 1 ≤ normI a)
    (hfinite : ∀ X : ℝ, Set.Finite {a : A | normI a ≤ X})
    (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : A,
      ((divisors coords a).card : ℝ) ≤ C * normI a ^ eta := by
```

### divisor_count_subpower_of_cutoffs

源码起始行：107。

```lean
theorem divisor_count_subpower_of_cutoffs
    (normI : A →* ℝ) (hn : ∀ a, 1 ≤ normI a) (cutoff : ℝ → Finset A)
    (hcomplete : ∀ X : ℝ, ∀ a : A, normI a ≤ X → a ∈ cutoff X)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : A,
      ((divisors coords a).card : ℝ) ≤ C * normI a ^ eta := by
```

### divisor_envelope_subpower

源码起始行：118。

```lean
theorem divisor_envelope_subpower
    (normI : A →* ℝ) (hn : ∀ a, 1 ≤ normI a)
    (hfinite : ∀ X : ℝ, Set.Finite {a : A | normI a ≤ X})
    (cutoff : ℝ → Finset A)
    (hcutoff : ∀ X : ℝ, 1 ≤ X → ∀ a ∈ cutoff X, normI a ≤ X) :
    SubpowerBound (divisorCountEnvelope cutoff (divisors coords)) := by
```

### mem_normCutoff

源码起始行：133。

```lean
@[simp] theorem mem_normCutoff (normI : A → ℝ)
    (hfinite : ∀ X : ℝ, Set.Finite {a : A | normI a ≤ X}) (X : ℝ) (a : A) :
    a ∈ normCutoff normI hfinite X ↔ normI a ≤ X := by
```

### actualDivisorEnvelope_nonneg

源码起始行：144。

```lean
theorem actualDivisorEnvelope_nonneg (normI : A → ℝ)
    (hfinite : ∀ X : ℝ, Set.Finite {a : A | normI a ≤ X}) (X : ℝ) :
    0 ≤ actualDivisorEnvelope coords normI hfinite X :=
```

### divisor_count_le_actual_envelope

源码起始行：149。

```lean
theorem divisor_count_le_actual_envelope (normI : A → ℝ)
    (hfinite : ∀ X : ℝ, Set.Finite {a : A | normI a ≤ X})
    (X : ℝ) (a : A) (ha : normI a ≤ X) :
    ((divisors coords a).card : ℝ) ≤ actualDivisorEnvelope coords normI hfinite X := by
```

### actualDivisorEnvelope_subpower

源码起始行：158。

```lean
theorem actualDivisorEnvelope_subpower
    (normI : A →* ℝ) (hn : ∀ a, 1 ≤ normI a)
    (hfinite : ∀ X : ℝ, Set.Finite {a : A | normI a ≤ X}) :
    SubpowerBound (actualDivisorEnvelope coords normI hfinite) := by
```

## HeckeSkeleton/LowHybrid/ProductBounds.lean

源码 SHA-256：`7e9b1d2e2f074a623c504582a75a80f09d2dd2db3af5afa6437340914ebb1ecf`。

### norm_sextic_le_one

源码起始行：19。

```lean
theorem norm_sextic_le_one (z : ℂ) (hz : z = 0 ∨ z ^ 6 = 1) : ‖z‖ ≤ 1 := by
```

### norm_sextic_neg_two_le_one

源码起始行：24。

```lean
theorem norm_sextic_neg_two_le_one (z : ℂ) (hz : z = 0 ∨ z ^ 6 = 1) :
    ‖z ^ (-2 : ℤ)‖ ≤ 1 := by
```

### norm_symbol_le_one

源码起始行：30。

```lean
theorem norm_symbol_le_one {I : Type*} (symbol : I → I → ℂ)
    (cop : I → I → Prop)
    (h6 : ∀ i j, symbol i j ^ 6 = if cop i j then 1 else 0) (i j : I) :
    ‖symbol i j‖ ≤ 1 := by
```

### norm_symbol_neg_two_le_one

源码起始行：41。

```lean
theorem norm_symbol_neg_two_le_one {I : Type*} (symbol : I → I → ℂ)
    (cop : I → I → Prop)
    (h6 : ∀ i j, symbol i j ^ 6 = if cop i j then 1 else 0) (i j : I) :
    ‖symbol i j ^ (-2 : ℤ)‖ ≤ 1 := by
```

### complex_mask_norm_le_one

源码起始行：52。

```lean
theorem complex_mask_norm_le_one (p : Prop) :
    ‖if p then (1 : ℂ) else 0‖ ≤ 1 := by
```

### mul_contraction_norm

源码起始行：56。

```lean
theorem mul_contraction_norm (z u : ℂ) (hu : ‖u‖ ≤ 1) : ‖z * u‖ ≤ ‖z‖ := by
```

### twisted_beta_norm_le

源码起始行：60。

```lean
theorem twisted_beta_norm_le (beta z w : ℂ) (p : Prop)
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖beta * z ^ 3 * w * (if p then (1 : ℂ) else 0)‖ ≤ ‖beta‖ := by
```

### twisted_column_mass_le

源码起始行：69。

```lean
theorem twisted_column_mass_le {I : Type*}
    (ps : Finset I) (a u : I → ℂ) (normI : I → ℝ)
    (hu : ∀ p ∈ ps, ‖u p‖ ≤ 1) (hn : ∀ p ∈ ps, 0 < normI p) :
    (∑ p ∈ ps, ‖(a p / (Real.sqrt (normI p) : ℂ)) * u p‖ ^ 2) ≤
      ∑ p ∈ ps, ‖a p‖ ^ 2 / normI p := by
```

### product_fiber_card_le_divisors

源码起始行：87。

```lean
theorem product_fiber_card_le_divisors
    (pairs : Finset (I × I)) (j : I) (divisors : Finset I)
    (hdivisors : ∀ d, d ∣ j → d ∈ divisors) :
    (pairs.filter fun x => x.1 * x.2 = j).card ≤ divisors.card := by
```

### quotient_injOn

源码起始行：102。

```lean
theorem quotient_injOn (rows : Finset I) (d : I) (quotient : I → I)
    (hquotient : ∀ k ∈ rows, d * quotient k = k) :
    Set.InjOn quotient (rows : Set I) := by
```

### row_pullback_le

源码起始行：111。

```lean
theorem row_pullback_le {I J : Type*} [DecidableEq J]
    (rows : Finset I) (target : Finset J) (phi : I → J) (f : J → ℝ)
    (hphi : Set.InjOn phi (rows : Set I))
    (hmap : ∀ i ∈ rows, phi i ∈ target) (hf : ∀ j ∈ target, 0 ≤ f j) :
    (∑ i ∈ rows, f (phi i)) ≤ ∑ j ∈ target, f j := by
```

### operator_bound_pullback

源码起始行：125。

```lean
theorem operator_bound_pullback {I J P : Type*} [DecidableEq J]
    (rows : Finset I) (target : Finset J) (columns : Finset P)
    (phi : I → J) (kernel : J → P → ℂ) (Q : ℝ)
    (hphi : Set.InjOn phi (rows : Set I))
    (hmap : ∀ i ∈ rows, phi i ∈ target)
    (hbound : ∀ a : P → ℂ,
      (∑ j ∈ target, ‖∑ p ∈ columns, kernel j p * a p‖ ^ 2) ≤
        Q * ∑ p ∈ columns, ‖a p‖ ^ 2) (a : P → ℂ) :
    (∑ i ∈ rows, ‖∑ p ∈ columns, kernel (phi i) p * a p‖ ^ 2) ≤
      Q * ∑ p ∈ columns, ‖a p‖ ^ 2 :=
```

### factor_norm_le_product

源码起始行：139。

```lean
theorem factor_norm_le_product {I : Type*} [Monoid I]
    (normI : I → ℝ) (hn : ∀ i, 1 ≤ normI i)
    (hmul : ∀ i j, normI (i * j) = normI i * normI j) (i j : I) :
    normI j ≤ normI (i * j) := by
```

### quotient_norm_le

源码起始行：146。

```lean
theorem quotient_norm_le {I : Type*} [Monoid I]
    (normI : I → ℝ) (hn : ∀ i, 1 ≤ normI i)
    (hmul : ∀ i j, normI (i * j) = normI i * normI j)
    (d q k : I) (hk : d * q = k) : normI q ≤ normI k := by
```

## HeckeSkeleton/LowHybrid/Rows.lean

源码 SHA-256：`86e85a62c7b2170ac787836981706a6fe75d0d62754772ed443d5ea925e9522a`。

### hybridEnergy_nonneg

源码起始行：35。

```lean
theorem hybridEnergy_nonneg (symbol : I → I → ℂ) (cop : I → I → Prop)
    (normI : I → ℝ) (a : I → ℂ) (beta : I → I → ℂ)
    (rows marks columns cubes : Finset I) :
    0 ≤ hybridEnergy symbol cop normI a beta rows marks columns cubes :=
```

## HeckeSkeleton/LowHybrid/SieveBounds.lean

源码 SHA-256：`2798478ee031d9112d5ed8fa6ce2d1f2be193b9b431158231b2f727b5744d36b`。

### hybrid_fixed_block_from_sieve_bounds

源码起始行：57。

```lean
theorem hybrid_fixed_block_from_sieve_bounds [DecidableEq I]
    (normI : I → ℝ) (sf : I → Prop) (symbol : I → I → ℂ)
    (hq : QuadraticSieveInput normI sf symbol)
    (hc : CubicSieveInput normI sf symbol) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
    ∀ K0 Y0 N0 L0 : ℝ, 1 ≤ K0 → 1 ≤ Y0 → 1 ≤ N0 → 1 ≤ L0 →
    ∀ (rows : Finset I) (pairs : Finset (I × I)) (qset : Finset I)
      (cset : I → Finset I) (hset : Finset I) (mc : Finset (I × I))
      (jset pset : Finset I)
      (qprod cprod : I × I → I) (a : I → I → ℂ) (beta : I → I → I → ℂ)
      (Dq Dc Cbound Ebound : ℝ),
      0 ≤ Dq → 0 ≤ Dc → 0 ≤ Cbound →
      (∀ k ∈ rows, sf k ∧ normI k ≤ K0) →
      (∀ j ∈ qset, sf j ∧ normI j ≤ Y0) →
      (∀ j ∈ jset, sf j ∧ normI j ≤ N0) →
      (∀ p ∈ pset, sf p ∧ normI p ≤ L0) →
      (∀ u ∈ pairs, qprod u ∈ qset) →
      (∀ j ∈ qset, ((pairs.filter fun u => qprod u = j).card : ℝ) ≤ Dq) →
      (∀ u ∈ pairs, ((cset u.1).card : ℝ) ≤ Cbound) →
      (∀ u ∈ pairs, ∀ c ∈ cset u.1, ‖beta c u.1 u.2‖ ≤ 1) →
      (∀ u ∈ pairs, u.2 ∈ hset) →
      (∀ u ∈ pairs, ∀ c ∈ cset u.1, (u.1, c) ∈ mc) →
      (∀ u ∈ mc, cprod u ∈ jset) →
      (∀ j ∈ jset, ((mc.filter fun u => cprod u = j).card : ℝ) ≤ Dc) →
      (∀ h ∈ hset, (∑ p ∈ pset, ‖a h p‖ ^ 2) ≤ Ebound) →
      (∑ k ∈ rows, ‖∑ u ∈ pairs, symbol (qprod u) k ^ 3 *
        (∑ c ∈ cset u.1, beta c u.1 u.2 *
          (∑ p ∈ pset, a u.2 p * symbol p (cprod (u.1, c)) ^ (-2 : ℤ)))‖ ^ 2) ≤
        C * (K0 * Y0 * N0 * L0) ^ eps * (K0 + Y0) *
          Cbound * (hset.card : ℝ) * Dq * Dc *
          (N0 + L0 + (N0 * L0) ^ (2 / 3 : ℝ)) * Ebound := by
```

## HeckeSkeleton/LowHybrid/SieveComposition.lean

源码 SHA-256：`b59601851cb677b730d0927d1b423140a98c601167cd580813662c778b11bbb9`。

### bounded_coefficient_sum_sq

源码起始行：27。

```lean
theorem bounded_coefficient_sum_sq {I : Type*} (s : Finset I)
    (b f : I → ℂ) (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) :
    ‖∑ i ∈ s, b i * f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
```

### bounded_coefficient_sum_sq_of_card

源码起始行：41。

```lean
theorem bounded_coefficient_sum_sq_of_card {I : Type*} (s : Finset I)
    (b f : I → ℂ) (D : ℝ) (hb : ∀ i ∈ s, ‖b i‖ ≤ 1)
    (hcard : (s.card : ℝ) ≤ D) :
    ‖∑ i ∈ s, b i * f i‖ ^ 2 ≤ D * ∑ i ∈ s, ‖f i‖ ^ 2 := by
```

### positive_fiber_sum_le

源码起始行：50。

```lean
theorem positive_fiber_sum_le {X Y : Type*} [DecidableEq Y]
    (source : Finset X) (target : Finset Y) (phi : X → Y)
    (E : Y → ℝ) (D : ℝ)
    (hmap : ∀ x ∈ source, phi x ∈ target)
    (hE : ∀ y ∈ target, 0 ≤ E y)
    (hfiber : ∀ y ∈ target, ((source.filter fun x => phi x = y).card : ℝ) ≤ D) :
    (∑ x ∈ source, E (phi x)) ≤ D * ∑ y ∈ target, E y := by
```

### column_fiber_sieve

源码起始行：77。

```lean
theorem column_fiber_sieve {K X Y : Type*} [DecidableEq Y]
    (rows : Finset K) (source : Finset X) (target : Finset Y)
    (phi : X → Y) (q : K → Y → ℂ) (a : X → ℂ) (Q D : ℝ)
    (hQ : 0 ≤ Q) (hmap : ∀ x ∈ source, phi x ∈ target)
    (hfiber : ∀ y ∈ target, ((source.filter fun x => phi x = y).card : ℝ) ≤ D)
    (hsieve : ∀ f : Y → ℂ,
      (∑ k ∈ rows, ‖∑ y ∈ target, q k y * f y‖ ^ 2) ≤
        Q * ∑ y ∈ target, ‖f y‖ ^ 2) :
    (∑ k ∈ rows, ‖∑ x ∈ source, q k (phi x) * a x‖ ^ 2) ≤
      Q * D * ∑ x ∈ source, ‖a x‖ ^ 2 := by
```

### positive_triple_enlarge

源码起始行：118。

```lean
theorem positive_triple_enlarge {M H C : Type*}
    [DecidableEq M] [DecidableEq H] [DecidableEq C]
    (pairs : Finset (M × H)) (cset : M → Finset C)
    (hs : Finset H) (mc : Finset (M × C)) (E : H → M → C → ℝ)
    (hh : ∀ p ∈ pairs, p.2 ∈ hs)
    (hm : ∀ p ∈ pairs, ∀ c ∈ cset p.1, (p.1, c) ∈ mc)
    (hE : ∀ h m c, 0 ≤ E h m c) :
    (∑ p ∈ pairs, ∑ c ∈ cset p.1, E p.2 p.1 c) ≤
      ∑ h ∈ hs, ∑ u ∈ mc, E h u.1 u.2 := by
```

### row_fiber_sieve

源码起始行：147。

```lean
theorem row_fiber_sieve {X Y P : Type*} [DecidableEq Y]
    (source : Finset X) (target : Finset Y) (columns : Finset P)
    (phi : X → Y) (chi : P → Y → ℂ) (a : P → ℂ) (D S : ℝ)
    (hD : 0 ≤ D) (hmap : ∀ x ∈ source, phi x ∈ target)
    (hfiber : ∀ y ∈ target, ((source.filter fun x => phi x = y).card : ℝ) ≤ D)
    (hsieve : ∀ u : P → ℂ,
      (∑ y ∈ target, ‖∑ p ∈ columns, u p * chi p y‖ ^ 2) ≤
        S * ∑ p ∈ columns, ‖u p‖ ^ 2) :
    (∑ x ∈ source, ‖∑ p ∈ columns, a p * chi p (phi x)‖ ^ 2) ≤
      D * S * ∑ p ∈ columns, ‖a p‖ ^ 2 := by
```

### fixed_block_energy_of_two_sieves

源码起始行：173。

```lean
theorem fixed_block_energy_of_two_sieves
    {K M H C J P : Type*}
    [DecidableEq M] [DecidableEq H] [DecidableEq C] [DecidableEq J]
    (rows : Finset K) (pairs : Finset (M × H))
    (cset : M → Finset C) (hset : Finset H) (mc : Finset (M × C))
    (jset : Finset J) (pset : Finset P)
    (q : K → M × H → ℂ) (phi : M × C → J) (chi : P → J → ℂ)
    (a : H → P → ℂ) (beta : C → M → H → ℂ)
    (Q S Cbound D Ebound : ℝ)
    (hQ : 0 ≤ Q) (hS : 0 ≤ S) (hC : 0 ≤ Cbound) (hD : 0 ≤ D)
    (hcount : ∀ p ∈ pairs, ((cset p.1).card : ℝ) ≤ Cbound)
    (hbeta : ∀ p ∈ pairs, ∀ c ∈ cset p.1, ‖beta c p.1 p.2‖ ≤ 1)
    (hh : ∀ p ∈ pairs, p.2 ∈ hset)
    (hmc : ∀ p ∈ pairs, ∀ c ∈ cset p.1, (p.1, c) ∈ mc)
    (hmap : ∀ u ∈ mc, phi u ∈ jset)
    (hfiber : ∀ j ∈ jset, ((mc.filter fun u => phi u = j).card : ℝ) ≤ D)
    (hcoef : ∀ h ∈ hset, (∑ p ∈ pset, ‖a h p‖ ^ 2) ≤ Ebound)
    (hquadratic : ∀ f : M × H → ℂ,
      (∑ k ∈ rows, ‖∑ u ∈ pairs, q k u * f u‖ ^ 2) ≤
        Q * ∑ u ∈ pairs, ‖f u‖ ^ 2)
    (hcubic : ∀ u : P → ℂ,
      (∑ j ∈ jset, ‖∑ p ∈ pset, u p * chi p j‖ ^ 2) ≤
        S * ∑ p ∈ pset, ‖u p‖ ^ 2) :
    (∑ k ∈ rows, ‖∑ u ∈ pairs, q k u *
      (∑ c ∈ cset u.1, beta c u.1 u.2 *
        (∑ p ∈ pset, a u.2 p * chi p (phi (u.1, c))))‖ ^ 2) ≤
      Q * Cbound * (hset.card : ℝ) * D * S * Ebound := by
```

### fixed_block_scalar_ledger

源码起始行：238。

```lean
theorem fixed_block_scalar_ledger (T G C r B Q S A : ℝ)
    (hC : C ≠ 0) (hr : r ≠ 0) (hB : T ^ 2 * G = B) :
    T ^ 2 * Q * (C / r) * (G / C) * S * A =
      Q * (B / r) * S * A := by
```

## HeckeSkeleton/LowHybrid/SquarefreeDivisors.lean

源码 SHA-256：`77aa3573cad1dd9599fac06db0b3cad248053cbf6b4fe3786b44656fd54bc374`。

### support_power_two_le_product

源码起始行：19。

```lean
theorem support_power_two_le_product
    {P : Type*} [DecidableEq P] (q : P → ℝ) (bad s : Finset P) (eta : ℝ)
    (heta : 0 ≤ eta) (hq : ∀ p : P, 1 ≤ q p)
    (hgood : ∀ p : P, p ∉ bad → 2 ≤ q p ^ eta) :
    (2 : ℝ) ^ s.card ≤
      (2 : ℝ) ^ bad.card * ∏ p ∈ s, q p ^ eta := by
```

### prime_power_ge_two_outside_cutoff

源码起始行：50。

```lean
theorem prime_power_ge_two_outside_cutoff
    {P : Type*} (q : P → ℝ) (bad : Finset P) (eta : ℝ) (heta : 0 < eta)
    (hbad : ∀ p : P, q p < (2 : ℝ) ^ (1 / eta) → p ∈ bad) :
    ∀ p : P, p ∉ bad → 2 ≤ q p ^ eta := by
```

### squarefree_support_subpower

源码起始行：68。

```lean
theorem squarefree_support_subpower
    {P : Type*} (q : P → ℝ) (hq : ∀ p : P, 1 ≤ q p)
    (hfinite : ∀ X : ℝ, Set.Finite {p : P | q p ≤ X})
    (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Finset P,
      (2 : ℝ) ^ s.card ≤ C * (∏ p ∈ s, q p) ^ eta := by
```

### squarefree_support_subpower_of_cutoffs

源码起始行：87。

```lean
theorem squarefree_support_subpower_of_cutoffs
    {P : Type*} (q : P → ℝ) (hq : ∀ p : P, 1 ≤ q p)
    (cutoff : ℝ → Finset P)
    (hmem : ∀ X : ℝ, ∀ p : P, q p ≤ X → p ∈ cutoff X)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Finset P,
      (2 : ℝ) ^ s.card ≤ C * (∏ p ∈ s, q p) ^ eta := by
```

### squarefree_divisor_count_subpower

源码起始行：99。

```lean
theorem squarefree_divisor_count_subpower
    {I P : Type*} (support : I → Finset P) (divisors : I → Finset I)
    (primeNorm : P → ℝ) (normI : I → ℝ)
    (hp : ∀ p : P, 1 ≤ primeNorm p)
    (hfinite : ∀ X : ℝ, Set.Finite {p : P | primeNorm p ≤ X})
    (hcard : ∀ i : I, ((divisors i).card : ℝ) ≤ (2 : ℝ) ^ (support i).card)
    (hnorm : ∀ i : I, (∏ p ∈ support i, primeNorm p) ≤ normI i)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ i : I, ((divisors i).card : ℝ) ≤ C * normI i ^ eta := by
```

## HeckeSkeleton/LowHybrid/SupportPower.lean

源码 SHA-256：`c7c0cb5c4df3fdefc0a97c89938d953be5a2352106aabc4b800162564f10f336`。

### support_power_base_le_product

源码起始行：19。

```lean
theorem support_power_base_le_product
    {P : Type*} (q : P → ℝ) (bad s : Finset P) (base eta : ℝ)
    (hbase : 1 ≤ base) (heta : 0 ≤ eta) (hq : ∀ p, 1 ≤ q p)
    (hgood : ∀ p, p ∉ bad → base ≤ q p ^ eta) :
    base ^ s.card ≤ base ^ bad.card * ∏ p ∈ s, q p ^ eta := by
```

### fixed_base_support_power_subpower_ge_one

源码起始行：45。

```lean
theorem fixed_base_support_power_subpower_ge_one
    {P : Type*} (q : P → ℝ) (hq : ∀ p, 1 ≤ q p)
    (hfinite : ∀ X : ℝ, Set.Finite {p : P | q p ≤ X})
    (base : ℝ) (hbase : 1 ≤ base) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Finset P,
      base ^ s.card ≤ C * (∏ p ∈ s, q p) ^ eta := by
```

### fixed_base_support_power_subpower

源码起始行：71。

```lean
theorem fixed_base_support_power_subpower
    {P : Type*} (q : P → ℝ) (hq : ∀ p, 1 ≤ q p)
    (hfinite : ∀ X : ℝ, Set.Finite {p : P | q p ≤ X})
    (base : ℝ) (hbase : 0 ≤ base) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Finset P,
      base ^ s.card ≤ C * (∏ p ∈ s, q p) ^ eta := by
```

### prime_support_power_subpower_of_counting

源码起始行：86。

```lean
theorem prime_support_power_subpower_of_counting
    {ι A : Type*} [CommMonoid A]
    (coords : A ≃* Multiplicative (ι →₀ ℕ))
    (normI : A →* ℝ) (q : A → ℕ) (hnorm : ∀ a, normI a = (q a : ℝ))
    (Ccount : ℝ) (hcount : LinearNormCounting q Ccount)
    (base : ℝ) (hbase : 0 ≤ base) (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : A,
      base ^ (PrimeArithmetic.support coords a).card ≤ C * normI a ^ eta := by
```

## HeckeSkeleton/LowHybrid/Transpose.lean

源码 SHA-256：`cf53f11bfabb6ae2d84784a8cf0e38b24708994bed3c77db017de5495538cad5`。

### finite_complex_sum_mul_sq_le

源码起始行：20。

```lean
theorem finite_complex_sum_mul_sq_le {I : Type*}
    (s : Finset I) (x y : I → ℂ) :
    ‖∑ i ∈ s, x i * y i‖ ^ 2 ≤
      (∑ i ∈ s, ‖x i‖ ^ 2) * (∑ i ∈ s, ‖y i‖ ^ 2) := by
```

### finite_operator_bound_transpose

源码起始行：31。

```lean
theorem finite_operator_bound_transpose {I J : Type*}
    (rows : Finset I) (columns : Finset J) (matrix : I → J → ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z : J → ℂ,
      (∑ i ∈ rows, ‖∑ j ∈ columns, matrix i j * z j‖ ^ 2) ≤
        C * ∑ j ∈ columns, ‖z j‖ ^ 2)
    (x : I → ℂ) :
    (∑ j ∈ columns, ‖∑ i ∈ rows, x i * matrix i j‖ ^ 2) ≤
      C * ∑ i ∈ rows, ‖x i‖ ^ 2 := by
```

### quadratic_sieve_input_transpose

源码起始行：98。

```lean
theorem quadratic_sieve_input_transpose {I : Type*}
    (normI : I → ℝ) (sf : I → Prop) (symbol : I → I → ℂ)
    (hq : QuadraticSieveInput normI sf symbol) :
    QuadraticSieveInput normI sf (fun a b => symbol b a) := by
```

## HeckeSkeleton/LowHybrid/Weighted.lean

源码 SHA-256：`30e1f4a7ced3a7a12109d5f9b634267975a64105953638e0fd21903c9cb8091f`。

### weighted_sum_sq

源码起始行：23。

```lean
theorem weighted_sum_sq {I : Type*} (s : Finset I) (w : I → ℝ) (f : I → ℂ)
    (hw : ∀ i ∈ s, 0 < w i) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤
      (∑ i ∈ s, 1 / w i) * (∑ i ∈ s, w i * ‖f i‖ ^ 2) := by
```

### weighted_mixture_energy

源码起始行：50。

```lean
theorem weighted_mixture_energy {K I : Type*}
    (rows : Finset K) (s : Finset I) (w : I → ℝ) (F : I → K → ℂ)
    (E : I → ℝ) (hw : ∀ i ∈ s, 0 < w i)
    (hE : ∀ i ∈ s, w i * (∑ k ∈ rows, ‖F i k‖ ^ 2) ≤ E i) :
    (∑ k ∈ rows, ‖∑ i ∈ s, F i k‖ ^ 2) ≤
      (∑ i ∈ s, 1 / w i) * (∑ i ∈ s, E i) := by
```

### reciprocal_grid_sum

源码起始行：72。

```lean
theorem reciprocal_grid_sum {T H : Type*}
    (ts : Finset T) (hs : Finset H) (wt : T → ℝ) (wh : H → ℝ) (R : ℝ)
    (hwt : ∀ t ∈ ts, 0 < wt t) (hwh : ∀ h ∈ hs, 0 < wh h) :
    (∑ t ∈ ts, ∑ h ∈ hs, R / (wt t * wh h)) =
      R * (∑ t ∈ ts, 1 / wt t) * (∑ h ∈ hs, 1 / wh h) := by
```

### sum_tcmh_swap（私有辅助）

源码起始行：91。

```lean
private theorem sum_tcmh_swap {T C M H : Type*}
    (ts : Finset T) (cs : Finset C) (ms : Finset M) (hs : Finset H)
    (f : T → C → M → H → ℝ) :
    (∑ t ∈ ts, ∑ c ∈ cs, ∑ m ∈ ms, ∑ h ∈ hs, f t c m h) =
      ∑ t ∈ ts, ∑ h ∈ hs, ∑ m ∈ ms, ∑ c ∈ cs, f t c m h := by
```

### weighted_cubic_total

源码起始行：109。

```lean
theorem weighted_cubic_total {T C M H : Type*}
    (ts : Finset T) (cs : Finset C) (ms : Finset M) (hs : Finset H)
    (wt : T → ℝ) (wh : H → ℝ) (E : T → H → M → C → ℝ)
    (R U : ℝ) (hR : 0 ≤ R)
    (hwt : ∀ t ∈ ts, 0 < wt t) (hwh : ∀ h ∈ hs, 0 < wh h)
    (hE : ∀ t ∈ ts, ∀ h ∈ hs, (∑ m ∈ ms, ∑ c ∈ cs, E t h m c) ≤ U) :
    (∑ t ∈ ts, ∑ c ∈ cs, ∑ m ∈ ms, ∑ h ∈ hs,
      (R / (wt t * wh h)) * E t h m c) ≤
        R * U * (∑ t ∈ ts, 1 / wt t) * (∑ h ∈ hs, 1 / wh h) := by
```

### weighted_energy_of_two_sieves

源码起始行：153。

```lean
theorem weighted_energy_of_two_sieves
    {K T C M H P : Type*}
    (rows : Finset K) (ts : Finset T) (cs : Finset C)
    (ms : Finset M) (hs : Finset H) (ps : Finset P)
    (q : K → M → H → ℂ) (chi : M → C → P → ℂ)
    (a : T → H → P → ℂ) (beta : T → C → M → H → ℂ)
    (rowMask : K → T → ℂ) (wt : T → ℝ) (wc : C → ℝ) (wh : H → ℝ)
    (Q S R A : ℝ) (hQ : 0 ≤ Q) (hS : 0 ≤ S) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hwt : ∀ t ∈ ts, 0 < wt t) (hwc : ∀ c ∈ cs, 0 < wc c)
    (hwh : ∀ h ∈ hs, 0 < wh h)
    (hmask : ∀ k ∈ rows, ∀ t ∈ ts, ‖rowMask k t‖ ≤ 1)
    (hbudget : ∀ t ∈ ts, ∀ c ∈ cs, ∀ m ∈ ms, ∀ h ∈ hs,
      wt t * wc c * ‖beta t c m h‖ ^ 2 ≤ R / (wt t * wh h))
    (ha : ∀ t ∈ ts, ∀ h ∈ hs, (∑ p ∈ ps, ‖a t h p‖ ^ 2) ≤ A)
    (hquadratic : ∀ f : M → H → ℂ,
      (∑ k ∈ rows, ‖∑ m ∈ ms, ∑ h ∈ hs, q k m h * f m h‖ ^ 2) ≤
        Q * (∑ m ∈ ms, ∑ h ∈ hs, ‖f m h‖ ^ 2))
    (hcubic : ∀ u : P → ℂ,
      (∑ m ∈ ms, ∑ c ∈ cs, ‖∑ p ∈ ps, u p * chi m c p‖ ^ 2) ≤
        S * (∑ p ∈ ps, ‖u p‖ ^ 2)) :
    (∑ k ∈ rows, ‖∑ t ∈ ts, ∑ c ∈ cs, rowMask k t *
      (∑ m ∈ ms, ∑ h ∈ hs, q k m h *
        (beta t c m h * (∑ p ∈ ps, a t h p * chi m c p)))‖ ^ 2) ≤
      Q * S * R * A * (∑ t ∈ ts, 1 / wt t) ^ 2 *
        (∑ c ∈ cs, 1 / wc c) * (∑ h ∈ hs, 1 / wh h) := by
```

## HeckeSkeleton/LowHybrid/WeightedSieveBounds.lean

源码 SHA-256：`508aaef817c8aba5b7f9ad33fb9e32b93e326c9b6a5b0dd18d5a6f1b5c94709f`。

### sum_zero_extension（私有辅助）

源码起始行：23。

```lean
private theorem sum_zero_extension {X A : Type*} [DecidableEq X] [AddCommMonoid A]
    (ambient good : Finset X) (f : X → A) (hgood : good ⊆ ambient) :
    (∑ x ∈ ambient, if x ∈ good then f x else 0) = ∑ x ∈ good, f x := by
```

### zero_extended_column_fiber_sieve

源码起始行：46。

```lean
theorem zero_extended_column_fiber_sieve
    {K M H J : Type*} [DecidableEq M] [DecidableEq H] [DecidableEq J]
    (rows : Finset K) (ms : Finset M) (hs : Finset H)
    (good : Finset (M × H)) (target : Finset J)
    (phi : M × H → J) (q : K → J → ℂ) (Q D : ℝ)
    (hQ : 0 ≤ Q) (hD : 0 ≤ D) (hgood : good ⊆ ms ×ˢ hs)
    (hmap : ∀ x ∈ good, phi x ∈ target)
    (hfiber : ∀ j ∈ target, ((good.filter fun x => phi x = j).card : ℝ) ≤ D)
    (hsieve : ∀ z : J → ℂ,
      (∑ k ∈ rows, ‖∑ j ∈ target, q k j * z j‖ ^ 2) ≤
        Q * ∑ j ∈ target, ‖z j‖ ^ 2)
    (f : M → H → ℂ) :
    (∑ k ∈ rows, ‖∑ m ∈ ms, ∑ h ∈ hs,
      zeroExtendedQuadratic good phi q k m h * f m h‖ ^ 2) ≤
      Q * D * (∑ m ∈ ms, ∑ h ∈ hs, ‖f m h‖ ^ 2) := by
```

### zero_extended_row_fiber_sieve

源码起始行：95。

```lean
theorem zero_extended_row_fiber_sieve
    {M C J P : Type*} [DecidableEq M] [DecidableEq C] [DecidableEq J]
    (ms : Finset M) (cs : Finset C) (good : Finset (M × C))
    (target : Finset J) (columns : Finset P)
    (phi : M × C → J) (chi : P → J → ℂ) (S D : ℝ) (hD : 0 ≤ D)
    (hgood : good ⊆ ms ×ˢ cs)
    (hmap : ∀ x ∈ good, phi x ∈ target)
    (hfiber : ∀ j ∈ target, ((good.filter fun x => phi x = j).card : ℝ) ≤ D)
    (hsieve : ∀ z : P → ℂ,
      (∑ j ∈ target, ‖∑ p ∈ columns, z p * chi p j‖ ^ 2) ≤
        S * ∑ p ∈ columns, ‖z p‖ ^ 2)
    (a : P → ℂ) :
    (∑ m ∈ ms, ∑ c ∈ cs,
      ‖∑ p ∈ columns, a p * zeroExtendedCubic good phi chi m c p‖ ^ 2) ≤
      S * D * ∑ p ∈ columns, ‖a p‖ ^ 2 := by
```

### weighted_energy_from_sieve_inputs

源码起始行：140。

```lean
theorem weighted_energy_from_sieve_inputs {I : Type*} [DecidableEq I]
    (normI : I → ℝ) (sf : I → Prop) (symbol : I → I → ℂ)
    (hq : QuadraticSieveInput normI sf symbol)
    (hc : CubicSieveInput normI sf symbol) (eps : ℝ) (heps : 0 < eps) :
    ∃ C0 : ℝ, 0 < C0 ∧
    ∀ K0 Y0 N0 L0 : ℝ, 1 ≤ K0 → 1 ≤ Y0 → 1 ≤ N0 → 1 ≤ L0 →
    ∀ (rows ts cs ms hs ps qset jset : Finset I)
      (goodPairs goodMC : Finset (I × I))
      (qprod cprod : I × I → I)
      (a : I → I → I → ℂ) (beta : I → I → I → I → ℂ)
      (rowMask : I → I → ℂ) (wt wc wh : I → ℝ)
      (Dq Dc Rbudget A : ℝ),
      0 ≤ Dq → 0 ≤ Dc → 0 ≤ Rbudget → 0 ≤ A →
      (∀ k ∈ rows, sf k ∧ normI k ≤ K0) →
      (∀ j ∈ qset, sf j ∧ normI j ≤ Y0) →
      (∀ j ∈ jset, sf j ∧ normI j ≤ N0) →
      (∀ p ∈ ps, sf p ∧ normI p ≤ L0) →
      goodPairs ⊆ ms ×ˢ hs → goodMC ⊆ ms ×ˢ cs →
      (∀ x ∈ goodPairs, qprod x ∈ qset) →
      (∀ j ∈ qset, ((goodPairs.filter fun x => qprod x = j).card : ℝ) ≤ Dq) →
      (∀ x ∈ goodMC, cprod x ∈ jset) →
      (∀ j ∈ jset, ((goodMC.filter fun x => cprod x = j).card : ℝ) ≤ Dc) →
      (∀ t ∈ ts, 0 < wt t) → (∀ c ∈ cs, 0 < wc c) → (∀ h ∈ hs, 0 < wh h) →
      (∀ k ∈ rows, ∀ t ∈ ts, ‖rowMask k t‖ ≤ 1) →
      (∀ t ∈ ts, ∀ c ∈ cs, ∀ m ∈ ms, ∀ h ∈ hs,
        wt t * wc c * ‖beta t c m h‖ ^ 2 ≤ Rbudget / (wt t * wh h)) →
      (∀ t ∈ ts, ∀ h ∈ hs, (∑ p ∈ ps, ‖a t h p‖ ^ 2) ≤ A) →
      (∑ k ∈ rows, ‖∑ t ∈ ts, ∑ c ∈ cs, rowMask k t *
        (∑ m ∈ ms, ∑ h ∈ hs,
          zeroExtendedQuadratic goodPairs qprod (fun k j => symbol k j ^ 3) k m h *
            (beta t c m h * (∑ p ∈ ps, a t h p *
              zeroExtendedCubic goodMC cprod
                (fun p j => symbol p j ^ (-2 : ℤ)) m c p)))‖ ^ 2) ≤
        C0 * (K0 * Y0 * N0 * L0) ^ eps * (K0 + Y0) * Dq * Dc *
          (N0 + L0 + (N0 * L0) ^ (2 / 3 : ℝ)) * Rbudget * A *
          (∑ t ∈ ts, 1 / wt t) ^ 2 *
            (∑ c ∈ cs, 1 / wc c) * (∑ h ∈ hs, 1 / wh h) := by
```

## HeckeSkeleton/LowFrozenCube.lean

源码 SHA-256：`5fc042ac8c009b6d0fe77d55cefd3fa6aa91d2d0afddb9771e936312f6247c84`。

此模块为入口或组织模块，没有新增公开定理声明。

## HeckeSkeleton/LowFrozenCube/AggregateSource.lean

源码 SHA-256：`548cff843904d4e98e0c571be980129c62ee5172da09ec1f419870aee18af7e0`。

### familySourceEnergy_eq_blocks

源码起始行：40。

```lean
theorem familySourceEnergy_eq_blocks (normI : A → ℝ)
    (family : A × A → SourceBlock ι A) (rows : Finset A)
    (hfamily : ∀ pair ∈ frozenRowPairs D.coords D.support rows,
      (family pair).rows = rows ∧ (family pair).pow = pair.1 ∧ (family pair).sup = pair.2) :
    D.familySourceEnergy normI family rows =
      ∑ pair ∈ frozenRowPairs D.coords D.support rows, (family pair).energy D normI := by
```

### aggregate_source_energy_ledger

源码起始行：65。

```lean
theorem aggregate_source_energy_ledger
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount)
    (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting q Ccount)
    (hq : HeckeSkeleton.LowHybrid.QuadraticSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (hc : HeckeSkeleton.LowHybrid.CubicSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (eps eta : ℝ) (heps : 0 < eps) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z O H v ell S B z T Rrad : ℝ,
      1 ≤ Z → 0 ≤ O → 0 ≤ H → 0 ≤ v → 0 ≤ ell → 0 ≤ z →
      ∀ rows : Finset A,
        (∀ k ∈ rows, normI (PrimeCoordinates.powerfulRowFactor D.coords k) ≤ Z ^ O) →
        normI (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport D.coords D.support) ≤ Z ^ Rrad →
      ∀ family : A × A → SourceBlock ι A,
        (∀ pair ∈ frozenRowPairs D.coords D.support rows,
          AnnularSupport D normI Z H v ell z (family pair)) →
        (∀ pair ∈ frozenRowPairs D.coords D.support rows,
          PrimitiveLocalBounds D normI (family pair)) →
        Z ^ (S + B) ≤ normI D.chargeIdeal →
        (∑ pair ∈ frozenRowPairs D.coords D.support rows,
          (family pair).energy D normI) * Z ^ (squaredKernelExponent T v ell) ≤
          C * Z ^ (reflectedExponent O H v ell S B z T +
            eps * (H + v + ell + z) + eta * (O + Rrad)) := by
```

### family_source_energy_ledger

源码起始行：154。

```lean
theorem family_source_energy_ledger
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount)
    (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting q Ccount)
    (hq : HeckeSkeleton.LowHybrid.QuadraticSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (hc : HeckeSkeleton.LowHybrid.CubicSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (eps eta : ℝ) (heps : 0 < eps) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z O H v ell S B z T Rrad : ℝ,
      1 ≤ Z → 0 ≤ O → 0 ≤ H → 0 ≤ v → 0 ≤ ell → 0 ≤ z →
      ∀ rows : Finset A,
        (∀ k ∈ rows, normI (PrimeCoordinates.powerfulRowFactor D.coords k) ≤ Z ^ O) →
        normI (HeckeSkeleton.LowHybrid.PrimeArithmetic.fromSupport D.coords D.support) ≤ Z ^ Rrad →
      ∀ family : A × A → SourceBlock ι A,
        (∀ pair ∈ frozenRowPairs D.coords D.support rows,
          (family pair).rows = rows ∧ (family pair).pow = pair.1 ∧ (family pair).sup = pair.2) →
        (∀ pair ∈ frozenRowPairs D.coords D.support rows,
          AnnularSupport D normI Z H v ell z (family pair)) →
        (∀ pair ∈ frozenRowPairs D.coords D.support rows,
          PrimitiveLocalBounds D normI (family pair)) →
        Z ^ (S + B) ≤ normI D.chargeIdeal →
        D.familySourceEnergy normI family rows * Z ^ (squaredKernelExponent T v ell) ≤
          C * Z ^ (reflectedExponent O H v ell S B z T +
            eps * (H + v + ell + z) + eta * (O + Rrad)) := by
```

## HeckeSkeleton/LowFrozenCube/Assembly.lean

源码 SHA-256：`9ffa5014ab3d98f8cf04deb78b3433e21091b1e09a1aef07232a66d3ae4ea7bb`。

### cubeProduct_injective_on

源码起始行：32。

```lean
theorem cubeProduct_injective_on (t : Finset (A × A)) (split : A → A × A)
    (hsplit : ∀ q ∈ t, split (cubeProduct q) = q) :
    Set.InjOn cubeProduct (t : Set (A × A)) := by
```

### fullCubeCoefficient_norm_le

源码起始行：42。

```lean
theorem fullCubeCoefficient_norm_le (t : Finset (A × A))
    (split : A → A × A) (hsplit : ∀ q ∈ t, split (cubeProduct q) = q)
    (B : A → A → A → ℂ) (c : A) (R : ℝ)
    (hB : ∀ q ∈ t, ‖B c q.1 q.2‖ ≤ R)
    (b : A) (hb : b ∈ t.image cubeProduct) :
    ‖fullCubeCoefficient split B c b‖ ≤ R := by
```

### fullCubeCoefficient_energy

源码起始行：52。

```lean
theorem fullCubeCoefficient_energy (t : Finset (A × A))
    (split : A → A × A) (hsplit : ∀ q ∈ t, split (cubeProduct q) = q)
    (B : A → A → A → ℂ) (c : A) :
    (∑ b ∈ t.image cubeProduct, ‖fullCubeCoefficient split B c b‖ ^ 2) =
      ∑ q ∈ t, ‖B c q.1 q.2‖ ^ 2 := by
```

### frozenCubeInner_eq_fullCubeInner

源码起始行：77。

```lean
theorem frozenCubeInner_eq_fullCubeInner
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0)
    (t : Finset (A × A)) (split : A → A × A)
    (hsplit : ∀ q ∈ t, split (cubeProduct q) = q)
    (B : A → A → A → ℂ) (d P c : A)
    (hPx : ∀ q ∈ t, Cop P q.1) :
    frozenCubeInner χ Cop B t d P c =
      fullCubeInner χ Cop (fullCubeCoefficient split B) (t.image cubeProduct) d P c := by
```

### frozenSeparatedRow_eq_hybrid

源码起始行：108。

```lean
theorem frozenSeparatedRow_eq_hybrid
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0)
    (marks columns : Finset A) (t : Finset (A × A))
    (split : A → A × A) (hsplit : ∀ q ∈ t, split (cubeProduct q) = q)
    (a : A → ℂ) (B : A → A → A → ℂ)
    (hPx : ∀ P ∈ marks, ∀ q ∈ t, Cop P q.1) (d : A) :
    frozenSeparatedRow χ Cop a B marks columns t d =
      hybridSeparatedRow χ Cop a (fullCubeCoefficient split B)
        marks columns (t.image cubeProduct) d := by
```

### frozenSeparatedRow_energy_eq_hybrid

源码起始行：127。

```lean
theorem frozenSeparatedRow_energy_eq_hybrid
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0)
    (rows marks columns : Finset A) (t : Finset (A × A))
    (split : A → A × A) (hsplit : ∀ q ∈ t, split (cubeProduct q) = q)
    (a : A → ℂ) (B : A → A → A → ℂ)
    (hPx : ∀ P ∈ marks, ∀ q ∈ t, Cop P q.1)
    (ρ : A → ℂ) (hρ : ∀ d ∈ rows, ‖ρ d‖ = 1) :
    (∑ d ∈ rows, ‖ρ d * frozenSeparatedRow χ Cop a B marks columns t d‖ ^ 2) =
      ∑ d ∈ rows, ‖hybridSeparatedRow χ Cop a (fullCubeCoefficient split B)
        marks columns (t.image cubeProduct) d‖ ^ 2 := by
```

## HeckeSkeleton/LowFrozenCube/CoefficientSeparation.lean

源码 SHA-256：`7fbb026cde8b1ad7d08838718310df0b0d183af03cb0ddc87b850bb9afed7aa6`。

### negativeOrdinaryInteraction_frozen

源码起始行：34。

```lean
theorem negativeOrdinaryInteraction_frozen (F : Finset ι) (ψ : ι → A → ℂ)
    (j v : ι → ℕ) (hv : ∀ p, AdmissibleExponent (v p)) (a : A) :
    negativeOrdinaryInteraction F ψ j v a =
      negativeOrdinaryInteraction F ψ j (frozenBase v) a := by
```

### positiveOrdinaryInteraction_frozen

源码起始行：44。

```lean
theorem positiveOrdinaryInteraction_frozen (F : Finset ι) (ψ : ι → A → ℂ)
    (j v : ι → ℕ) (hv : ∀ p, AdmissibleExponent (v p)) (a : A) :
    positiveOrdinaryInteraction F ψ j v a =
      positiveOrdinaryInteraction F ψ j (frozenBase v) a := by
```

### markCoefficient_frozen

源码起始行：73。

```lean
theorem markCoefficient_frozen
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0)
    (F : Finset ι) (ψ : ι → A → ℂ) (j v : ι → ℕ)
    (hv : ∀ p, AdmissibleExponent (v p)) (a₀ : A → ℂ)
    (amin x P : A) (hPx : Cop P x) :
    markCoefficient χ F ψ j v a₀ (amin * x ^ 3) P =
      markCoefficient χ F ψ j (frozenBase v) a₀ amin P := by
```

### columnCoefficient_frozen

源码起始行：86。

```lean
theorem columnCoefficient_frozen
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0)
    (F : Finset ι) (ψ : ι → A → ℂ) (j v : ι → ℕ)
    (hv : ∀ p, AdmissibleExponent (v p)) (lam : A → ℂ)
    (amin x c : A) (hcx : Cop c x) :
    columnCoefficient χ F ψ j v lam (amin * x ^ 3) c =
      columnCoefficient χ F ψ j (frozenBase v) lam amin c := by
```

### rowCoefficient_frozen

源码起始行：100。

```lean
theorem rowCoefficient_frozen (F : Finset ι) (ψ : ι → A → ℂ)
    (j v : ι → ℕ) (hv : ∀ p, AdmissibleExponent (v p)) (ρ₀ : A → ℂ)
    (amin x d : A) :
    rowCoefficient χ F ψ j v ρ₀ (amin * x ^ 3) d =
      rowCoefficient χ F ψ j (frozenBase v) ρ₀ amin d * (χ d x) ^ 3 := by
```

## HeckeSkeleton/LowFrozenCube/ColumnNormalization.lean

源码 SHA-256：`649b62b23007d23166c68964b038512f9df74fe2a4511fbbf144d58f7dfceec0`。

### unitAnnularColumn_norm_le

源码起始行：26。

```lean
theorem unitAnnularColumn_norm_le (normI : A → ℝ) (N : ℝ) (hN : 0 < N)
    (lam : A → ℂ) (c : A) (hlower : N ≤ normI c) (hlam : ‖lam c‖ ≤ 1) :
    ‖unitAnnularColumn normI N lam c‖ ≤ 1 := by
```

### annularColumn_eq_scalar_unit

源码起始行：42。

```lean
theorem annularColumn_eq_scalar_unit (normI : A → ℝ) (N : ℝ) (hN : 0 < N)
    (lam : A → ℂ) (c : A) :
    annularColumn normI lam c = (Real.sqrt N : ℂ)⁻¹ *
      unitAnnularColumn normI N lam c := by
```

### inv_sqrt_norm_sq

源码起始行：56。

```lean
theorem inv_sqrt_norm_sq (N : ℝ) (hN : 0 < N) :
    ‖(Real.sqrt N : ℂ)⁻¹‖ ^ 2 = 1 / N := by
```

### rawSourceRow_scale_column

源码起始行：65。

```lean
theorem rawSourceRow_scale_column (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ)
    (a₀ ρ₀ lam gamma : A → ℂ) (scalar : ℂ)
    (marks columns : Finset A) (inputs : Finset (A × A))
    (hlam : ∀ c ∈ columns, lam c = scalar * gamma c) (d : A) :
    D.rawSourceRow normI first prefactor atZero phase a₀ ρ₀ lam marks columns inputs d =
      scalar * D.rawSourceRow normI first prefactor atZero phase a₀ ρ₀ gamma
        marks columns inputs d := by
```

### rawBlockSourceEnergy_scale_column

源码起始行：85。

```lean
theorem rawBlockSourceEnergy_scale_column (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ)
    (a₀ ρ₀ lam gamma : A → ℂ) (scalar : ℂ) (pow sup : A)
    (rows marks columns : Finset A) (inputs : Finset (A × A))
    (hlam : ∀ c ∈ columns, lam c = scalar * gamma c) :
    D.rawBlockSourceEnergy normI first prefactor atZero phase a₀ ρ₀ lam
      pow sup rows marks columns inputs =
      ‖scalar‖ ^ 2 * D.rawBlockSourceEnergy normI first prefactor atZero phase
        a₀ ρ₀ gamma pow sup rows marks columns inputs := by
```

### weighted_raw_frozen_row_block_exit

源码起始行：105。

```lean
theorem weighted_raw_frozen_row_block_exit
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
    (phase : A → A → A → ℂ) (a₀ ρ₀ lam : A → ℂ)
    (K N B : ℝ) (hN : 0 < N) (hB : 0 < B) (pow sup : A)
    (rows marks columns : Finset A) (inputs : Finset (A × A))
    (hrows : ∀ k ∈ rows, normI k ≤ K)
    (hρ₀ : ∀ d, (∀ p, PrimeCoordinates.valuation D.coords d p ≤ 1) →
      PrimeCoordinates.Avoids D.coords D.support d → ‖ρ₀ d‖ = 1)
    (hmarks : ∀ P ∈ marks, PrimeCoordinates.Avoids D.coords D.support P)
    (ha₀ : ∀ P ∈ marks, ‖a₀ P‖ ≤ 1)
    (hcolumns : ∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hlam : ∀ c ∈ columns, ‖lam c‖ ≤ 1)
    (hcolumnLower : ∀ c ∈ columns, N ≤ normI c)
    (hsupport : ∀ q ∈ inputs, PrimeCoordinates.Supported D.coords D.ordinary q.1)
    (haway : ∀ q ∈ inputs, PrimeCoordinates.Avoids D.coords D.ordinary q.2)
    (hphase : ∀ c ∈ columns, ∀ q ∈ inputs, ‖phase c q.1 q.2‖ ≤ 1)
    (hlower : ∀ q ∈ inputs,
      B ≤ normI (PrimeCoordinates.residualCubeFactor D.coords q.1 * q.2)) :
    let residual :=
```

## HeckeSkeleton/LowFrozenCube/FrozenBounds.lean

源码 SHA-256：`3a2f969e0a03f241fc56be206c12d563045d35fd8ad3b30d78f9e3f292665ce1`。

### valuation_prime

源码起始行：25。

```lean
@[simp] theorem valuation_prime (p : ι) :
    PrimeCoordinates.valuation D.coords (D.prime p) = Finsupp.single p 1 := by
```

### symbol_norm_of_coprime

源码起始行：29。

```lean
theorem symbol_norm_of_coprime (a b : A)
    (hab : PrimeCoordinates.Coprime D.coords a b) : ‖D.symbol a b‖ = 1 := by
```

### ordinarySymbol_norm

源码起始行：35。

```lean
theorem ordinarySymbol_norm (a : A)
    (ha : PrimeCoordinates.Avoids D.coords D.ordinary a)
    (p : ι) (hp : p ∈ D.ordinary) : ‖D.ordinarySymbol p a‖ = 1 := by
```

### negativeInteraction_norm

源码起始行：47。

```lean
theorem negativeInteraction_norm (v : ι → ℕ) (a : A)
    (ha : PrimeCoordinates.Avoids D.coords D.ordinary a) :
    ‖negativeOrdinaryInteraction D.ordinary D.ordinarySymbol D.digit v a‖ = 1 := by
```

### positiveInteraction_norm

源码起始行：57。

```lean
theorem positiveInteraction_norm (v : ι → ℕ) (a : A)
    (ha : PrimeCoordinates.Avoids D.coords D.ordinary a) :
    ‖positiveOrdinaryInteraction D.ordinary D.ordinarySymbol D.digit v a‖ = 1 := by
```

### mark_norm

源码起始行：67。

```lean
theorem mark_norm (a₀ : A → ℂ) (P : A)
    (hP : PrimeCoordinates.Avoids D.coords D.support P) :
    ‖D.mark a₀ P‖ = ‖a₀ P‖ := by
```

### rowFactor_norm

源码起始行：77。

```lean
theorem rowFactor_norm (ρ₀ : A → ℂ) (d : A)
    (hd : PrimeCoordinates.Avoids D.coords D.support d) :
    ‖D.rowFactor ρ₀ d‖ = ‖ρ₀ d‖ := by
```

### column_norm

源码起始行：87。

```lean
theorem column_norm (lam : A → ℂ) (c : A)
    (hc : PrimeCoordinates.Avoids D.coords D.ordinary c) :
    ‖D.column lam c‖ = ‖lam c‖ := by
```

### source_energy_eq_hybridEnergy

源码起始行：99。

```lean
theorem source_energy_eq_hybridEnergy
    (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ) (Ω : A → A → A → ℂ)
    (rows marks columns : Finset A) (pairs : Finset (A × A))
    (hrows : ∀ d ∈ rows, PrimeCoordinates.Avoids D.coords D.support d)
    (hρ₀ : ∀ d ∈ rows, ‖ρ₀ d‖ = 1)
    (hmarks : ∀ P ∈ marks, PrimeCoordinates.Avoids D.coords D.support P)
    (hcolumns : ∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hpairs : ∀ q ∈ pairs, D.CanonicalCube q.1 ∧
      PrimeCoordinates.Avoids D.coords D.ordinary q.2) :
    (∑ d ∈ rows, ‖D.sourceRow normI a₀ ρ₀ lam Ω marks columns pairs d‖ ^ 2) =
      HeckeSkeleton.LowHybrid.hybridEnergy (fun a b => D.symbol a b)
        (PrimeCoordinates.Coprime D.coords) normI (D.mark a₀) (D.beta normI lam Ω)
        rows marks columns (pairs.image cubeProduct) := by
```

### residualCoefficient_norm_le

源码起始行：119。

```lean
theorem residualCoefficient_norm_le
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (lam : A → ℂ) (Ω : A → A → A → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (c x n : A) (hc : PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hlam : ‖lam c‖ ≤ 1) (hΩ : ‖Ω c x n‖ ≤ C / normI x) :
    ‖D.residualCoefficient normI lam Ω c x n‖ ≤ C / normI (x * n) := by
```

### beta_norm_le

源码起始行：137。

```lean
theorem beta_norm_le
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (lam : A → ℂ) (Ω : A → A → A → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (columns : Finset A) (pairs : Finset (A × A))
    (hcolumns : ∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hpairs : ∀ q ∈ pairs, D.CanonicalCube q.1 ∧
      PrimeCoordinates.Avoids D.coords D.ordinary q.2)
    (hlam : ∀ c ∈ columns, ‖lam c‖ ≤ 1)
    (hΩ : ∀ c ∈ columns, ∀ q ∈ pairs, ‖Ω c q.1 q.2‖ ≤ C / normI q.1)
    (c : A) (hc : c ∈ columns) (b : A) (hb : b ∈ pairs.image cubeProduct) :
    ‖D.beta normI lam Ω c b‖ ≤ C / normI b := by
```

### beta_bound_of_lower_annulus

源码起始行：158。

```lean
theorem beta_bound_of_lower_annulus
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (lam : A → ℂ) (Ω : A → A → A → ℂ) (B C : ℝ) (hB : 0 < B) (hC : 0 ≤ C)
    (columns : Finset A) (pairs : Finset (A × A))
    (hcolumns : ∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hpairs : ∀ q ∈ pairs, D.CanonicalCube q.1 ∧
      PrimeCoordinates.Avoids D.coords D.ordinary q.2)
    (hlam : ∀ c ∈ columns, ‖lam c‖ ≤ 1)
    (hΩ : ∀ c ∈ columns, ∀ q ∈ pairs, ‖Ω c q.1 q.2‖ ≤ C / normI q.1)
    (hlower : ∀ q ∈ pairs, B ≤ normI (cubeProduct q))
    (c : A) (hc : c ∈ columns) (b : A) (hb : b ∈ pairs.image cubeProduct) :
    ‖D.beta normI lam Ω c b‖ ≤ C / B := by
```

### unitBeta_norm_le

源码起始行：176。

```lean
theorem unitBeta_norm_le (normI : A → ℝ) (lam : A → ℂ)
    (Ω : A → A → A → ℂ) (B C : ℝ) (hB : 0 < B) (hC : 0 ≤ C)
    (c b : A) (hβ : ‖D.beta normI lam Ω c b‖ ≤ C / B) :
    ‖D.unitBeta normI lam Ω B C c b‖ ≤ 1 :=
```

### beta_eq_scalar_unitBeta

源码起始行：183。

```lean
theorem beta_eq_scalar_unitBeta (normI : A → ℝ) (lam : A → ℂ)
    (Ω : A → A → A → ℂ) (B C : ℝ) (hB : 0 < B) (hC : 0 ≤ C)
    (c b : A) (hβ : ‖D.beta normI lam Ω c b‖ ≤ C / B) :
    D.beta normI lam Ω c b = ((C : ℂ) / (B : ℂ)) * D.unitBeta normI lam Ω B C c b := by
```

### hybridRow_scale_beta

源码起始行：192。

```lean
theorem hybridRow_scale_beta (normI : A → ℝ) (β γ : A → A → ℂ)
    (aP : A → ℂ) (marks columns cubes : Finset A) (scalar : ℂ)
    (hβ : ∀ c ∈ columns, ∀ b ∈ cubes, β c b = scalar * γ c b) (d : A) :
    HeckeSkeleton.LowHybrid.hybridRow (fun a b => D.symbol a b)
      (PrimeCoordinates.Coprime D.coords) normI aP β marks columns cubes d =
    scalar * HeckeSkeleton.LowHybrid.hybridRow (fun a b => D.symbol a b)
      (PrimeCoordinates.Coprime D.coords) normI aP γ marks columns cubes d := by
```

### normalized_frozen_exit

源码起始行：213。

```lean
theorem normalized_frozen_exit
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (a₀ ρ₀ lam : A → ℂ) (Ω : A → A → A → ℂ)
    (B C : ℝ) (hB : 0 < B) (hC : 0 ≤ C)
    (rows marks columns : Finset A) (pairs : Finset (A × A))
    (hrows : ∀ d ∈ rows, PrimeCoordinates.Avoids D.coords D.support d)
    (hρ₀ : ∀ d ∈ rows, ‖ρ₀ d‖ = 1)
    (hmarks : ∀ P ∈ marks, PrimeCoordinates.Avoids D.coords D.support P)
    (ha₀ : ∀ P ∈ marks, ‖a₀ P‖ ≤ 1)
    (hcolumns : ∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hlam : ∀ c ∈ columns, ‖lam c‖ ≤ 1)
    (hpairs : ∀ q ∈ pairs, D.CanonicalCube q.1 ∧
      PrimeCoordinates.Avoids D.coords D.ordinary q.2)
    (hΩ : ∀ c ∈ columns, ∀ q ∈ pairs, ‖Ω c q.1 q.2‖ ≤ C / normI q.1)
    (hlower : ∀ q ∈ pairs, B ≤ normI (cubeProduct q)) :
    (∀ P ∈ marks, ‖D.mark a₀ P‖ ≤ 1) ∧
    (∀ c ∈ columns, ∀ b ∈ pairs.image cubeProduct,
      ‖D.unitBeta normI lam Ω B C c b‖ ≤ 1) ∧
    (∑ d ∈ rows, ‖D.sourceRow normI a₀ ρ₀ lam Ω marks columns pairs d‖ ^ 2) =
      (C / B) ^ 2 * HeckeSkeleton.LowHybrid.hybridEnergy
        (fun a b => D.symbol a b) (PrimeCoordinates.Coprime D.coords) normI
        (D.mark a₀) (D.unitBeta normI lam Ω B C)
        rows marks columns (pairs.image cubeProduct) := by
```

### kernel_numerator_frozen

源码起始行：268。

```lean
theorem kernel_numerator_frozen (normI : A →* ℝ) (X : ℝ) (c x n : A) :
    X * normI (D.minimum * x ^ 3) * normI c * normI n ^ 3 =
      X * normI D.minimum * normI c * normI (x * n) ^ 3 := by
```

## HeckeSkeleton/LowFrozenCube/FrozenCounts.lean

源码 SHA-256：`0943a754d3c66bc432801dbf390dbe8d3d056226be164bcd4ad175b454d659d1`。

### supported_squarefree_count_small_power

源码起始行：24。

```lean
theorem supported_squarefree_count_small_power
    (normI : A →* ℝ) (q : A → ℕ) (hnorm : ∀ a, normI a = (q a : ℝ))
    (Ccount : ℝ) (hq : ∀ a, 1 ≤ q a) (hcount : LinearNormCounting q Ccount)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ support : Finset ι, ∀ s : Finset A,
      (∀ a ∈ s, PrimeArithmetic.Squarefree coords a ∧ Supported coords support a) →
      (s.card : ℝ) ≤ C * normI (PrimeArithmetic.fromSupport coords support) ^ eps := by
```

### frozen_pair_count_small_power

源码起始行：46。

```lean
theorem frozen_pair_count_small_power
    (normI : A →* ℝ) (q : A → ℕ) (hnorm : ∀ a, normI a = (q a : ℝ))
    (Ccount : ℝ) (hCcount : 0 < Ccount) (hq : ∀ a, 1 ≤ q a)
    (hcount : LinearNormCounting q Ccount) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K → ∀ support : Finset ι,
      ∀ pairs : Finset (A × A),
        (∀ u ∈ pairs,
          (∀ p, valuation coords u.1 p = 0 ∨ 2 ≤ valuation coords u.1 p) ∧
          normI u.1 ≤ K ∧ PrimeArithmetic.Squarefree coords u.2 ∧
          Supported coords support u.2) →
        (pairs.card : ℝ) ≤ C * Real.sqrt K *
          (K * normI (PrimeArithmetic.fromSupport coords support)) ^ eps := by
```

### frozen_row_pair_count_small_power

源码起始行：105。

```lean
theorem frozen_row_pair_count_small_power
    (normI : A →* ℝ) (q : A → ℕ) (hnorm : ∀ a, normI a = (q a : ℝ))
    (Ccount : ℝ) (hCcount : 0 < Ccount) (hq : ∀ a, 1 ≤ q a)
    (hcount : LinearNormCounting q Ccount) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K → ∀ support : Finset ι,
      ∀ rows : Finset A,
        (∀ k ∈ rows, normI (powerfulRowFactor coords k) ≤ K) →
        ((frozenRowPairs coords support rows).card : ℝ) ≤ C * Real.sqrt K *
          (K * normI (PrimeArithmetic.fromSupport coords support)) ^ eps := by
```

## HeckeSkeleton/LowFrozenCube/FrozenPartition.lean

源码 SHA-256：`a5a61eff6d638c8c947c83fe7b6a6ff22e1437f1d55c1c811901a5d5d299c212`。

### sum_rows_eq_frozen_blocks

源码起始行：21。

```lean
theorem sum_rows_eq_frozen_blocks
    {R : Type*} [AddCommMonoid R] (support : Finset ι)
    (rows : Finset A) (F : A → R) :
    (∑ k ∈ rows, F k) =
      ∑ pair ∈ frozenRowPairs coords support rows,
        ∑ k ∈ rowBlock coords support pair.1 pair.2 rows, F k := by
```

### sum_rows_le_frozen_card_mul

源码起始行：49。

```lean
theorem sum_rows_le_frozen_card_mul
    (support : Finset ι) (rows : Finset A) (F : A → ℝ) (E : ℝ)
    (hblock : ∀ pair ∈ frozenRowPairs coords support rows,
      (∑ k ∈ rowBlock coords support pair.1 pair.2 rows, F k) ≤ E) :
    (∑ k ∈ rows, F k) ≤ ((frozenRowPairs coords support rows).card : ℝ) * E := by
```

## HeckeSkeleton/LowFrozenCube/FrozenReduction.lean

源码 SHA-256：`2269564693f13d8c724441fb97acf1c98f52a4fa3730cd7c42d21efb1b56fb8e`。

### minimum_supported

源码起始行：48。

```lean
theorem minimum_supported : PrimeCoordinates.Supported D.coords D.support D.minimum := by
```

### avoids_ordinary_of_avoids_support

源码起始行：52。

```lean
theorem avoids_ordinary_of_avoids_support (a : A)
    (ha : PrimeCoordinates.Avoids D.coords D.support a) :
    PrimeCoordinates.Avoids D.coords D.ordinary a := by
```

### canonical_admissible

源码起始行：72。

```lean
theorem canonical_admissible (x : A) (hx : D.CanonicalCube x) :
    ∀ p, AdmissibleExponent (D.exponents x p) := by
```

### canonical_minimum

源码起始行：78。

```lean
theorem canonical_minimum (x : A) (hx : D.CanonicalCube x) :
    frozenBase (D.exponents x) = fun p => PrimeCoordinates.valuation D.coords D.minimum p := by
```

### canonical_supported

源码起始行：85。

```lean
theorem canonical_supported (x : A) (hx : D.CanonicalCube x) :
    PrimeCoordinates.Supported D.coords D.support x := by
```

### canonical_supported_ordinary

源码起始行：93。

```lean
theorem canonical_supported_ordinary (x : A) (hx : D.CanonicalCube x) :
    PrimeCoordinates.Supported D.coords D.ordinary x := by
```

### canonical_split

源码起始行：101。

```lean
theorem canonical_split (x n : A) (hx : D.CanonicalCube x)
    (hn : PrimeCoordinates.Avoids D.coords D.ordinary n) :
    PrimeCoordinates.cubeSplit D.coords D.ordinary (x * n) = (x, n) :=
```

### canonical_coprime

源码起始行：106。

```lean
theorem canonical_coprime (P x : A) (hP : PrimeCoordinates.Avoids D.coords D.support P)
    (hx : D.CanonicalCube x) : PrimeCoordinates.Coprime D.coords P x :=
```

### canonical_coprime_ordinary

源码起始行：111。

```lean
theorem canonical_coprime_ordinary (a x : A)
    (ha : PrimeCoordinates.Avoids D.coords D.ordinary a) (hx : D.CanonicalCube x) :
    PrimeCoordinates.Coprime D.coords a x :=
```

### mark_frozen

源码起始行：129。

```lean
theorem mark_frozen (a₀ : A → ℂ) (P x : A)
    (hP : PrimeCoordinates.Avoids D.coords D.support P) (hx : D.CanonicalCube x) :
    markCoefficient D.symbol D.ordinary D.ordinarySymbol D.digit (D.exponents x)
      a₀ (D.minimum * x ^ 3) P = D.mark a₀ P := by
```

### rowFactor_frozen

源码起始行：139。

```lean
theorem rowFactor_frozen (ρ₀ : A → ℂ) (d x : A) (hx : D.CanonicalCube x) :
    rowCoefficient D.symbol D.ordinary D.ordinarySymbol D.digit (D.exponents x)
      ρ₀ (D.minimum * x ^ 3) d = D.rowFactor ρ₀ d * (D.symbol d x) ^ 3 := by
```

### column_frozen

源码起始行：147。

```lean
theorem column_frozen (lam : A → ℂ) (c x : A)
    (hc : PrimeCoordinates.Avoids D.coords D.ordinary c) (hx : D.CanonicalCube x) :
    columnCoefficient D.symbol D.ordinary D.ordinarySymbol D.digit (D.exponents x)
      lam (D.minimum * x ^ 3) c = D.column lam c := by
```

### mixedPhase_eq

源码起始行：164。

```lean
theorem mixedPhase_eq (d P c n : A) :
    D.mixedPhase d P c n =
      (if PrimeCoordinates.Coprime D.coords P d then (1 : ℂ) else 0) *
        ((D.symbol d (c * n)) ^ 3 * (D.symbol P c) ^ 4 *
          (if PrimeCoordinates.Coprime D.coords P n then (1 : ℂ) else 0)) := by
```

### sourceRow_eq_frozen

源码起始行：204。

```lean
theorem sourceRow_eq_frozen (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
    (Ω : A → A → A → ℂ) (marks columns : Finset A)
    (pairs : Finset (A × A))
    (hmarks : ∀ P ∈ marks, PrimeCoordinates.Avoids D.coords D.support P)
    (hcolumns : ∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hpairs : ∀ q ∈ pairs, D.CanonicalCube q.1) (d : A) :
    D.sourceRow normI a₀ ρ₀ lam Ω marks columns pairs d =
      D.rowFactor ρ₀ d * frozenSeparatedRow D.symbol (PrimeCoordinates.Coprime D.coords)
        (fun P => D.mark a₀ P / (Real.sqrt (normI P) : ℂ))
        (D.residualCoefficient normI lam Ω) marks columns pairs d := by
```

### sourceRow_eq_hybridRow

源码起始行：232。

```lean
theorem sourceRow_eq_hybridRow (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
    (Ω : A → A → A → ℂ) (marks columns : Finset A)
    (pairs : Finset (A × A))
    (hmarks : ∀ P ∈ marks, PrimeCoordinates.Avoids D.coords D.support P)
    (hcolumns : ∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hpairs : ∀ q ∈ pairs, D.CanonicalCube q.1 ∧ PrimeCoordinates.Avoids D.coords D.ordinary q.2)
    (d : A) :
    D.sourceRow normI a₀ ρ₀ lam Ω marks columns pairs d =
      D.rowFactor ρ₀ d * HeckeSkeleton.LowHybrid.hybridRow
        (fun a b => D.symbol a b) (PrimeCoordinates.Coprime D.coords) normI
        (D.mark a₀) (D.beta normI lam Ω) marks columns (pairs.image cubeProduct) d := by
```

## HeckeSkeleton/LowFrozenCube/FrozenSupportExtension.lean

源码 SHA-256：`ee5b96c4e2124a6eb9ae0aadc41fff7ee48f887368f2e48e7b648d20b1af9134`。

### valuation_ne_one_of_mem_powerful_support

源码起始行：24。

```lean
theorem valuation_ne_one_of_mem_powerful_support (k pow : A)
    (hk : powerfulRowFactor coords k = pow) (p : ι)
    (hp : p ∈ (valuation coords pow).support) : valuation coords k p ≠ 1 := by
```

### supportedRowFactor_extended

源码起始行：35。

```lean
theorem supportedRowFactor_extended (base : Finset ι) (k pow : A)
    (hk : powerfulRowFactor coords k = pow) :
    supportedRowFactor coords (extendedFrozenSupport coords base pow) k =
      supportedRowFactor coords base k := by
```

### residualRowFactor_extended

源码起始行：47。

```lean
theorem residualRowFactor_extended (base : Finset ι) (k pow : A)
    (hk : powerfulRowFactor coords k = pow) :
    residualRowFactor coords (extendedFrozenSupport coords base pow) k =
      residualRowFactor coords base k := by
```

### rowBlock_extended

源码起始行：61。

```lean
theorem rowBlock_extended (base : Finset ι) (pow sup : A) (rows : Finset A) :
    rowBlock coords (extendedFrozenSupport coords base pow) pow sup rows =
      rowBlock coords base pow sup rows := by
```

## HeckeSkeleton/LowFrozenCube/FullHybridBound.lean

源码 SHA-256：`577c7d134932c4b9135fc3e0f6c6eea4fa1deeb537ea56ff5fe860c317756cb8`。

### symbol_mul_first

源码起始行：25。

```lean
theorem symbol_mul_first (a b c : A) :
    D.symbol (a * b) c = D.symbol a c * D.symbol b c := by
```

### raw_frozen_hybrid_bound

源码起始行：37。

```lean
theorem raw_frozen_hybrid_bound
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount)
    (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting q Ccount)
    (hq : HeckeSkeleton.LowHybrid.QuadraticSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (hc : HeckeSkeleton.LowHybrid.CubicSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ K N B L Bmin : ℝ, 1 ≤ N → 1 ≤ B → 1 ≤ L → 0 < Bmin →
      ∀ (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
        (phase : A → A → A → ℂ) (a₀ ρ₀ lam : A → ℂ)
        (pow sup : A) (rows marks columns : Finset A) (inputs : Finset (A × A)),
        (∀ k ∈ rows, normI k ≤ K) →
        (∀ d, (∀ p, PrimeCoordinates.valuation D.coords d p ≤ 1) →
          PrimeCoordinates.Avoids D.coords D.support d → ‖ρ₀ d‖ = 1) →
        (∀ P ∈ marks, PrimeCoordinates.Avoids D.coords D.support P) →
        (∀ P ∈ marks, HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords P ∧
          normI P ≤ L) →
        (∀ P ∈ marks, ‖a₀ P‖ ≤ 1) →
        (∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c) →
        (∀ c ∈ columns, HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords c ∧
          normI c ≤ N) →
        (∀ c ∈ columns, ‖lam c‖ ≤ 1) →
        (∀ u ∈ inputs, PrimeCoordinates.Supported D.coords D.ordinary u.1) →
        (∀ u ∈ inputs, PrimeCoordinates.Avoids D.coords D.ordinary u.2) →
        (∀ c ∈ columns, ∀ u ∈ inputs, ‖phase c u.1 u.2‖ ≤ 1) →
        (∀ u ∈ inputs,
          Bmin ≤ normI (PrimeCoordinates.residualCubeFactor D.coords u.1 * u.2)) →
        (∀ u ∈ inputs,
          normI (PrimeCoordinates.residualCubeFactor D.coords u.1 * u.2) ≤ B) →
        D.rawBlockSourceEnergy normI first prefactor atZero phase a₀ ρ₀ lam
          pow sup rows marks columns inputs ≤
          (D.tableMajorant normI first prefactor atZero / Bmin) ^ 2 *
            (C0 * (D.residualParameter normI K pow sup * N * B * L) ^ eps *
              (D.residualParameter normI K pow sup + N * B) * B *
                (N + L + (N * L) ^ (2 / 3 : ℝ))) := by
```

## HeckeSkeleton/LowFrozenCube/HybridExit.lean

源码 SHA-256：`df548c91e179319940655e751c25bd14521ffe6aecac7bd44a63083a7b6e52ff`。

### hybridSeparatedRow_eq_normalizedRow

源码起始行：19。

```lean
theorem hybridSeparatedRow_eq_normalizedRow
    (chi : A → A →* ℂ) (cop : A → A → Prop)
    (h6 : ∀ a b, (chi a b) ^ 6 = if cop a b then (1 : ℂ) else 0)
    (normI : A → ℝ) (a : A → ℂ) (beta : A → A → ℂ)
    (marks columns cubes : Finset A) (k : A) :
    hybridSeparatedRow chi cop (fun P => a P / (Real.sqrt (normI P) : ℂ))
      beta marks columns cubes k =
    HeckeSkeleton.LowHybrid.hybridRow (fun i j => chi i j) cop normI a beta
      marks columns cubes k := by
```

### frozen_energy_eq_hybridEnergy

源码起始行：34。

```lean
theorem frozen_energy_eq_hybridEnergy
    (chi : A → A →* ℂ) (cop : A → A → Prop)
    (h6 : ∀ a b, (chi a b) ^ 6 = if cop a b then (1 : ℂ) else 0)
    (normI : A → ℝ) (rows marks columns : Finset A) (t : Finset (A × A))
    (split : A → A × A) (hsplit : ∀ q ∈ t, split (cubeProduct q) = q)
    (a : A → ℂ) (B : A → A → A → ℂ)
    (hPx : ∀ P ∈ marks, ∀ q ∈ t, cop P q.1)
    (rho : A → ℂ) (hrho : ∀ k ∈ rows, ‖rho k‖ = 1) :
    (∑ k ∈ rows, ‖rho k * frozenSeparatedRow chi cop
      (fun P => a P / (Real.sqrt (normI P) : ℂ)) B marks columns t k‖ ^ 2) =
      HeckeSkeleton.LowHybrid.hybridEnergy (fun i j => chi i j) cop normI
        a (fullCubeCoefficient split B) rows marks columns (t.image cubeProduct) := by
```

## HeckeSkeleton/LowFrozenCube/Ledger.lean

源码 SHA-256：`91dc9376f31f163e4082fc9c58ba69fff2d183d2db80f1a9a190cbc7e1dcb73c`。

### cubicSaving_nonneg

源码起始行：19。

```lean
theorem cubicSaving_nonneg {v z : ℝ} (hv : 0 ≤ v) (hz : 0 ≤ z) :
    0 ≤ cubicSaving v z := by
```

### cubicSaving_le_left

源码起始行：24。

```lean
theorem cubicSaving_le_left (v z : ℝ) : cubicSaving v z ≤ v :=
```

### cubicSaving_le_right

源码起始行：27。

```lean
theorem cubicSaving_le_right (v z : ℝ) : cubicSaving v z ≤ z :=
```

### cubic_growth_identity

源码起始行：31。

```lean
theorem cubic_growth_identity (v z : ℝ) :
    max v (max z (2 * (v + z) / 3)) = v + z - cubicSaving v z := by
```

### cubicSaving_dichotomy

源码起始行：38。

```lean
theorem cubicSaving_dichotomy {v z : ℝ} (hv : 0 ≤ v) :
    cubicSaving v z = z ∨ v ≤ 2 * cubicSaving v z := by
```

### reflected_exponent_identity

源码起始行：63。

```lean
theorem reflected_exponent_identity (O H v ell S B z T : ℝ) :
    O / 2 + squaredCoefficientExponent v ell S B +
      hybridGrowthExponent H v ell z + squaredKernelExponent T v ell =
        reflectedExponent O H v ell S B z T := by
```

### terminal_row_branch

源码起始行：74。

```lean
theorem terminal_row_branch
    (F M O H v ell S B z T Q z0 c : ℝ)
    (hO : 0 ≤ O) (hS : 0 ≤ S) (hB : 0 ≤ B) (hell : 0 ≤ ell)
    (hv : 0 ≤ v) (hz : 0 ≤ z) (hQ : 0 ≤ Q)
    (hz0 : z ≤ z0) (hH : H ≤ M - O)
    (hmargin : c ≤ F - M - Q - z0)
    (hrow : v + ell ≤ H) :
    reflectedExponent O H v ell S B z T ≤ F - c := by
```

### terminal_column_equal_branch

源码起始行：90。

```lean
theorem terminal_column_equal_branch
    (F M N Nstar V bh d0 O H v ell S B z T Q z0 c tau : ℝ)
    (hF : F = N + V) (hNstar : Nstar = N - 3 * bh)
    (hO : 0 ≤ O) (hell : 0 ≤ ell) (hQ : 0 ≤ Q)
    (hV : V ≤ d0) (hbh : bh ≤ d0) (hz0 : z ≤ z0)
    (hmargin : c ≤ F - M - Q - z0)
    (hconductor : T - S - B ≤ 2 * M - O + Q + V - Nstar + 2 * z)
    (hretained : v + 3 * ell ≤ T + tau)
    (hcolumn : H ≤ v + ell) (hu : cubicSaving v z = z) :
    reflectedExponent O H v ell S B z T ≤ F - 2 * c + 5 * d0 + tau := by
```

### terminal_column_other_branch

源码起始行：106。

```lean
theorem terminal_column_other_branch
    (F M N Nstar V bh d0 O H v ell S B z T Q z0 c tau : ℝ)
    (hF : F = N + V) (hNstar : Nstar = N - 3 * bh)
    (hS : 0 ≤ S) (hB : 0 ≤ B) (hell : 0 ≤ ell)
    (hV : V ≤ d0) (hbh : bh ≤ d0) (hz0 : z ≤ z0)
    (hmargin1 : c ≤ F - M - Q - z0)
    (hmargin2 : c ≤ 4 * F - 3 * M - 6 * z0)
    (hconductor : T - S - B ≤ 2 * M - O + Q + V - Nstar + 2 * z)
    (hretained : v + 3 * ell ≤ T + tau)
    (hcolumn : H ≤ v + ell) (hu : v ≤ 2 * cubicSaving v z) :
    reflectedExponent O H v ell S B z T ≤
      F - M / 4 - 3 * c / 4 + 5 * d0 / 2 + tau / 2 := by
```

### terminal_ledger

源码起始行：130。

```lean
theorem terminal_ledger
    (F M N Nstar V bh d0 O H v ell S B z T Q z0 c tau : ℝ)
    (hF : F = N + V) (hNstar : Nstar = N - 3 * bh)
    (hO : 0 ≤ O) (hS : 0 ≤ S) (hB : 0 ≤ B) (hell : 0 ≤ ell)
    (hv : 0 ≤ v) (hz : 0 ≤ z) (hQ : 0 ≤ Q)
    (hV : V ≤ d0) (hbh : bh ≤ d0) (hz0 : z ≤ z0)
    (hH : H ≤ M - O)
    (hmargin1 : c ≤ F - M - Q - z0)
    (hmargin2 : c ≤ 4 * F - 3 * M - 6 * z0)
    (hconductor : T - S - B ≤ 2 * M - O + Q + V - Nstar + 2 * z)
    (hretained : v + 3 * ell ≤ T + tau) :
    reflectedExponent O H v ell S B z T ≤ terminalBound F M c d0 tau := by
```

### terminalBound_le_half_margin

源码起始行：161。

```lean
theorem terminalBound_le_half_margin
    (F M c d0 tau : ℝ) (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hd : d0 ≤ c / 100) (htau : tau ≤ c / 8) :
    terminalBound F M c d0 tau ≤ F - c / 2 := by
```

## HeckeSkeleton/LowFrozenCube/LocalBudget.lean

源码 SHA-256：`fa874f95b1e8e113c42c26b9e50bb358e4a87f5b1a9b77be721280fdd0bf64fd`。

### minimumCharge_le_one

源码起始行：28。

```lean
theorem minimumCharge_le_one (j m : ℕ) : minimumCharge j m ≤ 1 := by
```

### ordinaryScalar_minimum_sq_le

源码起始行：34。

```lean
theorem ordinaryScalar_minimum_sq_le (q : ℝ) (hq : 0 < q)
    (first prefactor : ℂ) (atZero : ℕ → ℂ) (j m : ℕ)
    (hm : m = 0 ∨ m = 1 ∨ m = 3)
    (hfirst : ‖first‖ ^ 2 ≤ 1 / q)
    (hprefactor : ‖prefactor‖ ^ 2 ≤ q)
    (hzero : ‖atZero j‖ ^ 2 ≤ if j = 0 ∨ j = 4 then 1 / q else 1) :
    ‖ordinaryScalar (q : ℂ) first prefactor atZero j m‖ ^ 2 ≤
      (q ^ minimumCharge j m)⁻¹ := by
```

### norm_chargeIdeal

源码起始行：75。

```lean
theorem norm_chargeIdeal (normI : A →* ℝ) :
    normI D.chargeIdeal = ∏ p ∈ D.ordinary,
      normI (D.prime p) ^ LocalTable.minimumCharge (D.digit p)
        (PrimeCoordinates.valuation D.coords D.minimum p) := by
```

### minimum_cases_of_activeInput

源码起始行：81。

```lean
theorem minimum_cases_of_activeInput (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (inputs : Finset (A × A)) (q : A × A)
    (hq : q ∈ D.activeInputBlock normI first prefactor atZero inputs) (p : ι) :
    PrimeCoordinates.valuation D.coords D.minimum p = 0 ∨
    PrimeCoordinates.valuation D.coords D.minimum p = 1 ∨
    PrimeCoordinates.valuation D.coords D.minimum p = 3 := by
```

### tableMajorant_sq_le_charge

源码起始行：94。

```lean
theorem tableMajorant_sq_le_charge (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
    (hminimum : ∀ p ∈ D.ordinary,
      PrimeCoordinates.valuation D.coords D.minimum p = 0 ∨
      PrimeCoordinates.valuation D.coords D.minimum p = 1 ∨
      PrimeCoordinates.valuation D.coords D.minimum p = 3)
    (hfirst : ∀ p ∈ D.ordinary, ‖first p‖ ^ 2 ≤ 1 / normI (D.prime p))
    (hprefactor : ∀ p ∈ D.ordinary, ‖prefactor p‖ ^ 2 ≤ normI (D.prime p))
    (hzero : ∀ p ∈ D.ordinary, ‖atZero p (D.digit p)‖ ^ 2 ≤
      if D.digit p = 0 ∨ D.digit p = 4 then 1 / normI (D.prime p) else 1) :
    D.tableMajorant normI first prefactor atZero ^ 2 ≤ (normI D.chargeIdeal)⁻¹ := by
```

### coefficientScale_identity

源码起始行：129。

```lean
theorem coefficientScale_identity (Z v ell S B : ℝ) (hZ : 0 < Z) :
    (Z ^ (S + B))⁻¹ / (Z ^ ell) ^ 2 / Z ^ v =
      Z ^ (squaredCoefficientExponent v ell S B) := by
```

### normalizedCoefficient_le_ledger

源码起始行：141。

```lean
theorem normalizedCoefficient_le_ledger (C N cubeNorm chargeNorm Z v ell S B : ℝ)
    (hN : 0 < N) (hZ : 0 < Z) (hC : C ^ 2 ≤ chargeNorm⁻¹)
    (hNscale : N = Z ^ v) (hBscale : cubeNorm = Z ^ ell)
    (hcharge : chargeNorm = Z ^ (S + B)) :
    (C / cubeNorm) ^ 2 / N ≤ Z ^ (squaredCoefficientExponent v ell S B) := by
```

## HeckeSkeleton/LowFrozenCube/LocalCoefficients.lean

源码 SHA-256：`486278431935fef5d04d7deb969d19db779fb56eac7c459abf8fe3f52df8c497`。

### localPhaseDigit_add_cube

源码起始行：18。

```lean
theorem localPhaseDigit_add_cube (j e x : ℕ) (he : 0 < e) :
    localPhaseDigit j (e + 3 * x) = localPhaseDigit j e := by
```

### localPhaseDigit_frozen

源码起始行：25。

```lean
theorem localPhaseDigit_frozen (j e : ℕ) (he : AdmissibleExponent e) :
    localPhaseDigit j e = localPhaseDigit j (frozenMin e) := by
```

### normalizedCubeCoefficient_norm_le

源码起始行：47。

```lean
theorem normalizedCubeCoefficient_norm_le (Qx C : ℝ) (Ω : ℂ)
    (hQx : 0 < Qx) (hC : 0 ≤ C) (hΩ : ‖Ω‖ ≤ C / Qx) :
    ‖normalizedCubeCoefficient Qx C Ω‖ ≤ 1 := by
```

### normalizedCubeCoefficient_reassemble

源码起始行：62。

```lean
theorem normalizedCubeCoefficient_reassemble (Qx Qn C : ℝ) (Ω : ℂ)
    (hQx : 0 < Qx) (hQn : 0 < Qn) (hC : 0 ≤ C) (hΩ : ‖Ω‖ ≤ C / Qx) :
    Ω / (Qn : ℂ) = (C : ℂ) * normalizedCubeCoefficient Qx C Ω /
      ((Qx * Qn : ℝ) : ℂ) := by
```

## HeckeSkeleton/LowFrozenCube/LocalTable.lean

源码 SHA-256：`e290079515aa1f7fe00a8cd0f25fc16321b24482ca2a99e849c2def77ef8e8f8`。

### sphericalScalar_zero

源码起始行：33。

```lean
@[simp] theorem sphericalScalar_zero (q first : ℂ) :
    sphericalScalar q first 0 = 1 := by
```

### sphericalScalar_one

源码起始行：36。

```lean
@[simp] theorem sphericalScalar_one (q first : ℂ) :
    sphericalScalar q first 1 = first := by
```

### sphericalScalar_three

源码起始行：39。

```lean
@[simp] theorem sphericalScalar_three (q first : ℂ) :
    sphericalScalar q first 3 = q⁻¹ := by
```

### sphericalScalar_add_cube

源码起始行：42。

```lean
theorem sphericalScalar_add_cube (q first : ℂ) (e x : ℕ) :
    sphericalScalar q first (e + 3 * x) =
      sphericalScalar q first e * (q⁻¹) ^ x := by
```

### sphericalScalar_residue_two

源码起始行：50。

```lean
theorem sphericalScalar_residue_two (q first : ℂ) (e : ℕ)
    (he : e % 3 = 2) : sphericalScalar q first e = 0 := by
```

### ordinaryScalar_add_cube

源码起始行：54。

```lean
theorem ordinaryScalar_add_cube (q first prefactor : ℂ) (atZero : ℕ → ℂ)
    (j e x : ℕ) (he : 0 < e) :
    ordinaryScalar q first prefactor atZero j (e + 3 * x) =
      ordinaryScalar q first prefactor atZero j e * (q⁻¹) ^ x := by
```

### ordinaryScalar_residue_two

源码起始行：67。

```lean
theorem ordinaryScalar_residue_two (q first prefactor : ℂ) (atZero : ℕ → ℂ)
    (j e : ℕ) (he : e % 3 = 2) : ordinaryScalar q first prefactor atZero j e = 0 := by
```

### ordinaryScalar_nonzero_admissible

源码起始行：72。

```lean
theorem ordinaryScalar_nonzero_admissible (q first prefactor : ℂ)
    (atZero : ℕ → ℂ) (j e : ℕ)
    (he : ordinaryScalar q first prefactor atZero j e ≠ 0) :
    AdmissibleExponent e := by
```

### ordinaryScalar_positive_only_four

源码起始行：83。

```lean
theorem ordinaryScalar_positive_only_four (q first prefactor : ℂ)
    (atZero : ℕ → ℂ) (j e : ℕ) (he : 0 < e) (hj : j ≠ 4) :
    ordinaryScalar q first prefactor atZero j e = 0 := by
```

### ordinaryScalar_frozen

源码起始行：90。

```lean
theorem ordinaryScalar_frozen (q first prefactor : ℂ) (atZero : ℕ → ℂ)
    (j e : ℕ) (he : AdmissibleExponent e) :
    ordinaryScalar q first prefactor atZero j e =
      ordinaryScalar q first prefactor atZero j (frozenMin e) *
        (q⁻¹) ^ frozenCubeExp e := by
```

### ordinaryScalar_frozen_norm

源码起始行：111。

```lean
theorem ordinaryScalar_frozen_norm (q : ℝ) (hq : 0 < q)
    (first prefactor : ℂ) (atZero : ℕ → ℂ) (j e : ℕ)
    (he : AdmissibleExponent e) :
    ‖ordinaryScalar (q : ℂ) first prefactor atZero j e‖ =
      ‖ordinaryScalar (q : ℂ) first prefactor atZero j (frozenMin e)‖ /
        q ^ frozenCubeExp e := by
```

### minimumMajorant_nonneg

源码起始行：139。

```lean
theorem minimumMajorant_nonneg (s : Finset ι) (q : ι → ℝ)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ) (digit exponent : ι → ℕ) :
    0 ≤ minimumMajorant s q first prefactor atZero digit exponent :=
```

### cubeNorm_pos

源码起始行：144。

```lean
theorem cubeNorm_pos (s : Finset ι) (q : ι → ℝ) (exponent : ι → ℕ)
    (hq : ∀ p ∈ s, 0 < q p) : 0 < cubeNorm s q exponent :=
```

### localProduct_nonzero_admissible

源码起始行：150。

```lean
theorem localProduct_nonzero_admissible (s : Finset ι) (q : ι → ℝ)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ) (digit exponent : ι → ℕ)
    (hprod : localProduct s q first prefactor atZero digit exponent ≠ 0)
    (p : ι) (hp : p ∈ s) : AdmissibleExponent (exponent p) := by
```

### localProduct_frozen_norm

源码起始行：162。

```lean
theorem localProduct_frozen_norm (s : Finset ι) (q : ι → ℝ)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ) (digit exponent : ι → ℕ)
    (hq : ∀ p ∈ s, 0 < q p)
    (he : ∀ p ∈ s, AdmissibleExponent (exponent p)) :
    ‖localProduct s q first prefactor atZero digit exponent‖ =
      minimumMajorant s q first prefactor atZero digit exponent /
        cubeNorm s q exponent := by
```

### phased_localProduct_norm_le

源码起始行：178。

```lean
theorem phased_localProduct_norm_le (s : Finset ι) (q : ι → ℝ)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ) (digit exponent : ι → ℕ)
    (hq : ∀ p ∈ s, 0 < q p)
    (he : ∀ p ∈ s, AdmissibleExponent (exponent p))
    (phase : ℂ) (hphase : ‖phase‖ ≤ 1) :
    ‖phase * localProduct s q first prefactor atZero digit exponent‖ ≤
      minimumMajorant s q first prefactor atZero digit exponent /
        cubeNorm s q exponent := by
```

## HeckeSkeleton/LowFrozenCube/Overlap.lean

源码 SHA-256：`1b9aa5616ca015d4b4e14c19d175dcba5cb21a2801cf105477ee5e8d86ec528c`。

### not_coprime_of_shared_prime

源码起始行：26。

```lean
theorem not_coprime_of_shared_prime (a b : A) (p : ι)
    (ha : valuation coords a p ≠ 0) (hb : valuation coords b p ≠ 0) :
    ¬ Coprime coords a b := by
```

### not_coprime_iff_shared_prime

源码起始行：32。

```lean
theorem not_coprime_iff_shared_prime (a b : A) :
    ¬ Coprime coords a b ↔ ∃ p, valuation coords a p ≠ 0 ∧ valuation coords b p ≠ 0 := by
```

### wholeIndex_overlap_zero

源码起始行：49。

```lean
theorem wholeIndex_overlap_zero {σ : Type*}
    (chi : A → A →* ℂ)
    (h6 : ∀ a b, (chi a b) ^ 6 = if Coprime coords a b then (1 : ℂ) else 0)
    (row : A) (slots : Finset σ) (prime : σ → ι)
    (i : σ) (hi : i ∈ slots) (hrow : valuation coords row (prime i) ≠ 0)
    (a : A) : chi row a * idealWholeIndexMark coords slots prime a = 0 := by
```

### primal_marked_sum_overlap_zero

源码起始行：63。

```lean
theorem primal_marked_sum_overlap_zero {σ κ : Type*}
    (chi : A → A →* ℂ)
    (h6 : ∀ a b, (chi a b) ^ 6 = if Coprime coords a b then (1 : ℂ) else 0)
    (row : A) (slots : Finset σ) (prime : σ → ι)
    (i : σ) (hi : i ∈ slots) (hrow : valuation coords row (prime i) ≠ 0)
    (indices : Finset κ) (index : κ → A) (weight : κ → ℂ) :
    (∑ a ∈ indices, weight a * chi row (index a) *
      idealWholeIndexMark coords slots prime (index a)) = 0 := by
```

### mixedPhase_row_overlap_zero

源码起始行：82。

```lean
theorem mixedPhase_row_overlap_zero (d P c n : A) (p : ι)
    (hP : PrimeCoordinates.valuation D.coords P p ≠ 0)
    (hd : PrimeCoordinates.valuation D.coords d p ≠ 0) :
    D.mixedPhase d P c n = 0 := by
```

### mixedPhase_column_overlap_zero

源码起始行：90。

```lean
theorem mixedPhase_column_overlap_zero (d P c n : A) (p : ι)
    (hP : PrimeCoordinates.valuation D.coords P p ≠ 0)
    (hc : PrimeCoordinates.valuation D.coords c p ≠ 0) :
    D.mixedPhase d P c n = 0 := by
```

### mixedPhase_cube_overlap_zero

源码起始行：98。

```lean
theorem mixedPhase_cube_overlap_zero (d P c n : A)
    (hn : ¬ PrimeCoordinates.Coprime D.coords P n) :
    D.mixedPhase d P c n = 0 := by
```

### sourceTerm_row_overlap_zero

源码起始行：103。

```lean
theorem sourceTerm_row_overlap_zero (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
    (Ω : A → A → A → ℂ) (d P c x n : A) (p : ι)
    (hP : PrimeCoordinates.valuation D.coords P p ≠ 0)
    (hd : PrimeCoordinates.valuation D.coords d p ≠ 0) :
    D.sourceTerm normI a₀ ρ₀ lam Ω d P c x n = 0 := by
```

### sourceTerm_column_overlap_zero

源码起始行：110。

```lean
theorem sourceTerm_column_overlap_zero (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
    (Ω : A → A → A → ℂ) (d P c x n : A) (p : ι)
    (hP : PrimeCoordinates.valuation D.coords P p ≠ 0)
    (hc : PrimeCoordinates.valuation D.coords c p ≠ 0) :
    D.sourceTerm normI a₀ ρ₀ lam Ω d P c x n = 0 := by
```

### sourceTerm_fullCube_overlap_zero

源码起始行：119。

```lean
theorem sourceTerm_fullCube_overlap_zero (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
    (Ω : A → A → A → ℂ) (d P c x n : A)
    (hP : PrimeCoordinates.Avoids D.coords D.support P) (hx : D.CanonicalCube x)
    (hcollision : ¬ PrimeCoordinates.Coprime D.coords P (x * n)) :
    D.sourceTerm normI a₀ ρ₀ lam Ω d P c x n = 0 := by
```

## HeckeSkeleton/LowFrozenCube/Phases.lean

源码 SHA-256：`1b4fb1b889961baaca10b6720c41133b8556a3ce1efe0d420660ac6f501d0623`。

### inverse_square_eq_fourth

源码起始行：21。

```lean
theorem inverse_square_eq_fourth (z : ℂ) (hz : z = 0 ∨ z ^ 6 = 1) :
    (z⁻¹) ^ 2 = z ^ 4 := by
```

### inverse_fourth_eq_square

源码起始行：36。

```lean
theorem inverse_fourth_eq_square (z : ℂ) (hz : z = 0 ∨ z ^ 6 = 1) :
    (z⁻¹) ^ 4 = z ^ 2 := by
```

### zpow_neg_two_eq_fourth

源码起始行：51。

```lean
theorem zpow_neg_two_eq_fourth (z : ℂ) (hz : z = 0 ∨ z ^ 6 = 1) :
    z ^ (-2 : ℤ) = z ^ 4 := by
```

### zpow_neg_four_eq_square

源码起始行：55。

```lean
theorem zpow_neg_four_eq_square (z : ℂ) (hz : z = 0 ∨ z ^ 6 = 1) :
    z ^ (-4 : ℤ) = z ^ 2 := by
```

### sextic_symbol_zero_or_root

源码起始行：67。

```lean
theorem sextic_symbol_zero_or_root
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0) (a b : A) :
    χ a b = 0 ∨ (χ a b) ^ 6 = 1 := by
```

### symbol_zpow_neg_two

源码起始行：77。

```lean
theorem symbol_zpow_neg_two
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0) (a b : A) :
    (χ a b) ^ (-2 : ℤ) = (χ a b) ^ 4 :=
```

### symbol_zpow_neg_four

源码起始行：82。

```lean
theorem symbol_zpow_neg_four
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0) (a b : A) :
    (χ a b) ^ (-4 : ℤ) = (χ a b) ^ 2 :=
```

### row_mark_phase

源码起始行：88。

```lean
theorem row_mark_phase (hrec : ∀ a b, χ a b = χ b a)
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0) (d P : A) :
    (χ d P) ^ 4 * (χ P d) ^ 2 = if Cop d P then (1 : ℂ) else 0 := by
```

### row_column_phase

源码起始行：97。

```lean
theorem row_column_phase (hrec : ∀ a b, χ a b = χ b a) (d c : A) :
    χ d c * (χ c d) ^ 2 = (χ d c) ^ 3 := by
```

### mark_column_phase

源码起始行：103。

```lean
theorem mark_column_phase (hrec : ∀ a b, χ a b = χ b a) (P c : A) :
    (χ P c) ^ 2 * (χ c P) ^ 2 = (χ P c) ^ 4 := by
```

### frozen_cube_square_phase

源码起始行：109。

```lean
theorem frozen_cube_square_phase
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0)
    (P x : A) (hPx : Cop P x) :
    (χ P (x ^ 3)) ^ 2 = 1 := by
```

### full_cube_symbol_mask

源码起始行：119。

```lean
theorem full_cube_symbol_mask
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0)
    (P x n : A) (hPx : Cop P x) :
    (if Cop P (x * n) then (1 : ℂ) else 0) =
      if Cop P n then (1 : ℂ) else 0 := by
```

### frozen_cube_row_phase

源码起始行：127。

```lean
theorem frozen_cube_row_phase (d c x n : A) :
    (χ d x) ^ 3 * (χ d (c * n)) ^ 3 =
      (χ d (c * (x * n))) ^ 3 := by
```

### frozen_cube_hybrid_summand

源码起始行：134。

```lean
theorem frozen_cube_hybrid_summand
    (h6 : ∀ a b, (χ a b) ^ 6 = if Cop a b then (1 : ℂ) else 0)
    (d P c x n : A) (hPx : Cop P x) :
    ((χ d x) ^ 3 * (χ d (c * n)) ^ 3) * (χ P c) ^ 4 *
        (if Cop P n then (1 : ℂ) else 0) =
      (χ d (c * (x * n))) ^ 3 * (χ P c) ^ 4 *
        (if Cop P (x * n) then (1 : ℂ) else 0) := by
```

## HeckeSkeleton/LowFrozenCube/PowerfulCounting.lean

源码 SHA-256：`b74efa564cec7eb299d4f63444520719664d04d9b2202ff4e603d7e5c54e1271`。

### card_le_real_scale_of_linear_counting

源码起始行：24。

```lean
theorem card_le_real_scale_of_linear_counting
    {I : Type*} (q : I → ℕ) (normI : I → ℝ)
    (hnorm : ∀ i, normI i = (q i : ℝ)) (C : ℝ) (hC : 0 ≤ C)
    (hcount : LinearNormCounting q C) (X : ℝ) (hX : 0 ≤ X)
    (s : Finset I) (hs : ∀ i ∈ s, normI i ≤ X) :
    (s.card : ℝ) ≤ C * X := by
```

### product_pair_count_le_harmonic

源码起始行：39。

```lean
theorem product_pair_count_le_harmonic
    {I : Type*} (q : I → ℕ) (normI : I → ℝ)
    (hnorm : ∀ i, normI i = (q i : ℝ)) (C : ℝ) (hC : 0 ≤ C)
    (hq : ∀ i, 1 ≤ q i) (hcount : LinearNormCounting q C)
    (R : ℝ) (hR : 1 ≤ R) (pairs : Finset (I × I))
    (hpairs : ∀ u ∈ pairs, normI u.1 * normI u.2 ≤ R) :
    (pairs.card : ℝ) ≤ C * R * harmonicEnvelope C R := by
```

### powerful_pair_injOn

源码起始行：93。

```lean
theorem powerful_pair_injOn (s : Finset A)
    (hs : ∀ a ∈ s, ∀ p, valuation coords a p = 0 ∨ 2 ≤ valuation coords a p) :
    Set.InjOn
      (fun a => (powerfulSquareFactor coords a, powerfulCubeFactor coords a)) s := by
```

### powerful_pair_norm_le_sqrt

源码起始行：109。

```lean
theorem powerful_pair_norm_le_sqrt
    (normI : A →* ℝ) (hn : ∀ a, 1 ≤ normI a) (a : A) (K : ℝ)
    (ha : ∀ p, valuation coords a p = 0 ∨ 2 ≤ valuation coords a p)
    (hK : normI a ≤ K) :
    normI (powerfulSquareFactor coords a) * normI (powerfulCubeFactor coords a) ≤
      Real.sqrt K := by
```

### powerful_count_le_sqrt_harmonic

源码起始行：132。

```lean
theorem powerful_count_le_sqrt_harmonic
    (normI : A →* ℝ) (q : A → ℕ) (hnorm : ∀ a, normI a = (q a : ℝ))
    (C : ℝ) (hC : 0 ≤ C) (hq : ∀ a, 1 ≤ q a) (hcount : LinearNormCounting q C)
    (K : ℝ) (hK : 1 ≤ K) (s : Finset A)
    (hs : ∀ a ∈ s, (∀ p, valuation coords a p = 0 ∨ 2 ≤ valuation coords a p) ∧
      normI a ≤ K) :
    (s.card : ℝ) ≤ C * Real.sqrt K * harmonicEnvelope C K := by
```

### powerful_count_small_power

源码起始行：164。

```lean
theorem powerful_count_small_power
    (normI : A →* ℝ) (q : A → ℕ) (hnorm : ∀ a, normI a = (q a : ℝ))
    (Ccount : ℝ) (hC : 0 < Ccount) (hq : ∀ a, 1 ≤ q a)
    (hcount : LinearNormCounting q Ccount) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K → ∀ s : Finset A,
      (∀ a ∈ s, (∀ p, valuation coords a p = 0 ∨ 2 ≤ valuation coords a p) ∧
        normI a ≤ K) → (s.card : ℝ) ≤ C * K ^ (1 / 2 + eps) := by
```

### supported_squarefree_count_le

源码起始行：185。

```lean
theorem supported_squarefree_count_le
    (support : Finset ι) (s : Finset A)
    (hs : ∀ a ∈ s, PrimeArithmetic.Squarefree coords a ∧ Supported coords support a) :
    s.card ≤ 2 ^ support.card := by
```

## HeckeSkeleton/LowFrozenCube/PrimeCoordinates.lean

源码 SHA-256：`7e47063be8509c0256e69fe4300ff89bdf1a0bf5f049d0b80b07a8919577c09d`。

### valuation_injective

源码起始行：26。

```lean
theorem valuation_injective : Function.Injective (valuation coords) := by
```

### valuation_one

源码起始行：31。

```lean
@[simp] theorem valuation_one : valuation coords 1 = 0 := by
```

### valuation_mul

源码起始行：34。

```lean
@[simp] theorem valuation_mul (a b : A) :
    valuation coords (a * b) = valuation coords a + valuation coords b := by
```

### valuation_pow

源码起始行：38。

```lean
@[simp] theorem valuation_pow (a : A) (n : ℕ) :
    valuation coords (a ^ n) = n • valuation coords a := by
```

### valuation_mul_apply

源码起始行：42。

```lean
@[simp] theorem valuation_mul_apply (a b : A) (p : ι) :
    valuation coords (a * b) p = valuation coords a p + valuation coords b p := by
```

### valuation_pow_apply

源码起始行：47。

```lean
@[simp] theorem valuation_pow_apply (a : A) (n : ℕ) (p : ι) :
    valuation coords (a ^ n) p = n * valuation coords a p := by
```

### valuation_mapExponents

源码起始行：56。

```lean
@[simp] theorem valuation_mapExponents (f : ℕ → ℕ) (hf : f 0 = 0)
    (a : A) (p : ι) :
    valuation coords (mapExponents coords f hf a) p = f (valuation coords a p) := by
```

### valuation_supportedFactor

源码起始行：81。

```lean
@[simp] theorem valuation_supportedFactor (s : Finset ι) (a : A) (p : ι) :
    valuation coords (supportedFactor coords s a) p =
      if p ∈ s then valuation coords a p else 0 := by
```

### valuation_awayFactor

源码起始行：86。

```lean
@[simp] theorem valuation_awayFactor (s : Finset ι) (a : A) (p : ι) :
    valuation coords (awayFactor coords s a) p =
      if p ∈ s then 0 else valuation coords a p := by
```

### supportedFactor_supported

源码起始行：91。

```lean
theorem supportedFactor_supported (s : Finset ι) (a : A) :
    Supported coords s (supportedFactor coords s a) := by
```

### awayFactor_avoids

源码起始行：96。

```lean
theorem awayFactor_avoids (s : Finset ι) (a : A) :
    Avoids coords s (awayFactor coords s a) := by
```

### supported_mul_away

源码起始行：102。

```lean
theorem supported_mul_away (s : Finset ι) (a : A) :
    supportedFactor coords s a * awayFactor coords s a = a := by
```

### cubeSplit_mul

源码起始行：110。

```lean
theorem cubeSplit_mul (s : Finset ι) (x n : A)
    (hx : Supported coords s x) (hn : Avoids coords s n) :
    cubeSplit coords s (x * n) = (x, n) := by
```

### supported_away_unique

源码起始行：129。

```lean
theorem supported_away_unique (s : Finset ι) (a x n : A)
    (hx : Supported coords s x) (hn : Avoids coords s n) (ha : a = x * n) :
    x = supportedFactor coords s a ∧ n = awayFactor coords s a := by
```

### coprime_of_avoids_supported

源码起始行：136。

```lean
theorem coprime_of_avoids_supported (s : Finset ι) (P x : A)
    (hP : Avoids coords s P) (hx : Supported coords s x) :
    Coprime coords P x :=
```

### coprime_symm

源码起始行：141。

```lean
theorem coprime_symm (a b : A) : Coprime coords a b ↔ Coprime coords b a := by
```

### coprime_mul_right

源码起始行：144。

```lean
theorem coprime_mul_right (a b c : A) :
    Coprime coords a (b * c) ↔ Coprime coords a b ∧ Coprime coords a c := by
```

### coprime_fullCube

源码起始行：150。

```lean
theorem coprime_fullCube (s : Finset ι) (P x n : A)
    (hP : Avoids coords s P) (hx : Supported coords s x) :
    Coprime coords P (x * n) ↔ Coprime coords P n := by
```

### minimum_mul_residualCube

源码起始行：163。

```lean
theorem minimum_mul_residualCube (a : A)
    (ha : ∀ p, AdmissibleExponent (valuation coords a p)) :
    a = minimumFactor coords a * residualCubeFactor coords a ^ 3 := by
```

### residualCubeFactor_supported

源码起始行：172。

```lean
theorem residualCubeFactor_supported (s : Finset ι) (a : A)
    (ha : Supported coords s a) : Supported coords s (residualCubeFactor coords a) := by
```

### minimumFactor_supported

源码起始行：177。

```lean
theorem minimumFactor_supported (s : Finset ι) (a : A)
    (ha : Supported coords s a) : Supported coords s (minimumFactor coords a) := by
```

### coprime_residualCubeFactor

源码起始行：182。

```lean
theorem coprime_residualCubeFactor (s : Finset ι) (P a : A)
    (hP : Avoids coords s P) (ha : Supported coords s a) :
    Coprime coords P (residualCubeFactor coords a) :=
```

### symbol_zero_of_shared_prime

源码起始行：190。

```lean
theorem symbol_zero_of_shared_prime
    (chi : A → A →* ℂ)
    (h6 : ∀ a b, (chi a b) ^ 6 = if Coprime coords a b then (1 : ℂ) else 0)
    (a b : A) (p : ι) (ha : valuation coords a p ≠ 0)
    (hb : valuation coords b p ≠ 0) : chi a b = 0 := by
```

## HeckeSkeleton/LowFrozenCube/PrimeProducts.lean

源码 SHA-256：`a6fc4acef78d733ed5409f249e7ad383da57a83ab5b3ee7be184585053054f98`。

### valuation_primeElement

源码起始行：23。

```lean
@[simp] theorem valuation_primeElement (p : ι) :
    valuation coords (primeElement coords p) = Finsupp.single p 1 := by
```

### primeElement_injective

源码起始行：27。

```lean
theorem primeElement_injective : Function.Injective (primeElement coords) := by
```

### valuation_prod_apply

源码起始行：33。

```lean
theorem valuation_prod_apply {κ : Type*} (s : Finset κ) (f : κ → A) (p : ι) :
    valuation coords (∏ i ∈ s, f i) p = ∑ i ∈ s, valuation coords (f i) p := by
```

### supported_support

源码起始行：40。

```lean
theorem supported_support (a : A) :
    Supported coords (valuation coords a).support a := by
```

### factorization

源码起始行：47。

```lean
theorem factorization (s : Finset ι) (a : A) (ha : Supported coords s a) :
    a = ∏ p ∈ s, primeElement coords p ^ valuation coords a p := by
```

### norm_factorization

源码起始行：58。

```lean
theorem norm_factorization (s : Finset ι) (a : A)
    (ha : Supported coords s a) (normI : A →* ℝ) :
    normI a = ∏ p ∈ s, normI (primeElement coords p) ^ valuation coords a p := by
```

### norm_eq_prod

源码起始行：67。

```lean
theorem norm_eq_prod (normI : A →* ℝ) (a : A) :
    normI a = ∏ p ∈ (valuation coords a).support,
      normI (primeElement coords p) ^ valuation coords a p :=
```

## HeckeSkeleton/LowFrozenCube/Products.lean

源码 SHA-256：`f02ff56df81ff378b9dee2fb53a43370d18d995199bd845f2adb714cded39e9e`。

### valuationProduct_add

源码起始行：21。

```lean
theorem valuationProduct_add (prime : ι → A) (s : Finset ι) (v w : ι → ℕ) :
    valuationProduct prime s (fun p => v p + w p) =
      valuationProduct prime s v * valuationProduct prime s w := by
```

### valuationProduct_scale

源码起始行：26。

```lean
theorem valuationProduct_scale (prime : ι → A) (s : Finset ι)
    (v : ι → ℕ) (n : ℕ) :
    valuationProduct prime s (fun p => n * v p) = valuationProduct prime s v ^ n := by
```

### frozen_product_decomposition

源码起始行：36。

```lean
theorem frozen_product_decomposition (prime : ι → A) (s : Finset ι)
    (v : ι → ℕ) (hv : ∀ p, AdmissibleExponent (v p)) :
    valuationProduct prime s v =
      valuationProduct prime s (frozenBase v) * valuationProduct prime s (frozenCube v) ^ 3 := by
```

### fullCube_product_decomposition

源码起始行：50。

```lean
theorem fullCube_product_decomposition [DecidableEq ι] (prime : ι → A)
    (primes frozen : Finset ι) (v : ι → ℕ) :
    valuationProduct prime primes v =
      valuationProduct prime primes (supportedPart frozen v) *
        valuationProduct prime primes (awayPart frozen v) := by
```

### row_product_decomposition

源码起始行：62。

```lean
theorem row_product_decomposition [DecidableEq ι] (prime : ι → A)
    (primes frozen : Finset ι) (v : ι → ℕ) :
    valuationProduct prime primes v =
      valuationProduct prime primes (powerfulRowPart v) *
        valuationProduct prime primes (supportedRowPart frozen v) *
          valuationProduct prime primes (residualRowPart frozen v) := by
```

### powerful_product_decomposition

源码起始行：77。

```lean
theorem powerful_product_decomposition (prime : ι → A) (s : Finset ι)
    (v : ι → ℕ) (hv : ∀ p, v p = 0 ∨ 2 ≤ v p) :
    valuationProduct prime s v =
      valuationProduct prime s (fun p => powerfulSquareExp (v p)) ^ 2 *
        valuationProduct prime s (fun p => powerfulCubeDigit (v p)) ^ 3 := by
```

## HeckeSkeleton/LowFrozenCube/RawInput.lean

源码 SHA-256：`bc7c2c949346fb0db1d75479e140a2be68c3792a0bb01b96402fbec8e477420a`。

### mem_activeInputBlock

源码起始行：43。

```lean
@[simp] theorem mem_activeInputBlock (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (inputs : Finset (A × A)) (q : A × A) :
    q ∈ D.activeInputBlock normI first prefactor atZero inputs ↔
      q ∈ inputs ∧ PrimeCoordinates.minimumFactor D.coords q.1 = D.minimum ∧
        D.rawTable normI first prefactor atZero q.1 ≠ 0 := by
```

### rawTable_nonzero_admissible

源码起始行：50。

```lean
theorem rawTable_nonzero_admissible (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (a : A)
    (ha : PrimeCoordinates.Supported D.coords D.ordinary a)
    (htable : D.rawTable normI first prefactor atZero a ≠ 0) :
    ∀ p, AdmissibleExponent (PrimeCoordinates.valuation D.coords a p) := by
```

### canonical_of_minimumFactor_eq

源码起始行：62。

```lean
theorem canonical_of_minimumFactor_eq (a : A)
    (hminimum : PrimeCoordinates.minimumFactor D.coords a = D.minimum) :
    D.CanonicalCube (PrimeCoordinates.residualCubeFactor D.coords a) := by
```

### activeInput_reconstruct

源码起始行：75。

```lean
theorem activeInput_reconstruct (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (inputs : Finset (A × A))
    (hsupport : ∀ q ∈ inputs, PrimeCoordinates.Supported D.coords D.ordinary q.1)
    (q : A × A) (hq : q ∈ D.activeInputBlock normI first prefactor atZero inputs) :
    q.1 = D.minimum * (PrimeCoordinates.residualCubeFactor D.coords q.1) ^ 3 := by
```

### freezePair_injOn

源码起始行：89。

```lean
theorem freezePair_injOn (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (inputs : Finset (A × A))
    (hsupport : ∀ q ∈ inputs, PrimeCoordinates.Supported D.coords D.ordinary q.1) :
    Set.InjOn D.freezePair (D.activeInputBlock normI first prefactor atZero inputs :
      Set (A × A)) := by
```

### frozenInputPairs_canonical

源码起始行：109。

```lean
theorem frozenInputPairs_canonical (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (inputs : Finset (A × A))
    (haway : ∀ q ∈ inputs, PrimeCoordinates.Avoids D.coords D.ordinary q.2)
    (q : A × A) (hq : q ∈ D.frozenInputPairs normI first prefactor atZero inputs) :
    D.CanonicalCube q.1 ∧ PrimeCoordinates.Avoids D.coords D.ordinary q.2 := by
```

### minimum_supported_of_activeInput

源码起始行：118。

```lean
theorem minimum_supported_of_activeInput (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (inputs : Finset (A × A))
    (hsupport : ∀ q ∈ inputs, PrimeCoordinates.Supported D.coords D.ordinary q.1)
    (q : A × A) (hq : q ∈ D.activeInputBlock normI first prefactor atZero inputs) :
    PrimeCoordinates.Supported D.coords D.ordinary D.minimum := by
```

## HeckeSkeleton/LowFrozenCube/RawRowBlockExit.lean

源码 SHA-256：`a9d5641bad416cf67b4f529ffc38485e39dec9afd52bb36b547eddd50c72f4f1`。

### rawBlockSourceEnergy_reindex

源码起始行：33。

```lean
theorem rawBlockSourceEnergy_reindex (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ)
    (a₀ ρ₀ lam : A → ℂ) (pow sup : A) (rows marks columns : Finset A)
    (inputs : Finset (A × A)) :
    D.rawBlockSourceEnergy normI first prefactor atZero phase a₀ ρ₀ lam
      pow sup rows marks columns inputs =
      ∑ d ∈ PrimeCoordinates.residualRows D.coords D.support pow sup rows,
        ‖D.rawSourceRow normI first prefactor atZero phase a₀ ρ₀ lam
          marks columns inputs d‖ ^ 2 :=
```

### raw_frozen_row_block_exit

源码起始行：51。

```lean
theorem raw_frozen_row_block_exit
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
    (phase : A → A → A → ℂ) (a₀ ρ₀ lam : A → ℂ)
    (K B : ℝ) (hB : 0 < B) (pow sup : A)
    (rows marks columns : Finset A) (inputs : Finset (A × A))
    (hrows : ∀ k ∈ rows, normI k ≤ K)
    (hρ₀ : ∀ d, (∀ p, PrimeCoordinates.valuation D.coords d p ≤ 1) →
      PrimeCoordinates.Avoids D.coords D.support d → ‖ρ₀ d‖ = 1)
    (hmarks : ∀ P ∈ marks, PrimeCoordinates.Avoids D.coords D.support P)
    (ha₀ : ∀ P ∈ marks, ‖a₀ P‖ ≤ 1)
    (hcolumns : ∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hlam : ∀ c ∈ columns, ‖lam c‖ ≤ 1)
    (hsupport : ∀ q ∈ inputs, PrimeCoordinates.Supported D.coords D.ordinary q.1)
    (haway : ∀ q ∈ inputs, PrimeCoordinates.Avoids D.coords D.ordinary q.2)
    (hphase : ∀ c ∈ columns, ∀ q ∈ inputs, ‖phase c q.1 q.2‖ ≤ 1)
    (hlower : ∀ q ∈ inputs,
      B ≤ normI (PrimeCoordinates.residualCubeFactor D.coords q.1 * q.2)) :
    let residual :=
```

## HeckeSkeleton/LowFrozenCube/RawSource.lean

源码 SHA-256：`4e1ad546151492ede05feea5d8daabac5f431d5bd7a4d91b977288f86b72bb74`。

### rawSourceTerm_zero

源码起始行：46。

```lean
theorem rawSourceTerm_zero (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ)
    (a₀ ρ₀ lam : A → ℂ) (d P c a n : A)
    (hz : D.rawTable normI first prefactor atZero a = 0) :
    D.rawSourceTerm normI first prefactor atZero phase a₀ ρ₀ lam d P c a n = 0 := by
```

### rawSourceTerm_eq_sourceTerm

源码起始行：55。

```lean
theorem rawSourceTerm_eq_sourceTerm (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ)
    (a₀ ρ₀ lam : A → ℂ) (d P c a x n : A)
    (ha : a = D.minimum * x ^ 3) :
    D.rawSourceTerm normI first prefactor atZero phase a₀ ρ₀ lam d P c a n =
      D.sourceTerm normI a₀ ρ₀ lam
        (D.tableOmega normI first prefactor atZero (D.frozenPhase phase)) d P c x n := by
```

### rawSourceRow_eq_sourceRow

源码起始行：68。

```lean
theorem rawSourceRow_eq_sourceRow (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ)
    (a₀ ρ₀ lam : A → ℂ) (marks columns : Finset A) (inputs : Finset (A × A))
    (hsupport : ∀ q ∈ inputs, PrimeCoordinates.Supported D.coords D.ordinary q.1)
    (d : A) :
    D.rawSourceRow normI first prefactor atZero phase a₀ ρ₀ lam marks columns inputs d =
      D.sourceRow normI a₀ ρ₀ lam
        (D.tableOmega normI first prefactor atZero (D.frozenPhase phase))
        marks columns (D.frozenInputPairs normI first prefactor atZero inputs) d := by
```

### frozenPhase_norm_le

源码起始行：102。

```lean
theorem frozenPhase_norm_le (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ)
    (columns : Finset A) (inputs : Finset (A × A))
    (hsupport : ∀ q ∈ inputs, PrimeCoordinates.Supported D.coords D.ordinary q.1)
    (hphase : ∀ c ∈ columns, ∀ q ∈ inputs, ‖phase c q.1 q.2‖ ≤ 1)
    (c : A) (hc : c ∈ columns) (q : A × A)
    (hq : q ∈ D.frozenInputPairs normI first prefactor atZero inputs) :
    ‖D.frozenPhase phase c q.1 q.2‖ ≤ 1 := by
```

### frozenInputPairs_norm_lower

源码起始行：117。

```lean
theorem frozenInputPairs_norm_lower (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (inputs : Finset (A × A)) (B : ℝ)
    (hlower : ∀ q ∈ inputs,
      B ≤ normI (PrimeCoordinates.residualCubeFactor D.coords q.1 * q.2))
    (q : A × A) (hq : q ∈ D.frozenInputPairs normI first prefactor atZero inputs) :
    B ≤ normI (cubeProduct q) := by
```

### raw_local_table_frozen_exit

源码起始行：129。

```lean
theorem raw_local_table_frozen_exit
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
    (phase : A → A → A → ℂ)
    (hminimum : PrimeCoordinates.Supported D.coords D.ordinary D.minimum)
    (a₀ ρ₀ lam : A → ℂ) (B : ℝ) (hB : 0 < B)
    (rows marks columns : Finset A) (inputs : Finset (A × A))
    (hrows : ∀ d ∈ rows, PrimeCoordinates.Avoids D.coords D.support d)
    (hρ₀ : ∀ d ∈ rows, ‖ρ₀ d‖ = 1)
    (hmarks : ∀ P ∈ marks, PrimeCoordinates.Avoids D.coords D.support P)
    (ha₀ : ∀ P ∈ marks, ‖a₀ P‖ ≤ 1)
    (hcolumns : ∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hlam : ∀ c ∈ columns, ‖lam c‖ ≤ 1)
    (hsupport : ∀ q ∈ inputs, PrimeCoordinates.Supported D.coords D.ordinary q.1)
    (haway : ∀ q ∈ inputs, PrimeCoordinates.Avoids D.coords D.ordinary q.2)
    (hphase : ∀ c ∈ columns, ∀ q ∈ inputs, ‖phase c q.1 q.2‖ ≤ 1)
    (hlower : ∀ q ∈ inputs,
      B ≤ normI (PrimeCoordinates.residualCubeFactor D.coords q.1 * q.2)) :
    let pairs :=
```

## HeckeSkeleton/LowFrozenCube/RowCoordinates.lean

源码 SHA-256：`bfad86a8e62fd22a265edd50c44eb55680b2ec0637af485fe40f1258e26bc65d`。

### valuation_powerfulRowFactor

源码起始行：32。

```lean
@[simp] theorem valuation_powerfulRowFactor (k : A) (p : ι) :
    valuation coords (powerfulRowFactor coords k) p =
      powerfulRowPart (valuation coords k) p := by
```

### valuation_supportedRowFactor

源码起始行：37。

```lean
@[simp] theorem valuation_supportedRowFactor (s : Finset ι) (k : A) (p : ι) :
    valuation coords (supportedRowFactor coords s k) p =
      supportedRowPart s (valuation coords k) p := by
```

### valuation_residualRowFactor

源码起始行：43。

```lean
@[simp] theorem valuation_residualRowFactor (s : Finset ι) (k : A) (p : ι) :
    valuation coords (residualRowFactor coords s k) p =
      residualRowPart s (valuation coords k) p := by
```

### row_factorization

源码起始行：50。

```lean
theorem row_factorization (s : Finset ι) (k : A) :
    k = powerfulRowFactor coords k * supportedRowFactor coords s k *
      residualRowFactor coords s k := by
```

### powerfulRowFactor_powerful

源码起始行：59。

```lean
theorem powerfulRowFactor_powerful (k : A) (p : ι) :
    valuation coords (powerfulRowFactor coords k) p = 0 ∨
      2 ≤ valuation coords (powerfulRowFactor coords k) p := by
```

### supportedRowFactor_squarefree

源码起始行：67。

```lean
theorem supportedRowFactor_squarefree (s : Finset ι) (k : A) (p : ι) :
    valuation coords (supportedRowFactor coords s k) p ≤ 1 := by
```

### residualRowFactor_squarefree

源码起始行：72。

```lean
theorem residualRowFactor_squarefree (s : Finset ι) (k : A) (p : ι) :
    valuation coords (residualRowFactor coords s k) p ≤ 1 := by
```

### supportedRowFactor_supported

源码起始行：77。

```lean
theorem supportedRowFactor_supported (s : Finset ι) (k : A) :
    Supported coords s (supportedRowFactor coords s k) :=
```

### residualRowFactor_avoids

源码起始行：81。

```lean
theorem residualRowFactor_avoids (s : Finset ι) (k : A) :
    Avoids coords s (residualRowFactor coords s k) :=
```

### row_factors_pairwise_coprime

源码起始行：85。

```lean
theorem row_factors_pairwise_coprime (s : Finset ι) (k : A) :
    Coprime coords (powerfulRowFactor coords k) (supportedRowFactor coords s k) ∧
    Coprime coords (powerfulRowFactor coords k) (residualRowFactor coords s k) ∧
    Coprime coords (supportedRowFactor coords s k) (residualRowFactor coords s k) := by
```

### norm_row_factorization

源码起始行：98。

```lean
theorem norm_row_factorization (s : Finset ι) (k : A) (normI : A →* ℝ) :
    normI k = normI (powerfulRowFactor coords k) *
      normI (supportedRowFactor coords s k) * normI (residualRowFactor coords s k) := by
```

### norm_residualRowFactor

源码起始行：103。

```lean
theorem norm_residualRowFactor (s : Finset ι) (k : A)
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a) :
    normI (residualRowFactor coords s k) = normI k /
      (normI (powerfulRowFactor coords k) * normI (supportedRowFactor coords s k)) := by
```

### norm_residualRowFactor_le

源码起始行：111。

```lean
theorem norm_residualRowFactor_le (s : Finset ι) (k : A)
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a) (K : ℝ) (hk : normI k ≤ K) :
    normI (residualRowFactor coords s k) ≤ K /
      (normI (powerfulRowFactor coords k) * normI (supportedRowFactor coords s k)) := by
```

### valuation_powerfulSquareFactor

源码起始行：124。

```lean
@[simp] theorem valuation_powerfulSquareFactor (a : A) (p : ι) :
    valuation coords (powerfulSquareFactor coords a) p =
      powerfulSquareExp (valuation coords a p) := by
```

### valuation_powerfulCubeFactor

源码起始行：129。

```lean
@[simp] theorem valuation_powerfulCubeFactor (a : A) (p : ι) :
    valuation coords (powerfulCubeFactor coords a) p =
      powerfulCubeDigit (valuation coords a p) := by
```

### powerfulCubeFactor_squarefree

源码起始行：134。

```lean
theorem powerfulCubeFactor_squarefree (a : A) (p : ι) :
    valuation coords (powerfulCubeFactor coords a) p ≤ 1 := by
```

### powerful_factorization

源码起始行：139。

```lean
theorem powerful_factorization (a : A)
    (ha : ∀ p, valuation coords a p = 0 ∨ 2 ≤ valuation coords a p) :
    a = powerfulSquareFactor coords a ^ 2 * powerfulCubeFactor coords a ^ 3 := by
```

### powerful_factorization_unique

源码起始行：148。

```lean
theorem powerful_factorization_unique (a u v : A)
    (hv : ∀ p, valuation coords v p ≤ 1) (ha : a = u ^ 2 * v ^ 3) :
    u = powerfulSquareFactor coords a ∧ v = powerfulCubeFactor coords a := by
```

### residualRowFactor_injOn

源码起始行：175。

```lean
theorem residualRowFactor_injOn (s : Finset ι) (pow sup : A) (rows : Finset A) :
    Set.InjOn (residualRowFactor coords s) (rowBlock coords s pow sup rows : Set A) := by
```

### sum_rowBlock_reindex

源码起始行：189。

```lean
theorem sum_rowBlock_reindex {R : Type*} [AddCommMonoid R]
    (s : Finset ι) (pow sup : A) (rows : Finset A) (F : A → R) :
    (∑ k ∈ rowBlock coords s pow sup rows, F (residualRowFactor coords s k)) =
      ∑ d ∈ residualRows coords s pow sup rows, F d := by
```

### residualRows_avoids

源码起始行：196。

```lean
theorem residualRows_avoids (s : Finset ι) (pow sup : A) (rows : Finset A)
    (d : A) (hd : d ∈ residualRows coords s pow sup rows) : Avoids coords s d := by
```

### residualRows_squarefree

源码起始行：201。

```lean
theorem residualRows_squarefree (s : Finset ι) (pow sup : A) (rows : Finset A)
    (d : A) (hd : d ∈ residualRows coords s pow sup rows) :
    ∀ p, valuation coords d p ≤ 1 := by
```

### residualRows_norm_le

源码起始行：207。

```lean
theorem residualRows_norm_le (s : Finset ι) (pow sup : A) (rows : Finset A)
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a) (K : ℝ)
    (hrows : ∀ k ∈ rows, normI k ≤ K)
    (d : A) (hd : d ∈ residualRows coords s pow sup rows) :
    normI d ≤ K / (normI pow * normI sup) := by
```

## HeckeSkeleton/LowFrozenCube/RowTableExit.lean

源码 SHA-256：`72b78297c68685119c0772987e8cba187a67b836db624b2eae53fb5bf7d6e13c`。

### residualParameter_one_le

源码起始行：35。

```lean
theorem residualParameter_one_le (normI : A → ℝ) (K : ℝ) (pow sup : A) :
    1 ≤ D.residualParameter normI K pow sup :=
```

### residualRows_admissible

源码起始行：38。

```lean
theorem residualRows_admissible (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (K : ℝ) (pow sup : A) (rows : Finset A)
    (hrows : ∀ k ∈ rows, normI k ≤ K)
    (d : A) (hd : d ∈ PrimeCoordinates.residualRows D.coords D.support pow sup rows) :
    (∀ p, PrimeCoordinates.valuation D.coords d p ≤ 1) ∧
    PrimeCoordinates.Avoids D.coords D.support d ∧
    normI d ≤ D.residualParameter normI K pow sup := by
```

### blockSourceEnergy_reindex

源码起始行：50。

```lean
theorem blockSourceEnergy_reindex (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
    (Ω : A → A → A → ℂ) (pow sup : A) (rows marks columns : Finset A)
    (pairs : Finset (A × A)) :
    D.blockSourceEnergy normI a₀ ρ₀ lam Ω pow sup rows marks columns pairs =
      ∑ d ∈ PrimeCoordinates.residualRows D.coords D.support pow sup rows,
        ‖D.sourceRow normI a₀ ρ₀ lam Ω marks columns pairs d‖ ^ 2 :=
```

### local_table_row_block_exit

源码起始行：62。

```lean
theorem local_table_row_block_exit
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
    (phase : A → A → A → ℂ)
    (hminimum : PrimeCoordinates.Supported D.coords D.ordinary D.minimum)
    (a₀ ρ₀ lam : A → ℂ) (K B : ℝ) (hB : 0 < B)
    (pow sup : A) (rows marks columns : Finset A) (pairs : Finset (A × A))
    (hrows : ∀ k ∈ rows, normI k ≤ K)
    (hρ₀ : ∀ d, (∀ p, PrimeCoordinates.valuation D.coords d p ≤ 1) →
      PrimeCoordinates.Avoids D.coords D.support d → ‖ρ₀ d‖ = 1)
    (hmarks : ∀ P ∈ marks, PrimeCoordinates.Avoids D.coords D.support P)
    (ha₀ : ∀ P ∈ marks, ‖a₀ P‖ ≤ 1)
    (hcolumns : ∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hlam : ∀ c ∈ columns, ‖lam c‖ ≤ 1)
    (hpairs : ∀ q ∈ pairs, D.CanonicalCube q.1 ∧
      PrimeCoordinates.Avoids D.coords D.ordinary q.2)
    (hphase : ∀ c ∈ columns, ∀ q ∈ pairs, ‖phase c q.1 q.2‖ ≤ 1)
    (hlower : ∀ q ∈ pairs, B ≤ normI (cubeProduct q)) :
    let residual :=
```

## HeckeSkeleton/LowFrozenCube/Scale.lean

源码 SHA-256：`b52d0d911c7ad9cf1cf658ab0bbfa69b3a110173be5bf4a4baf6eb88cbf6bd93`。

### quadraticScale_le

源码起始行：24。

```lean
theorem quadraticScale_le (Z H v ell : ℝ) (hZ : 1 ≤ Z) :
    quadraticScale Z H v ell ≤ 2 * Z ^ (max H (v + ell)) := by
```

### cubicScale_nonneg

源码起始行：33。

```lean
theorem cubicScale_nonneg (Z v z : ℝ) (hZ : 0 ≤ Z) :
    0 ≤ cubicScale Z v z := by
```

### cubicScale_le

源码起始行：41。

```lean
theorem cubicScale_le (Z v z : ℝ) (hZ : 1 ≤ Z) :
    cubicScale Z v z ≤ 3 * Z ^ (max v (max z (2 * (v + z) / 3))) := by
```

### hybridScale_le

源码起始行：61。

```lean
theorem hybridScale_le (Z H v ell z : ℝ) (hZ : 1 ≤ Z) :
    hybridScale Z H v ell z ≤ 6 * Z ^ (hybridGrowthExponent H v ell z) := by
```

### frozen_scale_le

源码起始行：83。

```lean
theorem frozen_scale_le (Z O H v ell S B z T : ℝ) (hZ : 1 ≤ Z) :
    Z ^ (O / 2) * Z ^ (squaredCoefficientExponent v ell S B) *
        hybridScale Z H v ell z * Z ^ (squaredKernelExponent T v ell) ≤
      6 * Z ^ (reflectedExponent O H v ell S B z T) := by
```

## HeckeSkeleton/LowFrozenCube/SourceLedger.lean

源码 SHA-256：`8f24c5755c7e4a3035374b644223625517aa72b6d73111b3509fa26f957c46a8`。

### energy_nonneg

源码起始行：44。

```lean
theorem energy_nonneg (b : SourceBlock ι A) (D : Data ι A) (normI : A → ℝ) :
    0 ≤ b.energy D normI :=
```

### energy_zero_of_empty_active

源码起始行：48。

```lean
theorem energy_zero_of_empty_active (b : SourceBlock ι A) (D : Data ι A)
    (normI : A → ℝ)
    (hsupport : ∀ q ∈ b.inputs, PrimeCoordinates.Supported D.coords D.ordinary q.1)
    (hempty : D.activeInputBlock normI b.first b.prefactor b.atZero b.inputs = ∅) :
    b.energy D normI = 0 := by
```

### four_scale_power

源码起始行：99。

```lean
theorem four_scale_power (Z H v ell z eps : ℝ) (hZ : 0 < Z) :
    (Z ^ H * Z ^ v * Z ^ ell * Z ^ z) ^ eps = Z ^ (eps * (H + v + ell + z)) := by
```

### dyadic_coefficient_scale

源码起始行：106。

```lean
theorem dyadic_coefficient_scale (C N B : ℝ) (hN : 0 < N) (hB : 0 < B) :
    (C / (B / 2)) ^ 2 / (N / 2) = 8 * ((C / B) ^ 2 / N) := by
```

### source_energy_ledger

源码起始行：119。

```lean
theorem source_energy_ledger
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount)
    (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting q Ccount)
    (hq : HeckeSkeleton.LowHybrid.QuadraticSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (hc : HeckeSkeleton.LowHybrid.CubicSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z O H v ell S B z T : ℝ,
      1 ≤ Z → 0 ≤ H → 0 ≤ v → 0 ≤ ell → 0 ≤ z →
      ∀ b : SourceBlock ι A, AnnularSupport D normI Z H v ell z b →
        PrimitiveLocalBounds D normI b → Z ^ (S + B) ≤ normI D.chargeIdeal →
        Z ^ (O / 2) * b.energy D normI * Z ^ (squaredKernelExponent T v ell) ≤
          C * Z ^ (reflectedExponent O H v ell S B z T + eps * (H + v + ell + z)) := by
```

## HeckeSkeleton/LowFrozenCube/TableExit.lean

源码 SHA-256：`b2929327b6d8006b149e99d632785aea34e9f2422fce7ec6092fde8c07e93a37`。

### prime_eq_primeElement

源码起始行：25。

```lean
theorem prime_eq_primeElement (p : ι) :
    D.prime p = PrimeCoordinates.primeElement D.coords p :=
```

### canonical_residual

源码起始行：28。

```lean
theorem canonical_residual (x : A) (hx : D.CanonicalCube x) :
    frozenCube (D.exponents x) = fun p => PrimeCoordinates.valuation D.coords x p := by
```

### canonical_supported_on

源码起始行：35。

```lean
theorem canonical_supported_on (s : Finset ι)
    (hminimum : PrimeCoordinates.Supported D.coords s D.minimum)
    (x : A) (hx : D.CanonicalCube x) : PrimeCoordinates.Supported D.coords s x := by
```

### tableMajorant_nonneg

源码起始行：51。

```lean
theorem tableMajorant_nonneg (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) : 0 ≤ D.tableMajorant normI first prefactor atZero :=
```

### table_minimumMajorant_eq

源码起始行：62。

```lean
theorem table_minimumMajorant_eq (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (x : A) (hx : D.CanonicalCube x) :
    LocalTable.minimumMajorant D.ordinary (fun p => normI (D.prime p))
      first prefactor atZero D.digit (D.exponents x) =
      D.tableMajorant normI first prefactor atZero := by
```

### table_cubeNorm_eq

源码起始行：77。

```lean
theorem table_cubeNorm_eq (normI : A →* ℝ)
    (hminimum : PrimeCoordinates.Supported D.coords D.ordinary D.minimum)
    (x : A) (hx : D.CanonicalCube x) :
    LocalTable.cubeNorm D.ordinary (fun p => normI (D.prime p))
      (D.exponents x) = normI x := by
```

### tableOmega_norm_le

源码起始行：98。

```lean
theorem tableOmega_norm_le (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
    (phase : A → A → A → ℂ)
    (hminimum : PrimeCoordinates.Supported D.coords D.ordinary D.minimum)
    (c x n : A) (hx : D.CanonicalCube x) (hphase : ‖phase c x n‖ ≤ 1) :
    ‖D.tableOmega normI first prefactor atZero phase c x n‖ ≤
      D.tableMajorant normI first prefactor atZero / normI x := by
```

### local_table_frozen_exit

源码起始行：117。

```lean
theorem local_table_frozen_exit
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
    (phase : A → A → A → ℂ)
    (hminimum : PrimeCoordinates.Supported D.coords D.ordinary D.minimum)
    (a₀ ρ₀ lam : A → ℂ) (B : ℝ) (hB : 0 < B)
    (rows marks columns : Finset A) (pairs : Finset (A × A))
    (hrows : ∀ d ∈ rows, PrimeCoordinates.Avoids D.coords D.support d)
    (hρ₀ : ∀ d ∈ rows, ‖ρ₀ d‖ = 1)
    (hmarks : ∀ P ∈ marks, PrimeCoordinates.Avoids D.coords D.support P)
    (ha₀ : ∀ P ∈ marks, ‖a₀ P‖ ≤ 1)
    (hcolumns : ∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hlam : ∀ c ∈ columns, ‖lam c‖ ≤ 1)
    (hpairs : ∀ q ∈ pairs, D.CanonicalCube q.1 ∧
      PrimeCoordinates.Avoids D.coords D.ordinary q.2)
    (hphase : ∀ c ∈ columns, ∀ q ∈ pairs, ‖phase c q.1 q.2‖ ≤ 1)
    (hlower : ∀ q ∈ pairs, B ≤ normI (cubeProduct q)) :
    let Ω :=
```

## HeckeSkeleton/LowFrozenCube/TerminalSource.lean

源码 SHA-256：`8c60a24f7753a7562b965c38ff9d3c7b572459856b7cd901f81d5bacc1141fdb`。

### source_energy_terminal

源码起始行：24。

```lean
theorem source_energy_terminal
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount)
    (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting q Ccount)
    (hq : HeckeSkeleton.LowHybrid.QuadraticSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (hc : HeckeSkeleton.LowHybrid.CubicSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z F M N Nstar V bh delta O H v ell S B z T Q z0 c tau : ℝ,
      1 ≤ Z → 0 ≤ H → 0 ≤ O → 0 ≤ S → 0 ≤ B → 0 ≤ ell → 0 ≤ v → 0 ≤ z → 0 ≤ Q →
      F = N + V → Nstar = N - 3 * bh →
      V ≤ delta → bh ≤ delta → z ≤ z0 → H ≤ M - O →
      c ≤ F - M - Q - z0 → c ≤ 4 * F - 3 * M - 6 * z0 →
      T - S - B ≤ 2 * M - O + Q + V - Nstar + 2 * z → v + 3 * ell ≤ T + tau →
      ∀ b : SourceBlock ι A, AnnularSupport D normI Z H v ell z b →
        PrimitiveLocalBounds D normI b → Z ^ (S + B) ≤ normI D.chargeIdeal →
        Z ^ (O / 2) * b.energy D normI * Z ^ (squaredKernelExponent T v ell) ≤
          C * Z ^ (terminalBound F M c delta tau + eps * (H + v + ell + z)) := by
```

### source_energy_power_saving

源码起始行：59。

```lean
theorem source_energy_power_saving
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount)
    (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting q Ccount)
    (hq : HeckeSkeleton.LowHybrid.QuadraticSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (hcubic : HeckeSkeleton.LowHybrid.CubicSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z F M N Nstar V bh delta O H v ell S B z T Q z0 c tau : ℝ,
      1 ≤ Z → 0 ≤ H → 0 ≤ O → 0 ≤ S → 0 ≤ B → 0 ≤ ell → 0 ≤ v → 0 ≤ z → 0 ≤ Q →
      0 ≤ M → 0 ≤ c → F = N + V → Nstar = N - 3 * bh →
      V ≤ delta → bh ≤ delta → z ≤ z0 → H ≤ M - O →
      c ≤ F - M - Q - z0 → c ≤ 4 * F - 3 * M - 6 * z0 →
      T - S - B ≤ 2 * M - O + Q + V - Nstar + 2 * z → v + 3 * ell ≤ T + tau →
      delta ≤ c / 100 → tau ≤ c / 8 → eps * (H + v + ell + z) ≤ c / 4 →
      ∀ b : SourceBlock ι A, AnnularSupport D normI Z H v ell z b →
        PrimitiveLocalBounds D normI b → Z ^ (S + B) ≤ normI D.chargeIdeal →
        Z ^ (O / 2) * b.energy D normI * Z ^ (squaredKernelExponent T v ell) ≤
          C * Z ^ (F - c / 4) := by
```

## HeckeSkeleton/LowFrozenCube/UniformAggregateSource.lean

源码 SHA-256：`68b49207ff4b3545c941a3041e23053a5195241af11c3e8e0da6e7f762232b63`。

### varyingFamilySourceEnergy_eq_blocks

源码起始行：53。

```lean
theorem varyingFamilySourceEnergy_eq_blocks
    (coords : A ≃* Multiplicative (ι →₀ ℕ)) (base : Finset ι) (normI : A → ℝ)
    (data : A × A → Data ι A) (family : A × A → SourceBlock ι A) (rows : Finset A)
    (hf : FrozenFamilyAlignment coords base rows data family) :
    varyingFamilySourceEnergy coords base normI data family rows =
      ∑ pair ∈ frozenRowPairs coords base rows, (family pair).energy (data pair) normI := by
```

### uniform_aggregate_source_energy_ledger

源码起始行：77。

```lean
theorem uniform_aggregate_source_energy_ledger
    (coords : A ≃* Multiplicative (ι →₀ ℕ)) (symbol : A → A →* ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then (1 : ℂ) else 0)
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount) (hcount : LinearNormCounting q Ccount)
    (hq : QuadraticSieveInput normI (PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (hc : CubicSieveInput normI (PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (eps eta : ℝ) (heps : 0 < eps) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z O H v ell S B z T Rrad : ℝ,
      1 ≤ Z → 0 ≤ O → 0 ≤ H → 0 ≤ v → 0 ≤ ell → 0 ≤ z →
      ∀ (base : Finset ι) (rows : Finset A),
        (∀ k ∈ rows, normI (powerfulRowFactor coords k) ≤ Z ^ O) →
        normI (PrimeArithmetic.fromSupport coords base) ≤ Z ^ Rrad →
      ∀ (data : A × A → Data ι A) (family : A × A → SourceBlock ι A),
        (∀ pair ∈ frozenRowPairs coords base rows, (data pair).coords = coords) →
        (∀ pair ∈ frozenRowPairs coords base rows, (data pair).symbol = symbol) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          AnnularSupport (data pair) normI Z H v ell z (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          PrimitiveLocalBounds (data pair) normI (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          Z ^ (S + B) ≤ normI (data pair).chargeIdeal) →
        (∑ pair ∈ frozenRowPairs coords base rows, (family pair).energy (data pair) normI) *
          Z ^ (squaredKernelExponent T v ell) ≤
          C * Z ^ (reflectedExponent O H v ell S B z T +
            eps * (H + v + ell + z) + eta * (O + Rrad)) := by
```

### uniform_family_source_energy_ledger

源码起始行：169。

```lean
theorem uniform_family_source_energy_ledger
    (coords : A ≃* Multiplicative (ι →₀ ℕ)) (symbol : A → A →* ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then (1 : ℂ) else 0)
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount) (hcount : LinearNormCounting q Ccount)
    (hq : QuadraticSieveInput normI (PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (hc : CubicSieveInput normI (PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (eps eta : ℝ) (heps : 0 < eps) (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z O H v ell S B z T Rrad : ℝ,
      1 ≤ Z → 0 ≤ O → 0 ≤ H → 0 ≤ v → 0 ≤ ell → 0 ≤ z →
      ∀ (base : Finset ι) (rows : Finset A),
        (∀ k ∈ rows, normI (powerfulRowFactor coords k) ≤ Z ^ O) →
        normI (PrimeArithmetic.fromSupport coords base) ≤ Z ^ Rrad →
      ∀ (data : A × A → Data ι A) (family : A × A → SourceBlock ι A),
        FrozenFamilyAlignment coords base rows data family →
        (∀ pair ∈ frozenRowPairs coords base rows, (data pair).symbol = symbol) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          AnnularSupport (data pair) normI Z H v ell z (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          PrimitiveLocalBounds (data pair) normI (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          Z ^ (S + B) ≤ normI (data pair).chargeIdeal) →
        varyingFamilySourceEnergy coords base normI data family rows *
          Z ^ (squaredKernelExponent T v ell) ≤
          C * Z ^ (reflectedExponent O H v ell S B z T +
            eps * (H + v + ell + z) + eta * (O + Rrad)) := by
```

## HeckeSkeleton/LowFrozenCube/UniformAggregateTerminal.lean

源码 SHA-256：`42853345cdca0d180c6a22611d5d4e97ef76874947cd77afbcfab2a5261a6c77`。

### uniform_family_source_energy_subpower

源码起始行：29。

```lean
theorem uniform_family_source_energy_subpower
    (coords : A ≃* Multiplicative (ι →₀ ℕ)) (symbol : A → A →* ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then (1 : ℂ) else 0)
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ))
    (Ccount : ℝ) (hcount : LinearNormCounting q Ccount)
    (hq : QuadraticSieveInput normI (PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (hc : CubicSieveInput normI (PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (W eps : ℝ) (hW : 0 < W) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z O H v ell S B z T Rrad : ℝ,
      1 ≤ Z → 0 ≤ O → 0 ≤ H → 0 ≤ v → 0 ≤ ell → 0 ≤ z →
      (H + v + ell + z) + (O + Rrad) ≤ W →
      ∀ (base : Finset ι) (rows : Finset A),
        (∀ k ∈ rows, normI (powerfulRowFactor coords k) ≤ Z ^ O) →
        normI (PrimeArithmetic.fromSupport coords base) ≤ Z ^ Rrad →
      ∀ (data : A × A → Data ι A) (family : A × A → SourceBlock ι A),
        FrozenFamilyAlignment coords base rows data family →
        (∀ pair ∈ frozenRowPairs coords base rows, (data pair).symbol = symbol) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          AnnularSupport (data pair) normI Z H v ell z (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          PrimitiveLocalBounds (data pair) normI (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          Z ^ (S + B) ≤ normI (data pair).chargeIdeal) →
        varyingFamilySourceEnergy coords base normI data family rows *
          Z ^ (squaredKernelExponent T v ell) ≤
          C * Z ^ (reflectedExponent O H v ell S B z T + eps) := by
```

### uniform_family_source_energy_terminal

源码起始行：83。

```lean
theorem uniform_family_source_energy_terminal
    (coords : A ≃* Multiplicative (ι →₀ ℕ)) (symbol : A → A →* ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then (1 : ℂ) else 0)
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ))
    (Ccount : ℝ) (hcount : LinearNormCounting q Ccount)
    (hq : QuadraticSieveInput normI (PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (hc : CubicSieveInput normI (PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (W eps : ℝ) (hW : 0 < W) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z F M N Nstar V bh delta O H v ell S B z T Q z0 c tau Rrad : ℝ,
      1 ≤ Z → 0 ≤ H → 0 ≤ O → 0 ≤ S → 0 ≤ B → 0 ≤ ell → 0 ≤ v → 0 ≤ z → 0 ≤ Q →
      F = N + V → Nstar = N - 3 * bh →
      V ≤ delta → bh ≤ delta → z ≤ z0 → H ≤ M - O →
      c ≤ F - M - Q - z0 → c ≤ 4 * F - 3 * M - 6 * z0 →
      T - S - B ≤ 2 * M - O + Q + V - Nstar + 2 * z → v + 3 * ell ≤ T + tau →
      (H + v + ell + z) + (O + Rrad) ≤ W →
      ∀ (base : Finset ι) (rows : Finset A),
        (∀ k ∈ rows, normI (powerfulRowFactor coords k) ≤ Z ^ O) →
        normI (PrimeArithmetic.fromSupport coords base) ≤ Z ^ Rrad →
      ∀ (data : A × A → Data ι A) (family : A × A → SourceBlock ι A),
        FrozenFamilyAlignment coords base rows data family →
        (∀ pair ∈ frozenRowPairs coords base rows, (data pair).symbol = symbol) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          AnnularSupport (data pair) normI Z H v ell z (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          PrimitiveLocalBounds (data pair) normI (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          Z ^ (S + B) ≤ normI (data pair).chargeIdeal) →
        varyingFamilySourceEnergy coords base normI data family rows *
          Z ^ (squaredKernelExponent T v ell) ≤
          C * Z ^ (terminalBound F M c delta tau + eps) := by
```

### uniform_family_source_energy_power_saving

源码起始行：132。

```lean
theorem uniform_family_source_energy_power_saving
    (coords : A ≃* Multiplicative (ι →₀ ℕ)) (symbol : A → A →* ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then (1 : ℂ) else 0)
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ))
    (Ccount : ℝ) (hcount : LinearNormCounting q Ccount)
    (hq : QuadraticSieveInput normI (PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (hcubic : CubicSieveInput normI (PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (W eps : ℝ) (hW : 0 < W) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z F M N Nstar V bh delta O H v ell S B z T Q z0 c tau Rrad : ℝ,
      1 ≤ Z → 0 ≤ H → 0 ≤ O → 0 ≤ S → 0 ≤ B → 0 ≤ ell → 0 ≤ v → 0 ≤ z → 0 ≤ Q →
      0 ≤ M → 0 ≤ c → F = N + V → Nstar = N - 3 * bh →
      V ≤ delta → bh ≤ delta → z ≤ z0 → H ≤ M - O →
      c ≤ F - M - Q - z0 → c ≤ 4 * F - 3 * M - 6 * z0 →
      T - S - B ≤ 2 * M - O + Q + V - Nstar + 2 * z → v + 3 * ell ≤ T + tau →
      delta ≤ c / 100 → tau ≤ c / 8 → eps ≤ c / 4 →
      (H + v + ell + z) + (O + Rrad) ≤ W →
      ∀ (base : Finset ι) (rows : Finset A),
        (∀ k ∈ rows, normI (powerfulRowFactor coords k) ≤ Z ^ O) →
        normI (PrimeArithmetic.fromSupport coords base) ≤ Z ^ Rrad →
      ∀ (data : A × A → Data ι A) (family : A × A → SourceBlock ι A),
        FrozenFamilyAlignment coords base rows data family →
        (∀ pair ∈ frozenRowPairs coords base rows, (data pair).symbol = symbol) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          AnnularSupport (data pair) normI Z H v ell z (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          PrimitiveLocalBounds (data pair) normI (family pair)) →
        (∀ pair ∈ frozenRowPairs coords base rows,
          Z ^ (S + B) ≤ normI (data pair).chargeIdeal) →
        varyingFamilySourceEnergy coords base normI data family rows *
          Z ^ (squaredKernelExponent T v ell) ≤ C * Z ^ (F - c / 4) := by
```

## HeckeSkeleton/LowFrozenCube/UniformSourceLedger.lean

源码 SHA-256：`36ce6ae171d575a750fea3793351e0c12f3090d6ce0c88980db2ca2976173899`。

### source_ledger_bound_from_weighted

源码起始行：37。

```lean
theorem source_ledger_bound_from_weighted (normI : A →* ℝ)
    (hpos : ∀ a, 0 < normI a) (eps C0 : ℝ) (hC0 : 0 < C0)
    (hbound : WeightedRawHybridBound D normI eps C0) :
    SourceLedgerBound D normI eps (48 * C0) := by
```

### uniform_source_energy_ledger

源码起始行：123。

```lean
theorem uniform_source_energy_ledger
    (coords : A ≃* Multiplicative (ι →₀ ℕ)) (symbol : A → A →* ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (h6 : ∀ a b, symbol a b ^ 6 =
      if PrimeCoordinates.Coprime coords a b then (1 : ℂ) else 0)
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount)
    (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting q Ccount)
    (hq : HeckeSkeleton.LowHybrid.QuadraticSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (hc : HeckeSkeleton.LowHybrid.CubicSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : Data ι A,
      D.coords = coords → D.symbol = symbol → SourceLedgerBound D normI eps C := by
```

## HeckeSkeleton/LowFrozenCube/UniformTerminalSource.lean

源码 SHA-256：`4f1e9ba5697e8ff5734aafac5b2f405a0d82b482e1ac284d73be2aadd2495164`。

### uniform_source_energy_terminal

源码起始行：20。

```lean
theorem uniform_source_energy_terminal
    (coords : A ≃* Multiplicative (ι →₀ ℕ)) (symbol : A → A →* ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (h6 : ∀ a b, symbol a b ^ 6 =
      if PrimeCoordinates.Coprime coords a b then (1 : ℂ) else 0)
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount)
    (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting q Ccount)
    (hq : HeckeSkeleton.LowHybrid.QuadraticSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (hc : HeckeSkeleton.LowHybrid.CubicSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : Data ι A,
      D.coords = coords → D.symbol = symbol →
      ∀ Z F M N Nstar V bh delta O H v ell S B z T Q z0 c tau : ℝ,
      1 ≤ Z → 0 ≤ H → 0 ≤ O → 0 ≤ S → 0 ≤ B → 0 ≤ ell → 0 ≤ v → 0 ≤ z → 0 ≤ Q →
      F = N + V → Nstar = N - 3 * bh →
      V ≤ delta → bh ≤ delta → z ≤ z0 → H ≤ M - O →
      c ≤ F - M - Q - z0 → c ≤ 4 * F - 3 * M - 6 * z0 →
      T - S - B ≤ 2 * M - O + Q + V - Nstar + 2 * z → v + 3 * ell ≤ T + tau →
      ∀ b : SourceBlock ι A, AnnularSupport D normI Z H v ell z b →
        PrimitiveLocalBounds D normI b → Z ^ (S + B) ≤ normI D.chargeIdeal →
        Z ^ (O / 2) * b.energy D normI * Z ^ (squaredKernelExponent T v ell) ≤
          C * Z ^ (terminalBound F M c delta tau + eps * (H + v + ell + z)) := by
```

### uniform_source_energy_power_saving

源码起始行：60。

```lean
theorem uniform_source_energy_power_saving
    (coords : A ≃* Multiplicative (ι →₀ ℕ)) (symbol : A → A →* ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (h6 : ∀ a b, symbol a b ^ 6 =
      if PrimeCoordinates.Coprime coords a b then (1 : ℂ) else 0)
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount)
    (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting q Ccount)
    (hq : HeckeSkeleton.LowHybrid.QuadraticSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (hcubic : HeckeSkeleton.LowHybrid.CubicSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : Data ι A,
      D.coords = coords → D.symbol = symbol →
      ∀ Z F M N Nstar V bh delta O H v ell S B z T Q z0 c tau : ℝ,
      1 ≤ Z → 0 ≤ H → 0 ≤ O → 0 ≤ S → 0 ≤ B → 0 ≤ ell → 0 ≤ v → 0 ≤ z → 0 ≤ Q →
      0 ≤ M → 0 ≤ c → F = N + V → Nstar = N - 3 * bh →
      V ≤ delta → bh ≤ delta → z ≤ z0 → H ≤ M - O →
      c ≤ F - M - Q - z0 → c ≤ 4 * F - 3 * M - 6 * z0 →
      T - S - B ≤ 2 * M - O + Q + V - Nstar + 2 * z → v + 3 * ell ≤ T + tau →
      delta ≤ c / 100 → tau ≤ c / 8 → eps * (H + v + ell + z) ≤ c / 4 →
      ∀ b : SourceBlock ι A, AnnularSupport D normI Z H v ell z b →
        PrimitiveLocalBounds D normI b → Z ^ (S + B) ≤ normI D.chargeIdeal →
        Z ^ (O / 2) * b.energy D normI * Z ^ (squaredKernelExponent T v ell) ≤
          C * Z ^ (F - c / 4) := by
```

## HeckeSkeleton/LowFrozenCube/UniformWeightedHybridBound.lean

源码 SHA-256：`f88e701fd1de5ed6217136cd780f48efd490fb7e17f38a3a91d0d0a627a6c1ab`。

### uniform_weighted_raw_hybrid_bound

源码起始行：60。

```lean
theorem uniform_weighted_raw_hybrid_bound
    (coords : A ≃* Multiplicative (ι →₀ ℕ))
    (symbol : A → A →* ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (h6 : ∀ a b, symbol a b ^ 6 =
      if PrimeCoordinates.Coprime coords a b then (1 : ℂ) else 0)
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount)
    (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting q Ccount)
    (hq : HeckeSkeleton.LowHybrid.QuadraticSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (hc : HeckeSkeleton.LowHybrid.CubicSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ D : Data ι A,
      D.coords = coords → D.symbol = symbol → WeightedRawHybridBound D normI eps C0 := by
```

## HeckeSkeleton/LowFrozenCube/Valuations.lean

源码 SHA-256：`946c98e6ec8ae6a00759707d357199c1360dd7976209f4aef95e792de18eccbc`。

### frozenMin_zero

源码起始行：32。

```lean
@[simp] theorem frozenMin_zero : frozenMin 0 = 0 := by
```

### frozenCubeExp_zero

源码起始行：35。

```lean
@[simp] theorem frozenCubeExp_zero : frozenCubeExp 0 = 0 := by
```

### frozenMin_cases

源码起始行：38。

```lean
theorem frozenMin_cases (e : ℕ) :
    frozenMin e = 0 ∨ frozenMin e = 1 ∨ frozenMin e = 3 := by
```

### frozenMin_eq_zero_iff

源码起始行：43。

```lean
@[simp] theorem frozenMin_eq_zero_iff (e : ℕ) :
    frozenMin e = 0 ↔ e = 0 := by
```

### frozenMin_le

源码起始行：48。

```lean
theorem frozenMin_le (e : ℕ) (he : AdmissibleExponent e) :
    frozenMin e ≤ e := by
```

### frozenExponent_decomposition

源码起始行：55。

```lean
theorem frozenExponent_decomposition (e : ℕ) (he : AdmissibleExponent e) :
    e = frozenMin e + 3 * frozenCubeExp e := by
```

### frozenCubeExp_eq_zero_of_base_zero

源码起始行：62。

```lean
theorem frozenCubeExp_eq_zero_of_base_zero {e : ℕ} (he : frozenMin e = 0) :
    frozenCubeExp e = 0 := by
```

### frozenPair_canonical

源码起始行：71。

```lean
theorem frozenPair_canonical (e : ℕ) :
    CanonicalFrozenPair (frozenMin e) (frozenCubeExp e) := by
```

### frozenExponent_unique

源码起始行：79。

```lean
theorem frozenExponent_unique {e m x : ℕ}
    (hc : CanonicalFrozenPair m x) (he : e = m + 3 * x) :
    m = frozenMin e ∧ x = frozenCubeExp e := by
```

### canonicalPair_admissible

源码起始行：86。

```lean
theorem canonicalPair_admissible {e m x : ℕ}
    (hc : CanonicalFrozenPair m x) (he : e = m + 3 * x) :
    AdmissibleExponent e := by
```

### frozenValuation_decomposition

源码起始行：113。

```lean
theorem frozenValuation_decomposition (v : ι → ℕ)
    (hv : ∀ p, AdmissibleExponent (v p)) :
    v = fun p => frozenBase v p + 3 * frozenCube v p := by
```

### frozenValuation_unique

源码起始行：119。

```lean
theorem frozenValuation_unique {v a x : ι → ℕ}
    (hc : ∀ p, CanonicalFrozenPair (a p) (x p))
    (he : ∀ p, v p = a p + 3 * x p) :
    a = frozenBase v ∧ x = frozenCube v := by
```

### frozenBase_supported

源码起始行：129。

```lean
theorem frozenBase_supported {s : Finset ι} {v : ι → ℕ}
    (hv : SupportedOn s v) : SupportedOn s (frozenBase v) := by
```

### frozenCube_supported

源码起始行：134。

```lean
theorem frozenCube_supported {s : Finset ι} {v : ι → ℕ}
    (hv : SupportedOn s v) : SupportedOn s (frozenCube v) := by
```

### frozenBase_support_exact

源码起始行：139。

```lean
theorem frozenBase_support_exact (v : ι → ℕ) (p : ι) :
    frozenBase v p ≠ 0 ↔ v p ≠ 0 := by
```

### supportedPart_supported

源码起始行：155。

```lean
theorem supportedPart_supported (s : Finset ι) (v : ι → ℕ) :
    SupportedOn s (supportedPart s v) := by
```

### awayPart_avoids

源码起始行：160。

```lean
theorem awayPart_avoids (s : Finset ι) (v : ι → ℕ) :
    AvoidsSupport s (awayPart s v) := by
```

### fullCube_decomposition

源码起始行：165。

```lean
theorem fullCube_decomposition (s : Finset ι) (v : ι → ℕ) :
    v = fun p => supportedPart s v p + awayPart s v p := by
```

### fullCube_unique

源码起始行：172。

```lean
theorem fullCube_unique {s : Finset ι} {v x n : ι → ℕ}
    (hx : SupportedOn s x) (hn : AvoidsSupport s n)
    (hv : ∀ p, v p = x p + n p) :
    x = supportedPart s v ∧ n = awayPart s v := by
```

### disjoint_supported_of_avoids

源码起始行：186。

```lean
theorem disjoint_supported_of_avoids {s : Finset ι} {P x : ι → ℕ}
    (hP : AvoidsSupport s P) (hx : SupportedOn s x) :
    DisjointValuations P x := by
```

### disjoint_add_right

源码起始行：194。

```lean
theorem disjoint_add_right {P x n : ι → ℕ} :
    DisjointValuations P (fun p => x p + n p) ↔
      DisjointValuations P x ∧ DisjointValuations P n := by
```

### fullCube_collision_mask

源码起始行：223。

```lean
theorem fullCube_collision_mask {s : Finset ι} {P x n : ι → ℕ}
    (hP : AvoidsSupport s P) (hx : SupportedOn s x) :
    DisjointValuations P (fun p => x p + n p) ↔ DisjointValuations P n := by
```

### overlap_not_disjoint

源码起始行：229。

```lean
theorem overlap_not_disjoint {u v : ι → ℕ}
    (h : ∃ p, u p ≠ 0 ∧ v p ≠ 0) : ¬ DisjointValuations u v := by
```

### overlap_mask_zero

源码起始行：236。

```lean
theorem overlap_mask_zero {u v : ι → ℕ} (z : ℂ)
    (h : ∃ p, u p ≠ 0 ∧ v p ≠ 0) :
    (if DisjointValuations u v then z else 0) = 0 := by
```

### wholeIndexMark_row_overlap_zero

源码起始行：251。

```lean
theorem wholeIndexMark_row_overlap_zero {σ : Type*}
    (slots : Finset σ) (prime : σ → ι) (row : ι → ℕ)
    (χ : (ι → ℕ) → ℂ)
    (hχ : ∀ v p, row p ≠ 0 → v p ≠ 0 → χ v = 0)
    (i : σ) (hi : i ∈ slots) (hrow : row (prime i) ≠ 0)
    (v : ι → ℕ) : χ v * wholeIndexMark slots prime v = 0 := by
```

### sum_wholeIndexMark_row_overlap_zero

源码起始行：267。

```lean
theorem sum_wholeIndexMark_row_overlap_zero {σ α : Type*}
    (slots : Finset σ) (prime : σ → ι) (row : ι → ℕ)
    (χ : (ι → ℕ) → ℂ)
    (hχ : ∀ v p, row p ≠ 0 → v p ≠ 0 → χ v = 0)
    (i : σ) (hi : i ∈ slots) (hrow : row (prime i) ≠ 0)
    (t : Finset α) (index : α → ι → ℕ) (weight : α → ℂ) :
    (∑ a ∈ t, weight a * χ (index a) * wholeIndexMark slots prime (index a)) = 0 := by
```

### mergeCubePair_injective_on

源码起始行：284。

```lean
theorem mergeCubePair_injective_on (s : Finset ι)
    (t : Finset ((ι → ℕ) × (ι → ℕ)))
    (ht : ∀ q ∈ t, SupportedOn s q.1 ∧ AvoidsSupport s q.2) :
    Set.InjOn mergeCubePair (t : Set ((ι → ℕ) × (ι → ℕ))) := by
```

### sum_fullCube_reindex

源码起始行：300。

```lean
theorem sum_fullCube_reindex {R : Type*} [AddCommMonoid R]
    (s : Finset ι) (t : Finset ((ι → ℕ) × (ι → ℕ)))
    (ht : ∀ q ∈ t, SupportedOn s q.1 ∧ AvoidsSupport s q.2)
    (G : (ι → ℕ) → (ι → ℕ) → R) :
    (∑ q ∈ t, G q.1 q.2) =
      ∑ b ∈ t.image mergeCubePair, G (supportedPart s b) (awayPart s b) := by
```

### row_decomposition

源码起始行：328。

```lean
theorem row_decomposition (s : Finset ι) (v : ι → ℕ) :
    v = fun p => powerfulRowPart v p + supportedRowPart s v p +
      residualRowPart s v p := by
```

### supportedRowPart_squarefree

源码起始行：341。

```lean
theorem supportedRowPart_squarefree (s : Finset ι) (v : ι → ℕ) (p : ι) :
    supportedRowPart s v p ≤ 1 := by
```

### residualRowPart_squarefree

源码起始行：346。

```lean
theorem residualRowPart_squarefree (s : Finset ι) (v : ι → ℕ) (p : ι) :
    residualRowPart s v p ≤ 1 := by
```

### supportedRowPart_supported

源码起始行：351。

```lean
theorem supportedRowPart_supported (s : Finset ι) (v : ι → ℕ) :
    SupportedOn s (supportedRowPart s v) := by
```

### residualRowPart_avoids

源码起始行：356。

```lean
theorem residualRowPart_avoids (s : Finset ι) (v : ι → ℕ) :
    AvoidsSupport s (residualRowPart s v) := by
```

### row_parts_pairwise_disjoint

源码起始行：361。

```lean
theorem row_parts_pairwise_disjoint (s : Finset ι) (v : ι → ℕ) :
    DisjointValuations (powerfulRowPart v) (supportedRowPart s v) ∧
      DisjointValuations (powerfulRowPart v) (residualRowPart s v) ∧
      DisjointValuations (supportedRowPart s v) (residualRowPart s v) := by
```

### powerfulCubeDigit_squarefree

源码起始行：388。

```lean
theorem powerfulCubeDigit_squarefree (e : ℕ) : powerfulCubeDigit e ≤ 1 := by
```

### powerfulExponent_decomposition

源码起始行：392。

```lean
theorem powerfulExponent_decomposition (e : ℕ) (he : e = 0 ∨ 2 ≤ e) :
    e = 2 * powerfulSquareExp e + 3 * powerfulCubeDigit e := by
```

### powerfulExponent_unique

源码起始行：397。

```lean
theorem powerfulExponent_unique {e a b : ℕ} (hb : b ≤ 1)
    (he : e = 2 * a + 3 * b) :
    a = powerfulSquareExp e ∧ b = powerfulCubeDigit e := by
```

## HeckeSkeleton/LowFrozenCube/WeightedHybridBound.lean

源码 SHA-256：`9e0bfdf4a241a6c5777f74544d123d7851ab85ea74168a56ec4c5fb89a174c87`。

### weighted_raw_hybrid_bound

源码起始行：25。

```lean
theorem weighted_raw_hybrid_bound
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount)
    (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting q Ccount)
    (hq : HeckeSkeleton.LowHybrid.QuadraticSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (hc : HeckeSkeleton.LowHybrid.CubicSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ R K N B L Nmin Bmin : ℝ,
      1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L → 0 < Nmin → 0 < Bmin →
      ∀ (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
        (phase : A → A → A → ℂ) (a₀ ρ₀ lam : A → ℂ)
        (pow sup : A) (rows marks columns : Finset A) (inputs : Finset (A × A)),
        (∀ k ∈ rows, normI k ≤ R) →
        (∀ d ∈ PrimeCoordinates.residualRows D.coords D.support pow sup rows, normI d ≤ K) →
        (∀ d, (∀ p, PrimeCoordinates.valuation D.coords d p ≤ 1) →
          PrimeCoordinates.Avoids D.coords D.support d → ‖ρ₀ d‖ = 1) →
        (∀ P ∈ marks, PrimeCoordinates.Avoids D.coords D.support P) →
        (∀ P ∈ marks, HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords P ∧
          normI P ≤ L) →
        (∀ P ∈ marks, ‖a₀ P‖ ≤ 1) →
        (∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c) →
        (∀ c ∈ columns, HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords c ∧
          normI c ≤ N) →
        (∀ c ∈ columns, ‖lam c‖ ≤ 1) →
        (∀ c ∈ columns, Nmin ≤ normI c) →
        (∀ u ∈ inputs, PrimeCoordinates.Supported D.coords D.ordinary u.1) →
        (∀ u ∈ inputs, PrimeCoordinates.Avoids D.coords D.ordinary u.2) →
        (∀ c ∈ columns, ∀ u ∈ inputs, ‖phase c u.1 u.2‖ ≤ 1) →
        (∀ u ∈ inputs,
          Bmin ≤ normI (PrimeCoordinates.residualCubeFactor D.coords u.1 * u.2)) →
        (∀ u ∈ inputs,
          normI (PrimeCoordinates.residualCubeFactor D.coords u.1 * u.2) ≤ B) →
        D.rawBlockSourceEnergy normI first prefactor atZero phase a₀ ρ₀
          (annularColumn normI lam) pow sup rows marks columns inputs ≤
          ((D.tableMajorant normI first prefactor atZero / Bmin) ^ 2 / Nmin) *
            (C0 * (K * N * B * L) ^ eps * (K + N * B) * B *
              (N + L + (N * L) ^ (2 / 3 : ℝ))) := by
```
