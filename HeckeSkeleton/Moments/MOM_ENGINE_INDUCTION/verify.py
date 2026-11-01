#!/usr/bin/env python3
"""Validate the exact-head native build and recursive axiom audit for this task.

The workflow runs Lake and Lean explicitly with pipefail before invoking `check`.
All generated records live in the caller's output directory (RUNNER_TEMP in CI).
The existing skeleton adapter is a separate integration boundary: it imports
admitted upstream definitions and is not included in the clean proof target.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import re
import resource
import shutil
import subprocess
from pathlib import Path

TASK = Path(__file__).resolve().parent
ROOT = TASK.parents[2]
PREFIX = "HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION"
MODULES = ('ActiveChildAnnulus',
 'ActiveFamilyAnnulus',
 'ActualAnnularVolume',
 'ActualAtomPhases',
 'ActualCatalogueVolume',
 'ActualChildPrimitive',
 'ActualCommonReflection',
 'ActualCompleteLocalInputs',
 'ActualCompleteSourceFamily',
 'ActualEngineArithmetic',
 'ActualEngineLabels',
 'ActualEngineProfiles',
 'ActualLocalInputMeasures',
 'ActualLocalInputs',
 'ActualRecipeAtoms',
 'ActualRecipeTheta',
 'ActualReflectionDensity',
 'ActualReflectionRows',
 'ActualStrictConstants',
 'ActualStrictEngine',
 'ActualStrictFamily',
 'ActualStrictOrders',
 'ActualStrictSource',
 'AnnularMellin',
 'AnnularMellinSeparation',
 'AnnularMellinWindowControl',
 'AnnularReflection',
 'AnnularSchwartzControl',
 'BaseBranch',
 'BaseTerminal',
 'BaseUniformity',
 'BranchAssembly',
 'BranchParameterTransport',
 'BranchedIntegralRecursion',
 'CanonicalMovingSource',
 'CenteredMellinKernel',
 'Centering',
 'ChildStepCompatibility',
 'ClippedAnnulusSchedule',
 'CommonKernelMass',
 'CompleteParentSource',
 'CompleteRowAtoms',
 'CompleteSourceBudgets',
 'CompleteSourcePrimitive',
 'CompleteSourceReflection',
 'CoreGeometry',
 'CoreRecursion',
 'CoreStages',
 'CutoffReflectionLabels',
 'DataPrimitiveExtension',
 'EngineAnnulusSupport',
 'EngineOutputBudget',
 'ExceptionalCounting',
 'Family',
 'FiniteBranchMeasure',
 'FiniteMellinBudget',
 'FiniteProfileConstants',
 'FiniteRowKernel',
 'FiniteSchwartzProfileBridge',
 'FixedLineKernel',
 'FrozenEngineOutput',
 'GeneralBaseTerminal',
 'IndependentChildSupport',
 'Induction',
 'IntegralRecursion',
 'Interface',
 'KernelReduction',
 'LengthStages',
 'LiteralCalibrationSupport',
 'LiteralDirectFamilyAnnulus',
 'LiteralPassiveFamilyAnnulus',
 'LiteralPassiveSideAnnulus',
 'LiteralPooledFamilyAnnulus',
 'LiteralSideAnnulus',
 'LocalizedCompleteSource',
 'LogNormProfiles',
 'MaskDeletion',
 'MaskNorm',
 'MellinCoreRecursion',
 'MellinPreprocessing',
 'MellinProfileNormalization',
 'MellinScalarStep',
 'MellinSeparationMass',
 'MellinSourcePreparation',
 'MellinStrictTransfer',
 'MellinUniversalLabels',
 'MomentProfileScaling',
 'MovingPrimeAnnulus',
 'MovingPrimeArithmetic',
 'MovingPrimeProvider',
 'MovingPrimeRawCapacity',
 'MovingRecipeArithmetic',
 'MovingRecipeConductor',
 'MovingReflectionCalibration',
 'MovingRowConductor',
 'NormalizedPowerWindowEnergy',
 'NormalizedReflectionDensity',
 'Order',
 'OrdinaryDeletionReflection',
 'OrdinaryDyadicMass',
 'OrdinaryGamma',
 'OrdinaryGammaRight',
 'OrdinaryPowerWindows',
 'OrdinaryProfileNormalization',
 'OrdinaryReflection',
 'OrdinaryReflectionDecay',
 'OrdinaryReflectionDensity',
 'OrdinaryReflectionDyadic',
 'OrdinaryReflectionLines',
 'OrdinaryReflectionOperator',
 'OrdinaryReflectionProduction',
 'OrdinaryReflectionSmall',
 'OrdinaryReflectionSmooth',
 'OrdinaryReflectionTruncation',
 'OrdinaryReflectionUniformity',
 'OrdinaryReflectionWhole',
 'OrdinaryRestorationOperator',
 'OrdinaryRestorationTail',
 'OrdinaryRowReflection',
 'OriginalAtomConsumers',
 'OriginalFamilySupport',
 'OriginalMesh',
 'OriginalMeshDirectAnnulus',
 'OriginalMeshDirectEngine',
 'OriginalMeshEngineMass',
 'OriginalMeshPairedAnnulus',
 'OriginalMeshPairedEngineStep',
 'OriginalMeshPooledAnnulus',
 'OriginalMeshPooledEngine',
 'OriginalMeshUniformAnnulus',
 'OriginalMeshUniformEngine',
 'OriginalRowLocalization',
 'ParameterPrimitiveExtension',
 'ParameterTransport',
 'PlainMellinProfiles',
 'PowerWindowEnergy',
 'PowerWindowSeminorm',
 'PrimeAnnulus',
 'PrimeAnnulusActual',
 'PrimeAnnulusArithmetic',
 'PrimeAnnulusModel',
 'PrimeAnnulusSlice',
 'PrimeProfileSupport',
 'PrimitiveReflectionCalibration',
 'ProfileControlAnnulus',
 'ProfileControlScaling',
 'ProfileOrderSchedule',
 'ProfileScaling',
 'ProfileSupremum',
 'ProfileTimeIndependent',
 'ProfileTimeIndependentCore',
 'PrunedConductorModulus',
 'RankedAnnulus',
 'RankedAnnulusPrimitive',
 'RankedAnnulusReflectionAssembly',
 'RankedBaseBranch',
 'RankedDataReflectionAssembly',
 'RankedMeshReflectionAssembly',
 'RankedProfileControl',
 'RankedReflectionAssembly',
 'RankedSchwartzProfileBridge',
 'RecipeDataReflectionFamily',
 'RecipeInduction',
 'RecipeMellinFamily',
 'RecipeMellinInduction',
 'RecipeMeshReflectionFamily',
 'RecipeMovingThreshold',
 'RecipeRankedAnnulusReflection',
 'RecipeReflectionFamily',
 'RecipeReflectionParameters',
 'RecipeReflectionRoot',
 'RecipeRoot',
 'RecipeStrictEngineBox',
 'RecipeThetaFamily',
 'Recursion',
 'Reduction',
 'ReflectedRoot',
 'ReflectionBranch',
 'ReflectionChildGeometry',
 'ReflectionConductor',
 'ReflectionGeometry',
 'ReflectionMask',
 'ReflectionPrimitiveFamily',
 'ReflectionProfileBudget',
 'ReflectionTailLedger',
 'ReflectionTerminal',
 'ReflectionWeights',
 'RestorationRows',
 'RootNormalization',
 'RowIntegralKernel',
 'RowNonNorm',
 'ScalarRecursion',
 'ScheduleCompatibility',
 'SchwartzEulerControl',
 'SideAnnulusSupport',
 'SourceAdapter',
 'SourceConsumers',
 'SourceData',
 'SourceProfileAnnulus',
 'SourceReindex',
 'StepOutputAdapter',
 'StrictChildRank',
 'StrictProfileOrder',
 'TargetPrimeAnalyticInput',
 'Terminal',
 'TerminalCertificate',
 'UniformOrdinaryReflection',
 'UniversalNodeFamily',
 'UniversalReflectionBranches',
 'UniversalSourceRoot',
 'WeightedReflectionMass')
# Exact canonical single-step imports, including the complete-row atoms
# and genuine original positive source. These remain in the owner namespace.
PRODUCER_COMMIT = '76904bc272e28e0de866bea0aa60b53a54d6c01e'
PRODUCER_SOURCES = {'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActiveNormalizedFamily.lean': 'e818d8a0dd2d678fec6b78dd7c2a3ad7a41573aadf28301e09be795b48ef6db7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualArithmeticIndex.lean': '16da532872dadcb1e1adcd00da49a8fee8712941c113c8eed9994b3b9e3fd1b1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualCapacityCanonicalBridge.lean': 'ddb110c0f2b876ef4728267c3a3ed46e6423b68ea96837cd16a2faec62ff7f12',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualCapacityChildIntegrability.lean': 'f28804a69ef231e75b6697a113afb31f244f0687b1c7542f46ad380e964b38e5',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualCapacityProduction.lean': '05d527ae105a5c0c73bfd48f589faf82897aa709de3ae4c6c78be6b64c99b9e4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualCapacityProfileMass.lean': 'efff727cee1336a88c018182ea6413058a4f5f4843043cf8a7cd8f436c05062e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualCapacityRelativeScalar.lean': 'dcd82edf01a9a03c4bef59428c266ec9243ca392947d3fb7299f4eb07717c198',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualCapacityScalarMass.lean': 'd2bcef131c3f731da9d983c427a6c92d9e2edf73a8e855c2ffe20bb41049c34c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualChildAllowance.lean': '2ebb0f52bb27e8316404e2cf0fbf84016ce78a52dce559ebba549bed13840dae',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualChildInvariants.lean': 'd4971513b7e4f38c8b6bcdb3595d75772ff3d7003e073f576050540720090cde',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualChildMass.lean': '896ebe150a8b03743c779e4291f02e6cb1718e48427360cda84998abcf704ae7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualChildMassBudget.lean': 'ddea2696307f1bba8d767a1acdba7dd8484c9edb6205502c128ad27bd172ca32',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualChildRows.lean': 'ab2f29c47f570f01c2e56ccab9de8c71197424d41f22d2f0b79c71a933973ad2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualChildSectors.lean': '308f5ddaaa99696d56d073aaae0d12c8c9186ca0e93882811a1e20e530c4970c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualChildren.lean': '71081ee5face3a8ba76d88a84eab5eaf8048fae36f0631ee072c92510ad9731d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualCommonAtomBinding.lean': '96a3e73b5db8b510c258dea644a70502c0b24492be6d0a3b6aa9a9ac9978b08c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualCommonLabelConditions.lean': 'f6f079cdb4f7dfbf0fcab3f023f4824ab0deef84696aea03e27f65dbb634d3e5',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualCorrelationBound.lean': '6fb4f2288c9a8620b72cf50bbfd488678b853048d0237632ea007714319a3e0e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualCorrelationColumnSwap.lean': 'dafb1110797fa5e396dba2ea5d22cf390a4bd3cb7cf5f8e2e78b68d65b304993',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualCorrelationSupport.lean': 'e2d9d8d45677e1851d510a91f3df712bcd5756d8aac678d3e4d6afee8c601fab',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualCoveredFibre.lean': '0e2a29243d073649a49301f583e63c7ad37ea9f19d8f2735e00c11e0981cdf5c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualCoveredFibreMass.lean': 'f03ace1f90fb6cf1622d6a12900687fe1ca8b6774ed7a1d42cada7b820b424df',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualCoveredLabels.lean': '943a8125054fc28b795be9374d6ca77eb35e16af50849378cec299afb61c61e6',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualDirectFirstSource.lean': '50918c425b699f834c3b147d8cf8f516b0e1ed5c7fe340042234b9b4f986302e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualExceptionalAmplitude.lean': '1597b271bee928a3c4411f0ca3620ea05f4e87fa6db3af3bf0628e6c4642fe5e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualExceptionalBudget.lean': 'd9d21ef24c8450825b2c98dd5ad233aca61a84abd71f3b29fb87425b3ec614e1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualExceptionalColumnOrientation.lean': 'bc70a93db526345f510cb5978feaae632449866839d799222d7b80a5dfe4810a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualExceptionalContribution.lean': '16b5b5571c83734c32650c835e74388eb104be14ef563c6f4ff51d9d8739fa0a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualExceptionalIndexMass.lean': 'f581735c24d1684c6e347bd14fce135d1c50c85dccb2f2788f7beafb56c60d63',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualExceptionalLeafBudget.lean': 'd71a68c1e0592443d78ffa58d3438b9dddbec35cb14ef7f82c619c713e4f8fdf',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualExceptionalRows.lean': 'c48a6a7a65706ee20ac06f8d7588484ec39f5edee29d53dfac331318fa2d7bdd',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualExceptionalTerminal.lean': 'fed48fe65e9da3f1c305df90585a3f587dc59977ddc329164bff5863bf2431b3',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualFamilyIntegrability.lean': '7ba63049fad1dcbcbd32f3f028ca471546708384fd9258b17bd28da6b85084ab',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualFiniteKernelMass.lean': '636bb57e22f2d80ebe0d3a400d1fdfff750dcaea2f2663c555892f214f09dd99',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualFirstCharacters.lean': '25cbf685cdfcfc72cbd0b44214ad389a8ebd2629d4a79328700dd9c109b22500',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualFirstSaving.lean': '4e7e8a6cecf795ff6507a3865d3f6be7301ee79809e7493e45d98d00fe50b4e8',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualFirstSource.lean': 'dc88613c4c48317a4bdf508cf04eb162eea2f5799b8bc857fb7f8e90333992bb',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualFirstTerminalBudget.lean': 'db75853d56cec34f5f6f162d17e95b99208e981507b18619adafcdce802e49cd',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualFirstTerminalMass.lean': 'a5abcb702b596eadc6481b216c8bd73381fa00a7413ee96aec94d75543c4b4c4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualFirstZero.lean': '76f8766b5f4e9291f224d9f334a8cd6ea502ea03e97cb7de9a99fcecdec52ae7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualFrequencyClassStability.lean': 'd918daac0e7dac424e0eb8448bc4824c7e0efceb10bf399514d300fb78257510',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualFrequencyPartition.lean': '63766d1efe81dfbf915d1cd3a6cf76083ee81485b13749dafd6dda1c493c5933',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualGaussCoverHybridTerminal.lean': '079e25914d94531866e713528c6b8f0101df325fd9303a819e65da8c192fe468',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualGaussDualRawTerminal.lean': '36dd2d4a15dc8a264da33cdc4673b1d52aac0403b9af4fa1ab79d13f79e22735',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualGaussFiniteLeaves.lean': 'bf6ce477fe97647198a8414a054cbbb758c0800f1884c76229d46def0377e2e1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualGaussHybridTerminal.lean': '95d90539597628db7d8304d3c7caf2a6bdf0067126d1444ee20569af116362dd',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualGaussRawTerminal.lean': 'd12bec154229808cfe517d2e93a01a1f3c8f4d3e710ef4a35ac51150a472305e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualJointRowWindows.lean': '309698d4f524cc42a5bf0df203d8d59a3440bfae4ca5a43693468f115b520dcf',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualLeafArithmetic.lean': '46e815b3ae55ec60d815071e4475d6483bfeca5b8ee96db610ec5abc207f0f3d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualLeafNormWindows.lean': '738e769d5bfbbd8aec0d6a342025ec2f00bed8e9af47429bff2bb533d9e8a5d7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualLengths.lean': '99f803cfd98ec2a3a124c1d7192a4df3141c18b7d51c9e22d6b2490e6ca550c2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualMovingFrequencyFactors.lean': 'c0e4c45bc1614edae9234f6c8a54e8f252c059aa460ac4aa8544531485c1648d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualNominalGeometry.lean': 'e80d4861369b5dabe6f581bcb3f97fd22498fe4ea7fc208051b349f74f3f7f07',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualNominalPairAllowance.lean': 'a37f835eab15a5e5d8e634b04b191f7dc3a6fe0cd65df0ae9e35d2a4b43030f1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualNormalizedImageFibres.lean': '19e592ff90fdcc457149fe3dd1555ab0f634a3b2423a580c4b30e6556c67aff2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualNormalizedLabelWeights.lean': '86cb17c790332e883bf872f85d1c380e3509ea46740e20bb165eea1ef12abb76',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualParentFibre.lean': 'fcd5f859229b895675a650dc89383a1f2503b477bc754373fca74d96d9fa14e5',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualPool.lean': 'c0c43cf5dd688ee0ff777874def1fd75a87b5a5a1031f6cc0d51ab7dee940f33',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualScaleClipping.lean': 'b2ae32c5364c3881f5e014dee5642d69b39f8a3a39a00c73a7fcd68c36e8f180',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualSecondRowMassSwap.lean': 'a6c86f15ec45356475e25c412c47bc74c7d59a4dd918c2907e8ffd9238fb50fb',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualSecondSaving.lean': '918ecc86d4217cada35cbb52afaa83a29fe06d88cb81741a5c94093ffe3b6f3a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualSourceImageKernelMass.lean': 'd11b910475b638b3ea33b9468af900b8bd0faf12246d7e1721c3870454be3b0d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AllocatedCapacityProvider.lean': 'b2764f5265014ae9079c92838de514080072a6d874e23102cf48bf2e1f42d972',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AllocatedChildFamily.lean': 'e83d72f6b8c5bc3aad1d6e2114846096a7dcc4f3a3107329857d013cf7838765',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AllocatedChildProvider.lean': '6a9ed426974f5671004bccff5052756ef70569f62ffe5132ed2b1aa57b03d91a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AllocatedSubsupport.lean': 'e658a7d3667cc8908de48c552a4018ebb95624e89232898ae88b4c1ab7218012',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AllocationKernel.lean': '9b117cd06a5b2e81cc7c0d70eb17e681e70ef91478540dfd79a8ad808f1ed19e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AllocationMass.lean': 'ef3bf0bd41877b5a7daf978a460071ad42a4188fa98f1b28e9bd8edeefbbea84',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AllocationPadding.lean': 'f05af14b640b3e22fd0f9ac99e5ea9b99b5ac3237c082c775d13579a77aad10a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AllocationScalarNorm.lean': '00214b195df858b631f5d07a5fac8111b70177029afef13098b67104651ad835',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AmplifiedExceptionalMass.lean': '85cb72992b1272465456cb9000e7c3b3c05ea5dddca05cd33eda8b88ccfab944',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AmplifiedFiniteIndex.lean': '6573c6c2896d83310453a73f1cc94fbcdb5fd5000a9e37c34ca642bb24fc0cf1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AmplifierDifference.lean': 'b55418917a8d44c399d90012bcb551278de171566ef023b7b874512718894b41',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AmplifierGaussExtraction.lean': '3f26ddec7c41a220fa96042800f6c4c82761724355fed4712d8dd165caccc649',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AmplifierPoolReindex.lean': '1bc697ee109457bc7fe62963778608baa841457c911b4d4b451197558c67489c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AmplifierResidualSupport.lean': '674a35ec9973fe56741298f1071bf2fafb0f0a03a6852ba5948306908ac3e7b0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AmplifierSupportDictionary.lean': '9c33f2ea43ec8eb46463f7826ba9f17356215a5c305d8b6b39d859f7f6b8625a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AmplifierValuationSupport.lean': '70141b981aa29341fe2f32ba2d845aaf2c5c38060833b082148f8016e186ea70',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ArithmeticChildProduction.lean': 'b8d4dd6181a45b0e128516defc924ed688fd0cf208bf5d651f5c6c9bd8589761',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ArithmeticNormalizedLeaves.lean': 'c23b22695536586790c65ce5b60d86e320a0de8d726f58f097b7ae94288772b3',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ArithmeticPrimePool.lean': '01fdf4cd368703ac9d4a9de5dc4800790fd8e83a9807ffa1c8c9542bc9d9ed4a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalActiveDualTerminalWindows.lean': '8549498877fd9e254725e0ce84107de86a1dc1eab7a31769bfb97a4128887182',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalActiveGaussColumns.lean': 'cd0b7cea97e3ecf53b31c648cd772de10a3162e0237813e6c3b2d5874df885e6',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalActiveGaussLower.lean': '431e6dd50ad34132858e792a30a24e372041957979f612d699c73a28faf18d2b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalActiveProfileKernelMass.lean': '7c7206b23dd231784e716892fb5cd0b200c63fa9955f23c78074a8715abb72a7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalActiveSecondWindows.lean': '14c08862320d85fdee0717003525a2337d8ab8856defecea4d7267b2d350092a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalActualDualTerminal.lean': '39bb0530af6ea53a162028ad39efd57411fb5c03decea05bc52a12f430ff4ea0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalActualDualTerminalBounds.lean': 'e38e2c7adc3a8b8e81e679a01481867e6c87ccdd8a42ec9df3a29314b3cd780e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalActualGaussNumerators.lean': '3bf372c801af225c630e24e763a3e1cedde54e9215a26b3ecb0ea1d5db5970db',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalActualGaussReconstruction.lean': 'c698a8498bbdb0b5a74b0839b3a4b7bbc28aaa68ada9fd8b2b601964f125e23b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalActualGaussStage.lean': 'ca23c1719327bb2f42eac88812cec50ae3ee9e4586fad5d6a1667220aaaccda0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalActualSourceMass.lean': 'b3e27df269aa25519095689a22350bc02fdd8201a7c58a3686f3e52341677b20',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalAllocatedCosts.lean': '24ef004fb32019d8f83a6f180852099ff5446c56b7d6cb1bc0bfdf5e608e4faa',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalAppendedPhaseCalibration.lean': '6c19d20a2872ef75304ca204e99e6c853e3c436c6789f124853391cf680cc944',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalBlockGaussStage.lean': 'c4d979adefadf945baa9834ecbcd6596a081713952fb15d8e7b9529105ef3925',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalBlockRowClasses.lean': '897609baa123bd1d67c815d975f487153b27b1f3f78ca0dcd62c3902b94a63d1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalBlockRowSectors.lean': 'cce9213597d616439ca46fd6b44689826bdecd0771716f45e67364e59ce13a61',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalCapacityKernelMass.lean': '04b9e7924a94d1b32a4f50d4d2cf6d367898c19cc24b4d3abbf5836b2c523aff',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalChildFourierControl.lean': 'f5e5b8fc9dc5b10f0796bd6f82e9b29567fda28557f0aa5ce6575e0c06bf843e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalChosenChildProfiles.lean': '6462c0f56c2fb466d4a83df90a664f7a98d86e0a88134683e6324aa667010534',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalClippedProfileBounds.lean': 'c54eb50492640b2fa7c50290ea2da3b061b46ef4d7706bf6678635c9b3ffacd7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalComparisonScales.lean': '7245298a610609f29f2c69f263d34025aace69d0da24dd4dc26b6df20156f56d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalDirectParentWeights.lean': '6a1e59fc63b068dfa63c776fadede7ea0d13fde3892adb7eb7952f5f37e7568b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalDualProfileWindows.lean': '4cbda99fc2003e06e926a92cc2993159141c6118f135b49803c62135a6ece52b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalDualTerminalWindows.lean': 'd79b3b15c6e7a91ed43fb1e94bbb8281336e71317caa4c0354dcc8c0e56e1501',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalEmptySecondWindows.lean': 'ecd44c475c5798ce560300488d1846cbe281e6bb79d54010ced3925382fa4b12',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalEngineSmallParameters.lean': 'a3f5076a29d2b7bb76b7c10c8dfb0f34d86e4b1b261edafa14e830bd27ea31d6',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalExceptionalBinding.lean': '6eb4ad2aa63cc8789130591b5fe4de15b65ee83b8fc20c00062621ec4050007c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalExceptionalExactIndex.lean': '722e798b482a7b9503f415c93c74a8353805991011423314a11958f7666b3036',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalExceptionalOriginalIntegral.lean': '2ba6b9063328bae1836c94fe408af14fbb1dfa689f15c401ceb3e2c216cea5ee',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalExceptionalOriginalPointwise.lean': '4398b7873288279cb647da4c5502e1878213c475a2ced5cae9ceb2f94a469880',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalExceptionalOuterScalar.lean': 'a6698957d6b2ca94fccd13aec261fc37def3f1b9c7a15705361f7f6804da64d6',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalExceptionalPaidIntegral.lean': '41d485d2c9a4fa9836ff7189a833b0bc037a556474e4d82863cd4e7b72c45c9c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalExceptionalPaidNormalization.lean': 'eacd40db84290d51c6a5012cd9c6468886f3e63d56a3b8a9b1ce4802e4a388a2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalExceptionalPaidOrdinaryRows.lean': 'b97d78b98a44b6c1da12e1733d9825bc14b43198f6d3060ce2451e301f88e59d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalExceptionalPaidOrdinaryTerminal.lean': '774fa57082b52ffc1463124b4beb0b463e8b776d1c7cc3505e5eb843b9202a03',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalExceptionalPaidRows.lean': '2e8d74c830bd330634dc7d300f0bf1b298260c79642091e6b6772ac75418e310',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalExceptionalPaidTerminal.lean': '340a284e7b0d036d6ac7016bfcd24eee773cb040e3de0292f69cefdfdc8ed325',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalExceptionalParentWeights.lean': '8dd16832a57cc5aa0ed72e7dc495a99d471509a2d732fec15b610c7ba5cd9a63',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalExceptionalPrimitiveBounds.lean': '8b58afbdc582edde3e4a932223f92cbd09920bd78cde3b9abbd8b2ae8e048567',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalExceptionalRightTerminal.lean': '19d54193072c307d50612e73d54c5d09c5fb6d4aaf10629a3c82fa9519468b2d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalExceptionalSupportedVolume.lean': 'd394b8b34c0308b9c353e584620554f9d9ab5bb9239432a6ce3252af1020844d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalExceptionalUniformAmplitude.lean': 'e7f628b209f375417d0f1aa27d275d66c450eb3fdd6b27bbf20b034b7182b45b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalExceptionalUniformIndexBudget.lean': '6348171d40f6b031c4ef9c02f688b21293b29cb435fcb418f7f597bdbc7814cf',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalExceptionalUniformRows.lean': 'e7357bc437a2cc5487c5c7117c1629c32085860b850a7185f8116ffa06c16043',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalExceptionalVolume.lean': '8778cb1a13b7fa29d836f4358ce61dda9fb39c0999eac0aa987153b0be08da86',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalExceptionalWeights.lean': '98eb0c130db3036a2f941e2ca15bbacbdbcfa7c6a750ff0d652f8ab89302e826',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalFirstBlocks.lean': '1efb4f6882214dae1879392657c59637d406d116bc0299d0e6d7ecbd4bf24d19',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalFirstCombinedAllowance.lean': '6eac3b1497182afc09d87e3ac6c37a3b43b546efdb67487d439bd86a60585ffd',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalFirstDualTerminalWindows.lean': '749f7622d99a10f1b165ec6f979b6c52131381307d201e51c00c848d2ac7a255',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalFirstGaussData.lean': '541e32c8102646eb0ef8b0659a3e0cdcc71ba6f6db2b15cfeabfab34618d3c68',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalFirstLogBounds.lean': '354a99a403fadc7368bc7493872f0dcb7dc6a7de19baf9f61dff11b22c960564',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalFirstLogChart.lean': 'c638e91cbb4a470f4179d680acc7e2cb6fa77be75d516fe1f8fc6c0981016793',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalFirstLogMetadata.lean': 'ae6b20dfd5ea611929935a0200c3712252aefd8b329a895edb961f39488c7b89',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalFirstMaskWindows.lean': '865839b416077063ab5bf7e9fb215b40530d9b1848424f8dc1af5b05dd2b3219',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalFirstParent.lean': '9d1efaacc3e2011d529d2b0619450aff317c87a50d15bfc652649bd4f4188460',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalFirstResidualProfileCost.lean': '9da20917d58daddb185c4de1efd81dec5ace813f8ce32292e464cf37bc9553e8',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalFirstRowGeometry.lean': '93e52d1ae4cd4d4b9c65f5aecf949b71b3df21681de3fb80bb6d7f46a8d98261',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalFirstRowWindows.lean': '5ca3684bd53dba3c202d6cd291a1980548ecd52123155589b466c5992e1df63d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalFirstTerminalWeights.lean': '1ba7fcdbd65ddc46e8233d1afa2430c0082cb678420f2f70ed12ba44dda88a3f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalFullDeletionWindows.lean': '467ea3c0bec78600fded655758fe0883f1648646a60d74b9c799b08f57f8c969',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalFullKappaKernelMass.lean': '828317a937a2ed09c742946c30f9393bb83431553596cb3483cd52831486be74',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalFullKappaNormalization.lean': '5cfee3decbe634e97a437056c1c4167db8b7ac683562a869aaf30ab3a2e544d9',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalFullKappaPrime.lean': 'b2b7f119bfc19065a1243efe8f7fd0c577bf832f383cf65d1d446ce6dbd786f0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalFullKappaRightNormalization.lean': 'ad6286cfad22be87b55c49e8dfd5c70bbb0be3917193c19f3d6132325ede2913',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalFullSupportFirstTerminal.lean': 'e100882217c2a1f971fdc1ab0e816a512c394621e4c6635f401e0ae52fae3532',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalFullSupportFirstWindows.lean': '22fdfa6d9d3371b1e377de31bda09e310265d7a38c0af4775184920a0e41106a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalGaussOrbitRows.lean': '06f81c70b0127ef48e4d08a37cc15cbd874cf2199f74139b64d3da1b4a316ac1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalHeckePrimeAnalytic.lean': '875a5b6ebf798f5663c33dbde6f8a905950bc2dcf3b38134f18cf457b0b645e8',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalHybridMass.lean': '2ba33975011973aebfa9558f7ce3c7cb1449d2dd93c8ebff04358b90ba5ecb0a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalJointFirstSource.lean': 'e4d420b3c8238b809d70ff984d69953929a5ed5ac244eb8e7585f30600252f9a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralActiveCapacityWindow.lean': '7d814b4acb9a0d716d604b7af1cb34c930b3da9d5db041c8b9bbbe50ba278c06',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralActiveOriginalScale.lean': '7f2ead0fb3232c6eef4b65512784badda3a3cdec5242eb5fdcc363341ccb4430',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralActiveProfileBounds.lean': '6556d1b52c9e33c5b7148d40be3f524003d47626ac53d11580be853ec172d1ad',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralActiveRadius.lean': '88c941b5c624d1b01acda04e6fbcc6eb5079f3732e69a86594ef9180222f306e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralActualCapacity.lean': 'f2c3e5c75fea37df0bb2a16a8753c9ce4a934995e302eeaa4ee4a4891f41e304',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralActualCharacters.lean': 'f9f1845379c3468e4e2aceaa27962f33f8301083030419ac6d8dd31a10b75455',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralActualCoefficients.lean': '452f41ea52ab5a12c76c3ff441c20a9714510e9413bf038b5730d0ed471ab898',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralActualPredicates.lean': '46d532c81735c968f3cf5e2b2db9d6265bc7325044576e360e5913a341b0db32',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralActualProfiles.lean': '7a684e7f1ca1da64ea132d3c35509404e085708a3931f1940d702108475bad22',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralAllSideClipping.lean': 'da0a9717f77405d0eb19f832aa52e73b81f107fbefb5d9da078e7654751aecc0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralAllocatedData.lean': '55b6f3e24e2000f6a163e19bf1ca988a61959241d2442e579b6bb85dc3b3733b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralAllocatedRecipe.lean': '7ad5c22352b270d153e9a83a2f0eb214c05a680b6de69549995d5ce398aa9b2f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralAllocatedSupport.lean': '166998b2af62c148f877c14e2cf4ecd72c60d867df5ba0dd5e4b9afd66f30ce7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralAllocatedWindows.lean': '64c0997326682e0887b5689a32beb99bf550220e70362e3492afda233c02484f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralAllocationAtoms.lean': '1a6f5e60ccf23d72e5d39a9e35d43f2105599639df2315011a262471829ff695',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralAllocationProfiles.lean': '5492cc63dda9f51fd3e3e424b4f472be4c85998df405fb324e71727bdad0abe2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralArithmeticInput.lean': 'b76cac29859c18b35dcd7e6d9a861af420216a67331914fd21ac66af6d110bb6',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralAtlas.lean': 'c44f6a166fbdd83913b4526d1a52aac35874242e7333e760b94ec348e7080c55',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralAtlasAtoms.lean': '55fc1e67a8dcab5c0a49b28432476f4f519ddbb53a6b4bae04dea533ac33e63c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralAtomCosts.lean': '3f4110c838e003690887a21dcd12045471b87652b9a686e4daaa3ec14c81226c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralBalancedCovered.lean': 'bd760d1b61d2411b1fec4b47718f9eddbb5721d9feb01cc2e075af45032f4361',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralBalancedSchwartz.lean': '0395d2772b5fbd0a6cf49710949b5006ca416ef8c47a81b03b5015d2b3f5a277',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralCalibratedDeletion.lean': '37b3c46b9b8e7ba1796aa4260b021542b28760a90d2bb60be7b5a2e7de44df21',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralCapacityLengths.lean': 'ce50a4319890cedd8aafa224fc2abc69b5c881119a7faee4a27e1f7c417d5f26',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralCapacityMass.lean': '3043b8ffe9f0a986be835a8b59d8b829f9a0591a2e0a94f28c92b43beec1c540',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralCenteredPassive.lean': '0aa63e06901de3ade03c064c1a30465b709909590c69ec6a0e0f027ddd0221c9',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralChartCoefficients.lean': 'ee154c233e3a1c9025f03e437cd7495198cb724117e94e45222a25c3ffa50822',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralChartLocations.lean': '05bba1b54f07abf5c8287fe8a7a5d3add8d16bdf97a715062d247a2a8e30b91e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralCombinedMassCoefficient.lean': 'eeb976ebda01d887ade56546e7aaaa60de4a5bf1c31b3473792dc26fa5e1cb4c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralCommonLeaf.lean': '8d23cb95bbfa4e72079ec406d5ba7df95aa0cc5fecfe89dac861e5819e869d08',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralComparisonProduct.lean': 'a38c33db8443cac8ffcef89f22375f3d3d23b12b96c0eda752229379fa74ffdc',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralComputedLengths.lean': 'eb1641b2320b09f033ae38102e9041606e6eac50cb6c788e7723e76c348b4c22',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralCoveredCalibration.lean': '0eb563312581757655e0dc56415d306572d562105bcf004d104ecb32e2eb6a00',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralCoveredComputedProfiles.lean': '2c00e40b3635f62507e28a27f0af22447b22459930f9ffa66b778fd0802f8a82',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralCoveredGaussScale.lean': '370017a7290857b06f36e4822c8749e9b7b633762d4b3197e45bd06eb5d5425a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralCoveredLeaf.lean': '3929332db8e96bb288800abc4ccbcf53f50b50dc3c8f058247f902d8f6764bbe',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralCoveredScaleProduct.lean': '5c9dd77f975c2e199ac5c0e650420a66eaf777fcb917c7ec64f07909f3d48c80',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDeletion.lean': '068e17be791836fe4e4820c6a42bb587cc5b127c5c01e6b826538e031e12122b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectActiveScale.lean': 'ec0e8ccca12179be9e6634e52a737b49cfa43c91f4068f47040389d2b7105cf6',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectAtlas.lean': '07a25b8d170b95d05679549b88f8e8effbf24c6a3cc2d48605c67d1bf3412651',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectAtlasCoefficients.lean': '28ef6bd139a67c75dca538205122817d65255a51ad8547e9c765ceacb0cfd773',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectAtomCosts.lean': '04f0d33832790eb3a7d9ff2c8e90eeba7a871b5e2eadb18f67d2f9924715e6fe',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectAtoms.lean': '1b9e37716a66e6efc54066404b555eab8aa4d82da1bd5cac263a8636302ad8f6',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectBinding.lean': '2bad41f90a068c34a9f937588d6a3300335aecdea478ca042b8e96456e989db1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectCharacters.lean': '72ff89f07bfa7ab3f37c5c427d1886d240457b818446b0d48d66b142c10f8842',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectCoefficients.lean': '53896caa77bd86a47b42a0f6dea6cc0341741dac46208680f95af9ff91586b3a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectCombinedProfile.lean': '9237270d3af595843ecc71460db5ab82243b0cc59eebbd4871950436e09fe6d4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectComputedProfiles.lean': 'b10ec98ad636eb1d835d93d929c6bbc57a265dfff343823dc52aacdb0dfe48e7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectExceptionalBinding.lean': '391583dd85718641d1ba663ad12724754e5f10707e6b634275d2ee727247bea8',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectExceptionalBudget.lean': '6f1b9d8e1973eb8f230db577d00982f3a2cc4e5b00ea50790de326fb8e012b31',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectExceptionalKernels.lean': 'fd50b70d5c0e6b5efae9cc3ce4a1f06e8a725cb9e76c5b5bd9c6f86e835a2310',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectExceptionalSides.lean': 'd0cae57e1e53eceae437e615b1606f53e6462a625cb7216ac765a9667c4e9cc5',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectFactorFreeComputed.lean': '07846700453a4bec30f4b7c09211905828ff13448ae12beaa22c68a67fb991c3',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectFactorFreeNormalization.lean': 'c89b951e873b4cdb2bbbd3934916bf71c407bdf79f48479b60a28e6cd4794fee',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectFactorFreeWeightWindows.lean': 'b742c4957d865936b225085bd60204637620dacc335b328f3edaa268cbe13209',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectGaussScale.lean': '45fce11c297154a820ba1d970cd900a5904976f41e4836bfb7d322042c8afe86',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectOriginalWeightWindows.lean': '2b105f9be299f6bfb566d9a0b84d170af57a0df4b3aad8ba6e1d7a34d6b79021',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectPassiveIndexedWeights.lean': '8ea7924028e2655de175ba49d506a93524e85a5b664c37947baf0e906e3fb00b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectPassiveInput.lean': 'c572532e3fe368e2e70fe09911159a41d13e3f57296c5b9186803120f5895b6a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectPassiveKernelMass.lean': 'c6600bea5822fc8b2c777521b967e58f3de3d74e0f9d4bb00a0a09fce7ef1f4b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectPassiveNormalization.lean': 'aa5a5230c0b88c98f7da9c9986678f27a95f71b2f32f283592d1b2c5ee1967a5',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectPassiveOutput.lean': '854b59c9731a132f31a491d972ae0a6e3655cdfc06d15700ea253feee2e55d16',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectPassiveSourceIntegral.lean': '9bdbf6c03d3dac61e5d1a3a152da26f6f2751249feba161b36c4fb717c94602b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectProfiles.lean': 'c025bc9a3f7d9f8bb9dba3d0c1972a4411f817cf091a62e9200880b397b5dd52',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralDirectScalars.lean': 'ead076740301344ee1bc39995ecfc8a7516d887a9a0ad749c8e12a0cef58c90b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalArithmetic.lean': '2be210a4529f436cbbcaa5557757211e7bfce96e61a536c6e79f024c904495a7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalAtomBudget.lean': '1c7f40ede5c09c4de887ee01637892e57cc47905a702396f5dc7880410bfb896',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalAtoms.lean': '5523054440a8229ac0435d2bf8cd2b4784daa13fcbf17bfc627f5e88d9f9ae5f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalBinding.lean': 'bd2067cfc42449550caf111c0ee30eb5ec3becefd35fa732e57c2c9bb9780a67',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalCharacters.lean': '0b962debff49dc7ed8aef4113a84088381daf50dea06eea6380a1bde0ecb6a7f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalCharts.lean': '014f4338a863eeba3205f3d9eca9c5a936c7bc1ede2e25610e266d23e87d81d1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalClassification.lean': 'a0141632fca97989084621cef087c1d919d0e5c7bcc7a26c10929bac6caeabde',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalCommonBudget.lean': '20070a1d5a686e34825afe17cb20eefae9578644716b2e25892f6f85020f381c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalExistingBinding.lean': '6081d77e50419f7c1f3302e3b24f9094d61431152611078b8b4b924d05c424cd',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalFactory.lean': 'b2267a0850261e07b33892a9b960964ec0463800c1421a45b65db0ae3fecdbe1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalFirstSupport.lean': '187fbc0d6125d35c4d6bc497d84f67219290e2a77015c186a4002023e9e36e33',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalFrames.lean': '9a1709c947d8b88cc72861a3661fc94e54a5aa5e7eb451ca8c1a63302b3de9d7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalGauss.lean': 'd406d2e262d992ca8740808286f3c77a3840b7edd6befb756e2caae3629220d0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalGeometry.lean': 'df192f68c23a8493eef6bed8cbf283b05f0c2ed5c5b8b9790ef59a3e27596819',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalNumbers.lean': '49e76b22c0aa52db3a5509a8171455255b4ede0c3eb3d39be8d96ddd6e4eb36a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalOrdinaryMagnitude.lean': 'c847a26abe42ebb8227d48eb591437dc40c601032c3577a01a9e8990b9a0224b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalOriginalSideFactory.lean': '817f979f37553bcd72ba14998fb60c7bfcbaa8e6248ff30bae1bbe13c2288039',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalPaidAtomBudget.lean': '76ac08ce192b5296ae0566c66c40ed1a7a0eda39f2ff9e73c9ac55475b784610',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalPaidRightSource.lean': 'd2022ec70cc5fe1781daf9cf55368f4a3c8ce6fe56f950e3a16599a5ee43879b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalPaidScales.lean': '6c7ba98683e51decc221d7a6aa50d071cf3d3e0e027b01c3bb8a6ed418fc8006',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalPaidSource.lean': '46be60e2b0fe98dc030c8e2e61719414c2b8e49cfc7f8cc16341d2ab37aa7009',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalPairBinding.lean': '378741f8d1374f18522a9db55baf3e028b2a6c00518acd1e16b27ab16aa3a1d9',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalPhysicalBox.lean': '5b00bf1531ab9c55a648419a77047a0fd56eab7172895f970602c28a19fd7a02',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalProfileWindow.lean': '7c7f42466fe4b840b09b12e60e2f3b682b3122a8fb97fe82071fe70f0867371a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalRelativeSource.lean': '34340c8d93a46adb2a3a46c880b9c50dd5f525b0d958bec37bcad427a1f94c97',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalRightRelativeSource.lean': '1f381df509b858048ade7d5c97656ddbeab633f81c4997ef98519749f4b6e46f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalSourceBudget.lean': '8db2cc50d9f437082409a0e612b2429eaad8ff464294ec7d250354d0c3c240bc',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalStoredSource.lean': '745fbb4757edee08c9ccf1ea8849b25ae007a51f916d40e6c8fdf0fa4b61da6c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalUnifiedChoice.lean': 'b9eda36b692785593f20da981f1982cc3c065809c955e77d347a6da443149cbc',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalWindows.lean': '38a04237383f6d0a00c868377c77260071cd08f317d8f8902dce0e34fac169ba',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExtraction.lean': 'b2d42f4308a4fb0ff84f848c1ccbe67c96b6285e5643d8ac44829d599f5a968b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralFactorFreeAtomCosts.lean': '2611446df1b96b09f03f941b20a2133a2503a32f7414930d7eae19324bf6bc32',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralFactorFreeProfiles.lean': '58413252542507a79f1ad46b1b2958391eb642a2d179a59c637b0db6ddef296e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralFactorFreeSchwartz.lean': '0244f0b5a006513b0ae44d04d0ce7910d658e0ee8e282f1af175a459a73f1f25',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralFirstPhase.lean': '8242820a6cdce62ebb251a345167559bb129f9d0a1767c1c7521fc3db994d7b6',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralFirstScalarCost.lean': '53cae2b45d55c6be5fc2c9727c27da667e7979d8bcc1264e0a1aeb99ed0e9330',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralFixedPhases.lean': 'b6e9649da0c05ff1745908c97bfc9261c25cb404e74984cfde4188338b227b09',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralFourierWindows.lean': '6daf2d45ef6bfe630a4a45828c9d5eb54841b136c278630b61c6ccf3e7ff967f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralFrameCalibration.lean': '8436b4e0f49b06dcdf6136fa9dddd21a0359502aed3f3e0949e176b58eb6babe',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralFrameLengths.lean': 'c14e4e8fe40d9db4d06a36d80ef3a1249e5e0f4e625ddb717cb75e555fbe997e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralFrozenBounds.lean': 'a710aa80eff28837f48865b84dc0c56fa14cbe21a32aeeffc4de377d6747e45a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralFrozenInverse.lean': '3acfe66762efce3198277be1bacc9f38c20733755844e90242b3e74f19db74d7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralFullKappaInput.lean': '1186d11ed23a58d63fa96bb49230e917ecc1cb251c289ee3e094e30ad3427c35',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralGaussScale.lean': 'fa9ea92ec782c7327411a0f7e31165c13538eae73c20910f692f845b39800513',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralInactiveRectangle.lean': '8f967fb73757da9321fb000e4303e077d31ca69b2d09d531e3f1555cd0c971a1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralKernelConstants.lean': '32aefc87861353b978da74e94063742f3f1bf8bdba8fe10b8545ef5b25e30ed1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralLocations.lean': 'a7282b5485b11222530be58edc6737cac84c868add13c43f7e73b5616e45d85a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralMainBinding.lean': 'e147f47a4381cc2c347eb3ed0a9ce4b47c13daaacdb2df83a005e2aeea4a68bd',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralMainFactorFreeNormalization.lean': '865d7f55c4fa109d3b7d52a02f93d69bf30a27b042dd8a85816a5851618a373e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralMainPassiveIndexedWeights.lean': '43ff885e4d59adf9c362603b7725cd9b88b2b7b81b1749bef328b867c738fd48',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralMainPassiveInput.lean': 'ab39a816e1dadd6cbc88dbd5a34a8de2152c0f54665932d418819bd0475ebf4e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralMainPassiveKernelMass.lean': 'b7dab65b222a81b31272da06eefbc17e19f14efb63c6b591b4447bc466a37467',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralMainPassiveNormalization.lean': '191d17816d9e6e3a93f31d2db46a8cdf754301d9dddcefe7a59568c110778ba7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralMainPassiveOutput.lean': '180e73d242d98314282aa42afb683a0d5e1442211d12d90ebfa95c3553f9a479',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralMainPassiveSourceIntegral.lean': '902cc11de4ccb960ed17c4c5053b80fbb6a88fc488f7c89d1710d84d982cf052',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralMaskSupport.lean': '9cfbe9c3ec95d65d0e4dc62f98cdcfd1de76f04a63e2ee3fe6beb378924f13b8',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralMassProfilePower.lean': '79bd88c0edea0c90cd7341e366e327b3a33e026e9b627d44586a55b466d0c8d9',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralMovingTwist.lean': 'e23b4cf8b25e23abac4fd201dc233c36b4c270f9e9726bea8d915ff3d97fad2e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralNominalWeightWindows.lean': 'd332ef2f3d8b1aa84119ebe2abb0cb3676a7538a15fc93f9f09567d8ccf9eedd',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralNormFactorTransport.lean': 'cfa95ee9397fd95ccbb242e643419892cc91df0283495484d3636d23cd44fb57',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralNormalizedLeaf.lean': '64f3a9c54a74068fae78f9dbec26463418d3909865dbf9a4a889bbc22a4b8a93',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralOriginalEnergy.lean': '0fd9ce8d01c2010b2682eb21bc5f4803c290fb28708c779fc66b1954a0e844e0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralOriginalFrozenCost.lean': '543b35a5cedb9e610231799a9c8b2c4dcc1d4a9560cdd71644cb062c52038881',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralOriginalFrozenPairCost.lean': '46302e50c08e3442a8b0261b3f7ed6419e1ff54408a88f893457fceb48cc190e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralOriginalPoolStages.lean': '651f3c9b44dc15a20f945a4b88e830fc92ce5fbdd4d04bcf17b2d27651a8e33f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralOriginalWeightWindows.lean': '1192e6108f7a54abe8c1f022be502cf6f28d818097aae374bb59ac9f8cc73b75',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPaidCharacters.lean': 'cea3f254eb90b7a8a039fab81ed12a0a8cced60783e6539890c8007498ca7420',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPaidRowCharacters.lean': '7bff87b316d1d3e362e9c2cc9e80e6545e41b8796f707b05228d57da81f43e6b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPaidSupport.lean': '485caa5f826bdc61aef2c604fb1912bfd6eadfe09fbb200587bc51ffdbb7891c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveActiveRadius.lean': '9ddcd7b73b36a2c7c761f41b192ebe6d910e92a5e36894adf19c33219ff23d27',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveActivity.lean': 'a9244b8d24732200afb66445adeca67d0b2af8907c4889493e1ab20b53ffe51a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveActualCapacity.lean': 'bbf8349d131a2145f15de42586455e2ad6454b53f3f4f200785ae16cb129d1b2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveCalibration.lean': '052e8e466401110d2d3ac6f90799fa78c32d28b26cdc2699ac15b602cee71136',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveCapacityMass.lean': 'ee0bea7acabd7c74a3d1bb74279e8f6a12838c86a46a0cc692f1044164bea677',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveCapacityWindow.lean': 'e3f813ea19f069d18cd9c6d679358aaf86799313a9160d9e3c1fe8f3b3f037a7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveCoveredBound.lean': '7e694c4f241cd10ab004722cdefe8cfdaf2792dd719686c90dc3653d07066f91',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveCoveredProduction.lean': '46094d0335d000dbdcde2c762e4b3542a50f1d76ac23bea3c0f926cfb955fbc3',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveDeletion.lean': 'c4274ace9e26f3f9f70eceb2539f391a535c75c0a1231891b5f7bdbfd73b5d91',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveEnergy.lean': '6c1a8dc0945ab08dbaeaab84448da95a2aa7eb2eabb1bf94ae15987d547ee90e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveFamilyInput.lean': '812c5f6c8509a912b469277d9964af015173b677c5713a389b2d4faadb3df866',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveFourierControl.lean': 'b27d215588ca1d6c48865fdc99e88a46f98073ff58240d45707303cb3f469253',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveFrameCalibration.lean': '8218d42342340e609c800e127a35f811e848fdd15e94b9481d4e6fbf2660a561',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveFrameEnergy.lean': 'cdb61890c26373a0cecc0bad293fc4a843094ddbb2ff56cb0863d8943bffe2f2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveFrameIdentity.lean': '871e4d26380fd8b7f65bd6d11bf18e5e2f4ac7a9c86834682b0bf9564b77f9f9',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveFrames.lean': '996870f065873a51138d05d699d7b87fa27613f0511175c6b2d331efc29a796a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveIndexedWeights.lean': 'e368c64cd31fbe4060575610f99793035c70ad305d650ce24b446723f1803ebd',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveInheritance.lean': '1eecc674cab57ce69008924ecbfcdc48a41b62de2c611e2e4dc70e0f471b439a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveInverseSlots.lean': 'f522f3f9ff9b3b6510e60a370667fccedca70ae2bb8a167a9f18122b40707269',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveKernelMass.lean': '8d4a8d0fc19eb27d8d1ba18f1f19e2914b2e209d09f0bb1637684ad8a21b6060',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveLabelMass.lean': 'e5d1a8714366cf8d0a1fa7991df2dfdbc967442ef3e9b360ac48e92b8b59b39d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveMassCoefficient.lean': '2158bd36c6b74462ff7dff83a8260401fe2d276c940648e88f61ac356ed7a182',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveNonzero.lean': '62aa39e61c86dbdaa33dfa394139e6c978d6b160d203f01ddab8dbc2c79ecd7d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveNonzeroMass.lean': 'fef51c255245835fcffb4aea57f63c1b8094db3bb0757e0edc4ef32627b18400',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveNormalizedFamily.lean': 'cea67f125267edd349d7ed1b11d3a4ed47638567630d92682d33c0123e7cc608',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveNormalizedRadii.lean': '50c05062872d6f928c78af4d143981a2a309c1857c5b11f4e6c11074cb41628f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveOriginalBound.lean': '7d48f6895067c22250df8179f989de13174828f3e60cee5893d9a595ffc1e9bf',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveOutput.lean': '4ef30fc168b3db7110c33c5cf3a0fce0cc27ef7a61be5cb0ad697ddb2db433d6',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveOutputInputs.lean': '7c13090fdf167c3b2c909b753bdb4a5a27beabbc6552553a54d8d6f3c2fe50f7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassivePairCard.lean': 'ef5fd4b36c01e12b1208a8a0e14bcd10e86333d026aeba2b202f8533836a822d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveParentGeometry.lean': 'b5fd0a53dccaa5e196e583207e0740775d10f6179afc161960b308182cc28e67',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassivePhases.lean': '25b128de6d67131ea72f3afbbaa5d894fa2a6a18e1fb4bbc0b11c9fa7e34f25e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveSideAnalyticInput.lean': '138685f285daafeb85a128887732c6be7bfedff948db5fa073e60ba3afe13cb4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveSideProduction.lean': '7607448caaac852e47d5a7d1817304c6e235c76d705233e55ea7e720a607d802',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveSideRadii.lean': 'a888b685bc0e0b242afeffd73bf13851dce5c66dbd8d074ddff139634327bb09',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveSource.lean': 'b3e60e8a5643a1f6bf2bb2de8bc1e6fbe5acf27a4b642881ceb60aefadc4bd1a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveSourceBound.lean': '64197705cf0768e5c7678865793e4efa362829d0b095f865bf4305a9ef2ea143',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveSourceIntegral.lean': '8eb989c22207b9217ac61c62156facce5191a56310764f4e4c52c0990709732a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveSupport.lean': '75f93cb7857b5e0033bb1f1a719ea7bb4f6c1ddd05896a884c48bf16836fe4db',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPhaseCalibration.lean': '63a89e12ac8815cac2bf60fca57bd3160e22343a8a6c25743cff52ec3c5e65cc',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPlainBalance.lean': 'cf8c0635f888eb560f7086d3a77ad58cef0d508f48f2f11b67a89afabeb41d26',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPoolActiveScale.lean': '14ee730a31e8fac12f8ef2baad9959a05c922a394bb8329dc37496efb0c838d1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPoolAtlas.lean': '355b85426780c34068f1390e1a180b55de88fcadb77a422d446b332ae5eebf63',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPoolAtlasCoefficients.lean': '1131f5f7cd98fa35354c4ff5555ca0e7a7b2acf0fd0a300e3e05a3f07b50bc3b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPoolAtomCosts.lean': '5533a39cadf5a1e5125e7b93741d813dba6471fdd37115f36b7d6ee0981524c9',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPoolAtoms.lean': '357b1c831fd9a6aa29783060618518228c842968cbe929793d1a12e0f8787483',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPoolBinding.lean': '6c01d5401322b5d57a338d59047509fdf3e8fe765fc3711c89b4aed17135e5ee',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPoolCharacters.lean': '01933c51135b8c61fd10333c67f96bd9760de40ab98fa8a18a3ef00e98f719e9',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPoolCombinedProfile.lean': 'af48dfedb1f7af426bdad2a916ea9f5fb8d39d6b02c5b0c9bf63130b0c7980b8',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPoolComputedProfiles.lean': '5398b139fb291699d68c7036a888d8f95615a09492f24208386965e478251a46',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPoolFactorFreeComputed.lean': 'a87bff095be7e13f5b6f25c63bd373bec433a86415b45c6de615f0f577989cda',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPoolFactorFreeNormalization.lean': 'ab4ec566932cdd4e109c8a362b3f61193c455dea64bb8a5bc14a00b4834b44db',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPoolFactorFreeWeightWindows.lean': 'f8b920ca445470cee604e4090dac0236c53bc241111981e437b6a8bd525489be',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPoolGaussScale.lean': '7030cf4474b7fb89bc7a0c53be0bcd710cbcfd5bc9f8c43a69bd04e311eb8be7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPoolOriginalWeightWindows.lean': '4567fb05f2998d4e693543486f13a67f4000933c9349ab86ffbd5cb8ea3e0562',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPoolPassiveIndexedWeights.lean': 'a856fdba7f0815b12ae0ca4c97777714f348e06c33b3b8d8fa1ace12106e9217',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPoolPassiveInput.lean': 'bb021274ab44f00c53f2bd2372c32753dff1547f474bbdf7c8d5aa4f1910a433',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPoolPassiveKernelMass.lean': '9a69143d915c62f3608a3ee77693f754b4a95736876a6896a9880f747c6b5b25',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPoolPassiveNormalization.lean': '1a02822f1f4d544434148ab08388265c0eb0f275b880577ec89c3798587359f9',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPoolPassiveOutput.lean': '97b3241caa051077c77a009fe7e64764b7f6508009602d65d3808186dcbde114',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPoolPassiveSourceIntegral.lean': '571a29181672b6dc252aed3ccfdc18837bccdc7a0236464eceb9b5b583e9f511',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPoolProfiles.lean': '08cc82a514ecebc2b672e8f7df8a16f6df3674be74a9d69fb2c784391b241037',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPoolScalars.lean': 'cffedefcd621445da598463588d4c08d8e47b338c6bdca2eb32de5f841f5fed6',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPooledExceptionalBinding.lean': '208ed6d6d1ecf51b2c43f2e9193d4e24abf91b0e461bc27b91602ac6fc409d50',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPooledExceptionalBudget.lean': '16f1e8a5756416198c0e955846b0524f334c5d205f92a5021727c43fd7fdc3e9',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPooledExceptionalKernels.lean': '69f5b26d47bb7d0969903f264d71e8d8afa2ac4c55279ef961be91f3898370e7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPooledExceptionalSides.lean': '58e72fc392bb12ecd9d9965d51523742a69d882da879f04d7abe83b058480dca',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPreparedBinding.lean': 'f84866109b754158897720583dce6c9f04afdeba03488c9963bb233ca0a5c7f3',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPreparedChart.lean': 'fff95f4dd90ae15119299bfc7527ca681d746cf1fbb9fbc97fba712e2116f0fc',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimeSupport.lean': 'f0f16c745535b7be372fd1da8f4d345e8dd2569d703e500889e50d8cfeb3c7c7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveCharacters.lean': '1e26face7d1dce169b1e4c1f5236653b0042c860d52e8de254b0f399b7564678',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveDirectColumns.lean': 'a514dc3dbfeb183f173c010ae1c031208c5f553983b2f3c4eb4b27b51650d04e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveDirectConclusion.lean': '571d373e98be65a87c777f810325d87ceec6137dbb5984285f623c61d297acfd',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveDirectExceptionalIntegral.lean': 'daadf33b59ee3f6cb2da48494d0c5d8fe2b53e9c753eceb277079d8ddebde27d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveDirectExceptionalSource.lean': '06e3b95ca660b23cf693bb1035ef0577851f4a6d7b43a6ea2ebb8582aef8de3d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveDirectFactory.lean': 'bbc044b7da33b33cb11fc3f6e073c5132c5bb90fabc548758388fdce1c0953ba',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveDirectGlobalMass.lean': '925a6817d68dd5f694409d54607c1f37073633e801c10f63bc03301662ab9228',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveDirectIndexedWeight.lean': '37b41322c3cea0b7a1adee8923bc51aa2bc9a9508d7bed0160abc4e865d06469',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveDirectInput.lean': '9029fe9a41155a8698f97f8ce48086c55fb16b9e9a64adffc4e1128242c91723',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveDirectKernelMass.lean': 'c73cf049a41b1d29aa0dbb817be107cc617ecfc62276dfc0c07ec2992f6fea29',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveDirectMassWindows.lean': 'c439875cff143350c59612240e6a4dce6bb04bc20711f04bedf153b1fcd6fb75',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveDirectOutput.lean': 'b5d05a98b5f6365c49020aa053971de3ccb760c551fc4c19e8186e0561e22ff5',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveDirectParentBound.lean': 'ba1344a087dd631323e29b0b3b18a53dc96df6f39bb04a4de6f2da51c3f9100f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveDirectSourceIntegral.lean': 'f26b8c1b4b045d8b842123d6e391bac9277a6042b86f4f72176b205a8a81ba18',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveDirectStages.lean': '34efc987c4c50deb77d9ffe0fccda67e936154015a828c6b1106a5265cca83ae',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveDirectTerminal.lean': 'c41ebd730fd297419c848b1c2fb7a45c86efa3790be73bb2779c80977ce6bf55',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveDirectTerminalBounds.lean': '4d9fda759e71a6cd02e558f26740f6726f5fad2de8f88c67e87f9273e8fa320b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveEngineConclusion.lean': '1f795a0cc9cfffe2167f612a422d824761b2eb85f6ff03f591eabef7adb48ac5',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveExceptionalFirstProfile.lean': '9870df932e600e7e99869171bd164bf1b1a694723499ebccd6c473e31031ec1c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveFirstSource.lean': 'fcddfd5741028e9f2064df460826a83c9fe50aa4b184f8b2a86449ef49ff2895',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveMainFactory.lean': 'b1680f7218d7cbbaa940d7e25d150a41f87c282084e5d28e51e6704af672a3fc',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveMainIndexedWeight.lean': '8503be8d6c704818afe2de320b669c6b0a1bfd82eb5f18cfd64e43f2dbd6d7ee',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveMainInput.lean': '0f35af0ad7e5c059b3d77912914082f67ccdf605f96f06e5c6a3f0e401b3cbff',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveMainKernelMass.lean': '45116e6e0846f0a182ca9f72d2f89b0bb2c08dc992a0b9dd3aa178bcca1dd657',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveMainOutput.lean': 'fc700114a4621f3fde183c36791e57d0e33c7180e8ef3e77fca1ab2f2fb3bd99',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveMainSourceIntegral.lean': '187088d3070531f8bbd534dc7a143838763eed0e367ad37437dae3bdd20fdc8f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveMassCoefficient.lean': '134cdc0155526a0f612afcbd3e02eff62dfdf6168bae5a9d53d1536d533e0b19',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveMassConstants.lean': 'e7c004ef63b598696aa8e928e1febcda2c1cbe4a0b12e1c1b208be5cfbd7aa96',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveParentBound.lean': '1894fc956af5b13de640402d2c7addb497ffba2f9aa84255c3e95384f81c5667',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePoolFactory.lean': '9c49d7b3c761689018038bab6924ca8673eb9616e24f5e5dc952bb63b50a36c4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePoolIndexedWeight.lean': '44951f1caf797450408b0edd15b478cffd50254915616716687499b050dcc3ec',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePoolInput.lean': '9871bca2de87ea15cab7428c511e8da961bb28ae06ba64c191039fa30208a827',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePoolKernelMass.lean': '3f4e216388650d86e25dcf1cf710d402edaf4716db933327335b768671f587e0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePoolOutput.lean': 'f90e551865675cdaf7297dc258e5a81fdcf0520facfafdcfa748f9e0d702a3da',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePoolSourceIntegral.lean': 'e5faffd49f2c1291716f66654ad15c761e4a7d28fd8ba2aa0a6b7eeb7cf465d4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePooledColumns.lean': '5a413fcef9a24657d2b27b7899b8b3229c08090e9ba92a1d8ff787661a8a7084',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePooledConclusion.lean': '85822274e174a7dd9499fb57b3feaf7b575a98d64ff292f6e5cd1a76d49ff4c1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePooledExceptionalIntegral.lean': '277dc8c9e5e98f5f43558145ed2a27a90fd104fa8a12a227a727fbc92e19a45c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePooledExceptionalSource.lean': '4c933dfae084754bf69755f2aa1060d77bcd1b84ec7484d4ef9fb74ae82c4563',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePooledFactory.lean': 'ea84ac029b5acc2b4d45e968441b6964081c6bd1ee1cd1d9c8e5fbc4b50781db',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePooledGlobalMass.lean': '62f5a4a3f6679eb6154458406164f13e9181c0b9c3a174987ba6ac56d83a3997',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePooledIndexedWeight.lean': 'b18b695725363c8762d9bdc2aee3811ae9994017edd11ef186b6f9b5f6d38a43',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePooledInput.lean': '0a3b82e0156f38c92bc839f9e873ccacde95aea50dd70831a0c5a88bd6a24836',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePooledInverseSlots.lean': '6c5d332d133b2d7b0a08df5e1df4db52247294ebe8f99a2912e1bba1d9507cc9',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePooledKernelMass.lean': 'f86b8f8826af4bb4252f26cc9f8204d949182160be9d71deffe17d94088fa633',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePooledMassWindows.lean': '06ef8606f2dba05f5f387c5a63356c85208191cd939983fc73e9f684bebff78d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePooledOutput.lean': '2a6d7fc4c93d92bc8da453225828d1fdf1ab337328639afff056b827a6d221cd',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePooledParentBound.lean': '2af6b4af4b97936af694846d79b75037bdd449bb524ccde85fc8b888c33ec38f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePooledScalar.lean': '60384cb7a0809ed0d2ae42d0a7bc1d34807f62294eda955149f665832c9b25e9',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePooledSource.lean': 'd851f4f31e2ea77f683b350ee9d0ff9d327032650f7667f56988b863f21615f3',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePooledSourceIntegral.lean': 'fa9250d83451a72450445d98cb6bb65f7250dc2b529a600173e8dfb39eab09b9',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePooledStages.lean': '9389cd8be586695fd82c90c66575fd4575a20447b1ccb4a9472ad2e5ab7ffbe4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePooledTerminal.lean': 'a048b366dfbd47150e451d05f3a39f70de4a6707678903e270c3ec4e3f3f9ebe',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitivePooledTerminalBounds.lean': 'c854874c7758a2038f48f85e0b41aa1f3df3033f66f63fd1189368d285ec1b70',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralProfileCarrier.lean': 'a48bf18ed8febe51c5f5e2f0eea2f46310a5d69ba451f47e843ff8665f2017c0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralProfileData.lean': '015c27fc438358637bcbe3660dc5b013316cb88a978b32b49ad0c313b0d18f86',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralProfileFactorExtraction.lean': 'e5587bb5974d141cf12366689f5bffca6ad562b0880cbd39837d9c8acfc3ffb2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralProfileScalars.lean': '67c26a71b42632c5764d76bac967bfdf301b40d88e4d1306d5d1bcdba2547cfb',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralQuotientScales.lean': 'dd71b36d9863fa273a59d4c2e483c5d1b49fdb98a93218f215723b9376f1222e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralRadiusBound.lean': '933778383078cc94ff793976fa887f42430c6367da6a77b4eb7fb8ed76ffa460',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralRawWidth.lean': '268f749dc73ebef9cb4d8e77a77f042225c0370446961ee8bcb26ac5dce6dde6',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralRawWindows.lean': 'b1c7f2f6765946777d49e9167431c2acf8b32f813159076d6225ae82b8b7b104',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralRectangles.lean': 'd45546114dd17f14bc535ce61226ceb4da17c45c79acc2a27734d5138b280cb5',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralRedistributedBinding.lean': '64e86926cc4c658454d617432bf64b6bed37b6bbf2e0ab85b9e32b0a1e2a8e89',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralResidualDeletion.lean': '398a7bdc415c15803e7a083f3877c68693951640c40fa353e4e96e4c814fffac',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralResidualDirectScalarCost.lean': '030aaa999d4161bfc9170d16a50f54480cfa47e3d9b21d5f37a6c5369bbcd7e7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralResidualPoolScalarCost.lean': '8e55da1613db93a641c4f9c65f491e507072558523a5af066216b98c8bce452c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralResidualScalarCost.lean': '678a3535ab1ab1ab871cb9e5ea619f39622ee80015d0619325f89b310f16277d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralRightDirectExceptionalBudget.lean': '13e8a613431f744e56e8ce1f52a1ad9cc29649a0d3a9a720736d9e679869dc8e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralRowCharacters.lean': '7bb99ee6fc28cbff2f8651f7bff7e5acaae171c0fc76a4b7bf87715c9e1d40e3',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralRowMass.lean': '2a1c124193c28c96d1eca93d8af2c0a84a55b0246afc4ae0d56925f15f673e85',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralRowProfileBound.lean': '9005bad13988eb1a118687c982469caf0ea1a2a083d2a24769f3fdbacc3a0417',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralRowSectors.lean': '8a479658b7f622e51e0beafe634f9ac459983faa78b94a6eb9df9b2d710c0b7e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralScalarNormalForm.lean': 'cdefd3f90bb50dc0b9dcc5bca8ba2b66f33a9eac889299f865edcdb9658b2828',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralScaleProduct.lean': 'cf99114b0b127c903027cd423ea5b099c3ab459a0642df4afa8ee60f64dc1aff',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralSchwartzProfiles.lean': '5085dfed3a99ce64eff46054c0e1c9e02c54dc2fc2e0cd91e457b1b0ad42edfe',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralSectorStage.lean': 'f3dfccf40f303a39032f0e01612cda7e853245d27623edacdf4b9c6d9de0e5c0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralSelectedRawWindow.lean': '901fe7f8f9bd2ce66b5cb0c8328e08036c107f9c2ab197348eca0c02fceb038e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralSideAnalyticInput.lean': '88244f56dccbdd67bb17f9f76dac944e61cdfc0065b5ba5c1b7df1b6960ef2ed',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralSideProduction.lean': 'bbd0e9d03ba2aa78772bf5177a3fad206f8b43a9b0c3974e05f1e8eaf5b79efc',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralSideProductionAll.lean': 'fed1ef4ad6923c9f07489ee857695323fd10c16fd9fc0692f44c8a525dd9edd0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralSideRadius.lean': '2eaaec8ff9f0d7475a78134d475c1f6e7afb1f5bcafb20037d082320d38eda41',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralSmoothCarrier.lean': 'a36f50ad7d9eb0c759df0f62ce7c493e9161556b82dc28af4ae5cebbc9f4cce5',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralSourceCoefficients.lean': 'b3d6f707f13da9eaea933fcde000d9c194742ef13cc54ddb1956249d328df232',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralSourceCoordinates.lean': 'a1155bdef39365d3421e56bdeb2c237ddbf3590fad4d17b962840b35d2dcda61',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralStageFibres.lean': '601081fdf4e8e0d15edaa12b8db7c860bc1d52236dc47d911d2ba1782024fde8',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralStripExistingBinding.lean': 'f089947a9db439adc6cc089bb27dc271c98343e137e5ad71e37e7c80e863ef51',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralStrippedCovered.lean': '749a7808e7fad7f80cbbe84529bde678f31a77bd9f1e43a65d244899be4bc2b2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralSupport.lean': '86c336ddd9e81c2ece9db9402301f8252e7b5e2ea5db465e14ec017034dee1e3',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralTerms.lean': '984194e405c741b8ab6355eeea9a83e632aa0e282cce10ab9aeb7703160c3961',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralTransforms.lean': '281b9c54d9a5d17cf713a5b29d0d950082b8ffd977556206fafe687ce14a3c55',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralTwoStages.lean': 'c08285a1af3b3f2d4dcaac91ec1fe48ca8d9fc52ff9f87497d1c15462d6cb6bb',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralUniformMassCoefficient.lean': 'f309f011d76307d2056310243e34a31a142c309f6cc416d7d9892969ec771f44',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLogOrbitalKernel.lean': 'cd0d7e8764ec62e938cf08ee62e36d34943c80e93e7b6166c24a4856b0012f0a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLogProfileBounds.lean': '30aae10806002d579936b09320b566e51ff5aa6a5a662538c7ea784dbef31f07',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLogProfiles.lean': '5806cf13076b665836e238fe02697a5a118db8b9b558290554fe03264e9bd40d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalMovingFactorAppend.lean': 'b7adaa4c9d4e85b558f1f05b4ed30589e13cc17364ee3e1f41b24dd97e80c37b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalMovingParentSource.lean': '38766b217de6327712976374191a70ca1e3ed102e2a9e9f014b057cde21d830f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalNormalizedPrimeAtoms.lean': '082e6a1828a4c4fed029d99b528d2b1ebfeac6a320b01b1881238672efc6ef62',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalOrdinaryWeights.lean': '2f498f469dfaf86e871babadc8c8418e35ef90a805b39abeecd04b801d2e6978',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalOriginalAtomPhases.lean': 'a326215ee3a29fb457b1fddbe69599bbdb64bf1b10d798b4eb6c3fd37672a930',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalOriginalChildData.lean': '58f9d1bf67cc4eaa4be689b07829f3a980909376df580848a0acb4bb4eabc93f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalOriginalDualFactory.lean': '936b16f14ddb3da2a2de20b398097ff27fbf5ce2ef77affd9ddb0b35627b6d71',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalOriginalDualTerminal.lean': 'ccbdd457e4aa8579783862c8c277030aabc4a2a31f4b51cd37b5829f77dc7975',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalOriginalFibreRows.lean': 'c5c0051bd55c1863be8c863e1d623896c9d4bb89c7fa4857263aabdb3ae16155',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalOriginalFirstProfilePower.lean': '6451128ff73b9113eb7600742d0ebe150999744b92dbbc3e26e92affdf4e7b19',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalOriginalFirstTerminalWindows.lean': '062e627a6c907bb54df5dc5c1b45779590a973654ddff74da12b39b3ad6adfc2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalOriginalFirstTerminals.lean': '766367b99a8f8a230e337b92004a89d739b437f69c112bb164339877c6b116b5',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalOriginalFirstWindows.lean': '137348617c0b93b2d5a59b24cd116606906dda3c90bcf527f14ee5bfaf6e755f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalOriginalGaussTuples.lean': 'cc0d6c0c677f32686a2378f5d1cb601580f30a83a3a8a42c0b0308919502bef4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalOriginalIdealWindows.lean': 'db9ce7c9c932eb22bfa761055b7d6fd7458a77ecede13277d5cce5bb7661d91a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalOriginalParentFactory.lean': 'dd9a1bf68da7dfdb65378312cfa47ae6bb919f8c5a4a0c6081a280944b872d81',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalOriginalPhaseCalibration.lean': 'd887870a4819f13a3ee105bbf2e1439f00d4812ac8352f3aa284b7136c5f8a09',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalOriginalPool.lean': '71c53d93c9f98f61042923e410d81c01c14db07ab3674525390457211462b4c1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalOriginalPrimeAnalyticProvider.lean': 'da0e4ff8da02358b1b85f9ea534a68b3320d4e56a63f6f8289c68bd54f1bad28',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalOriginalPrimeWindows.lean': '533fac6a4c6eec570a9bd3c96498acb40af28b61a9862254ef86116a9d37c607',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalOriginalPrimitiveSource.lean': '447e78e4e348b69afc08f6e03ba982aa92daf9653613b8c22960823332aa603e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalOriginalTerminalPowers.lean': 'a524db1e67046c1f504fd90861fef543cbc75dca152cb49fd075267e1d3c6120',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalParentSource.lean': 'b4a132c78b243a7d34c6823644566707eed4fe9e0681500a3f85920019964d11',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalParentWeights.lean': '64af5b042d67140b8411fb9d76217f1c7441e950236427b35b910b10b2dee076',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPatternChildWindows.lean': 'cac13e9ac44574e3fd1394ac34d32150b0277aa1783b50623c57a40a4e205dd7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPlainBackgroundTransport.lean': '12f4dbdec19ad2baa1b6b7203f29122a11bf6a271c7e79545a5ded66bc16c8f2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveDirectEngine.lean': 'd7b360c141037b4ddcbc828e79654bc46552f84f524bb39147ea63283d2c02f4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveDirectExceptionalBudget.lean': 'ee0f9993292954bf19bf57ee1e35800b36f67cb1ed4fc045a52c7c6685ff3350',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveDirectTerminalBudget.lean': 'd4e63625b9ec70fb17a4076790327a27604f85de6edb1414f1377152202d5f48',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveDirectTerminalWindows.lean': '61b7a2f7ced511a73c5bd75ce70e7cbe3dbe913ce108fc88818cff28f0ff05fb',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveEngineAnnulus.lean': '4692359a773e6b3e4a4ddc413e4652a8897546a243e323396c1ebbe71e5b427a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveEngineChoices.lean': 'f3e0cc3beb79dc464ad419d8125f4f37246e194202772988e8c72bf6153fd474',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveEngineControl.lean': '8f389ec92ad130cf36ceeac6b0245f167cd4773ccb87d1743055774f680f92c2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveEngineFinalBudget.lean': '4c761379bc19741d53d447d141ffd7ac3ba3f8f6b5c56a774790b93d4aa29527',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveEngineInheritance.lean': 'd997201f753eabc81de0a2ff5e009caf91dda339c7206c5d67927afbf77bab52',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveEngineMassChoices.lean': 'd3909907036cab4116654763acdc463c6d7a2c230fbc334caff5efed22668907',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveEngineOriginalWindows.lean': 'd161b8c54dc160d67863e07ceaa53b4b0c3943f4568e38fbf0246dc09d11874a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveEnginePool.lean': 'ae649a123fda09d7fce0b8e649e34b0d7cd152cff91bb49a42da3db13cb19737',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveEngineProfileOrders.lean': 'dbbaf7a5530a005621feaa508170aafb7c208a75fc16bf2aa80b0fc27574e436',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveEngineSetup.lean': '1004852773f747536c69cd80da061ef079de166b752a2b6e82574e7721c430ad',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveExceptionalChoices.lean': 'eba61471dd9013a0d721829e0f7a868ac9f88405e8bbe01f21d070fedaac84a6',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveFirstTerminalBounds.lean': 'd7dd4e14c340ce06dd9596c8700870e702801992abc183e9a8400edf80d12b86',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveFirstTerminalConstants.lean': 'cd9577b05fc862bed92015cbaa53ac17b1ab4a2d74c51dec9d0e35a5a5d239db',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveFirstTerminalNonneg.lean': '85335f8e43fb9e690e4833f041d56461c65d56e7f16ab751e766de6142663f56',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitivePooledEngine.lean': 'db9e7f1c581b784e9b48795e9527135edd80cd88aeb5fa7036f306730ec369d8',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitivePooledExceptionalBudget.lean': 'ff85a11724c9a13cb2751fb7141e2c4a8dcd1a784c59b2f47042dd7893636e68',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitivePooledTerminalAtoms.lean': '2fad937b79a250e0442204108e33012b79ecb41a48919f442c3bc942f2413a0e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitivePooledTerminalBudget.lean': 'b472b7f253fe5d545bea3abb2eb8f598c0e04e27eeadb4d8c76d3d2c81e25e5d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitivePooledTerminalWindows.lean': '782ec092d306eb402563dad258cd16ffb961da3ad79064be8f27d06c29e1da32',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveSecondTerminalConstants.lean': 'f66b9b66a5cf099be8876a730b71715acbbdc9fa1e4f611848eddd9da2ed6b9f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveSecondTerminalUniform.lean': '72a8e57796f528011a1ab2ae2b6e7d26a03c6634118316c2dfe5306f9bb4966d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveTerminalGeometry.lean': '7afb2b2f05a892ec26a877177f35826961e0127b43714d7cf9c47a11b093f581',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveTerminalLedgers.lean': '6889a729bdfcc0b2a6764fe9e475490f8e930edd3840f9c9a460a4a164f444c5',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveUniformEngine.lean': '2a87f41a4dc03755f06ae96ef352603f42a339813b405099860af61bdfcdf5bf',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalProfileNormalizationInput.lean': 'ea2c6c0effb966b2b786952f91a0beaa7d01d2e5437a402aad97ce06ec38205c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalProfileScaleBudget.lean': 'ee683f01852a4f83285d4a3174dcca1ea5ffa123f4b8acf665d6188bd62936d9',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalRadiusParentSource.lean': '7e7eaedd6973a7b820254e8caa510cd13d22c86d526d7ef0017482bfee5318e1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalRowBallChart.lean': '24f7fd2303ee4497415f9654db15546c4c04c7520b5e66452007cda1ffde0503',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalRowScalar.lean': 'd5126863078f30b2642c761c4f0bd60129702adc75ad1a1f7f3ae33c578aad5f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalSecondLogChart.lean': 'ff922178ce8dd2b5d37b1060501e40e7525706b18328d4020d9af86da7c2c9b0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalSecondRectangularFactors.lean': '4005deb1a37ac38403fae840b49d1c8f354fed4ea5c50fd5f11759f7aab621c0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalSecondRowWindows.lean': '29893057e0a7aad6cdb5eb3c8d7704fbed967697acfdf8611c631a4338d54bf1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalSeparateAtomMass.lean': '5794ff49590fe77ab0ce8ea531db409570e1d230c778a33e3918acf4a069a521',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalSharpDualTerminal.lean': '13c7ff49b3e1b7de769abecfe4c4993a732fd3227d77800b9651f7b40985c6fd',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalSharpFirstFrequencies.lean': 'c36a16f34bb61465ad876bb486fd9e3d4205b5395347159dc1b63f534627f2eb',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalSharpSecondZeroLedger.lean': '7d36ee57a34aebfade2192a393e636cd14b4ccbca34c7a6e32f3f85117613746',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalSupportedRowMass.lean': '27a8237232b313a4f92d6f626b81b38f9dfc01d68618591ab9235bcaa40bd772',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalTerminalBudget.lean': '48c9782766379068a6134a581b2f699e66b7a4f6d4f9525a19995f1b8336039d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalUnmaskedBlockStage.lean': '05db47e971aabb1e926452757502ced669c40fefd21e704fa592e79fadb006cd',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalUnmaskedSecondStage.lean': '6ca154d0dc48ae3194ecffed18b3691ec870505cc497cb3b20da5d9ae26256ba',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/Capacity.lean': 'afe8803e7fe57c56c163f5a2b84df6584ccf6efb9fbad611aa8b3594ba461109',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CenteredAllocatedChildren.lean': '97a0b0f16e7803a7eb6fe7198f1b78774c820cb475d304d06a6edc3006bd8d08',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CharacterRecipePreservation.lean': '79bcdc0e77629fd923fbed7553740b4c562c53abe505a75d13316274920ba36a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ChildAssembly.lean': '8d3b7c785934789a837371ec2c6e7232a136a16c7763ad6f02f3c2060dd23bfb',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ChildMomentDataAdapter.lean': '1e7dcb1995557bc809b7a3f01bdddab942db6db538baf2f675a20546b3063086',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ChildTermDictionary.lean': '23103c46a6b76e190e43b710c88bcf46e4e13e25ca260a8629689e9534e599a5',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/Coefficient.lean': '18488694967da3d55b23c68a5df1be49096f4b5cccb30aeabbabfa9ca6970ecd',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CombinedDirectSecondTerminal.lean': 'cc4e38f60fe8611d566de4ae2ade014ba3ea3ba313e753362114e4d21d584743',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CombinedDirectSourceTerminal.lean': 'b983cb1504090bfba61db12391ed88aaf96335b8d67b2c5abaa24d717f4acebd',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CombinedDualTerminalPower.lean': '57291da3d986cd05f04feb6e609953244206e84f1fbf7226bdf182437d9197cf',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CombinedPoolSecondTerminal.lean': '3fcb2f1a90be595a519ba9a1513913f4b63a79b30618ba1dd9e011de3a19a4e1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CombinedPoolSourceTerminal.lean': '3b815fdb5acce44d8dd90591dec88d76a4462d6436163bc4c4960f03fcb2801a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CombinedPoolTerminalPower.lean': 'd3bfbc458d549348a6666cb1c92a138816cb9fa81fb4a92d7a7fca8c3ec5639d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CombinedSupportPoolAtlas.lean': 'a10e77fdbcb7b37cee0f5a7147c9d0912766c32dd42543bf5762395f850a12ab',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CommonCoefficientExtraction.lean': '0180816f8bc4b61e6672121c7b80e9a5f178c3838b24734f92d8834c4273699c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CommonFirstOrigin.lean': '14a3be2e18bb041942bb089bd2906967c12d16bd533d36bd7670c144d41aec04',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CommonGaussOrigin.lean': '801dc3f42b9979050b9db38b589667990bf7314a2c3b21781bf84dd9ee9d9e4a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CommonHarmonicMass.lean': '104d0c157d979dedd9534fc74ba79e039598f3c58ff9e94476b57e8d79d667b4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CommonRadical.lean': 'dea66dd26ae9e657fe8e8a8d8f20d620199dd24c4a3d860abdf16822e21bfe2f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CommonScalarReweight.lean': 'e6ae277f78e9656d0146de57c0426645aead2dfa224106ea7caa7f9f622fb567',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CommonSupportPartition.lean': 'd4f4b603a71824855a5e009759599ccf85963fab82efa8eebc8753cae098852f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CommonTerminalCalibration.lean': '804e3b21740954fcdafba49288a0a27aa28bcebc9292f8d44831a277f2e09a34',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CompleteEngineOutput.lean': '4b8c56f5d4b12e9448aa8591d60b51cd00515e7d2ac66cc801622192485b08e6',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CompleteMovingRowRecipe.lean': '4a789f822374661f257682c1c3ccf3c4eb025546512f9e960a63ada706c599a4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CompleteOriginalArithmeticAtoms.lean': '2f19244828695e9584f76478572c7dfcce45cb593ed974ecb09e892f0b690eb3',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CompleteRowRecipe.lean': '6905f2a1a41b56392639247e542f81ed8c91c9b6f0deff203b073663357f2270',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ConstantCommonLeaf.lean': 'f7df02d24d9c6f66ccff22e9fc3c2e043af91a810c93e98f529c592927b54ef4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ConstantProfileExtraction.lean': '86b901e36f8bdf4b2d73fe8d7c5a673558613e2c002a7baddbe22801335be7a4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ConstantRowWeightOuter.lean': '446110fa232f84500319861e502991d7057ef1f968adc9d75edacff6937a0f17',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CoprimeCoefficient.lean': '64ccd35ebf33d9ee2d262889696156c3a75067c8bba6e16fbecf9e056b833790',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CorrelationKernel.lean': '75b953a93ca96be104ebfc6fb85162f7feecc7904eea35df6049f6e442c9dca0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CoverHybridPhaseIntegral.lean': '44883b0dad17336f94266ced1a7777c8a1ad0f28c80aa6f8f6b25c42ff7712e6',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CurriedNormalizedFamily.lean': 'c45a30148e3bb4ff921442836540076108136b864f81d952d4efbd34d1005171',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CurriedNormalizedIndex.lean': '0c37d9191e5943172df905e9cf23176baf6fa90ea2b7b636ca92642144b2cbad',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CurriedNormalizedMass.lean': '9356ff5dbc178ec085d9811698800e3d85a4ce51c572aa179c78db7858e0d50d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CurriedNormalizedOutput.lean': '0e6ce3d0990c1bc09cb64c03e9136bd6f661c4175c126cc8bea682b840818ce2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CurriedNormalizedSource.lean': 'e0e14d85c9704bdda604ec785abd9f7f04239c5461c5bb83c6b4bf904becf33b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DependentNormalizedFamily.lean': '74a59b2bb2e162311994f36a7cec7a7c497c57e664cf2f8f3da3af0df053a527',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DependentNormalizedFibres.lean': '4615f958c912fa860bb643cca604c7a9f632ecb1b74cfa251aaa5efb7ced4468',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DependentNormalizedGeometry.lean': '6ede1000edc70d15e62f44b23ba257ca4b00f01095ee814e91388bac139bac15',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DependentNormalizedKernels.lean': '9b2edf2baf53e90c1c36d4a79e459110840850f092bf68899532fabca58395c5',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DependentOriginalArithmetic.lean': 'd0f7fe17fb41081d0244cd5435694f4a9820f60660b988fc10637d8732d4e22b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DerivedCapacity.lean': 'eb08e9f4e2a93b1848fc4c25b5ef3e3df7542ab3cd9a7e94f54d5f8dbf8740f0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DirectCoveredFibreMass.lean': '678330bf989c6b82616434941afcf46589c904e925864ef99e654c1a324403bb',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DirectCoveredStage.lean': '243ed35cc7230b41cd4dbaae596b1332e98da6707253d08ba7de58c4650f8372',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DirectFiniteLeaves.lean': '6cbe6b97ad293729d315b12dd98c965ace3624da3af363eec636ef23ca7a957f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DirectFirstBlock.lean': '27da700bcc9a23913399cd38845578a209e6a63d3385345536f1bf2cfaa30651',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DirectFirstDualTerminal.lean': 'f0768d865ab2437091533df04b289927f55c47fe63483f6e550417f17e350daa',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DirectFirstReduction.lean': '0feb88f6802be5d5568484cf1637bb83d5eff10d83a25598294320f02d63eace',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DirectFirstTerminal.lean': 'a6a0dea715bd65a6568af3755144728cff07cb7c0758a1f79e02528bdf84cc3c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DirectFirstTerminalMass.lean': 'd297282122bd44f726241fddd21d0ad1342249abb3199b8196421ce11eed00b9',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DirectGaussSource.lean': '812d5035b1f52e6c2586afe9bf01b98c284aa2c92577f1f241e837960f4b30b4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DirectLeafArithmetic.lean': '43d94c960cc8f5ebe621518cc438223060b5a63dceb54b813f39af452b7ec14e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DirectLeafNormWindows.lean': 'bdba7d6528fd3b8cc5112dfd17bab073e0b9810ff689c28ab4e9f904057c5265',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DirectNormalizedChildren.lean': 'c6294356e1056e93445da000c57023ae2535f73ec2a5c8325a9c56538319035c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DirectOriginalData.lean': 'b9aba763c67e83aced48cfacd49a40814de63138c16bd558172717c019333a49',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DirectParentFibre.lean': '3a31608f2b6776001385e2719f6f9f57e1ad9cd61ac30db4bb6e9ed54c418194',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DirectParentLeaves.lean': '453ba2c62e6c1c40f6005ea03ab19197883776ff1a4bf9cbbbae56511c45d24b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DirectSecondSourceTerminal.lean': 'd12976d8deeb7b20520b98539d319739516585560cd196e9d74d35826c2d656a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DirectSecondStages.lean': '824f2f4b63fdca90db17136ed92b13131e7df6ecad6ed71dd28bc2150e8c0750',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DirectSecondTerminalAtoms.lean': '14e13508ad3f25f4923b7e47dfe0d931052e5afe59ccdb8bc5ead28cdce7ede1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DirectSourceCover.lean': '60914ed00ea6caaa079f87ef92486960498dab845162db275ca7ce3170d6a9ae',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DirectSupportedLeaves.lean': 'bb7caafc0f6caf14a22d56446beba6cdd691513e38f5dffb9e7bdeeca250d0ef',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualDirectCoveredStage.lean': '2de7bf5fa561ae25616fc1705345aa1a4d0b1cec36a702d0935fd65a97fa9641',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualDirectNormalizedChildren.lean': '252e882b4c629e7c81c68f527e874d0c12a6e1f9d6153b65996429c2094f64ac',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualDirectSecondSourceTerminal.lean': '9fc6dcdabb27cd403e9d286d7d86033f0da897c8bcb6c48bea97ac71a1709f23',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualDirectSecondStages.lean': '27b1fa02a664c7945ac5ebb1f1bafb3316f02a4eae82a7e811d03dc5bae6ddb4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualDirectSecondTerminalAtoms.lean': 'ad20d907165f858d98f871e0037dd34f14041697899f47ec796f9ec66ff7b257',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualFirstBlockFiniteLeaves.lean': '0e72993cc08991f80ee208c534a22207aa26acea652563fd281c121547c74bdd',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualFirstDivisorBlockTerminal.lean': '7cf9595fbce8764b1d791ce0b8bb4dd24994d626088d1af310662c19e7bbd9cf',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualFirstDivisorSourceTerminal.lean': 'f368b114786e6fd2927eba334429b548b9aa83d9301063513a401acb4001f75d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualFirstSecondCoveredSource.lean': '71c3331b6844d2831716aa3a11b9580091a5657ff6d3a19cb8321454fdd34e95',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualFirstSecondSource.lean': '63c4a673042fd9b2ebe5bdae1cac4e32a8614c6095edcb52c10565670b5c5fc7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualFirstSourceFiniteLeaves.lean': '5726febddae155c207ba57f55efd6c609a793027b0a233c302eaaaee7176ccea',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualFirstSourceTerminalNonneg.lean': '53c2b62ce479e048a7482ac3f56f10b28bc7a40e25bdc9e971f5dedd21d9b84d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualGaussHybridTerminal.lean': 'b2be306ecb762e87a7ccd695a3cd870e438d74b7e5eb1cb32396f89bf24f4b06',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualPoolFiniteLeaves.lean': 'c1155c75f88638abe593ef15c4efbb087530766676972616ce2caac3fe084d40',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualPoolTerminal.lean': '6ed0e4b059b95868844d2f29b194e127ea7c6b3e27d0f9d55081d87a64bb7c1f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualPoolTerminalMass.lean': '93745ccc4451fa797f52155e86b3d2174f7479b208cd6d68ff604f76848142ad',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualStageTerminalBudget.lean': '2b7af10a7ea7c644ca993437c42d1c208629937b8e16a44eccb299abc546e354',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualSupportedStages.lean': '131f8493cc23761d9ed9520d01973c200bffef8ec25a1ce8d4daca12d6b2edef',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualTerminalCalibration.lean': 'd954870a0d0bdf9f7fb6ab6a7013c45888d4f17b6432905db17bdda02c0e265a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DualTerminalPower.lean': '93583ea52b9350daf5bc6b2e2a032cdb86d21ce48b337eff3dca4738a2804db8',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/EffectiveChildSupport.lean': '611d554ad36d60e85f31bc3d35a123476dd19d2edd73e360f767b09be6e1d835',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/EmptyGaussMask.lean': '31b63106785fddbf263a4a1ae02f72fa8d47baa3fddcbe9f52af3a1746762284',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/EmptyParentEngineOutput.lean': '5ff1813f6a134667d6d2c57cb8e10cd6239d876b2d2e0456957206c1120a42f2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ExceptionalAmplitude.lean': '3ce86a9b6ee2e8ecde4008361cde52e65169e86ce5c23de123d1f604607ea958',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ExceptionalAtomBudget.lean': '32d972d268f6a1e879e97ea7b14a90db2f6af875849b651612093574cc24c12a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ExceptionalAtomEnvelope.lean': '36e1ea9c491cb20f62a3a85020a53418bfbe00aec25d21d59850e220b4c8be8e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ExceptionalFrequency.lean': '432a3dc6d31d6dc601d9ae1c165fda8d57ca4338bbc2e3683cba6cffcfcc399c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ExceptionalOriginalAtomWindow.lean': '3f699d4bd0013992356c5576a8a6189c6f3e2e912ba8d39532d110f8147d88f8',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ExceptionalOriginalIntegral.lean': '1a5010c056f811c9337712994a61cf41bb979f5b96f51c1408a438c8b6bafd6a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ExceptionalOriginalLabel.lean': '27f5c120aad01282a962c3c30d4ca55f689dfc0e60e09d04ceef979fee8b8278',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ExceptionalPoolAllowanceTransport.lean': '75b1e27bc4236c4f3646d4479c998cecff2242fa6116c8119de6a30ecda794ce',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ExceptionalRawNormalization.lean': '801ae0d26a5b8743a18bfe04901b2e029b71d5c57761d12fdae3cc4bdfd060b3',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ExceptionalRelativeBudget.lean': '22e2a0c7de4eb64c55c419dc9d46000be5e6db9f611a93a52c27bffbc40fef6a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ExceptionalRows.lean': '97653451975051630e030d7ac725a853d75d17a75581f46243e6490ade4acb30',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ExceptionalSameCarrierMass.lean': 'd21b47c9f5c11359b98b2edfcb348c7e5c04c9c3df0a407559312bbd3b422cca',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ExceptionalSourceBinding.lean': '7fb562d3c9c6efdfa4add4096b194cb2a5e93468f42d30ae9559fa4df42c859b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ExceptionalThetaPartition.lean': '6f987639cfd2934c842423ce2b35578d34c513a851c297ca3023eea871cba5b3',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ExceptionalThetaRows.lean': '252e0e38087ea3a99b9e284479a91448e94ecdc7788c3f31b6afe56b8b9cd2b6',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ExponentialTiltSchwartz.lean': '1c45b122d78506ae7c1ea24700709acd6ecfa33ae0bcf065d0dba2181bc67980',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FiniteBranchIndex.lean': '238f0b27b692a1eccd6abfa85afda6951829f873e17f2c572b54b072d9746adc',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FiniteBranchMass.lean': 'c6fbb7c1d907465dfc85b1fc35dd49eb0fc5d9280d3dc30d6da03047bddde014',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FiniteEngineOutput.lean': 'c756efd660e0d07b012dff9f4ec78714b2bdeb933b2c3055d7a85b9a7d1d9cc7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FiniteNormalizedChildren.lean': '19a72a11d1f18cf6a9312e6af45a1456acca3baacd38b3ce8c3d0502d0a76452',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FiniteNormalizedProductFamily.lean': 'ffb420cd1a7e6e7e971e43ef48c1e0ad3ee333691994c1d2aa28da2bdf933e45',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FinitePhase.lean': 'd62af9bf2239ba2af37779b564cea80129ab08ef7a80abbb0f27cba11e801a89',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FiniteProductGauss.lean': 'a46cca3aa980fccfea50e9ab7b7911f6def6ae52444b0a8c81ad50d6ea5f5c48',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FiniteThetaAction.lean': '2833b93db06e4b60d43e3bc5abc03ecea4971ccd89f52d080ae12e7ca9c2b62b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstActiveDictionary.lean': '364942cfa67cbf35ba4a2dd841c410493f3c0cf00dc249ca5c355d59713a5562',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstActiveDualZeroSupport.lean': 'd3b3859108245754192c7344d096350bc9e2d2fdc2eb513b986a9268ffcffd79',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstAllowanceNormalization.lean': 'b3bf5df6acfbd150565d3db75960ed3decce62f41a0175ddafc7b77d2792fd79',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstBlockFiniteLeaves.lean': '499a93874358abd2291adaa6ebaab1ebd2ac993f88f799b5fbb67c3eb990a11e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstBlockMaskCardinality.lean': '622aa0e9cc2af14067292114e4ed24fec10e1223bf0087730e7ef4612650a741',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstCharacterSource.lean': '59e91672ccaa4a018ac56e5cd8b4d2579e0d1280dac13a03c49d372fde6fa90e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstCommonGauss.lean': 'eaac209a18f01f27434fadc24948699c65e4170835fa66ea7446c41c55e00cdf',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstCommonMass.lean': '35705d812d04ab543ecf0733bd1a11b63a4957f78f3df57958a60e5450f30258',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstCommonNormalization.lean': '6097804596a340ba504c8934742b968e959dec889c97e92ac6441821ee1d67e4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstCommonSupportSource.lean': '48ee928520e29c17f951040ab4bb85f08bf27c23cceb50d0792e4bbab9a988e8',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstCommonTupleFibers.lean': 'da464105f0a196221941d9882bf0dfddeac1443ae3ad90ef1b8e631fc0e0d9e7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstDivisorBlockTerminal.lean': '0138c435f48a9e323c8df08aae254120e03c72e2a9ab455430845dfab0b7cb4d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstDivisorFrozenCost.lean': '41d167518900d7d4bfcf8d3755ee8ff860a6a6cad19f4546d70ea5745899842e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstDivisorNormCalibration.lean': '952bd6130c948fbb847edb95a1d3f258d2cdceb242194b8b1b6e0539f721cd14',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstDivisorPhysicalSource.lean': 'abfc2b370917a690068212b805a519a347372bf36d6d4f22b5349202c3908df3',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstDivisorPool.lean': 'dda1a00dd8d04193154934f45281f45cfd987320e28c550db45c68541bf07e5e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstDivisorPoolTerminal.lean': 'a3d18156bebe86694354b26a1c74884723df14b80a389257cce8dceac91ee814',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstDivisorSourceTerminal.lean': '6c13b056fe7bb683a1c9a41d9866c6cf2041bdd6d6c2e23cd01d95360fc890cd',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstDivisorTerminalCalibration.lean': '69c2d68309e50d9b548f4e314c2611e2a809256edf9cdfcdffdc06830283d334',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstDualOriginalExponent.lean': '7a11987de8b83c531fa2859be38c3bd4ec737f2c6e24b7768ebe4d8df17f4854',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstDualTerminalBudget.lean': 'b89607e3c25f19122037f296943db5a17050dbad2e52d04df01b78f2f80945cb',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstDualZeroSupport.lean': 'c9857a07122a02a7f52e1667f998ffd49ebe377f5f6c1ff6b0898b6e3cc6f1fc',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstFiniteSource.lean': 'db40b6d6348915719ce2286082f4fbc89fb224de8253e46aa071b841f75747c8',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstGaussPool.lean': 'a78b5ee229876fa68c248a0092ac2d9345ed719c1230d501a9dac6dc990b5059',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstGaussPoolKernel.lean': 'a6c4a14e5baa281ce941658e59729e12e5253675995ff972a1cc37ff1f5638b6',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstKernel.lean': '7541c06b82206f0f36bf06812cf1c045e24ef85b344dd12c5b9c15e123a56e2c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstLinearizedSource.lean': '72204e8c1112154c40e79f53576cb3f3ce8999ceb14c236011caf9520fe4c290',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstPoissonColumnNormalization.lean': '114e79f0062993fc0ec10557a84b499795d6935af1bda96538c6df036cacde55',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstPooledResidual.lean': 'f198cfcab140d13aaebf0ff9b29539e1c00eaf29ffc44f2a6d8d3533f7327c96',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstPooledStage.lean': '7d796a5f7d44c8a70d80217d7278c376e1a23258c47ca1454b29dfa5ca02641e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstResidualSource.lean': '6c637993efdf5f61bf0867dab45bff240c0e6fbff9bd45ae8af0c0dc8cfc1574',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstSecondCoveredSource.lean': '831ffdd21c287ce4a7f06ccbb9d481a0f4cca7a65b62266b3499587ae5434ecc',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstSecondRawSource.lean': 'bb9418a42bda66b9de3cc3add18e8a29d6a72320673f06518c1da0e25e047d82',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstSecondSource.lean': 'a56b713cabe75b99f308d3b04c2789bb8edf9a7db67aa9edf4b403f64a204a65',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstSourceFiniteLeaves.lean': '104792224d72db08b175bbc3956f1abcff71fd79c3ff2ed92124680a29408791',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstSourceTerminalNonneg.lean': '369de5ef467dfc46d61476df4a0484715e829e449a6c0fe2cd8db3053c0f2d21',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstStage.lean': '0aba764a2787ef3fa39ccc8e1befef8946d64842507af5afb48dedd3723f49a4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstTerminalIndexMass.lean': '3ac075c0a668666a75aaa251b8814ece11892981d8578eb4f106c6b91f062f3e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstWeightedReduction.lean': '3b30943b0e4be0c2d99aa242e1097a28dcc3ab7899c1ae129c4bb1eed113b378',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstZeroAmplitude.lean': '9ff72712351ab57f911065b9ddf8847a0f7e82b026366ec22b446dde3e837286',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstZeroDiagonal.lean': '5b0a78ab63fd1c2833beb6f386b7f8710099a05a1c0e9fbe6205ffb2ef7571ec',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstZeroMaskSubpower.lean': '0d3ff325c6d1715bb365f7bdf7d012fbea4e3038ebd017d65b9af6c1d0b951d2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstZeroSupport.lean': '591202f1693eb198a9e02d65ec303d393aa15f8d8c939693c93cec1c1904dc5e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FixedChildFamily.lean': '09e34e8301c7998e0a5090e08a6516ce81df931a14c79200bbbae8754cb06d7f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ForcedPowerfulDiagonal.lean': '6967dabfe251abc33804f752ad64f2a9baa84ec2b8b96a427dd978b9f8b5f51d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FrozenScalarMass.lean': 'a806f08ca8a0d5405846927bbf5970675c419dd774c477e73c80ff2d034d1198',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FullSecondDeletionSupport.lean': 'a0433df6965efe3a680fbcf4cf95955912c88069b7f9f41e4d4db04843ae2d19',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/GatedGaussStages.lean': '74103e801a3bcb1326d9c9dbf5f7b4238b66e034bba021436ad5d7059faf1d96',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/GaussEnergySource.lean': '58d470fe3463ae86543543b75d2aaeda87e10b76ca4493a4dcfedde419718699',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/GaussPairTransform.lean': 'd2eb52a4c576670b56316b9561e50b06b071b26542bca3a6f66d1cbb8d1d170f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/GaussPhaseTerminal.lean': 'e6432fca1500c7ed46bf2d8d5aed2c763d372f7db5ac8aad7dd2018abe7722b9',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/GaussPoolDictionary.lean': 'cad391bf04567ddc8556c7639af1ed0699ffd6b273a87c8d5867f055846c4468',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/GaussScaleCompensation.lean': '9e10f170367596f67e4306768ceb080a4eba17e9f8d29735307969e2dbbee400',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/GaussSource.lean': 'a6830ad272d546ec682457d916fdd58b52f81a43a02260c5c053cf7a6c69f045',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/GaussStageKernelIntegral.lean': '8905fc7e918f2ad85e7022f99584ea754249bd1899fff121f63bdb5d7d166422',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/GaussStagePhaseTransport.lean': '8c590ee571e30e5b0e51221a32e0fb30aa5107cb6be306fc09f602cf02b70dec',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/GeneratedCorrelation.lean': 'a9954a4895cd9b961f3dc11d887845af4c0f70b714797a0009eeb52aa3abdca9',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/GeneratedZeroGauss.lean': '0e38d05c180923881046fc14dfe66c062593bd54f1ac9c525d7615e08ab69b13',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/HybridFiniteLeaf.lean': '6b31d140726f2840ee28eaddafdcfc4b69a614b22d4841c8ec2505fbb10506e0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/HybridLeafColumnSwap.lean': '91de4d25fbcf46d710f8e4e62f7c159fa98a3a0d5416f6b057fe937e109e067a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/HybridLeafExceptionalBinding.lean': '8d981feeb6b4f1ed890cc8f923e00653ced0ffbf1917b94cbefe091f09598e38',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/HybridLeafOrdinaryBinding.lean': 'ebb42ce6f98e2a9857c7c4273488046c41dc7577bf295247857ec02cf87cf4ec',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/HybridLeafRowZero.lean': '9ee5b1c1c9a083fc15367c6d2e936255473462471fc9f126ac9531c55b3ff190',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/HybridLeafSupport.lean': '1f7ddd1741d0165497ed531646ae26a10927b2b8d8f29fa8abeb7fc6451155d2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/HybridNormalizedProduction.lean': '8e1ae2c04462f809d8d8f72fe77d134c69da0a19b66bf210890860225ed90af8',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/HybridOrdinaryProduction.lean': '548f779ba6abc5997bba64341fa86e0c8b8bd712d39fd376806ee620cd39576a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/HybridZeroRowSupport.lean': 'a157823180da41ac60c9270626eb1f2bdd57ae3ff5573369295d567d65d26358',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/IdealPool.lean': '92535888ebd2a4156e709addfde0f559fa87674602bbbeed7848df159d6f22bc',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/JointKernel.lean': '086b04d6a986e56b54ae640d8c35a5ea74196bdb6a12c0b679500be7950b8b83',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/JointKernelBounds.lean': '3fdb156c2ce7dc0a4345207118702a140c713ad250e5a164fe6a85c3eaad3865',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/JointKernelExceptionalSplit.lean': '93ee7a65a0320a92b56369a792d9035dfebaca816d21a30c2d7b5ddfcd184bc0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/JointNormalizedLeaves.lean': '08866b50ce1c9fc3c945977e76972e76620672f813ac7d4d0b1a1883fc921787',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/JointRowBudget.lean': 'fd2b8372edfacb687d68018aeca9be31c393742bdb53d2eb103e993d8803120b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/JointRowBudgetProduction.lean': '85d9fe7c86650aae4aded5d0679f83b61ce33c3cd83df9a3e32781fa0dbc2b30',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/Ledger.lean': '54378988612a95e65e1275cd9652ff3a47f659db5df22192201aa87928381b40',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/LiveSourceConditions.lean': '1d731676176a0eb92cb04f376db383b2ec4f591bdcfefcc1f1523f41f451c3a8',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/LocalAmplifier.lean': '9ec335750270c2d8f711cde5cd1b5a3d7dc3ccb69558840369af5f6dba2475d5',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/LocalCRT.lean': 'e153ca3345dd682b7dd08307fb28150aa27805f40b497db1236da2f3b9bf4c50',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/LocalCorrelation.lean': 'd340279846d99ae441f66e26f126ebce65eba6641f9d166bef2c64a4310aaaad',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/MomentDataAdapter.lean': '4353d443440dee67c8b9b93adc4fce1f61361ae1ea830534c68af6b02d2f7c0d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/MovingEngineOutput.lean': 'b9273892533ae9fa33614764969c5c3e26f945ae4d2c4f8f56da42e06e8abcaa',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/MovingOriginalArithmeticAtoms.lean': '38cbb7e59aa83b59d7ffab0465379a8c75c6a7722416493873373d24fb1a4680',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NestedCommonMass.lean': 'b39f077d53fdf98577161a20bf2ce283f31059bf88a939c3d4e031fa4559abff',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NestedFourierMeasure.lean': '3c55a6dcb90d72e28d938a10c05313db9492f486947c910ba18fdd55e220d5b4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NestedHilbertPhase.lean': '385031a3d13346323bbc52cfe623db86634e30e7f1fe952c588715f01584435a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NestedHybridKernel.lean': 'c1e5df911df2451e621c8c984bcee6f6bcdfebc6e6aafaa80afde65ca9f40e3a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NestedHybridResidual.lean': '2245d6eeda7a34102dcb14fb9715624cf1558ded0aa865e9b8f0b49a7029e1e1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NestedSecondClassProduction.lean': '8103cedd33d1f7f0e2c8e56a381773ee6fced0c4b35eb86d17e4cd53442b2a30',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NestedSecondResidual.lean': '1ac29a7b78fd484d4ea80eb089e429330439df6b04045cbbf8d33f36b3426d0e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NonzeroQuotientSupport.lean': 'ec69fdf0d3f5090007d153a0df8f03752f2cab476965592a5b37c505fff41564',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormCompleteEngineOutput.lean': 'dab7339275ee2b1cf1122d85ad7572eeade3f02c465bfc1471cab83ee1d1452b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormIndependentProfiles.lean': 'bb47047b4183a9badd14ba787ff10d00d2458e35dba05352404892b9909957d0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedActualCapacityChild.lean': 'ad695692360a857299d0311001435d74231225fb33ef0cc2c7d9c9ad7a6c9732',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedCapacityChild.lean': '0663e09cc3609437fc2942e6d02003b585b26ba2a32811c8501ef64ef2f03af9',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedCapacityMassBridge.lean': 'e2db1a8dea9311720cf86460c2a2a77ca26cfa4bb86423c1e8a894bf61400a87',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedCapacityRawBridge.lean': '3f836167bd61c4c30aa1f18490a2976e8f6f0c4b1f6987b594e95261648f734b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedChildKernel.lean': '53e6fb39322169b2e364611a6789b50310222147338e3ad0b3fdcabd015dee83',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedEngineOutput.lean': '16486c6bf4d27c534277b3cbfebe55f43bd95222457356556791ad14d010f3f7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedFamilyAtoms.lean': 'a3db865fedc5b5e66bd0a1639d84a656758e11955d6cfb9188ad8f62e4f02196',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedFamilyBase.lean': 'ec1b08e756dd8d4c358a1ffefdc765a0906f6de0005f31836ddc714913eea097',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedFamilyGeometry.lean': 'f0b7c147fe3f7f3ba28b844ef7939976b51577aaf5926827a54ba31c3a4dbada',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedFourierChildren.lean': '453df343e8988bf5de8b6bfe424cbc3f840c2fcb4df25e6dfb89cc4a32f7e51a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedHybridGeometry.lean': '0561b8e8cc68fcf0b81361ff89d00f9b1a6cdc1e357708af29519f7d137b8913',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedHybridLeaves.lean': '481e544998139ad2e5680383c757c1d4b4dfe48d69a39d64218b65e2b222c03e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedIndexedKernelMass.lean': '88b6c4339279aefde70d205282daee510fd9c6359ec1e55514bb39ad5c0edf8e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedMomentProfiles.lean': '3e256b726acf33c3cf4f8c1efc2a60696a683ac903cef7f4f8cd75c821c8cc26',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedOriginalFamilyWeights.lean': '9bce546fa36b4786367431c3c6830a49e22b1948705651830a43968e9a693597',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedOriginalImageMass.lean': '50bbe521d52563f93352811be71aabb3aeeefd4eadb13e7fb3e96aaf9735f59c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedOriginalLabelMass.lean': '17e9e76cd4644fc83ed6940a55c771c629d47f679a9a86033c991ee1dcdf900a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedOutputConditions.lean': 'd8f22913fad71b26a44aa4c518834ab1f139fb7f03f6eef9ba809dbc34f02ef8',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedRectangleFibres.lean': '2430180094b0b62d592430367c45b6b919592f4466cfcf8d15cc2695f1a71bdd',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedSlotRemoval.lean': '2c651ac42fb17f3e28fc13262e7e1ef8a7b9b2bcd829e6d8ca53651c29f69fed',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedSourceBudgets.lean': '5804eaf3f8ea73dc92e1533853e456cf61b98b48a8dad5b8c5c2172b73df14be',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OrbitalCorrelation.lean': 'fa757ae49a82918f03b3571e157af5f6e4dddc88556daf46ebb440c2f671a7c1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OrdinaryActualExceptionalBudget.lean': '4e8d88fa8a2589606f37704db3a8efbeea61abe965adec1a273b874cecdff3f8',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OrdinaryActualExceptionalTerminal.lean': 'd05c3863dcffbdb3322ed877e2d44b2f236dae9fb32b59c700b41fa9297ac0a7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OrdinaryExceptionalAmplitude.lean': '0e144a373803bda37e8e345908c9de7f40c489521e71d1bfa321f2c0d987cc5b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OrdinaryExceptionalContribution.lean': 'a44f3a33faab8eacc22cef1fb2a9254ec34c4150a8e249139b15b073c64b9c63',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OrdinaryExceptionalLabelIntegral.lean': '386bc0f0cef212f23d39aab53cd44c76a3749df27988dbe05ed5eb7cfae3dd55',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OrdinaryExceptionalRelativeBudget.lean': '5a92087f2e95770b513db47013a3b47649074f32c71f4233b02a150b818b6f2c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OrdinaryLiteralExceptionalLeaf.lean': '1df8f9bec7cc906a2c19c5b0a492f99b28e6e1f582f6eb01041b5d0b8a279fea',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OrdinarySecondExceptionalBinding.lean': 'debd1cc354d1ae6ce48401c804efbebee4b240eff3b361f039686cb999c087e2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalActiveColumnLower.lean': '9f8ac18c1335cb75683af34fb02dc573763ea0b9af0de841a3cb6261469c7ffb',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalActiveColumnNorm.lean': '5bab667ac094cfd38b40895c9fade58409586aec5145cc1404af5c44bdb0f265',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalActiveColumnWindow.lean': '251c51842febfbb8a58ef3d55a7af9874a5c2cb1d50c8f829b6b61c7477b84e8',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalAllocationFingerprint.lean': 'b50f21a68cb572860a4a46fbd8520981e70a39fbe5016d51faa05f1bf5c2077a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalAmplifiedCarrier.lean': 'e2cc3d9d07b165cfa3d7529e2424048d93e7a5ab9414fb72e78366f98ce74768',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalArithmeticCarrier.lean': 'f8f9b8fe1fc3e430c330da270b924e5a074bd9ac949b21289610782fa34781c8',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalCentralCoefficientBound.lean': 'dedbd5394d13397fa3784de87f08e604b3935e61c6fc5e4e2abb6d225c76dce4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalCoordinateSubpower.lean': '6323376a01e02bc463c47bd62a3d4e29b7fad21d32dd0b213855582cbffcf52f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalCoverCardinality.lean': 'a898003612d5e64779ca39a84e3e99bc52a4f1c2c9af4f4e480ebf1cedb98873',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalExceptionalExponent.lean': '7d85a16ee182434ffd6e69f2fb7b6bace51482833d03b79b77c410bb640a085d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalExceptionalPlainWindows.lean': '2aef63fc63a105cc0a80b3fd7413ae1b7678da9e64b9372e383e56627f52d7ed',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalExceptionalSavingCalibration.lean': 'f438b9f6b9b64eed2a9e41829312ba1675ef2353d8bb581673f514376173cc10',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalFibreRowsMonotone.lean': '7b200b7b9c5552a3632a566531fe1dbf6ebfb1434630bc609d537498c9310064',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalFirstDualCalibration.lean': 'fe9ba931a8487bdcb785613e8ad405095e56900868ac6d6310aca8a450f449ca',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalFirstPhysicalWindows.lean': '8deeee3020be77f8141e39fd5b51c84505376a7e47b34a4335afe54573024f7c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalFirstTerminalCalibration.lean': '64ea223adb1cd06a833dd5806ccc78f0255dd9ef62429465ac86919c66bee297',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalFullSupportParameters.lean': 'a6bd4d92dcfcdc63c46b13d278a3a3ee466f9735d5ce4a1a3d8ecb3080f02f48',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalGaussScaleProduction.lean': '851e883ad0816f79df45c007937da0ceb7af03e1b709995bd4bb244de9263fd7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalLogNormLocations.lean': '0374ff5ca383f5d7a69d5a182a806e40f1c373c112fd8262fbf76621bfc17e93',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalLogTiltWindows.lean': 'e3889d8ce8bbac175cc6a078815abdc9651105f64fa220696fb21d222bd3373e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalMaskCardinality.lean': '58e72148c817bedf729cfc57d344d7293dec247a936f052ff72e4995bd3ac4c7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalMovingCoefficientBound.lean': '4ddd7e586f9fc7e916f9a8214e53183d8f65ba1cc6452d3549453dec8ebef2d0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalMovingFactorAppend.lean': 'b680bc79bd058c3181df484900002575439aab26c1e35fb7b3984503e161f932',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalMovingSupportWindows.lean': '1c34d705423ae09c4a224af8f60ea2da1072d4d6476f370040966fd22e0e81a0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalOrbitFibre.lean': '8cc3a5bfe937611b6054986ab410b03bbdd384b710b66a2bca7b3873989789a2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalOrdinaryExceptionalCalibration.lean': 'c2baaa2c6d42a7658f8da11e07774f2123d455a4b61ab4d8550849af44b4d4ad',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalPairAllowanceProduction.lean': '3d7557864e3cfc9317834ef4f56e918fb8b26c875a17fb0ad23e4b21b77252da',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalParentKernelFamily.lean': '4741e0266898cacc485444f8214bf9072602beab37a175a72bd0ba0a17298076',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalParentLeafScaling.lean': '842a2b8360d776de1ee833389d0c5433faa6f2d782629c14498c7cd39752a035',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalParentTuples.lean': '4abf56555bdd26932b694a756606793db16dce991065930eaece457bb992887e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalPoolAllowanceTransport.lean': '6c6989b8e6f2f8130f25af0e4a0e3132e6c1debc77cd3152c60ea6aa96b34891',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalPoolMonotonicity.lean': '2baf112fd720b2d2f065558ed440f0068f395a53d8a38428d1854230bc81aba1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalPooledTerminalGeometry.lean': 'cb3dd6a5d7690ed41781e03d15f63104ac8f088270b69cbf425595f44e5bc43b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalProfileAtomBounds.lean': '6fe6f083bee21e11214ceead9d7a2a17003595eb429cce70395a35f09eb86156',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalProfilePowerControl.lean': 'fac63cda360d5d10ec849185cd545e441a2b279e192733c97f78fdac3f39e476',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalSourceMassInputs.lean': '42c59749bbb610d755ce3bc2c62bdaab030555eb3573287dabab2c0c7ba7e0e7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalSourceSlotCaps.lean': 'c8f2623c56f18b4c34608a2ebf6108f1cdb4b9c6f3a6a3c44ec8bb5231e7a5d7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalTaggedLocalIndex.lean': 'c77cbdae27d978c4f62ac0d09fb1a2996eb35ec5c99d4fe79b33ba074f97a8c1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalTerminalPoolCharges.lean': 'ac360a00150ed1440de2aa3bae2f020d38133361284780079f6466db47ed1f8f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalUnionColumnNorm.lean': 'f999fbc73bb9d3ce0e1e371a48a8542c1c368461c243b3fe0c06e5dd63ba5994',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PairedEngineAdmissibilityTransport.lean': '217a588d1358a6ebabc4c43b9febfb3be73d298dee30f616799431c4c285c417',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PairedEngineStep.lean': 'f4907daca83b1a14c102d06ef02c7199215277c30efe26fcb2dec8a9a72cef1a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ParentArithmeticAtoms.lean': '923a36fd01e5d7f05758d1cce602445c9cab153db7d11bb77a63073e4559d6fa',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ParentColumnPhaseBinding.lean': 'dd2a7f17ef5f897dbe3f3bbc2dd9f526521b3927730baa1511f098f99d8a32ae',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ParentConstantSource.lean': '30a7c6a7313f2b663d3850a7e14a511d0a29574fd44d2c14aff89abe44b8f5f3',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ParentMoment.lean': '2ad71b4fcede7f07ec9fd898dc154aa37597d94ac0ea1a0e40f4d25f9612e391',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ParentOrbitFibre.lean': 'f3e3277ef6ee6323ae8604300080736aaa4f6600fbc3f0b1e38c9a5ab80991b4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ParentOriginalAtlas.lean': '8b044be690a0bc226cfdc9f52021e8aabda965aa7fbb1e850241490701a1d320',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ParentRawSourceInput.lean': '88ef307a32cb6b0b4447bbda60428461ca4dda39f559acfeb2e5b2b81e16f9ac',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ParentSource.lean': '73ac3e93e067302c3eb18a7f71c0c91bd608958c415f7974987511c9235a22ed',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ParentTruncation.lean': '5e0037fcbc200996801c7c35cd923db65c1c613d0641e841b046374d5d8d7385',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PassiveAllocationScalarMass.lean': '846383844b7635dd219a483dfef8f2b454468fecbbb7bc68548e2bf5a1f8643d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PassiveDeletionMass.lean': '1b8f94fc9866568b6552035988b63e8dffb161d821a3e2c3d2e945a008697218',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PhaseDictionary.lean': '3836cc54e1651a2ba786d32c1c6808054ffec893c851e1a74fb792c6ba1dcf65',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PolynomialProfileEnvelope.lean': '5d42884a644aa6dab644e8643e221fc0a4bdebed99a747fdcb76efa511b84c9f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/Pool.lean': '98a8f2bc36a6c8095bf7a169cd66ad763875ddd0d27236bcf879804daf525601',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PoolCoverHybridStage.lean': '6276ce2ad9817a4db1165f573a2e9a0bfe3a562918c4b3dec630db8e84f39753',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PoolFiniteLeaves.lean': '7fafdf5687b18cf53f9e6f4792e999198a0ab875396376690e1c625f0a718c01',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PoolFourierStage.lean': '6f664e25940ece3774c7f2753dd555598f7f48fb75e77a20d202c4a499d7119e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PoolGaussDecomposition.lean': 'e72ebb092b4487d2ad8b57b84ae4d92525daebff533c3a25ec8c2d1f59363b48',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PoolMass.lean': '5264886bcb89bdb45386f8394c736f0b435911d3fa908e7f3492b39ad29f2ac8',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PoolRawFourierStage.lean': '201dbd316ec63c34396a4319992410b1d9a44b0d8233fcf4c35d9b1f435f5ecf',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PoolSecondStage.lean': '1b8db53310396fcb3abc1168a402cf1f35fc11038ada5b01bb9be80f05ddcc4f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PoolStageTerminalBudget.lean': 'f87e3729935c96dce6952418627a1f19fe772cca66efb30029f6a5e32d3bda8b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PoolTerminalMasks.lean': 'd33a841f7e6b9a907f06f4c228e263fab287e2ce71682d80e6652a72dfb2960d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PoolTerminalMass.lean': '3274c6d73f56faa967df46e95a5520e9ee8ddeea52aaf921f3f2ba68117b0c02',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PowerfulDiagonal.lean': 'b9c47f8550f6be598ff1c414e014b59c8120e35edd385cf00761ff9b37ec820e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PowerfulProducts.lean': 'c5d8a333b6fbb4929066a47e0cc82a1075748d45fe3fe17e58c2a524ce2e2274',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PreCauchySource.lean': '168bcd3b745516c82e5d07337e8597dcb1d91dc5ed210fcf7b4179ae20068f24',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PreparedDualBudgetBounds.lean': 'cadea9d87def7ef4094c616c1043c25ef1c06e00e34675efd5c121913fc33512',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PreparedOriginalFibreRows.lean': '71e0e75a5c03300f230450c0035e258a7899615fece2c60a9905913d6cd4a811',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PrimePool.lean': '4dc443e953823525a803d5cc24311903bb28de66582a839788164560074369c4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PrimePowerGcd.lean': '22c17bc3ae50b86bc3947f790673ed74ad2ba19d7b0599b0b6c8417f75c0d2f7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PrimePowerQuotientSupport.lean': 'ba4d96eb6bfbf5b3a3667b2ece7dce23d68dc9d0dc593a52c2ed2a267acdf609',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PrimeSupportMass.lean': 'a36fd44ed18275e4e2ce89e2e309c85328abf624579413d3fd940cbad8f9c8ce',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PrimitiveDirectFactoryCard.lean': '17198abe83f35c23f53d0a00b272df6d412790413970f96e580bd6dc54af2bbe',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PrimitiveDirectFactoryFibres.lean': 'c0a35e598f644287fa0f3ad1185ca04294ee1c9118049dfc9d471188d9f98096',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PrimitiveDirectPassiveFactoryCard.lean': '86373e5b2f8a13da774fb4db6a38e2ed9c10375ec478d17efa85a28f07fba6d8',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PrimitiveMainPassiveFactoryCard.lean': '800930a737c223f82450785564ad35804ea651b9e391c1a06d5c7b32e8acdf64',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PrimitivePassiveFactoryCard.lean': '8b22a9c5e40e5e3bb37e27948a8a647f6b199041d324a88e6f024653677f793b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PrimitivePoolPassiveFactoryCard.lean': 'c21fb87d321a9b77029817d267acd924f54856187851a1219cb88b2ca1a3bb5a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PrimitivePooledFactoryCard.lean': '7a882dd85c61c527574dffeeaf3ae0df8b1021717e5cffdfe2ac027e23df0ce2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PrimitivePooledFactoryFibres.lean': '714f33a26d32da5bd46b8c7ff3ca7db217ebf30ebfd366eb9e6b7d95c04b9889',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ProfileEnvelopeNormalization.lean': '7f3e461fd6d106f63919acfcae82dc03d7d718b001dec82b9d54ce3d57998623',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ProfileNormalizationInput.lean': '12c3de33520b5e21c05b7bc8048a6972649da20f404fedec7ab094f0f55bd9bc',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ProfileSeminormNormalization.lean': 'fc95b37ca712799b62951ef89afd85a90b3f8fcf3636053a901aec6d3fed9dec',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/RankinLabels.lean': '50b15b54b192a0ac3c84722a9caeae24469e95d821bbe70eb275cfa74d7a07cf',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/RawSourcePhaseIntegral.lean': '9bb691deda58369ae12b83db99cc74b681b2f8e9e70eedadca080993616b59a1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ReductionOutput.lean': 'd575b59236c84b4cdb76f67930d4b5dc15e671f47811a18818afd9a9882f1b5f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/RemainingMaskRadical.lean': '825ed7b62cfc82819e667c5e27a80e8b16789543051a9bf3c43ddc0e6db169e5',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ResidualTerminalCalibration.lean': '7c809f49528d98ea30860cc452299b60a1582d6987d7763400745bc91b4d3bd4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ResidualTupleCount.lean': 'fd83c6bba5281de4f4100ed5dcb6e153cf6880b654dc3aa0cd6d790229786c73',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ResidualZeroBudget.lean': '47db064d3b0eacb49d4c7080796f65aec25da5d3d9236b6a577bbc85f7843dc1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/RowBudgetPreservation.lean': '22c2719a59af9489cc002d50bf0e00fb6ce53aa9b0b93749ccd472db5ba0c344',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SIntegerFirstFourier.lean': 'fe0a3cfc8cc2920234be4f0f7c97a3aa3d9d2223c426527b6bac3d0c2e1c545f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SameCarrierTerminalBudget.lean': 'd9427906808b475189570eb0806fcc5da8721d1e427967b5f90baed055214372',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ScaledNormalizedKernels.lean': '12302cdc7d93af84c9e418345ff8659476eeba064f9987dfdcf76f278ea80468',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondActiveDualZeroDiagonal.lean': 'd2c59897dd809684fedd81f2f004da54d88c9b30c870efcccf98cb7e51f8b86f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondAllocatedSource.lean': 'd8426ec207ba34d95ae860287333e1ebf3e48a55e9acc7d25be5b66ce252799b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondAllocationKernel.lean': '4bb4581524e5d44c519c4b21f039fb6c947f1278bd19586ce0cade95029be498',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondAllocationLabels.lean': 'f14b8ce6ca4b6d99bd30d738eca4ab4929be433546e8e5b3e54bdaf49e1341b4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondAllowanceCancellation.lean': '589514b6ac5554582e70ac4812d8190431d74fa087dd6265da2b461352ed014d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondBranchPartition.lean': 'a57b2ce89a6593c2e4392a40c8d2a62086eb19a87a2f2053b5ab8062000929eb',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondBranchProduction.lean': '3fd14c3c386c13a06317affd705ba9779389ce341a92a5ab6759b04d194a2389',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondCenteredBinding.lean': '7331ea7ef9ed51a062313d0b02994e388bbf8547df963984f0940e6828c5c218',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondChartAllocation.lean': '620d87a394e2598b68dc3f34c22019b7f323c3496cdd897d055fb03e67f3c719',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondClassProduction.lean': 'cea8180b53963968b2ca104e9a015afe8a16a366e0f0acbd4e297356922935a1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondCoefficientBinding.lean': 'bf312c4fc2a264b23c0fdba380cfdebc200781e5314cdd3747ab658ca0a7613b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondCoefficientNormalization.lean': '1eecc40ec643be114284b63eb00df47f65e60490a227428b562fb10e16ae3a0f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondCommonIndexSwap.lean': 'b6f48d1ac742344a8cea75dd4873039a94e5e9959808a8d081f39f6e9d181e39',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondCommonNormalization.lean': '08f968228a63e35e0597d3207dd718b01755db86f15b51e2ddb46fc03e866638',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondCommonSource.lean': '2cefea84d0e6e2f4b9d22bab52feafa493e26a34974d7034f8643eb250e3752b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondCorrelationSource.lean': '2865723c7c046892e3827e028c95f964aa6e77136f2e169ae1dc8d9c8a125daa',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondDivisorDualZeroDiagonal.lean': 'db0853533ca5fd86c5e3890acf3af7c48b9060647bc140490a76a00925af0c1e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondDivisorMass.lean': 'd77818469c1805f0cdc11680c8496a8b6a9dc34fc86656aa665e7b635c39919c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondDualZeroAmplitude.lean': '834e534fedaecd297456bc8c56ff64695879cdc61a2b059d10427644900cce49',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondDualZeroDiagonal.lean': '9ff3a87d0ea3e7a660b9cd17e143f31e466e99eddbd125246c7e589d74d6f6e1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondExceptionalBinding.lean': 'c44cdaa658ed34ad0ea0cd762ce8974409b3e3add59041eb1ce2ff73dffaa4ec',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondExceptionalPartition.lean': '0b85a835a6b4c8654d97a7f335248277ad8f83cc787cf228a5e9a57e512c4058',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondFactorHybridBridge.lean': '6bd1f8d9566993195a7469961f92122fea8220e7edd70c7a48cfb551458752dd',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondFactorIdentification.lean': '7876a04d7b58509fe0e8408c7ab63d59a96c862b3246251b223b5e8386a67c52',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondFrameColumnSwap.lean': '5125d85e6a9c105290afcd9ac6a62ef17ffd794d12fc142d2a6b433947d2316e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondGeneratorSource.lean': '35695098f678a15f583fb2a8f195bf93e9b2aa209c7462f119a84075a9c2a005',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondHybridAllocation.lean': 'daa9d5de107101da87688692145fd7b01c5e297c976c0387fa650de4d5ff9184',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondHybridChart.lean': '99aa5b634fcc38d23687858533e5fc9992a420d273c506d4b983de1fe5901738',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondHybridCoverSource.lean': 'f1aac5eec100b9b5a768421bcf125fe25923779502b4b4a8e93fcfed3d10426d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondHybridSource.lean': '959cbcfb343d284ae3d4d9d13853889438c985a79e8ea7ec7ce12aec5e873afa',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondResidualSource.lean': '30fd0dd004ecc9a5a08101bc769116c596722b7dd3df3056920fa4f8c6263a83',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondRowPartition.lean': 'b50560e47f4a04db3e7cf3f0ba8f1b231df16be019446a8b0ca025a32f5eb8c3',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondSourceNormalization.lean': '006f6ec6f10a8e08d0d4b16255fc938d34e1dcede91361dcb56f57c5d7b49489',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondStage.lean': 'c004d250ec24cbb3db68a0968163f5df0ad9cc4cb0957dbf64f3a3d6c43fe6cd',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondTailBudget.lean': 'ba33e21cd25f9d2eef47736ae753a7a4f1b920ac48557ad9449069d8511524e6',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondZeroAmplitude.lean': 'f3cdd8169d09eb848756dcf680c7a246cb1cb385e645a129966cceda844b0bc9',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondZeroDiagonal.lean': 'd17c8b180bb11d75ae84854dc42fe53d8055ba259701c94b6fb43150abf8cadc',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondZeroSupport.lean': '47123d9778de5f1fdf4e873e354ff0d15f95ca253fa3dc399d17f7cd9e2b6ad7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SignedActualFirstSource.lean': 'dedb71a6ff83f41dca31ff50cab3d9a36bdc0f037297384de9603b9131d3a1d7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SignedDirectFirstSource.lean': '3f8ac62fb2832517e80a1a504145d27bf1d3d42b1d44b3d530ea4463e7f40818',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SignedFirstStage.lean': '763c55b077990826f276e3cd88c845673dec2eb72ffc25fb76fe8cee467e4e49',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SignedPoissonZero.lean': 'deaea0d595b41dbb48539472aeb646b4c124aeeb2247b8e8b1a83041b09ed54d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SignedSecondStage.lean': 'f6f8fb9d6d3cb4bb56f8fda60d393470693ea5adae6961dd0446dccaa2b265c3',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SixthDeletionCapacity.lean': '5e5b9001fde21d997b8dddb5b8c0add77d3dbd1029ec3b5ffa06a8cb498cec89',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SixthDeletionFamilyMass.lean': '551082ac8af1f709f8fd92ae53c45308ccf938254562d1d1de0dc82307379184',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SixthDeletionGeometry.lean': 'ccc37686d2cc3fc1e52bfe1d5597108b4b1ef30bae5af2bce06bd5ae63bbc3c0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SixthDeletionIndependentMass.lean': '32d74c39c18cd611b4624f34b33ac1b7c8ca3448aac20a96098325896f2e45b5',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SixthDeletionScalarMass.lean': 'e5f6192c1893a53876f0814d9c0170786b5cf98a5ac0da65dfcf5b77404d6a92',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SixthDeletionSeparateMass.lean': 'b486a39cc4bc602a10202778b1215773af59925ee88f34b2b134e040a5008a14',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SixthRootSupportBudget.lean': 'af1a7df75ba04c1336bc14f05d697b06f25d28516d1c9af6bab4605890c6a47d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SlotCompleteEngineOutput.lean': 'b35b55aa79d2cc3b0fa629090e86ca105e9d025a761eabcc28d5b2b806c665db',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SlotMeshPreservation.lean': '21d9fae40b3bac01da84e777f00a09f92b1d3b51c57d7695aee7ef6b5eef4ab2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SlotRestriction.lean': 'c873f6367169dd9cda2e29582a1ecc24a203e3657b23091191c0464bd41772e2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SourceCartesianAtlas.lean': '6da3c1ce8b24b17c572d0a1f7f6471867e9049944b47a11d15901e44dd5c24a6',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SourceCartesianCover.lean': '9f09f2a18ec51d958b7f98b7ed09d1a3de3892fea96d429058fffde898a2abae',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SourceFactorExtraction.lean': '7a305075ef11e206335c7ffe9cffc1ba0eef8fa379dcb70863288b747d61c160',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/StageTerminalBudget.lean': '863c86722d66ad2a91984a969f978a48f3ff9c6dbaaf857d7cf25bd6eff85251',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SupportCartesianReindex.lean': '309bd9a7675260b5ab99da6e9f2ce9bb848c9fc6787af26f429a76b2ac59081d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SupportKernelPartition.lean': '710bbb995daeb7d9930c4a2685f2a1a487c015d5c1420077413509c5445ec11e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SupportSourceExtraction.lean': 'ba9b30e917c4498c2fdde891acbfe0295105d8ef7578a0086fd792bddf00f789',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SupportedGaussStages.lean': '4592be4830bbe8e922c5e245b4e605bc5af24fa72a69a043a12e1c35bc189f7e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/TailBudget.lean': '532fac1749febedea40d5a7aadc2865412ad549b8fcb922ccac75dd9a5295fc2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/TailFiberCount.lean': 'e92607c3524f89b35bd2ae199c5ca4337f96d0a149d7993e354f8db120581bca',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/TerminalPowerBudget.lean': '0c77eaab2b5f2d90d2f8c5c40348d3d08ec965b78accf1a5f4da29b9694a72f7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/UniformLengthCapacity.lean': 'cae19e238208c691da09df58b81afbbda8639d85f5b5388c6794f13b281c7040',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/UnrestrictedSixthCapacity.lean': 'dd9510be48699bede3ac9db08a0943dd81079c725716f6ed27744b1846543e63',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ValuationAllocation.lean': '4099ec5ce0c3fcaf5b611a6b2c7a35c906321b130b7a1338f1d63a88edf9288a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/WeightedNestedFourierMeasure.lean': '047684bf2d6ebd6e23ae0473787242d5602a85b0a9ea89af75e1bc9cf4d7ed47',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/WholeAllocation.lean': '1447e7e84cfea07f65b9feeb2bc732ca380789f86d6155de0e11d6e93c3f03e5',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/WholeGramOrigin.lean': '26cfc196b6dc2d31a94d59a64308bd06fae758b5729fc2b25d883d57df71f4ef',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ZeroTerminalBudget.lean': '4b0981114dc50a3e67c4c4b4ddcaba601e4e3e91ef82de0d684dad44ff1ff9b7'}
# Proof/elaboration compatibility repairs are recorded separately from the owner pin.
# Their baseline and exact replacement digests remain visible in the CI artifact.
PRODUCER_REPAIRS = {'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualCoveredLabels.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                    'owner_sha256': '943a8125054fc28b795be9374d6ca77eb35e16af50849378cec299afb61c61e6',
                                                                    'reason': 'Exact published STEP repair '
                                                                              'a48360581b2b0ed368a375911d937cc4b44228f8 '
                                                                              'source: infer the original '
                                                                              'SourceCovers.tag data d from '
                                                                              'the same cover, then '
                                                                              'normalize the same finite-sum '
                                                                              'identity with ring_nf and '
                                                                              'close its definitionally '
                                                                              'equal tagPoint functions by '
                                                                              'rfl. No labels, branches, '
                                                                              'coefficients, or public '
                                                                              'conclusions change.',
                                                                    'repair_sha256': '165356d5ecbc018b0c0968856dd806e297969e53a38889b5116289ebcd208cbf'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualNormalizedLabelWeights.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                             'owner_sha256': '86cb17c790332e883bf872f85d1c380e3509ea46740e20bb165eea1ef12abb76',
                                                                             'reason': 'Restore the original '
                                                                                       'OriginalPairAllowanceWindow '
                                                                                       'certificate L in '
                                                                                       'arithmeticCosts_family_original_index_weight '
                                                                                       'and '
                                                                                       'arithmeticCosts_family_outer_index_weight '
                                                                                       'so both existing '
                                                                                       'calls retain the '
                                                                                       'same input. The '
                                                                                       'original arithmetic '
                                                                                       'indices, children, '
                                                                                       'and full labelled '
                                                                                       'bounds are '
                                                                                       'unchanged.',
                                                                             'repair_sha256': '7da8b4b90629f88923394ab7f7fffff6bdb2ded359f62d832c2e10f81628eeb4'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalActiveProfileKernelMass.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                                 'owner_sha256': '7c7206b23dd231784e716892fb5cd0b200c63fa9955f23c78074a8715abb72a7',
                                                                                 'reason': 'Apply the same '
                                                                                           'finite '
                                                                                           'scaled-kernel '
                                                                                           'proof required '
                                                                                           'by the CI74 '
                                                                                           'diagnostic; '
                                                                                           'preserve the '
                                                                                           'original measure '
                                                                                           'and scalar.',
                                                                                 'repair_sha256': '58e2763edce10ca8b38f97c2207b99c3c555e4f74d7b2e20e56f575bdc077836'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalActualGaussNumerators.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                               'owner_sha256': '3bf372c801af225c630e24e763a3e1cedde54e9215a26b3ecb0ea1d5db5970db',
                                                                               'reason': 'Restore primitive '
                                                                                         'parameters already '
                                                                                         'supplied by actual '
                                                                                         'callers, or place '
                                                                                         'include before its '
                                                                                         'declaration doc '
                                                                                         'comment; preserve '
                                                                                         'the actual '
                                                                                         'producer data and '
                                                                                         'output.',
                                                                               'repair_sha256': '751ae606890549ba2bb28d56a5c54c9bfc19ce8677d4e7a4f79caf97f8ac01ab'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalActualGaussReconstruction.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                                   'owner_sha256': 'c698a8498bbdb0b5a74b0839b3a4b7bbc28aaa68ada9fd8b2b601964f125e23b',
                                                                                   'reason': 'Restore '
                                                                                             'primitive '
                                                                                             'parameters '
                                                                                             'already '
                                                                                             'supplied by '
                                                                                             'actual '
                                                                                             'callers, or '
                                                                                             'place include '
                                                                                             'before its '
                                                                                             'declaration '
                                                                                             'doc comment; '
                                                                                             'preserve the '
                                                                                             'actual '
                                                                                             'producer data '
                                                                                             'and output.',
                                                                                   'repair_sha256': '39fde7f0bf7343f045fb982b652ce065dbf1f89ffd4edd6db5e85e492f9cc6d6'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalFirstMaskWindows.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                          'owner_sha256': '865839b416077063ab5bf7e9fb215b40530d9b1848424f8dc1af5b05dd2b3219',
                                                                          'reason': 'Restore primitive '
                                                                                    'parameters already '
                                                                                    'supplied by actual '
                                                                                    'callers, or place '
                                                                                    'include before its '
                                                                                    'declaration doc '
                                                                                    'comment; preserve the '
                                                                                    'actual producer data '
                                                                                    'and output.',
                                                                          'repair_sha256': '16260c7162879a200dc049788e5ca0e7e21e7db1ca6d7c7f0d76a4e49fcf398c'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalHybridMass.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                    'owner_sha256': '2ba33975011973aebfa9558f7ce3c7cb1449d2dd93c8ebff04358b90ba5ecb0a',
                                                                    'reason': 'CI74/75: explicitly prove '
                                                                              'finite scalar measure with '
                                                                              'Measure.smul_finite; '
                                                                              'construct active-combination '
                                                                              'filter membership directly '
                                                                              'and expose the same Sigma sum '
                                                                              'before Fintype.sum_sigma. The '
                                                                              'measure, tags, and total mass '
                                                                              'are unchanged.',
                                                                    'repair_sha256': '6cf5bad0529e39f2f68ccd8f57b2f1ad2eab393f111df23c17631355e648227f'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalAtoms.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                                 'owner_sha256': '5523054440a8229ac0435d2bf8cd2b4784daa13fcbf17bfc627f5e88d9f9ae5f',
                                                                                 'reason': 'Restore '
                                                                                           'primitive '
                                                                                           'parameters '
                                                                                           'already supplied '
                                                                                           'by actual '
                                                                                           'callers, or '
                                                                                           'place include '
                                                                                           'before its '
                                                                                           'declaration doc '
                                                                                           'comment; '
                                                                                           'preserve the '
                                                                                           'actual producer '
                                                                                           'data and output.',
                                                                                 'repair_sha256': 'f3071e41d1090776984d1c20f2bf21b8f6692bb6c5f3df9d5398afd58be2ade8'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalBinding.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                                   'owner_sha256': 'bd2067cfc42449550caf111c0ee30eb5ec3becefd35fa732e57c2c9bb9780a67',
                                                                                   'reason': 'Restore '
                                                                                             'primitive '
                                                                                             'parameters '
                                                                                             'already '
                                                                                             'supplied by '
                                                                                             'actual '
                                                                                             'callers, or '
                                                                                             'place include '
                                                                                             'before its '
                                                                                             'declaration '
                                                                                             'doc comment; '
                                                                                             'preserve the '
                                                                                             'actual '
                                                                                             'producer data '
                                                                                             'and output.',
                                                                                   'repair_sha256': '693266e6115d448d83a1b9f54cbff6bfb80b9147b928cd20a43d2b22fb7a33c3'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalPaidScales.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                                      'owner_sha256': '6c7ba98683e51decc221d7a6aa50d071cf3d3e0e027b01c3bb8a6ed418fc8006',
                                                                                      'reason': 'Restore '
                                                                                                'primitive '
                                                                                                'parameters '
                                                                                                'already '
                                                                                                'supplied by '
                                                                                                'actual '
                                                                                                'callers, or '
                                                                                                'place '
                                                                                                'include '
                                                                                                'before its '
                                                                                                'declaration '
                                                                                                'doc '
                                                                                                'comment; '
                                                                                                'preserve '
                                                                                                'the actual '
                                                                                                'producer '
                                                                                                'data and '
                                                                                                'output.',
                                                                                      'repair_sha256': 'ae73255d20036028c00e465daa1cf2b19fcb1aa34037f523cc7527c2c2e03e24'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralExceptionalProfileWindow.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                                         'owner_sha256': '7c7f42466fe4b840b09b12e60e2f3b682b3122a8fb97fe82071fe70f0867371a',
                                                                                         'reason': 'Restore '
                                                                                                   'primitive '
                                                                                                   'parameters '
                                                                                                   'already '
                                                                                                   'supplied '
                                                                                                   'by '
                                                                                                   'actual '
                                                                                                   'callers, '
                                                                                                   'or place '
                                                                                                   'include '
                                                                                                   'before '
                                                                                                   'its '
                                                                                                   'declaration '
                                                                                                   'doc '
                                                                                                   'comment; '
                                                                                                   'preserve '
                                                                                                   'the '
                                                                                                   'actual '
                                                                                                   'producer '
                                                                                                   'data and '
                                                                                                   'output.',
                                                                                         'repair_sha256': 'fb71944699a221d76f5e054567ba0b55b32485502329144b0ded6c08d98165d0'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralFixedPhases.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                            'owner_sha256': 'b6e9649da0c05ff1745908c97bfc9261c25cb404e74984cfde4188338b227b09',
                                                                            'reason': 'Native elaboration '
                                                                                      'repair from the exact '
                                                                                      'owner CI log; '
                                                                                      'original mathematical '
                                                                                      'input and conclusion '
                                                                                      'retained.',
                                                                            'repair_sha256': '821fa33cbd448d9b72ae4cda675d3b72d6807320c90a2d2dcf427051a3363013'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralOriginalEnergy.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                               'owner_sha256': '0fd9ce8d01c2010b2682eb21bc5f4803c290fb28708c779fc66b1954a0e844e0',
                                                                               'reason': 'Restore primitive '
                                                                                         'parameters already '
                                                                                         'supplied by actual '
                                                                                         'callers, or place '
                                                                                         'include before its '
                                                                                         'declaration doc '
                                                                                         'comment; preserve '
                                                                                         'the actual '
                                                                                         'producer data and '
                                                                                         'output.',
                                                                               'repair_sha256': 'ea8c1978294558d3027ec5c3f8e91d0c6886a49b78cf8fb3787ab304e8838594'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassivePhases.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                              'owner_sha256': '25b128de6d67131ea72f3afbbaa5d894fa2a6a18e1fb4bbc0b11c9fa7e34f25e',
                                                                              'reason': 'CI75: open the '
                                                                                        'actual '
                                                                                        'SquarefreeAmplification '
                                                                                        'namespace, remove a '
                                                                                        'redundant tactic, '
                                                                                        'and prove unit '
                                                                                        'radical and '
                                                                                        'coprimality masks '
                                                                                        'explicitly. Retain '
                                                                                        'the previously '
                                                                                        'reviewed include R '
                                                                                        'parameters and '
                                                                                        'doc-comment '
                                                                                        'placement; preserve '
                                                                                        'the literal phase '
                                                                                        'objects.',
                                                                              'repair_sha256': '1d837d63dac375a2a21123349a4491790044284beb5ddfa397dffb9ef5af9d6f'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPassiveSource.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                              'owner_sha256': 'b3e60e8a5643a1f6bf2bb2de8bc1e6fbe5acf27a4b642881ceb60aefadc4bd1a',
                                                                              'reason': 'Restore primitive '
                                                                                        'parameters already '
                                                                                        'supplied by actual '
                                                                                        'callers, or place '
                                                                                        'include before its '
                                                                                        'declaration doc '
                                                                                        'comment; preserve '
                                                                                        'the actual producer '
                                                                                        'data and output.',
                                                                              'repair_sha256': 'ea091be2158da418544a1c9f3a0590d9074e914870479ed281cc4d829ebff27b'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveDirectColumns.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                                       'owner_sha256': 'a514dc3dbfeb183f173c010ae1c031208c5f553983b2f3c4eb4b27b51650d04e',
                                                                                       'reason': 'Restore '
                                                                                                 'primitive '
                                                                                                 'parameters '
                                                                                                 'already '
                                                                                                 'supplied '
                                                                                                 'by actual '
                                                                                                 'callers, '
                                                                                                 'or place '
                                                                                                 'include '
                                                                                                 'before its '
                                                                                                 'declaration '
                                                                                                 'doc '
                                                                                                 'comment; '
                                                                                                 'preserve '
                                                                                                 'the actual '
                                                                                                 'producer '
                                                                                                 'data and '
                                                                                                 'output.',
                                                                                       'repair_sha256': '45258ed40855bac155406762930b7e7c4553b4546cc93dcacd16025ef6e17115'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralPrimitiveFirstSource.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                                     'owner_sha256': 'fcddfd5741028e9f2064df460826a83c9fe50aa4b184f8b2a86449ef49ff2895',
                                                                                     'reason': 'Restore '
                                                                                               'primitive '
                                                                                               'parameters '
                                                                                               'already '
                                                                                               'supplied by '
                                                                                               'actual '
                                                                                               'callers, or '
                                                                                               'place '
                                                                                               'include '
                                                                                               'before its '
                                                                                               'declaration '
                                                                                               'doc comment; '
                                                                                               'preserve the '
                                                                                               'actual '
                                                                                               'producer '
                                                                                               'data and '
                                                                                               'output.',
                                                                                     'repair_sha256': 'a7142dd19092e35a021d1bc10492841014bcc889d8694448033c0297191d6ff8'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLiteralScaleProduct.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                             'owner_sha256': 'cf99114b0b127c903027cd423ea5b099c3ab459a0642df4afa8ee60f64dc1aff',
                                                                             'reason': 'Restore primitive '
                                                                                       'parameters already '
                                                                                       'supplied by actual '
                                                                                       'callers, or place '
                                                                                       'include before its '
                                                                                       'declaration doc '
                                                                                       'comment; preserve '
                                                                                       'the actual producer '
                                                                                       'data and output.',
                                                                             'repair_sha256': 'c1452b1fa1f783703fb3afa3a81e8d64ad5c75afdbb36497b396e91d877350f9'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalLogProfileBounds.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                          'owner_sha256': '30aae10806002d579936b09320b566e51ff5aa6a5a662538c7ea784dbef31f07',
                                                                          'reason': 'Exact owner-reviewed '
                                                                                    'ea5e384fc84dca2408cbda293e60492e7f0824c2 '
                                                                                    'source: scope ContDiff '
                                                                                    'to derivative proofs, '
                                                                                    'type finite sums over '
                                                                                    'the original Type 0 '
                                                                                    'carriers, and transport '
                                                                                    'restricted and frozen '
                                                                                    'families along their '
                                                                                    'original '
                                                                                    'data/count/time '
                                                                                    'equalities. Resolve '
                                                                                    'CI75/80 elaboration and '
                                                                                    'positivity failures '
                                                                                    'without changing public '
                                                                                    'signatures, profiles, '
                                                                                    'support, selected '
                                                                                    'slots, or bounds.',
                                                                          'repair_sha256': 'bfe5aaf7df67243453e7e1c11352e2af8cd270929e7fd0f4d24d16d2521afe5c'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalPrimitiveFirstTerminalConstants.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                                         'owner_sha256': 'cd9577b05fc862bed92015cbaa53ac17b1ab4a2d74c51dec9d0e35a5a5d239db',
                                                                                         'reason': 'Restore '
                                                                                                   'primitive '
                                                                                                   'parameters '
                                                                                                   'already '
                                                                                                   'supplied '
                                                                                                   'by '
                                                                                                   'actual '
                                                                                                   'callers, '
                                                                                                   'or place '
                                                                                                   'include '
                                                                                                   'before '
                                                                                                   'its '
                                                                                                   'declaration '
                                                                                                   'doc '
                                                                                                   'comment; '
                                                                                                   'preserve '
                                                                                                   'the '
                                                                                                   'actual '
                                                                                                   'producer '
                                                                                                   'data and '
                                                                                                   'output.',
                                                                                         'repair_sha256': '03200a75789c87371a478940abfe89cf468318641e8f2acb99830cf2091974c0'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CompleteEngineOutput.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                     'owner_sha256': '4b8c56f5d4b12e9448aa8591d60b51cd00515e7d2ac66cc801622192485b08e6',
                                                                     'reason': 'CI76: open IsDedekindDomain '
                                                                               'explicitly for '
                                                                               'HeightOneSpectrum. CI78: '
                                                                               'restore the original section '
                                                                               'certificate h in identify '
                                                                               'and raw in '
                                                                               'left_background/right_background; '
                                                                               'existing consumers already '
                                                                               'pass these same '
                                                                               'complete-child and '
                                                                               'parent-character '
                                                                               'certificates. CI80: unfold '
                                                                               'leftData/rightData to the '
                                                                               'same frozenData before '
                                                                               'transporting the parent '
                                                                               'background. Preserve all '
                                                                               'original data and '
                                                                               'conclusions.',
                                                                     'repair_sha256': '9bd9c6bce9d844d473812caba0e9c0393e4286c40ef1bd6561930ff1d09b61bd'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ConstantCommonLeaf.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                   'owner_sha256': 'f7df02d24d9c6f66ccff22e9fc3c2e043af91a810c93e98f529c592927b54ef4',
                                                                   'reason': 'CI75: retain required hc/hd '
                                                                             'hypotheses with scoped '
                                                                             'include/omit, unfold the same '
                                                                             'leaf projections, make '
                                                                             'restricted-row membership '
                                                                             'explicit, and align only the '
                                                                             'normalization wrapper universe '
                                                                             'with its existing upstream '
                                                                             'NormalizationData type.',
                                                                   'repair_sha256': '14333a516b704aab245241b80f32658298ab4231774034b2a601872f0ecd567a'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CoverHybridPhaseIntegral.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                         'owner_sha256': '44883b0dad17336f94266ced1a7777c8a1ad0f28c80aa6f8f6b25c42ff7712e6',
                                                                         'reason': 'Native elaboration '
                                                                                   'repair from the exact '
                                                                                   'owner CI log; original '
                                                                                   'mathematical input and '
                                                                                   'conclusion retained.',
                                                                         'repair_sha256': 'cd1a3218ef99de2638d9c7e88cae6db6e9626b3ddcedc138a7ae8825e64e2d82'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CurriedNormalizedOutput.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                        'owner_sha256': '0e6ce3d0990c1bc09cb64c03e9136bd6f661c4175c126cc8bea682b840818ce2',
                                                                        'reason': 'Same namespace root cause '
                                                                                  'as CI76 '
                                                                                  'CompleteEngineOutput: '
                                                                                  'open IsDedekindDomain '
                                                                                  'explicitly for the '
                                                                                  'original '
                                                                                  'HeightOneSpectrum '
                                                                                  'arguments. No declaration '
                                                                                  'or mathematical object '
                                                                                  'changes.',
                                                                        'repair_sha256': 'b29f8ce7dfa8586771a8681e0667589d1a31a52ee2d524e910a3892b2cf596bc'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DependentNormalizedFibres.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                          'owner_sha256': '4615f958c912fa860bb643cca604c7a9f632ecb1b74cfa251aaa5efb7ced4468',
                                                                          'reason': 'CI75: prove the finite '
                                                                                    'dependent-fibre bound '
                                                                                    'by an explicit '
                                                                                    'injection on the '
                                                                                    'original active '
                                                                                    'carrier, avoiding '
                                                                                    'subtype-dependent '
                                                                                    'rewriting; retain the '
                                                                                    'same labels and bound.',
                                                                          'repair_sha256': '4381c2d451dbbbef46342d80e60125c75eacce2bc39ceea68feaac34cc6ae15d'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ExceptionalOriginalLabel.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                         'owner_sha256': '27f5c120aad01282a962c3c30d4ca55f689dfc0e60e09d04ceef979fee8b8278',
                                                                         'reason': 'CI75 and owner769 native '
                                                                                   'diagnostics: split '
                                                                                   'expensive scalar and '
                                                                                   'divisor transports into '
                                                                                   'explicitly typed proof '
                                                                                   'steps at the default '
                                                                                   'heartbeat budget, '
                                                                                   'retaining the same '
                                                                                   'original-label costs and '
                                                                                   'public conclusions.',
                                                                         'repair_sha256': '8e3d2677b1b469c5fe62656b13cc200049adaf8f3e576325f9fbb963b463a5a9'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ExceptionalThetaRows.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                     'owner_sha256': '252e0e38087ea3a99b9e284479a91448e94ecdc7788c3f31b6afe56b8b9cd2b6',
                                                                     'reason': 'Native elaboration repair '
                                                                               'from the exact owner CI log; '
                                                                               'original mathematical input '
                                                                               'and conclusion retained.',
                                                                     'repair_sha256': 'ade5c5c4361864958287b39733ec841047e385c76e452c7e3d1c6177c7fbba1d'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/HybridLeafExceptionalBinding.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                             'owner_sha256': '8d981feeb6b4f1ed890cc8f923e00653ced0ffbf1917b94cbefe091f09598e38',
                                                                             'reason': 'Exact owner-reviewed '
                                                                                       'e76eb348a867a89dc873b6abe3b4e1211621741f '
                                                                                       'source: reduce the '
                                                                                       'two original lambda '
                                                                                       'applications with '
                                                                                       'dsimp only after '
                                                                                       'finite-sum '
                                                                                       'congruence, before '
                                                                                       'rewriting the same '
                                                                                       'leaf coordinates and '
                                                                                       'coefficients.',
                                                                             'repair_sha256': 'c2eb40c901b7a5067af19d49d1c5e19f785fa21ce9fd29072dca328c11f3448f'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/HybridLeafOrdinaryBinding.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                          'owner_sha256': 'ebb42ce6f98e2a9857c7c4273488046c41dc7577bf295247857ec02cf87cf4ec',
                                                                          'reason': 'Native elaboration '
                                                                                    'repair from the exact '
                                                                                    'owner CI log; original '
                                                                                    'mathematical input and '
                                                                                    'conclusion retained.',
                                                                          'repair_sha256': 'bb5a3ee332b3213d7d8e829d06ca9df635b2c04c1c58982e8e97181c292154fc'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/MovingEngineOutput.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                   'owner_sha256': 'b9273892533ae9fa33614764969c5c3e26f945ae4d2c4f8f56da42e06e8abcaa',
                                                                   'reason': 'Restore the original '
                                                                             'moving-child certificate h in '
                                                                             'fitsMesh and slot_count; '
                                                                             'actual consumers already '
                                                                             'supply it. For the same '
                                                                             'universe cause as CI82 '
                                                                             'NormCompleteEngineOutput, '
                                                                             'specify PUnit.{1} for frozen '
                                                                             'row and profile witnesses '
                                                                             'hidden under '
                                                                             'existential/Nonempty Prop '
                                                                             'fields. Retain arbitrary '
                                                                             'orbit/Fourier-space universes, '
                                                                             'original moving factors, both '
                                                                             'budgets, and all slot '
                                                                             'conclusions.',
                                                                   'repair_sha256': 'b4d33b8237ce8ad06634537ed2f0d7d9f7836a3e3da2f21ad8baf00ee0cea057'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormCompleteEngineOutput.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                         'owner_sha256': 'dab7339275ee2b1cf1122d85ad7572eeade3f02c465bfc1471cab83ee1d1452b',
                                                                         'reason': 'Open IsDedekindDomain '
                                                                                   'explicitly for the '
                                                                                   'original '
                                                                                   'HeightOneSpectrum '
                                                                                   'arguments. CI82: specify '
                                                                                   'PUnit.{1} for the frozen '
                                                                                   'singleton profile '
                                                                                   'witness hidden under '
                                                                                   'Nonempty in the Prop '
                                                                                   'structure, matching the '
                                                                                   'existing '
                                                                                   'ParentArithmeticAtoms.at/constantAtoms '
                                                                                   'application. Arbitrary '
                                                                                   'orbit and Fourier-space '
                                                                                   'universes and every '
                                                                                   'profile identity remain '
                                                                                   'unchanged.',
                                                                         'repair_sha256': '14aff9bfba6619c3e6a82192e56b39184a4d625e2259ff196bcfba0e5f511b21'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedOriginalFamilyWeights.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                                'owner_sha256': '9bce546fa36b4786367431c3c6830a49e22b1948705651830a43968e9a693597',
                                                                                'reason': 'Restore the '
                                                                                          'original '
                                                                                          'OriginalPairAllowanceWindow '
                                                                                          'certificate L in '
                                                                                          'arithmetic_outer_index_weight, '
                                                                                          'completing the '
                                                                                          'existing '
                                                                                          'label-window call '
                                                                                          'chain. Both '
                                                                                          'actual '
                                                                                          'source-mass '
                                                                                          'consumers already '
                                                                                          'construct and '
                                                                                          'supply this same '
                                                                                          'pairWindow '
                                                                                          'locally from the '
                                                                                          'original nominal '
                                                                                          'geometry; no '
                                                                                          'final mass input '
                                                                                          'or numerical '
                                                                                          'bound changes.',
                                                                                'repair_sha256': 'd32290cba9454c78eac2c6fbc4eebb70731f356e2a8fbbb5dfbd2c568d038e95'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedOriginalLabelMass.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                            'owner_sha256': '17e9e76cd4644fc83ed6940a55c771c629d47f679a9a86033c991ee1dcdf900a',
                                                                            'reason': 'Restore the original '
                                                                                      'OriginalPairAllowanceWindow '
                                                                                      'certificate L in '
                                                                                      'normalized_pair_original_allowance_from_atoms '
                                                                                      'and '
                                                                                      'normalized_pair_original_index_weight. '
                                                                                      'Their proofs and '
                                                                                      'callers already use '
                                                                                      'this same original '
                                                                                      'length/scale window; '
                                                                                      'normalized children, '
                                                                                      'divisor weights, and '
                                                                                      'numerical bounds are '
                                                                                      'unchanged.',
                                                                            'repair_sha256': '42de50813a1a211a09f234f29eae7abb57e01f0ea95f94e039a91ca45318a073'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedOutputConditions.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                           'owner_sha256': 'd8f22913fad71b26a44aa4c518834ab1f139fb7f03f6eef9ba809dbc34f02ef8',
                                                                           'reason': 'CI74 finite '
                                                                                     'scaled-kernel '
                                                                                     'diagnostic: provide '
                                                                                     'Measure.smul_finite '
                                                                                     'with '
                                                                                     'ENNReal.ofReal_ne_top '
                                                                                     'explicitly.',
                                                                           'repair_sha256': 'd7a8e3100eb2181ad7aa5a68bd70f2b01dacec09eb665265ee8414fd331029d0'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalCentralCoefficientBound.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                                'owner_sha256': 'dedbd5394d13397fa3784de87f08e604b3935e61c6fc5e4e2abb6d225c76dce4',
                                                                                'reason': 'Same '
                                                                                          'section-certificate '
                                                                                          'cause as CI78 '
                                                                                          'CompleteEngineOutput: '
                                                                                          'include the '
                                                                                          'original parent '
                                                                                          'domain in '
                                                                                          'comparison_scale_left_nonneg '
                                                                                          'and '
                                                                                          'comparison_product_eq_power. '
                                                                                          'Their proofs '
                                                                                          'already use that '
                                                                                          'domain and their '
                                                                                          'actual consumers '
                                                                                          'already supply '
                                                                                          'it; both '
                                                                                          'comparison '
                                                                                          'rectangles and '
                                                                                          'scale conclusions '
                                                                                          'are unchanged.',
                                                                                'repair_sha256': '399ef90a44c0ecfb95e70d9c5768642fefbbe942b889f2473ccaf9714c049582'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalExceptionalExponent.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                            'owner_sha256': '7d85a16ee182434ffd6e69f2fb7b6bace51482833d03b79b77c410bb640a085d',
                                                                            'reason': 'Restore the original '
                                                                                      'parent domain in '
                                                                                      'original_total_excess_le '
                                                                                      'and '
                                                                                      'labelled_total_excess_le. '
                                                                                      'The proofs consume '
                                                                                      'its existing '
                                                                                      'padded_core field and '
                                                                                      'every caller already '
                                                                                      'supplies that same '
                                                                                      'domain; original '
                                                                                      'lengths, padding, and '
                                                                                      'all conclusions are '
                                                                                      'unchanged.',
                                                                            'repair_sha256': '9f0f9d425c674b6c36a02810878eab42543a68cef35410a3c49b1e28c56161bc'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalProfileAtomBounds.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                          'owner_sha256': '6fe6f083bee21e11214ceead9d7a2a17003595eb429cce70395a35f09eb86156',
                                                                          'reason': 'CI75 and owner769 '
                                                                                    'native diagnostics: fix '
                                                                                    'all seminorm sup '
                                                                                    'parameters before '
                                                                                    'transitivity, normalize '
                                                                                    'schwartzSeminormFamily_apply '
                                                                                    'explicitly, and unfold '
                                                                                    'the left/right '
                                                                                    'representative in each '
                                                                                    'support-membership '
                                                                                    'goal. Retain owner '
                                                                                    'include parameters; the '
                                                                                    'profile and bound are '
                                                                                    'unchanged.',
                                                                          'repair_sha256': '95f4e8c8a975b21cd1b66f719b6df572ce5ffc89e38d95a5e2df7e08439161e7'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalUnionColumnNorm.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                        'owner_sha256': 'f999fbc73bb9d3ce0e1e371a48a8542c1c368461c243b3fe0c06e5dd63ba5994',
                                                                        'reason': 'Exact owner-reviewed '
                                                                                  'e76eb348a867a89dc873b6abe3b4e1211621741f '
                                                                                  'source: restore include '
                                                                                  'domain in for the '
                                                                                  'existing centered-union '
                                                                                  'scale-window lemma; '
                                                                                  'actual comparison and '
                                                                                  'Cartesian-column '
                                                                                  'consumers already supply '
                                                                                  'this original domain.',
                                                                        'repair_sha256': 'b834d9bebdc59790b5d0dd17760e846daabe44f169cab7a820ec0b66dd7ffcb3'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SixthDeletionCapacity.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                      'owner_sha256': '5e5b9001fde21d997b8dddb5b8c0add77d3dbd1029ec3b5ffa06a8cb498cec89',
                                                                      'reason': 'CI75: join four field '
                                                                                'projections to their '
                                                                                'parenthesized receiver to '
                                                                                'correct Lean parsing. No '
                                                                                'primitive parameter or '
                                                                                'child-budget conclusion is '
                                                                                'added or changed.',
                                                                      'repair_sha256': '305da4121e42b6236f757ee6a5ccc28635754c0db699d30c7279c2114e6ad4a8'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SixthDeletionGeometry.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                      'owner_sha256': 'ccc37686d2cc3fc1e52bfe1d5597108b4b1ef30bae5af2bce06bd5ae63bbc3c0',
                                                                      'reason': 'Native elaboration repair '
                                                                                'from the exact owner CI '
                                                                                'log; original mathematical '
                                                                                'input and conclusion '
                                                                                'retained.',
                                                                      'repair_sha256': '6df10b0155e859f365e5ebe67d8593bb63aaecb86b81ec2f0b7a1e3da337c638'},
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SlotCompleteEngineOutput.lean': {'owner_commit': '76904bc272e28e0de866bea0aa60b53a54d6c01e',
                                                                         'owner_sha256': 'b35b55aa79d2cc3b0fa629090e86ca105e9d025a761eabcc28d5b2b806c665db',
                                                                         'reason': 'Same namespace root '
                                                                                   'cause as CI76 '
                                                                                   'CompleteEngineOutput: '
                                                                                   'open IsDedekindDomain '
                                                                                   'explicitly for the '
                                                                                   'original '
                                                                                   'HeightOneSpectrum '
                                                                                   'arguments. No '
                                                                                   'declaration or '
                                                                                   'mathematical object '
                                                                                   'changes.',
                                                                         'repair_sha256': '2a65b1b341c24852fa774cd040330f4cd1ce46d1508acb33ac19eb8fedf6cc16'}}
PRODUCER_REPAIRED_SOURCES = {path: entry["repair_sha256"] for path, entry in PRODUCER_REPAIRS.items()}

SOURCE_COMMIT = 'c92578b1fa556b72d01c6ff49bac7f27885f09d7'
SOURCE_SOURCES = {'Expansion/ActualAnnularIdentification.lean': '1dc3f7a434dc16630aaea627222dd5a162b17a6fa89da2337c0e2107f06eb61e',
 'Expansion/ActualCanonicalRecipe.lean': 'bbe2d85b9aad898c8e32dbbdb3f22d91c39830a4f7fc4aeedde38947badfc011',
 'Expansion/ActualDeletedZetaResidue.lean': '31fbe2aff54ee678c67bee969447463f960732a4a8f1bf41582f76726cf56026',
 'Expansion/ActualDetectorSaturation.lean': '3a8c293e07e58a6505db566fb1a9b2de80333dc0e47ee81b7b963fb8de0c61dd',
 'Expansion/ActualFiniteRowHeightBudget.lean': '97ea69d75e2fb1cae44bfc2e84a7c0c541c95a32b58ffea77b9ab81835c06c77',
 'Expansion/ActualHeckeSaturation.lean': '4ea487d23e3e6c5fe11faaef7a06e9092397d4bbf32c247cb3cbe73372836273',
 'Expansion/ActualHeckeWitness.lean': 'da3ec13f0bdde1b2de57980f951157475660f5cfd8a789208b2f45f53b5ac405',
 'Expansion/ActualLargeRowBound.lean': '46dc115926409427b19d2584a9157e0f06828cc5b54faa795e77fa1bdbe6fb49',
 'Expansion/ActualLogDividedContour.lean': '9e14ecd8fe8498643e554a32b17a40f2ffe2a1d633b228740fd095b05d2dda47',
 'Expansion/ActualMellinStripDecay.lean': '73c00eda5131f29cfea906a3483250eed3da00bbbb21af949bcf95d57c8cb086',
 'Expansion/ActualModerateCorrectionBound.lean': '5660fb1d95b512403338a42fb76eefa99837f19c7feda5f4b32a2d9c897e91dd',
 'Expansion/ActualModerateKernelDecay.lean': '778c13c45c344c0770c85b2a96296bf4258b0d10e8ecf76a446b2cf528efeead',
 'Expansion/ActualModerateSweepHolomorphy.lean': '7ebfd01d5aac9854147ce15c513be6fafbcf8c3f619b2678452e3f1050bcb4c8',
 'Expansion/ActualOuterComponents.lean': '84e99b5530583555396a7afe7bd41aa706bd9bf6fcbb5370f274c2319afd2ae6',
 'Expansion/ActualOuterContourTransport.lean': 'b5ff3e936c49959490740a0a78c3db3fe8de4f8b3cb2ceb76cdaf24cb480d05d',
 'Expansion/ActualOuterCorrectionStrip.lean': '2572d083e959ed1ee998b5fbca9f4d3a8c581fd1c0bb132aaf248f98cf974ae2',
 'Expansion/ActualOuterHeightBudget.lean': '900da9cbfed27777c2352159c634d22348f098137be4f799b14eaf26a2df6c69',
 'Expansion/ActualOuterKernelDecay.lean': '262be533bba0398b829338ea51f65e3f72318d1ab306219b30614158ecb5fad8',
 'Expansion/ActualPrimeArithmetic.lean': 'e8a63261ed581fcff293ab9af4afe10e510eda42d96de011f25ac83041166fb0',
 'Expansion/ActualPrimeCancellation.lean': '7cd1bf4be3997341fa22fa6795c049a3b338149efce152337262133e65227a73',
 'Expansion/ActualPrimeContour.lean': 'd87e90e11109c5af6e0254454cbabfd5bf5017cc33152dd1561a0a7344a6ee2e',
 'Expansion/ActualPrimeIdealWindow.lean': '72198cb0bb4e5dcc8a64dc4c6765f76a085e357673e253f79404424d0db24f97',
 'Expansion/ActualPrimeLogSeries.lean': 'd2abe03bd6d98f00d513d8ab658dd9ab7f9e6322100b3bad45c4a8880809e0a3',
 'Expansion/ActualPrimeNormalizer.lean': '6900a84fd739a1e38ec5bdd734962755a5ad1b4e13aa436b06b7bf1316406292',
 'Expansion/ActualPrimeWindowPositivity.lean': 'dfb1a7ff8f999882a2a180be2b700528f5f70d9b3c69a3dfe53272219c198fdb',
 'Expansion/ActualPrincipalExpansion.lean': 'f277111992a792054ddea6059d9b5ea381c10c06ce497d70d222eab9b19ad027',
 'Expansion/ActualPrincipalInitialTransport.lean': 'bc34c8d8d7286cf13237b77fb53a97a5c303569f410997393a2d145d23da351a',
 'Expansion/ActualPrincipalKernelBound.lean': '357611ecc8ab4eda287038028c76132cde05353a1109082ad2c814b32b6a9d7f',
 'Expansion/ActualPrincipalMainContour.lean': 'f40b015e729b442f2407baf13f9f59fadaab47291568ef711e24f1c37e298580',
 'Expansion/ActualPrincipalPoleLimits.lean': '960adebae7e327e764ff3ad5ad8ad4d2dcd42b3500f2c8433ff61ad79e615999',
 'Expansion/ActualPrincipalResidueAssembly.lean': 'ed8b6db965375897b4aa3fcfbce951e757c145adfa90cd2b598708ee36167750',
 'Expansion/ActualPrincipalResidueIdentification.lean': '7de01f9eeb97b56e2d3a4f4d395efec18263ea2b5dfe8ca3585ca4e4fbc4848f',
 'Expansion/ActualPrincipalResidueKernels.lean': 'c19817c2d6f0f6cb4fcfa58a892608b1a5bf594f550c5e54294bbcefd56af469',
 'Expansion/ActualPrincipalResidueTails.lean': '19ad1476683499b50b974a8701f46497ce6d918b6b60819485e5558d2968b7aa',
 'Expansion/ActualPrincipalSlotRemainder.lean': '00868a35d993c4ba89e658c0f542d71e01e9b9fb2d296f01b2e6abb8457e3b24',
 'Expansion/ActualPrincipalSweepDecay.lean': '576cfba227f79f9743b97867f22b36f79a23a66d98a4654ef8c8b9e297617292',
 'Expansion/ActualPrincipalTruncatedShifts.lean': 'cfc2467aab2b23d257202ba3a133f980ae1a3ca38b3acae78fa3566c5f1c9429',
 'Expansion/ActualPrincipalUniformDecay.lean': 'f2900f8817e66dee37a7b112bb1c40c3e2ea72f7f561c8b7f32435b2f819e4fd',
 'Expansion/ActualPrincipalVerticalRemainders.lean': '0efd0c4aaf432eed27955c7e8cf93bf157a0b8e1fbe734e6c5e32918e901971f',
 'Expansion/ActualPrincipalWShift.lean': 'da037f6d7f67db8ea4e47d70b9cadeb4fc8d043489974e22b84ca09f6e23503a',
 'Expansion/ActualPrincipalZShift.lean': '279e8da392dfe0683104415537e5cc10c764eaadcf22b5a69ab0260d82289963',
 'Expansion/ActualProbeContext.lean': 'cb767701f1b7d16bdb1bb6b74ece8fc1aa0fe138127f38066324e8e50416d782',
 'Expansion/ActualRecipeData.lean': 'c59210c89f560cc474dd5621c0338fa7b08cd4903b3a16d534fdeff22c8d0484',
 'Expansion/ActualRecipePolynomials.lean': '0a738a23390e9ae0e2028989942d61f9a28c6c8ac4d9aa02c2a8dfe08c6a31c1',
 'Expansion/ActualRetainedComponents.lean': '45a8f91840908596c495f10fa6b15be77e0db16c5a9cc09a3a69d67d646a3aa2',
 'Expansion/ActualRowKernelHolomorphy.lean': '34f2c80bd324d43bbe3724c4fbe12ab1d5f9608ea8965793e62a63cdd1126273',
 'Expansion/ActualRowStripBounds.lean': 'b57c338c297783015ec8a2a079454a88b9ff44767576045f41c78fc81849a613',
 'Expansion/ActualSmallRowBound.lean': '98f10d69b8c08f887fcc6d1382e873ff0e3c3278e4d18d5ea3faa428b6877831',
 'Expansion/ActualTargetReciprocalStrip.lean': 'ee62cf2486eaa24dccde2d6cad506d4205070cef0ab9868b5ecbeecd5af6df2a',
 'Expansion/ActualTerminalFourier.lean': 'f0eb11f389868be04168875ad66e20042fcfd99d775d4a1b3fd65fb2cf9ec16d',
 'Expansion/ActualTerminalSaturation.lean': '63073693a647d599466452d19a0c710e48d61b8eac66c621570e8fccfaf07426',
 'Expansion/ActualZetaHeightBounds.lean': 'db264769f500195c6f31892b88e56753ca84ec850d0b4a5330e9c41222cfab3c',
 'Expansion/ActualZetaLogDerivative.lean': '05bcaddd740f91cdcfe843764e93a8cb64922bf39dd6ba8764e7807a256e5b21',
 'Expansion/BufferedSelection.lean': '28e2fbcbcf6031e48e1e579dfb7eeace7f2dc5bebc628ae8fa0a175e8ec1ade3',
 'Expansion/CanonicalAmplitudeCover.lean': '6460448b05c1ce236940681fca7a4d4fdc530e45d35c9cf41996aeeaa2f7d099',
 'Expansion/CanonicalCutoff.lean': '52bc85bc1bcf0baa8b4fc8234536aafe907171d16e4c6ad77f5384e2c18bfd2f',
 'Expansion/CanonicalDetectorBounds.lean': 'f7d5adc0112531467b01420354ed55e6889cdccc939b0c786deb74e1bca7dacc',
 'Expansion/CanonicalDetectorCharacters.lean': 'ae0ef1f683194e8f1659935437b48b76ff3d5ea7acc7e98b9e777f7b76ef6609',
 'Expansion/CanonicalModelExclusion.lean': '6b6da1345cbb4d880711bb617430080db7b2dc896e0048257337ad2804ac14dc',
 'Expansion/CanonicalRowSaturation.lean': '1c2c577ae9774ab25c7098af9a19fbc9e388017101a02483bbecacc148a7440c',
 'Expansion/CommonSampleTransport.lean': '7b32f92da0d22440144341883a306c75a0343b63515a79a6261e2ff57d97142e',
 'Expansion/DetectorHeightGeometry.lean': 'df740825aa600ce9e1a7f616157eb096c88c6b6450a5d19e5864c33b81a5c6dd',
 'Expansion/DetectorProductBudget.lean': '3886136ed9503b3ceb8199b1213ff994c8bd9e5fa6acfe9fe9e52822e3d5c0aa',
 'Expansion/DyadicSupport.lean': '28892e04de8b2d6c38b30b9575c2683370ec753c24b6c37f60c829fdc00b9270',
 'Expansion/FiniteTerminalLabels.lean': 'c9a26ddc427903c253538f278f56f5fc4db23440b71bbe0fe3459f3f7a8872c0',
 'Expansion/FiniteTripleContourTransport.lean': '54cce32fedc41281e6600fa1d2a5b3fe13177e0c94a0e4193e2a550c6ade5e00',
 'Expansion/IdealDyadicExtraction.lean': '9da8c97c60c875305dbdeebfe5ffffc9adc4ebc56911a70a4d694571fa9b4814',
 'Expansion/LogDyadicBridge.lean': 'eebb2d09cb1ee65ee1dd12dd9454dfa6b8e7398494992d2a620bb6cd4e7c789d',
 'Expansion/MeromorphicZeros.lean': 'fbef3321b0b35d0b7b6dec0d3498a4a96824c46ca2410efea2750ab9d26cb736',
 'Expansion/NormalizedContourBudget.lean': '45ddb881528db6a21eef9dcf7e41487c9dbafd2294e1fa56515b934ca18b49b1',
 'Expansion/NormalizedDyadicExtraction.lean': '19fd4f17d72f33571d22ada83588642ce5b7f5bc9d57e3251bbbea9882c6a760',
 'Expansion/PhysicalAdditiveOrigin.lean': '0829777b022808235e807b3ceddbb2d398345f474fe20a9571ab207fa61fa716',
 'Expansion/PhysicalAmplitudeIntegral.lean': 'c68ad56f655a1623dd627fcec59aed145ca74d58d136491a8762155ab3ca3408',
 'Expansion/PhysicalAmplitudeProvenance.lean': '84d5aec710fe6176d9168191133ba14ed068ef9e80fb01173de246fa36c04491',
 'Expansion/PhysicalAmplitudeSource.lean': 'ef8c7d77b294faff22b0e1c79b242537d378fc295aae59268936c8787492a4a2',
 'Expansion/PhysicalCompensatedInitial.lean': '724edb9c5b16c41fe390446f480040e2b0feb2927a72d807163c8bfebf4c4730',
 'Expansion/PhysicalCompletedPoisson.lean': 'ba10bf2f7d02e6a90ccebd3722dbc08fb214dcef4d7d53bcde24364cfe519950',
 'Expansion/PhysicalContourMeasure.lean': '74b86d44f9436b0dc08759494af1540aa280a25dc188edfa479f39342f2134ec',
 'Expansion/PhysicalDetectionParameters.lean': '87dd3caaa21b17d3608cd27b10dae4c2f7eee0758a02627883e210c2fc183cf0',
 'Expansion/PhysicalEulerRegionFactorization.lean': 'fb060045819429a9848f1acc7b7a20a0606557c397f0dd197fdc573e706757fd',
 'Expansion/PhysicalFinitePoisson.lean': '93e089a5819fb05269e795d446269ecf6d7fe3e43f731a42c5132e0ac637989e',
 'Expansion/PhysicalFloorSource.lean': '15a181e51614ea4563634347eb058d83e8ffe2c527c49e8f2a753e4440ded179',
 'Expansion/PhysicalFourierNormalization.lean': '022d0693c56a662eb14f0f0b56129cc6ba6321e3e75f321ac49907a082e9557c',
 'Expansion/PhysicalFrequencyReindex.lean': '65a9e1c316822d88b9193125704f4170b9d5645cb9bd403ae26577eb7abb17ea',
 'Expansion/PhysicalInitialHeight.lean': 'f0d60ba187a546d43eee2de099d557f01386c4e62342f1f28de42cb03a334cc3',
 'Expansion/PhysicalInitialMellinAbsolute.lean': '00f913fcc65c9fac923f7231c282d976ead4e6dff2946539ed981190bcb93e33',
 'Expansion/PhysicalInitialMellinIdentity.lean': 'bac104fd1f3e5526104f312fda12a9dcf72c86413997a9ed94d309d09c8f35f0',
 'Expansion/PhysicalInitialMellinTerm.lean': '2a6b2f8fdeb1d2b6be10afa14ddb59be131c2f1ff3e664d7ad265425d2ccc92d',
 'Expansion/PhysicalInitialMellinWeights.lean': '7386f1225e9fa2db366213664a9787d3119f6ed842830363e7d4ea296f2efe8c',
 'Expansion/PhysicalInitialPowers.lean': '377c313a36049f42fc4f12ce74991265dfd95cb1543177215d9f82eee6e6fd4e',
 'Expansion/PhysicalInitialRowSum.lean': 'b4f9bfc182878ed7dc670208532e3342d3dc223fe254cea046673363180afb7e',
 'Expansion/PhysicalInitialRowTruncation.lean': '59b736044893abf48e3f58b987d18f94f09a81353f76ca7568e75f96e09f1c37',
 'Expansion/PhysicalLogDerivative.lean': 'f5d8933df9050b2e2a63c5f5dfd0ee3c8a43c36fa59182d2cf39b5de22ffa8c5',
 'Expansion/PhysicalPositiveMellinInversion.lean': 'fc44870fc80d124fa557a440133dc18616c933ab14495b7732a67e896764ac82',
 'Expansion/PhysicalProbePoisson.lean': '5b071749a321d4832bb47fb0b93f0cffbc8634f80ad4159a1f18d78605cd273b',
 'Expansion/PhysicalRapidTruncation.lean': '4ff4b8579411fd5d14127fb4a83da2c3e618757b7efe2a48d23efdae8f4040a2',
 'Expansion/PhysicalRecipeAssembly.lean': 'd6cb8bc2861ded09fcc04fd7d6c1ffd5a417f65eca844c1ae6cbc0fb368633f3',
 'Expansion/PhysicalRecipeOrigins.lean': '1fdcb8688b9098e2b0d89cf8796be584cb393944d32fda0ab71fbe9880f5fe23',
 'Expansion/PhysicalRecipeParameters.lean': '0da77b957ffbd26d3841bf57b2360215bb5b7b4b53279950d72e44c067abf219',
 'Expansion/PhysicalRecipeRemainders.lean': 'd039d63796dd67a85b9e5e8fd54ac35970c8403c5f59d8ba9b743274fc4bc7ad',
 'Expansion/PhysicalRecipeSchedule.lean': '4e32d72c5cae417d793458054b2a3d817638e19c4f4a6d61c8e12d47bdabfb6c',
 'Expansion/PhysicalRowDetection.lean': 'f5f3bede39888735c19374c5105e8f0c46c87e955c62c54b8e48e93010e58ca2',
 'Expansion/PhysicalRowPoleExclusion.lean': '9122960e92a479bf7ff73699653e8492c156e8b304fd592d2bf5cf790f9aced9',
 'Expansion/PhysicalRowSupport.lean': '7c760942cfcd236df01f6388cdb2db9144e0f9662319d769abd904ed73455fa8',
 'Expansion/PhysicalShellPartition.lean': '0829292b45a3c98e4e45552c39a1523142cbd185659f1c788543c69389c7a0e7',
 'Expansion/PhysicalWitnessCover.lean': '39309b2514528aa8585fa244573ec08ea3326b8cbe05138dfdc393dfbb067bad',
 'Expansion/PowerHeightTailAlgebra.lean': '666ddb65c2d509082f830c5961a37623287054ec5f3aad66516dc1bd32c8560e',
 'Expansion/ProjectMeromorphicDetector.lean': '8868c1ade967c1a11fd909ed0a44fd94abe5728594060cdb5a34e2eaead2d6d6',
 'Expansion/ProjectSelectedPhysicalRows.lean': 'c5bb8e16b51db2783deaa31fc377b33e5bae5c9f506862b4e6daf17200026f0f',
 'Expansion/SelectedBufferedRows.lean': '0ad3a3b34de88ec51c93da378d003349235a2ed383d31093e3a2ae7b73b06f5e',
 'Expansion/SmoothDyadicPartition.lean': '64ea8254a1085ae37f1e76683c3baf082094a25f21bf07bcad839544322d05a3',
 'Expansion/TerminalCoefficientMass.lean': '899b83b2c0f2d6d93d31c239c934d84da54faf5c6262907fd8a839c51611b323',
 'Expansion/TerminalFourierTail.lean': '070d38d0a670043b4a0185379c3c2969958dea6122bf24833c9f164c094d853e',
 'Expansion/TerminalTailBudget.lean': '7266f213cea6d6c48ea596fbdf63b9a2a314443ac12d011be357f16cbd5906b5',
 'Expansion/UniformTerminalFourier.lean': 'b51bd296e1b45eef5091a563f820e449ae03f6d0c9a14c4522b58309915dcbc9',
 'Expansion/WitnessLoss.lean': 'b5f6edf51ac9a62ff43ddc3a859222476798717b2daa307a3cb8d177e36c0457',
 'ExpansionDetector/AnnularNormalization.lean': '24583d851cf7af982e51855d20526992bdaff87520f1e1f15d56d34242331eef',
 'ExpansionDetector/DetectorPower.lean': '108099a277612fbda6e10883c0c7d5efff73032dc3014ec585a6ae75eb22aa48',
 'ExpansionDetector/EulerDeletionBounds.lean': 'ec0efe02f60a7227834a6768ae44da757162eca652010a003f92cc2bd4f63d45',
 'ExpansionDetector/EulerDeletionNegative.lean': 'e438ea4cbf69210e10ef886b23a207d865e78f493aff2cfb8f6288f8e7e12015',
 'ExpansionDetector/EulerDeletionSpectrum.lean': '15175170c5789a9f018096a5c0a50c18c6a3cdf0174f75357a86d20e149dfcf2',
 'ExpansionDetector/ExponentialMellin.lean': '0f0cc5a020fb8e89a63362f8903df27a73dcfc7e5f05fb890dbe912f59626269',
 'ExpansionDetector/ExponentialSummability.lean': '2dc92793705fe05a5f545ce1ff665317758a744eb195c1168c1d50720c58bcd4',
 'ExpansionDetector/ExponentialTail.lean': '2526f0b0ee101e267053e0415f7180e56b2d11e68bdc97284996d4b3d8f0eb30',
 'ExpansionDetector/FixedTypeGammaReflection.lean': '83c5e5946d783d01f6ef3ffa91f29d81bf1ca36bf42b7b351e31a504febbd8d0',
 'ExpansionDetector/FourierNormalized.lean': 'c626fcf3dbb04c84160c6777ee1fb61a5996079e09a0ca42793d66ddf852d4e4',
 'ExpansionDetector/FourierSeparation.lean': '77b151de0ceab7f4db6e278bbdbacecd615cf560c468892e8fdc23fd27bfff3d',
 'ExpansionDetector/FourierWitness.lean': 'd70d35df15cf99bad0e3fa14b15d26f55ce6f6603f48aa03c40daa239df7830c',
 'ExpansionDetector/GammaDecay.lean': 'f3a1198fc2cdb4dd130c3ddaa4a27a1171743564bb904b28fcc81af2ddceff29',
 'ExpansionDetector/GammaVerticalMoments.lean': '34f0ee22a102596459abb47785037edaedd092a0438d17b729a81f99d04046ca',
 'ExpansionDetector/GammaWeightedZeroShift.lean': 'e6f5fb247267bdcfac2823b616a827c64ebf6f1c04f412e6b3b69523b1cb9334',
 'ExpansionDetector/HeckeFixedTypeReflection.lean': 'e2dbbcbc801fea47b2ee4c0c4b4209e41e641f92c34b8ce5a6a775af9f304c58',
 'ExpansionDetector/HeckeGammaDetector.lean': 'e086aa668e631c196b6c71ceffcbfcdb4bc82f26657d10dd0de750bd4d58c252',
 'ExpansionDetector/IdealConvolution.lean': '9f66d176f0cff781eefcf2e71875bd5a017f4f044ca87e87c2db1bd9f82b3f61',
 'ExpansionDetector/IdealCutoff.lean': '6da0bdd00db0e332cacd361b2687360cdf24dc526d58832a74c230d3110e4d87',
 'ExpansionDetector/IdealDirichletProduct.lean': '2ee49a3adc9f74164ad934a034d5c37403368c73d0baea95d8f5e1328f31f32a',
 'ExpansionDetector/IdealFinitePair.lean': 'b53a18cb9bfb540e5b8c4e5d099d1f62e052bb028d5e729f4407bee2b14052f1',
 'ExpansionDetector/IdealMellinIdentity.lean': 'fb884ce445300c7450749bb98792c5b62bfd2a8a9dd1fa835e9ceae2824a7e6e',
 'ExpansionDetector/IdealTail.lean': '3021ed2f4c72ca5ebba7623239505cfbe7b87d09bff8c82a8f8ffe0b14a54f62',
 'ExpansionDetector/IdealTerminal.lean': '14d901d648800ddeeed7962a8cd9e9e6898719bcd51400d4f1fe84d5ede2c4f3',
 'ExpansionDetector/IdealZeroSource.lean': '11288f1010d98b8b246a058527f09255894ac9ac493b44098dc0a8de3341af68',
 'ExpansionDetector/MellinPowerBudget.lean': 'c6190f86cfaa38e4b1e869962d4cd4ddefaee36f4468917b41f79530772d2c61',
 'ExpansionDetector/MellinScaleBounds.lean': 'c865ebcc2954afde38a2ed942b0bf44bfd758ba4819c7f37e287a2c65e3158a3',
 'ExpansionDetector/ZeroDetectorBound.lean': '60818a49846beaf2ae8faf81b967bdfa80a7dae0028d1b16edc2947d859d9f4b',
 'ExpansionInterfaces/AmplitudePartition.lean': '3c4422dc184cb1bb8db2c0b66acf848382951da004be0f173f788b78c5612e76',
 'ExpansionInterfaces/AnnularContourBound.lean': 'fb4ad718c2df49ae582608d40d45be2de4ce86a3457cb06f70dd8ecb00be02c5',
 'ExpansionInterfaces/AnnularContourDataBound.lean': 'b41d94d9fd50f785dccae6ca37671d87b53f121d6023daa51f9ce74e83c833a9',
 'ExpansionInterfaces/AnnularContourUniform.lean': 'f48ae45e0b338b5ccf478147c94efe10175cd9bf5fe9f49e167494a383355ab0',
 'ExpansionInterfaces/AnnularCutoffFamily.lean': '3988372ad92c139223d3c1e3b997f56cd568b7339c8a192d91a94f34a88aac7d',
 'ExpansionInterfaces/AnnularMellinDecay.lean': 'f2c958f3b8af1c68a8648193bafe55c2b80a955df594281173b0d425ff1d22bb',
 'ExpansionInterfaces/AnnularMellinIdentity.lean': '1a13bc6a1913b07c140362158e191e4651e339d2c690202c2727eae3b4be2fd6',
 'ExpansionInterfaces/AnnularMellinProfile.lean': '61627a285dbe597fc15b0f6efaad7b1bc5e3da1f469bec2dc6201039a21e148d',
 'ExpansionInterfaces/BufferedHeights.lean': '6f4c9763dbd499486234b510d7c3d287423c18537702da685ad668929642adfd',
 'ExpansionInterfaces/DyadicCount.lean': 'a52681bd30d1e18c7c20b32165ddf11136870f357a21f267502caffb13f95331',
 'ExpansionInterfaces/DyadicShells.lean': 'a8330e7066ff7a3b3c53f9b4e8b6d6af137041a29cb6b0dab5d1bd31b3123610',
 'ExpansionInterfaces/FiniteMellinRectangle.lean': '850472edc58e3fd80b9ea43cb9dd406549ab250be2e0d714404c43e51995d506',
 'ExpansionInterfaces/LogDividedAnnularProfile.lean': '4156f263db3f8b7bb9b191754561e548fbacdd96060c7c9840f9caa0d893221e',
 'ExpansionInterfaces/ParameterChoices.lean': '371926930bf1e35af484c711c2e2d0668f4dd978f466ca34009c8c425fc86d61',
 'HeckeAxiom/ProbeNormalization.lean': 'e63bb8a68b02cd254bc312dc1ab7a6eef1f389d6974d3685662304adc2883b25',
 'HeckeGeneral/Analysis/CompensatedRowKernelFactorization.lean': '06b0dd8ba3c445ac8b679969f6c600bedbbb8deaeed5ad7549c5842bc883d1b4',
 'HeckeGeneral/Analysis/ExpansionBufferedPolynomials.lean': 'd00e27d3a4d9e0e8a11c0b2e4dc5a41018c73606695e3895df3fe8e81910c337',
 'HeckeGeneral/Analysis/ExpansionCutoffPolynomials.lean': '90c9d28a5ca653f8a6781163cbf9ca553714d30d81bc031b243ac1c6e6a5c0ca',
 'HeckeGeneral/Analysis/ExpansionDeletedControl.lean': '888aab27a88299ef4372e2955385d78d6bb31be5fc822926e1a3fc11847b8cf3',
 'HeckeGeneral/Analysis/ExpansionDetectorInitial.lean': 'cc56b060ccfa4ea41bd1341306baea84708417288bcae5cd28738a33c5ed8592',
 'HeckeGeneral/Analysis/ExpansionPolynomialSupport.lean': '053301ad593b551b8056181776574c16d4bb5b9bf450f9f3dd3d55cb0f04b510',
 'HeckeGeneral/Analysis/ExpansionReflectedPolynomials.lean': '8288c0a42967d6d89789330ffa92e4035ee3672493252cdb09c47441d26cde39',
 'HeckeGeneral/Analysis/ExpansionScaleBounds.lean': '30028ee5faa10950b650a2a7a5c87bf48d179a0308453efc349fbc4736199c1e',
 'HeckeGeneral/Analysis/PhysicalProbeContours.lean': '39a0362fbd49c3e06a4f8fec7534412171d5ad5b3dda16ab9cf1368b9d8f4a16',
 'HeckeGeneral/Analysis/PhysicalProbePrincipal.lean': '9722c13ec6321c2e83156bf90fc7fe4b504caaae5cb16546b8d85e04bd36c0ff',
 'HeckeGeneral/Analysis/TInputFixedBinTransfer.lean': '0ddc83ca56ed45bbe0cb9793b64e7fe9d165000410c1b04cfee2125bc3c9a015',
 'HeckeGeneral/Analysis/TInputRanges.lean': '08d32797004b33d20b34ae988083a4f011aec04ab957f3fa02287e392f5e9d45',
 'HeckeGeneral/Characters/RadialNormalization.lean': '4dd46d94309b79ffe0129ed80e7352a6b0448a9031cb31c646a5772bcdb8c42c',
 'HeckeSkeleton/ExpansionDetectorBridge.lean': 'f66269eea8e90fd1ffe4e76000cfa00c9b2d09d04bb6049530c7c11a5f3cc9ab',
 'HeckeSkeleton/ExpansionModels/ActualKernelRegularity.lean': '5ecd2af7e7e7f19d925fe86444a0356d39a65649382b753686ad392e1802dce2',
 'HeckeSkeleton/ExpansionModels/ActualMellinRegularity.lean': '6df7ddd61d7f29f5d4f3f2d4699db3bc5bc146d36c300467341933d2fdc3e930',
 'HeckeSkeleton/ExpansionModels/CoefficientZeroCalibration.lean': '4e6025a85bf031c539c00eca2383c5c0cabb512272cd00efcc3e16fe2e16ab3c',
 'HeckeSkeleton/ExpansionModels/CommonPhysicalSample.lean': '97669340b5fcb0d721550a491cea5ecfcb88ec5fcabaf6ea3e7bd0154de89543',
 'HeckeSkeleton/ExpansionModels/Core.lean': '537b4afd82871e007cb438518e663e9a45c064c3cefecaa81a7ce557eda0f6f4',
 'HeckeSkeleton/ExpansionModels/CutoffLogProfile.lean': 'a5a7140b2b608ae21d9224c8539a1df33412d8e0a6c32886617f39f6b2df1d23',
 'HeckeSkeleton/ExpansionModels/DyadicMomentEnvelope.lean': '63bd533c5a5b4bd2be880ceeb22ef5880f0753e01a2139dfd051bf98f899fcea',
 'HeckeSkeleton/ExpansionModels/FixedAmplitudeLabels.lean': '2c201390ebe4f2e848e7bde655180bbc536443f64081855e599fa07096889910',
 'HeckeSkeleton/ExpansionModels/FixedSectorParameters.lean': 'ac941e5e713cdd29ac0fbbce8a35039d737877e3bb27c338f92141bd2a07d05f',
 'HeckeSkeleton/ExpansionModels/LargeRowAllScales.lean': '1d4c56d87c48814ffbff50236389af2db2d9f75b9dca67fac6387d98a39959f9',
 'HeckeSkeleton/ExpansionModels/LargeRowCorrection.lean': '580e1e7cac31eab82d4b2e8ed6cef676a7ff5f33720a2929056d4e564097f20d',
 'HeckeSkeleton/ExpansionModels/LargeRowKernel.lean': '42aace0b838e8351149ec65f10d4ea98b674d0cfa9b347be2a57b4597dea3691',
 'HeckeSkeleton/ExpansionModels/LargeRowMellin.lean': '1787d3c46c60598d3e90938f2f1a8eea9e0191ed69fe45851053a03dad2093a1',
 'HeckeSkeleton/ExpansionModels/LargeRowSum.lean': '88ab4ae2270048101615b9122f72c759179e89613aa0e7e50e751a75fdc1be26',
 'HeckeSkeleton/ExpansionModels/LargeRowTail.lean': '203e4582616b8359b448f370dbe210a392a8aa23a10fd765cd5d07ac8c8c61b0',
 'HeckeSkeleton/ExpansionModels/LogProfileFourier.lean': 'ea3b5334076360ceeec751684e6b3fcafa55de018a3179bbccc9b3d0d0f341be',
 'HeckeSkeleton/ExpansionModels/LogProfileUniform.lean': '8c5a6f18d612cf822500da52e8f0b98b5ab3906636d8178cecc402568d4d62db',
 'HeckeSkeleton/ExpansionModels/LogTwistedProfiles.lean': 'dad20d5d44d14a927614bfa325ddc65a9d6694323db470c2b541e1d053c37ace',
 'HeckeSkeleton/ExpansionModels/NormalizedRecipePolynomials.lean': 'fc70b3051ba72fceacbaa2c12ee28d0f6f5b86f3ff14585c8436a78a11ba13bc',
 'HeckeSkeleton/ExpansionModels/OriginalMask.lean': '54d66c7dba7a8c5e4065c8909c5b6cccc82612998c0103e3f99fed301e79db4c',
 'HeckeSkeleton/ExpansionModels/OriginalMaskBounds.lean': 'e33ac652c1cce56a0d0d6050810e6061505f94e95b59e5b77de50bd1a5c60fe8',
 'HeckeSkeleton/ExpansionModels/PrincipalRowCorrection.lean': 'caf5204ec69239ef0aea024d742d1623b4a8e37bba6c4df98774b5362cdf64bd',
 'HeckeSkeleton/ExpansionModels/PrincipalRowLocal.lean': '0c5b121d50b0442e7289b0fd128b648a78c67f8e143b8f9bdc5e3d52e3d15972',
 'HeckeSkeleton/ExpansionModels/RecipeDetectorNormalization.lean': 'f2122e09fde131e9b4f0f1ef69e701c0871caa1434e2f22bf3b338eba9c61ce4',
 'HeckeSkeleton/ExpansionModels/RecipeSchedule.lean': '48b1838bd6aa0a1c7229424653ca47c8ca8ebba1abe850592c968964e41a3b48',
 'HeckeSkeleton/ExpansionModels/RowLocalWitnessRecipe.lean': '55cb49edfde46cc947520c2dd44aa57eb2c3d1708ece03b7e377aeaabc487075',
 'HeckeSkeleton/ExpansionModels/ScaleCutoff.lean': '98a5345a361d159a7d17d02b7953cf7f9e562402cda8d3eec912321fd43cad65',
 'HeckeSkeleton/ExpansionModels/SharedWitnessRecipe.lean': '78011ed1fb6076260b23abae7dc22ab40c34686ec032a9e5e39e2b7a83d9d611',
 'HeckeSkeleton/ExpansionModels/SmallRowCorrection.lean': 'c69e9c26751587df8b17964b6a6c753f3f7e501d23eca57bc3ac312443356546',
 'HeckeSkeleton/ExpansionModels/SmallRowCorrectionSums.lean': '49077a9ce25cc22fb4dbb48d9af753e75cdee6b51221e8f773049759c61ce23f',
 'HeckeSkeleton/ExpansionModels/SmallRowEulerBounds.lean': 'c3053c4672741307401b8d56a83b6bd4f1d6aa1a7b4e6e275087918e27275a5f',
 'HeckeSkeleton/ExpansionModels/SmallRowKernel.lean': '9624c9a9b0b4b68126b3fb94d7950b09fd8e1e02476792126150597c6787f5b6',
 'HeckeSkeleton/ExpansionModels/SmallRowMellin.lean': 'ea666c070455042506f26a30cd3cba05aa163f8203ff1b9daeab2fe7c15a94f7',
 'HeckeSkeleton/ExpansionModels/SmallRowNormContinuation.lean': 'c1b548aa57a3e208b39e3642bc48be14bdc752daed6136e0c37a6613371255b6',
 'HeckeSkeleton/ExpansionModels/SmallRowNormReciprocal.lean': '844e037151ab4dd83ed11dd238b0c4c2e7ef8b4130ea53bc10ae63a5fabecb3d',
 'HeckeSkeleton/ExpansionModels/SmallRowNumerator.lean': '8aedc8ac1752d220fccc01b4d21799d4553dae858df55d84a019eec3ad7e4ca3',
 'HeckeSkeleton/ExpansionModels/SmallRowReciprocal.lean': '7b97ea4ddfd5c3f5c3625e955a6e5ca48c181731f2be6cc3e4f6d6fbfcb34141',
 'HeckeSkeleton/ExpansionModels/SmallRowSum.lean': 'd0aa539c587c031be3face33110e8ebb6256c152b75291ee6b1c5a5dfcd4f741',
 'HeckeSkeleton/ExpansionModels/SourceData.lean': '4b40c6980a5cb1e4e4f6b5196c4034049b6c9af107b8bf21356ad7f681f8cdc3',
 'HeckeSkeleton/ExpansionModels/SourceGeometry.lean': '71cf993ca28b14f63ed4fe02456e0227a0affdb9dc02c1bff156cb2d048b6419',
 'HeckeSkeleton/ExpansionModels/WitnessHeightNormalization.lean': '31c92678b8e973f1c1ff65ae9e0ff3d43c17c2d440c2a90d5fea63204ed58520',
 'HeckeSkeleton/HighBinSupport/ActualDeletedEulerProduct.lean': '67e5e608bc6892885b4a3347d47e832812bf143b071413272629867602517f91',
 'HeckeSkeleton/HighBinSupport/ActualDenominatorMellin.lean': '3c810ae5003a98fca3d1f24b74bc565ceaab649373031e850db97a7f586d76fb',
 'HeckeSkeleton/HighBinSupport/ActualEulerCRT.lean': 'fbe1ffbc0cfd85a2ba76515809f59ca956f4594185099f2a0aa100e432b6373b',
 'HeckeSkeleton/HighBinSupport/ActualEulerData.lean': '321d867d65a2975572a0bf5ad59d8ba337ae3ee770472e8cdf1ccd297619583f',
 'HeckeSkeleton/HighBinSupport/ActualEulerProduct.lean': '1892f2c34f7f3786d2244a4f36af051f828a22cbc0ecaf5a5cab4069af6c6802',
 'HeckeSkeleton/HighBinSupport/ActualEulerRegion.lean': 'aed3f755dee0df796ade0bf4d2319408985ff30f35ce7da35eac4a5660bc8cb6',
 'HeckeSkeleton/HighBinSupport/ActualFinitePoisson.lean': 'ba4ff81281de45a25e2dcb91188d5a6d3e1625f1ecb5b2e04bcb359f066e3781',
 'HeckeSkeleton/HighBinSupport/ActualGaussCalibration.lean': '6a6c1a58ceae65776ac8a2f88dcb5d4c8744a934e9f0ec779aa4ae6300970e5e',
 'HeckeSkeleton/HighBinSupport/ActualGaussData.lean': 'a95949016a6329fd2d08d5075cb0ca7c94d2b5facf3adcdc0beff52dc794c680',
 'HeckeSkeleton/HighBinSupport/ActualGaussPhases.lean': 'f5f7a8a302d9a369421d9af122c0673b64142fd2e798b3dbb1804933298806eb',
 'HeckeSkeleton/HighBinSupport/ActualGaussSigns.lean': 'f880ad91d2271c379e66ba3d9731da5bb79b3089242b2a0893313bbba117c951',
 'HeckeSkeleton/HighBinSupport/ActualGeneratorPowers.lean': '2a753173c9a29a9e31bf4c91b7cdddd11561f77305b93e34bf4e01e428d3e188',
 'HeckeSkeleton/HighBinSupport/ActualInitialAbsolute.lean': '0fa849c4bc1a5ebfebe78812849c4eb7b65a3974cec1ad0acab4e3a5b5c54588',
 'HeckeSkeleton/HighBinSupport/ActualInitialCalibration.lean': '551a66e9a323104a5d8e98b61bb65b258c7d9a3aa125f10e26b72fec203e04d4',
 'HeckeSkeleton/HighBinSupport/ActualInitialEulerProduct.lean': '796be2effff6985f91ffef8898b00a3de26cd7ae77ef06f2b822409ab396a77c',
 'HeckeSkeleton/HighBinSupport/ActualInitialLocal.lean': '92bd08f66892af76291a4585980e94587604c1e42713cfdf22cc8da1a98ce2b5',
 'HeckeSkeleton/HighBinSupport/ActualInitialMultiplicative.lean': '9bb0ae53cd7b32de990c92613d79d698a8fa6ebef687e5040a55f8c0d5aaa4b1',
 'HeckeSkeleton/HighBinSupport/ActualLocalBlockSummation.lean': 'faa9ea3ba62e98df73240cbf8f6770391fe0825666b3f85b1744e4e996350f22',
 'HeckeSkeleton/HighBinSupport/ActualNormFormFullCorrection.lean': '4b24030b1f000daf9242ea47affb9138292bc20499b66edcdc1664c493b15ed2',
 'HeckeSkeleton/HighBinSupport/ActualNormFormHigherPrimePowers.lean': '423e0497f5564af0efbdabd1f9b60132d94416a1cb456fe0e6258ff896960a77',
 'HeckeSkeleton/HighBinSupport/ActualNormFormMellinInversion.lean': '1a295d20a1fa7b6b506306ff746420ce0dcf2a41f231c671be34dec14f2798a4',
 'HeckeSkeleton/HighBinSupport/ActualNormFormPrimeCap.lean': 'b2394dffbdb942960e62bebf1d3b7b85852f3e1ce3fc20854304ca8cc1e30d08',
 'HeckeSkeleton/HighBinSupport/ActualNormFormPrimeContour.lean': 'f8115afff04e735daa302256f08fc2a02a442b55360c7c13a2acc02d55469cb3',
 'HeckeSkeleton/HighBinSupport/ActualNormFormPrimeDeficit.lean': '09b0fec3ec6f1c8e5e45e76d0c828bdcc31b40b2659722f87f1313fc164e9632',
 'HeckeSkeleton/HighBinSupport/ActualNormFormPrimeDetector.lean': '7dfc0417f8c1ce6cad8ff6ad2de92438f0e26f2054e572d538482907e848f236',
 'HeckeSkeleton/HighBinSupport/ActualNormFormRepeatedTuples.lean': '53f10ec515c0e835ff417f838f869ba01c9f24eb66c4195fa8021f89dd65b397',
 'HeckeSkeleton/HighBinSupport/ActualNormFormUniformMellin.lean': 'eac9cc576b9310b7351a28c58eb322ea93e9462dd9b0699aa7817d3e053421d7',
 'HeckeSkeleton/HighBinSupport/ActualNormFormWindowDetector.lean': 'b3241f10a4db590a06b039073949be14678a3950389d78aecc4a22ebf405cf94',
 'HeckeSkeleton/HighBinSupport/ActualOrbitalRapidDecay.lean': 'cad1f26eab1a6ee8d316dce3d3d30a917765c4635f5652e937b3dcbc5e6eff94',
 'HeckeSkeleton/HighBinSupport/ActualPrimeExponentIndex.lean': 'ae38cf49b6b2f968b41458b572ae3b5d55ee62dc96afe9700d0d0d9594f97aa2',
 'HeckeSkeleton/HighBinSupport/ActualPrimePowerGauss.lean': '46f24f662005886d1c855bf5bd0737b51bb52d2e345a254aaede6425b304a8f0',
 'HeckeSkeleton/HighBinSupport/ActualPrimePowerSymbols.lean': '4f82201183017cce36e90447bfb0340fc7aa048cb6f2256c9d506eda9ae9697f',
 'HeckeSkeleton/HighBinSupport/ActualRegularEuler.lean': '7fe793e156b5955679947eb8f002965dab901b73f4df167a0ef06fc8a7d4ef59',
 'HeckeSkeleton/HighBinSupport/ActualRowLogDerivative.lean': '292c41de0488989c497fc810b0bcf35002119be684143f28a1124c60a9144e14',
 'HeckeSkeleton/HighBinSupport/ActualRowPrimeCharacter.lean': '5d5cc393c18479bd09b3adfc16a0f59514b91b7ef4a5f107c76f642f8036fa91',
 'HeckeSkeleton/HighBinSupport/BoundaryEulerCoarse.lean': '8b1b4d4fd9dfde16ac32d5782a1ab58846b5f93c36e1f23f7bcf13aed7b25493',
 'HeckeSkeleton/HighBinSupport/BoundaryRectangle.lean': 'b0a1b739b29437a016ea8fbeb8db5c0b03c5a3f6286137695f981a76c7489e97',
 'HeckeSkeleton/HighBinSupport/ContractiveGaussPhases.lean': '69a824bdc2da0e8c168fe4475d9f58e2577ccf08b770da1d051bd57dc8de83bd',
 'HeckeSkeleton/HighBinSupport/EulerAnalytic.lean': '1bc00e3bd1b3efaf93e7ca0672526ac0d0afdedf4197cd39d5ed2097045efe7d',
 'HeckeSkeleton/HighBinSupport/EulerCorrectedRegion.lean': 'bfce53f8f77af5251dc1beb4c2e4822b757fd6b3db98ace079118acf19aa4660',
 'HeckeSkeleton/HighBinSupport/EulerMarkedSubpower.lean': '461632524cb3a1703a7724520f0f64c5ecfea36b0f93ecec419a0f5133ab2caf',
 'HeckeSkeleton/HighBinSupport/EulerPhase.lean': '264a77fd890ff6636ce1404d9253b9c4f3d9713b180f3f3082842b2b8cf554cc',
 'HeckeSkeleton/HighBinSupport/EulerProductBounds.lean': '152d99ba008c32360c8900a2873f37fe4b94cc1f09fd4c585563a5615d5dd9bd',
 'HeckeSkeleton/HighBinSupport/EulerProducts.lean': '7bb0c3af4d3dd96b0add9ba88d3a585f2dc5fdd6b2eff62a8679b711a4ef253f',
 'HeckeSkeleton/HighBinSupport/EulerRegionAnalytic.lean': 'ac40274ca2a30f8e0d421cce71c7fd2795c8c17a80c03767395b181b8dd8f42e',
 'HeckeSkeleton/HighBinSupport/EulerRegionProduct.lean': '65790197956fee62f0753b5f69df9c30e9bf54d50e261c2c9a5ded7d57323134',
 'HeckeSkeleton/HighBinSupport/EulerSweptTube.lean': '55a763de32a7d3f5a28772363cf23df29912c8deccd1d0db9d2d861a8a17908f',
 'HeckeSkeleton/HighBinSupport/EulerUniformSubpower.lean': '7053be2186f1fd38eb4e9e9f961cb89a03963859224968789436e15b7a77f624',
 'HeckeSkeleton/HighBinSupport/ExceptionalSweptTube.lean': '0a500a05ed330618a17c5f1e23168a2c9c426df5b16a365741fd9cd71c9442d9',
 'HeckeSkeleton/HighBinSupport/ExplicitEulerFamily.lean': '3b58a29e92489d184cdcc4b3283c4562d9a90614c4d85932f9422e1cd0c946b7',
 'HeckeSkeleton/HighBinSupport/FiniteEulerTables.lean': '3c579de29d5bd529b8a1f244215c2ff285bf024a22f9c08635a712495356a1c2',
 'HeckeSkeleton/HighBinSupport/FiniteLocalTable.lean': '734b6937a22d97b4cca0e9adc0d90d52f9e3b18dfbc8672b4b6a881de4db1a45',
 'HeckeSkeleton/HighBinSupport/FiniteResidueFourier.lean': 'e11d9af3abda89cb4e726324f949a4fea9a24468abea9fab2ad339a8bed9e772',
 'HeckeSkeleton/HighBinSupport/FourierInversion.lean': '428520d9eebb07d5ee9fef19f2a988ad7dc532781fe1497f938197ce51dc2c9a',
 'HeckeSkeleton/HighBinSupport/GeneratorUnitInvariance.lean': 'd9e4de14bc7f1cc496fabd0a1331508bcd0144ed7a9be9303bfc3ed87b6d0479',
 'HeckeSkeleton/HighBinSupport/HighCorrectionAlgebra.lean': '84d56bad9265474a5ddebb2a317b4f3b2b293bfe2dc7844526c1d332a0c53e17',
 'HeckeSkeleton/HighBinSupport/HighEulerScalarBounds.lean': '9c299bd0fa767c3edc850ff2bbb545aaeccb1fcbb3fd54fa1bb10ab66a39b5a6',
 'HeckeSkeleton/HighBinSupport/HighNormFormDeficit.lean': '73611608ca3ce16ed165bda8b7f5d6dc24542cd285baf609d75b194efd21ac61',
 'HeckeSkeleton/HighBinSupport/HighNormFormHeight.lean': 'd996b296cd437086c35efd94f2bb868b965aef149fe8e96cbc649aa787b4dda5',
 'HeckeSkeleton/HighBinSupport/HighNormFormLogDerivative.lean': '3f7f26443be259a2988b36509bca9b1036f0bd11e97237bbff4824bde16460ad',
 'HeckeSkeleton/HighBinSupport/HighNormFormScalar.lean': 'b956c321076fbd1f34b3bc3ce75e0cb1a504ee3cf0f71d60c66b63ba962b7f5b',
 'HeckeSkeleton/HighBinSupport/HighNormFormSlots.lean': '75dc9a2dd31fb3a39511b5ed0d2c682d1d88fdfe6a24e0486f0431186055167c',
 'HeckeSkeleton/HighBinSupport/HighNormFormTuple.lean': '7590fbdc9abb1af5262a80545bc03edd48fd2c8c4feb408a09d3871059349334',
 'HeckeSkeleton/HighBinSupport/JointAnalyticLimit.lean': '992742c85b088e8e9fc334d3fe10b895e8c68a21c6ba2082856acea6661acf1f',
 'HeckeSkeleton/HighBinSupport/LocalBlockSummation.lean': '648e6ea11aab2684d64b3f060b2a6a3cd75f0e00f49521f28b15e00cc4988007',
 'HeckeSkeleton/HighBinSupport/LocalSeriesFactorization.lean': '6ee875e53822f578d6353a15713b4151fa15ef8915ac1fa0083606891297c3c8',
 'HeckeSkeleton/HighBinSupport/LogFourierDecay.lean': '50a7e65841f12471336ce07f3e5cb444876cb6a18ddbce91acdd8084bd29fd3b',
 'HeckeSkeleton/HighBinSupport/PrimeBlockEuler.lean': '39f76defccab6939c70709104ca76807d281c74d75f6898e0390623d7fc00a1a',
 'HeckeSkeleton/HighBinSupport/PrimePowerFourier.lean': '1e4e7dd9cc408df5d33ed38c180e42a14b3780c02a6bd1243b4aab55d70402c7',
 'HeckeSkeleton/HighBinSupport/PrincipalPowerGauss.lean': '89121e7dddcfb1b23c6ecaf0b8505fc3593aa222f5df1aeddecdaa6568a785a5',
 'HeckeSkeleton/HighBinSupport/PrincipalPowerSupport.lean': '6d601f4fb60c36ccefa16b4f20d788d670020a3c15ff3bffc468dd868edc2c1d',
 'HeckeSkeleton/HighBinSupport/SelectedCompensation.lean': 'd23bbd7632f452781526a5469696bfb448d37c950ce72dc67e3840904fdfdef3',
 'HeckeSkeleton/HighBinSupport/UnramifiedFiniteTable.lean': '1d157e4e56b04da65951e4a066c2f650d443850f2a93ba2fbc4a938a17e7f420',
 'HeckeSkeleton/HighBinSupport/ValuationSeries.lean': 'bd6f8048b66e264bb553564f808a4a5e51ca7f960f8d2c2662708e97c78882df',
 'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/CanonicalProfileControl.lean': '455a93239a5443522884f6440b4418e38758ce10923df245fb3b789020277f9b',
 'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/FinitePropagation.lean': '2d56c6ade485561c70bb63f79a223b58da22020d639053eed374ba2d75aa2bde',
 'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/FourierApplication.lean': '9b0b1b59f5aa4f50dd501ad5b1da5982191d29475f5ada1bf88a5c8fcea064ea',
 'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/ProfileCommonFourier.lean': 'a0142cd705c48227b0f8dd035c97359c45751da1d5a1abf4b8c03a244dfc4cea',
 'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/ProfileControl.lean': 'f468f01041a78294121b2630b5b2746f3ce81bdb1410e4ec8606dda08e509ec7',
 'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/ProfileEuler.lean': 'd934522f0c9dc38db578540c5754c94097c4fb207e7ddfcbdf63267b625850e6',
 'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/ProfileFourier.lean': '5f598d667d69abf21e5e0773ec909967129535eb0ff321b213b5f97305f74f31',
 'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/ProfileLogCoordinates.lean': '24a02b3a0daba13696d80f91b75e90127265b4f79e2502909972a9eb8c85d474',
 'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/ProfileNormTwists.lean': 'b9860830fc115a6d3bbad462e55f079da96ac9f4d7bbd9286caa5a1fb7894168',
 'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/ProfileScaleJets.lean': '4c1b697476e61b8d36a806ff3878de3d86b75bdba36e8a703c9b69ebaccba6c2',
 'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/SharedFourierPropagation.lean': '1bf9c4b8585685b86d52f1d00e93c9ba876ea8dfa83829265088da8f7fd61c97',
 'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/SixthPowerSeed.lean': '0e97d693603ec2bff02bb04e2e455b057099bfa833b8527e9cd9fd96d4b8ed54',
 'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/SourceFourierControl.lean': 'c3edb2140fe1db4b98dabdd5764a3bc7241f2a014d85ec3109a29cc01a6bb747',
 'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/SourceProfileControl.lean': 'fab98200750a16121aac89399cd385349cb2e847283b703bc3a673e7ce532fe1',
 'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/SourceProfileJets.lean': 'c6a1b172afa2109cecd31be8d87d3c806e0e3798640a3e11c329dfd4542ad9fc',
 'HeckeSkeleton/SourceData.lean': '0262582fc36f7e0d4ce08966987b8628987a8f22c042d62d4e009870c80e6c84'}
REINDEX_COMMIT = 'c92578b1fa556b72d01c6ff49bac7f27885f09d7'
REINDEX_SOURCES = {'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/FiniteSectorCore.lean': 'aec890cdfe84c6a6bb97fa3d48ac88117ced794a5ead2b5aded1b469d1d636eb',
 'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/FiniteSectorReindex.lean': 'c9cc4fb6c7156db541c69b1e50dd709cd198d9ab791572ffcb72e4857178de9b'}
# The actual source and aligned arithmetic choice retain their owner pins.
# Integrated files include the original three target calls and are hashed
# separately from immutable imported owner sources.
INTEGRATED_SOURCE_PARENTS = ('624698fe21181df5cfda09434c407e9cf2ef075f', 'c92578b1fa556b72d01c6ff49bac7f27885f09d7')
INTEGRATED_SOURCES = {'HeckeSkeleton/Moments.lean': '9fbafa0bceff9faffd10ddb77cfd45bb9c7d193b11481f29f763dd8539c3c3c0',
 'HeckeSkeleton/Moments/MOM_BASE/LocalGauss.lean': 'fd1552537104f93fb975803605bd53ab800861ba6162e1300476c40e3dd94567',
 'lakefile.toml': '2d4deb66cc8a08f069ce72e873ea53f0877ac8aa181a57b08676a7a73aad1af0'}
INTEGRATED_SOURCES['HeckeSkeleton/Moments/MOM_BASE/LocalGauss.lean'] = 'fd1552537104f93fb975803605bd53ab800861ba6162e1300476c40e3dd94567'

# Subsequent owner proof repairs and the actual annular-volume dependency.
SOURCE_FOLLOWUP_COMMIT = 'c92578b1fa556b72d01c6ff49bac7f27885f09d7'
SOURCE_FOLLOWUP_SOURCES = {'HeckeSkeleton/Base.lean': '61d6e13788bea3f54488f6950a589ffa9738279579288d205391ca43ad744f43',
 'HeckeSkeleton/ExpansionModels/ActualRowEligibility.lean': 'f161d907df3b1f93697d20024ac8eef44a8ece0e47b6d4afa613e32b51bafcd3'}
PRIME_COMMIT = 'c92578b1fa556b72d01c6ff49bac7f27885f09d7'
PRIME_SOURCES = {'HeckeSkeleton/Moments/MOM_PRIME/AnnularMellin.lean': '9fb6c6cd9fb631c9ddd69901100f260e6a887042e98e0cd6c94ce6b628b17c58',
 'HeckeSkeleton/Moments/MOM_PRIME/ExceptionalAnnular.lean': 'd812ad10a9fa0d0a55381378bbb674650115e50d387b435fca21bc17a94002c0',
 'HeckeSkeleton/Moments/MOM_PRIME/ExceptionalAnnularBounds.lean': '05e1636201bb0f5a3f71b1b3d85d02039ffa4d0c1345d5a40050d4408ee8e8c1',
 'HeckeSkeleton/Moments/MOM_PRIME/ExceptionalContinuation.lean': '6223c1cee9669c43d759d10a069b2b0dcf67ddd0e056358188fe660b5294d74f',
 'HeckeSkeleton/Moments/MOM_PRIME/ExceptionalHecke.lean': 'c371bb9fc7a6c8934015a519412875c2a8f9c3cd04db762ffc65f89dcc3f6204',
 'HeckeSkeleton/Moments/MOM_PRIME/ExceptionalSmooth.lean': '4c69785cb08c112d61755cffc56abc9451a5e506f4693208b76d067e6a5dd3f9',
 'HeckeSkeleton/Moments/MOM_PRIME/ExceptionalTerminal.lean': '32554318a772686316dfdd3e975e32b8d491386055c79c9aa2b5542304eb337b'}
CANONICAL_SOURCES = (PRODUCER_SOURCES | SOURCE_SOURCES | SOURCE_FOLLOWUP_SOURCES
                     | PRIME_SOURCES | REINDEX_SOURCES | INTEGRATED_SOURCES
                     | PRODUCER_REPAIRED_SOURCES)
SOURCE_MODULES = ("SkeletonFamily", "SkeletonSource")
EXCLUDED = {name + ".lean" for name in SOURCE_MODULES}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc3"
COMPILER_COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"
MATHLIB = "0493595ecd5da8ef14742febab99728f98e948e8"
UPSTREAM_PROBES = (
    "HeckeSkeleton.paired_zero_slot_models",
    "HeckeSkeleton.paired_positive_below_one",
    "HeckeSkeleton.paired_positive_endpoint",
    "HeckeSkeleton.targetData",
    "HeckeSkeleton.momentModels",
)
REQUIRED_SKELETON_TARGETS = {
    "HeckeSkeleton.Moments.EngineInduction.paired_zero_slot_models_of_parent_reduction",
    "HeckeSkeleton.Moments.EngineInduction.paired_positive_below_one_of_parent_reduction",
    "HeckeSkeleton.Moments.EngineInduction.paired_positive_endpoint_of_parent_reduction",
    "HeckeSkeleton.Moments.EngineInduction.skeletonSourceIndexEquiv",
    "HeckeSkeleton.Moments.EngineInduction.skeleton_uniformMomentBound_iff",
    "HeckeSkeleton.Moments.EngineInduction.skeleton_plainSource_of_generic_model_bounds",
}
REQUIRED_TARGETS = {
    "HeckeSkeleton.Moments.EngineInduction.paired_zero_slot_models",
    "HeckeSkeleton.Moments.EngineInduction.paired_positive_below_one",
    "HeckeSkeleton.Moments.EngineInduction.paired_positive_endpoint",
    "HeckeSkeleton.Moments.EngineInduction.ClosedParentReduction.energy_bound",
    "HeckeSkeleton.Moments.EngineInduction.ParentReductionInput.sectorBound",
    "HeckeSkeleton.Moments.EngineInduction.RawParentReduction.closeTerminals",
    "HeckeSkeleton.Moments.EngineInduction.LocalStep.bound",
    "HeckeSkeleton.Moments.EngineInduction.LocalStep.uniform_rank_bound",
    "HeckeSkeleton.Moments.EngineInduction.IntegralStep.bound",
    "HeckeSkeleton.Moments.EngineInduction.IntegralStep.uniform_rank_bound",
    "HeckeSkeleton.Moments.EngineInduction.Reduction.power_bound",
    "HeckeSkeleton.Moments.EngineInduction.normalized_child_transfer",
    "HeckeSkeleton.Moments.EngineInduction.repaired_child_for_recursion",
    "HeckeSkeleton.Moments.EngineInduction.SourceFamily.uniformBound_of_dyadic_rowWidth",
    "HeckeSkeleton.Moments.EngineInduction.CommonKernelReduction.toIntegralStep",
    "HeckeSkeleton.Moments.EngineInduction.CommonKernelReduction.toIntegralStep_mass",
    "HeckeSkeleton.Moments.EngineInduction.CommonKernelReduction.toRawParentReduction",
    "HeckeSkeleton.Moments.EngineInduction.logNormSeparatedProfiles_plainPolynomial₁",
    "HeckeSkeleton.Moments.EngineInduction.logNormSeparatedProfiles_plainPolynomial₂",
    "HeckeSkeleton.Moments.EngineInduction.logNormSeparatedProfiles_primePolynomial",
    "HeckeSkeleton.Moments.EngineInduction.Source.SourceMomentIndexFor",
    "HeckeSkeleton.Moments.EngineInduction.Source.SourceMomentModelsFor",
    "HeckeSkeleton.Moments.EngineInduction.sourceFamily",
    "HeckeSkeleton.Moments.EngineInduction.moment_mesh_total_loss_budget",
    "HeckeSkeleton.Moments.EngineInduction.Node.normalizedEnergy_absolute_bound",
    "HeckeSkeleton.Moments.EngineInduction.Node.absoluteBaseComponents",
    "HeckeSkeleton.Moments.EngineInduction.Node.exists_absolute_base_components",
    "HeckeSkeleton.Moments.EngineInduction.Source.plainSource_of_dyadic_model_bounds",
    "HeckeSkeleton.Moments.EngineInduction.SourceFamily.uniformBound_of_rowWidth_le_from",
    "HeckeSkeleton.Moments.EngineInduction.slotProduct_sq_uniform_absolute_bound",
    "HeckeSkeleton.Moments.EngineInduction.uniform_absolute_base_components",
    "HeckeSkeleton.Moments.EngineInduction.PolynomialSystem.comparison_earlier_of_lengths",
    "HeckeSkeleton.Moments.EngineInduction.PolynomialSystem.positive_comparison_earlier",
    "HeckeSkeleton.Moments.EngineInduction.uniformBaseConstant_height_le",
    "HeckeSkeleton.Moments.EngineInduction.uniform_polynomial_height_base_components",
    "HeckeSkeleton.Moments.EngineInduction.BranchedIntegralStep.uniform_rank_bound",
    "HeckeSkeleton.Moments.EngineInduction.branchedIntegralStep_power_bound",
    "HeckeSkeleton.Moments.EngineInduction.PolynomialSystem.baseBranch_mass",
    "HeckeSkeleton.Moments.EngineInduction.uniform_polynomial_height_base_branch",
    "HeckeSkeleton.Moments.EngineInduction.engineOutputToBranchedAt",
    "HeckeSkeleton.Moments.EngineInduction.engineOutputsToBranchedStep",
    "HeckeSkeleton.Moments.EngineInduction.engineOutputsToClosedParentReduction",
    "HeckeSkeleton.Moments.EngineInduction.BranchedIntegralAt.combine_mass",
    "HeckeSkeleton.Moments.EngineInduction.PolynomialSystem.core_reflection_earlier",
    "HeckeSkeleton.Moments.EngineInduction.PolynomialSystem.earlier_core_of_length",
    "HeckeSkeleton.Moments.EngineInduction.CoreReflectionData.toAt",
    "HeckeSkeleton.Moments.EngineInduction.CoreReflectionData.toAt_mass",
    "HeckeSkeleton.Moments.EngineInduction.general_uniform_polynomial_height_base_components",
    "HeckeSkeleton.Moments.EngineInduction.uniform_modelProfileControl_base_components",
    "HeckeSkeleton.Moments.EngineInduction.sliceControl_norm_le",
    "HeckeSkeleton.Moments.EngineInduction.Source.recipeRoot_slotCount_le",
    "HeckeSkeleton.Moments.EngineInduction.Source.recipeRoot_length",
    "HeckeSkeleton.Moments.EngineInduction.Source.recipeRoot_fitsMesh",
    "HeckeSkeleton.Moments.EngineInduction.Source.recipeRoot_uniform_profiles",
    "HeckeSkeleton.Moments.EngineInduction.Node.base_length_of_zero_padded_core",
    "HeckeSkeleton.Moments.EngineInduction.Node.base_length_of_positive_capacity",
    "HeckeSkeleton.Moments.EngineInduction.Node.quarterCentered_energy_decomposition",
    "HeckeSkeleton.Moments.EngineInduction.PolynomialSystem.comparison_same_length_schedule",
    "HeckeSkeleton.Moments.EngineInduction.ReflectedComparisonData.earlier",
    "HeckeSkeleton.Moments.EngineInduction.ReflectedComparisonData.toAt",
    "HeckeSkeleton.Moments.EngineInduction.ReflectedComparisonData.toAt_mass",
    "HeckeSkeleton.Moments.EngineInduction.OuterReflectionAt.power_bound",
    "HeckeSkeleton.Moments.EngineInduction.ReflectedRootInput.sectorBound",
    "HeckeSkeleton.Moments.EngineInduction.paired_zero_slot_of_reflected_core",
    "HeckeSkeleton.Moments.EngineInduction.moment_mesh_loss_budget_with_outer_reflection",
    "HeckeSkeleton.Moments.EngineInduction.Node.plainPair_scaleProfiles",
    "HeckeSkeleton.Moments.EngineInduction.Node.energy_scaleProfiles",
    "HeckeSkeleton.Moments.EngineInduction.Node.normalizedEnergy_normalizeProfiles",
    "HeckeSkeleton.Moments.EngineInduction.Source.paired_source_reindex",
    "HeckeSkeleton.Moments.EngineInduction.engineOutput_zero_parameters",
    "HeckeSkeleton.Moments.EngineInduction.PolynomialSystem.centeredComparisonBranch",
    "HeckeSkeleton.Moments.EngineInduction.CoreRecursionInput.toClosedParentReduction",
    "HeckeSkeleton.Moments.EngineInduction.Source.RecipeLocalInput.toParentReductionInput",
    "HeckeSkeleton.Moments.EngineInduction.Source.paired_zero_slot_recipe",
    "HeckeSkeleton.Moments.EngineInduction.Source.paired_positive_recipe_below_one",
    "HeckeSkeleton.Moments.EngineInduction.Source.paired_positive_recipe_endpoint",
    "HeckeSkeleton.Moments.EngineInduction.annularIdealSum_mellin",
    "HeckeSkeleton.Moments.EngineInduction.annularHeckeSum_mellin",
    "HeckeSkeleton.Moments.EngineInduction.annularHeckeSum_shift",
    "HeckeSkeleton.Moments.EngineInduction.annularHeckeSum_reflectedContour",
    "HeckeSkeleton.Moments.EngineInduction.pairedEnergy_normalizedMomentProfiles",
    "HeckeSkeleton.Moments.EngineInduction.sqrt_pairedEnergy_normalizedMomentProfiles",
    "HeckeSkeleton.Moments.EngineInduction.normalizedMomentProfiles_unit_control",
    "HeckeSkeleton.Moments.EngineInduction.annularHeckeSum_reflection",
    "HeckeSkeleton.Moments.EngineInduction.ordinaryGammaRatio_strip_bound",
    "HeckeSkeleton.Moments.EngineInduction.ordinaryReflectedProfile_decay_seminorm",
    'HeckeSkeleton.Moments.EngineInduction.exists_centeredMellin_preprocessing',
    'HeckeSkeleton.Moments.EngineInduction.Node.mellinPlain_row_identity',
    'HeckeSkeleton.Moments.EngineInduction.Node.energy_le_normalizedMellinPlain_kernel',
    'HeckeSkeleton.Moments.EngineInduction.mellinPairEnvelope_kernel_mass',
    'HeckeSkeleton.Moments.EngineInduction.rankedAnnulus_child_enlargement_subset',
    'HeckeSkeleton.Moments.EngineInduction.scalarRecursion_power_bound',
    'HeckeSkeleton.Moments.EngineInduction.MellinStrictBranchAt.bound',
    'HeckeSkeleton.Moments.EngineInduction.MellinCoreRecursionInput.energy_bound',
    'HeckeSkeleton.Moments.EngineInduction.Source.RecipeScalarLocalInput.sectorBound',
    'HeckeSkeleton.Moments.EngineInduction.Source.paired_zero_slot_recipe_mellin',
    'HeckeSkeleton.Moments.EngineInduction.Source.paired_positive_recipe_mellin_below_one',
    'HeckeSkeleton.Moments.EngineInduction.Source.paired_positive_recipe_mellin_endpoint',
    'HeckeSkeleton.Moments.EngineInduction.universalMellinStrictBranch',
    'HeckeSkeleton.Moments.EngineInduction.Source.recipeMellinFamily_preparation',
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def runner_resources() -> dict:
    disk = shutil.disk_usage(ROOT)
    result = dict(system=platform.system(), kernel=platform.release(), cpu_count=os.cpu_count(),
                  lean_num_threads=os.environ.get("LEAN_NUM_THREADS"),
                  disk_total_bytes=disk.total, disk_free_bytes=disk.free,
                  address_space_limit=list(resource.getrlimit(resource.RLIMIT_AS)),
                  open_file_limit=list(resource.getrlimit(resource.RLIMIT_NOFILE)))
    mapping_limit = Path("/proc/sys/vm/max_map_count")
    if mapping_limit.is_file():
        result["vm_max_map_count"] = int(mapping_limit.read_text())
    memory = Path("/proc/meminfo")
    if memory.is_file():
        for line in memory.read_text().splitlines():
            name, _, value = line.partition(":")
            if name in {"MemTotal", "MemAvailable", "SwapTotal"}:
                result[name + "_kB"] = int(value.split()[0])
    return result


def command(*args: str) -> str:
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def lean_code(text: str) -> str:
    """Remove nested Lean comments, retaining lines and quoted strings."""
    result: list[str] = []
    depth = 0
    quoted = False
    i = 0
    while i < len(text):
        char = text[i]
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                result.append("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                result.append("  ")
                i += 2
            else:
                result.append("\n" if char == "\n" else " ")
                i += 1
        elif quoted:
            result.append(char)
            i += 1
            if char == "\\" and i < len(text):
                result.append(text[i])
                i += 1
            elif char == '"':
                quoted = False
        elif pair == "/-":
            depth = 1
            result.append("  ")
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            if end == -1:
                end = len(text)
            result.append(" " * (end - i))
            i = end
        else:
            result.append(char)
            quoted = char == '"'
            i += 1
    require(depth == 0, "Unclosed Lean comment in audited source")
    return "".join(result)


def declarations(path: Path) -> set[str]:
    """Inventory explicit public declarations in these conventionally laid-out files."""
    scopes: list[tuple[str, str]] = []
    names: set[str] = set()
    declaration = re.compile(
        r"^(?:@\[[^\]]*\]\s*)*"
        r"(?P<modifiers>(?:(?:noncomputable|protected|private)\s+)*)"
        r"(?:def|abbrev|theorem|lemma|structure|inductive)\s+(?P<name>[^\s({:]+)"
    )
    for raw_line in lean_code(path.read_text()).splitlines():
        line = raw_line.lstrip()
        namespace = re.match(r"^namespace\s+(\S+)", line)
        section = re.match(r"^(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$", line)
        end = re.match(r"^end(?:\s+(\S+))?\s*$", line)
        if namespace:
            scopes.append(("namespace", namespace[1]))
        elif section:
            scopes.append(("section", section[1] or ""))
        elif end:
            require(bool(scopes), f"Unmatched end in {path.name}")
            scopes.pop()
        else:
            match = declaration.match(line)
            if match and "private" not in match["modifiers"].split():
                namespace_name = ".".join(name for kind, name in scopes if kind == "namespace")
                names.add(".".join(filter(None, (namespace_name, match["name"]))))
    return names


def audit_commands(text: str) -> tuple[list[str], list[str]]:
    imports: list[str] = []
    printed: list[str] = []
    for raw_line in lean_code(text).splitlines():
        line = raw_line.strip()
        if not line:
            continue
        imported = re.fullmatch(r"import\s+(\S+)", line)
        audited = re.fullmatch(r"#print axioms\s+(\S+)", line)
        require(imported is not None or audited is not None,
                f"Audit.lean contains a command other than an import or #print axioms: {line}")
        if imported is not None:
            imports.append(imported[1])
        else:
            assert audited is not None
            printed.append(audited[1])
    return imports, printed


def inventory() -> tuple[dict[str, str], list[str]]:
    expected_files = {name + ".lean" for name in MODULES} | {"Audit.lean"} | EXCLUDED
    actual_files = {path.name for path in TASK.glob("*.lean")}
    require(actual_files == expected_files,
            f"Update the audit module inventory: missing={sorted(expected_files - actual_files)}, "
            f"unlisted={sorted(actual_files - expected_files)}")
    imports, printed = audit_commands((TASK / "Audit.lean").read_text())
    require(len(imports) == len(MODULES)
            and set(imports) == {PREFIX + "." + module for module in MODULES},
            "Audit.lean must import exactly the clean task modules listed in MODULES")
    require(len(printed) == len(set(printed)), "Duplicate #print axioms declarations")
    declared: set[str] = set()
    hashes = {}
    for module in MODULES:
        path = TASK / (module + ".lean")
        code = lean_code(path.read_text())
        forbidden = re.findall(r"\b(?:sorry|admit|axiom|sorryAx|native_decide)\b", code)
        require(not forbidden, f"Forbidden proof shortcut in {path.name}: {forbidden}")
        require(not re.search(r"^import\s+HeckeSkeleton\.Moments(?:\s|$)", code, re.M),
                f"{path.name} imports the admitted skeleton")
        require(all("MOM_ENGINE_INDUCTION." + source not in code for source in SOURCE_MODULES),
                f"{path.name} imports the separate skeleton adapter")
        module_declarations = declarations(path)
        require(not (declared & module_declarations),
                f"Duplicate public declarations in {path.name}: "
                f"{sorted(declared & module_declarations)}")
        declared.update(module_declarations)
        hashes[str(path.relative_to(ROOT))] = digest(path)
    require(set(printed) == declared,
            f"Audit declaration inventory mismatch: missing={sorted(declared - set(printed))}, "
            f"extra={sorted(set(printed) - declared)}")
    require(REQUIRED_TARGETS <= declared,
            f"Missing target declarations: {sorted(REQUIRED_TARGETS - declared)}")
    for relative, pinned in CANONICAL_SOURCES.items():
        path = ROOT / relative
        require(path.is_file(), f"Missing canonical producer interface: {relative}")
        actual = digest(path)
        require(actual == pinned,
                f"Canonical imported source differs from its recorded owner pin or explicit repair: {relative}")
        hashes[relative] = actual
    for path in (TASK / "Audit.lean", TASK / "verify.py", ROOT / "lean-toolchain",
                 ROOT / "lake-manifest.json", ROOT / "lakefile.toml"):
        hashes[str(path.relative_to(ROOT))] = digest(path)
    return hashes, sorted(declared)


def verify_checkout(expected: str) -> None:
    require(re.fullmatch(r"[0-9a-f]{40}", expected) is not None, "Expected a full commit SHA")
    actual = command("git", "rev-parse", "HEAD")
    require(actual == expected, f"Checking {actual}, expected head {expected}")
    paths = [str((TASK / (module + ".lean")).relative_to(ROOT)) for module in MODULES]
    paths += [str((TASK / name).relative_to(ROOT)) for name in ("Audit.lean", "verify.py")]
    paths += [".github/workflows/mom-engine-induction.yml"]
    paths += list(CANONICAL_SOURCES)
    subprocess.run(["git", "ls-files", "--error-unmatch", "--"] + paths, cwd=ROOT,
                   check=True, stdout=subprocess.DEVNULL)
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--"], cwd=ROOT, check=True,
                   stdout=subprocess.DEVNULL)


def preflight(expected: str, output: Path) -> None:
    verify_checkout(expected)
    hashes, names = inventory()
    require((ROOT / "lean-toolchain").read_text().strip() == TOOLCHAIN, "Toolchain pin changed")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    package = next((p for p in manifest["packages"] if p["name"] == "mathlib"), None)
    require(package is not None and package.get("rev") == MATHLIB, "Mathlib manifest pin changed")
    actual_mathlib = command("git", "-C", str(ROOT / ".lake/packages/mathlib"), "rev-parse", "HEAD")
    require(actual_mathlib == MATHLIB, f"Unexpected Mathlib checkout: {actual_mathlib}")
    version = command("lake", "env", "lean", "--version")
    require("version 4.35.0-rc3," in version and COMPILER_COMMIT in version,
            f"Unexpected compiler: {version}")
    output.mkdir(parents=True, exist_ok=True)
    record = dict(head_sha=expected, toolchain=TOOLCHAIN, compiler=version, mathlib=MATHLIB,
                  source_sha256=hashes, declarations=names,
                  modules=[PREFIX + "." + name for name in MODULES],
                  producer_interface_commit=PRODUCER_COMMIT,
                  producer_interface_sha256=PRODUCER_SOURCES,
                  producer_compatibility_repairs=PRODUCER_REPAIRS,
                  canonical_source_commit=SOURCE_COMMIT, canonical_source_sha256=SOURCE_SOURCES,
                  source_followup_commit=SOURCE_FOLLOWUP_COMMIT,
                  source_followup_sha256=SOURCE_FOLLOWUP_SOURCES,
                  annular_volume_commit=PRIME_COMMIT, annular_volume_sha256=PRIME_SOURCES,
                  integrated_source_parents=INTEGRATED_SOURCE_PARENTS,
                  integrated_source_sha256=INTEGRATED_SOURCES,
                  finite_reindex_commit=REINDEX_COMMIT, finite_reindex_sha256=REINDEX_SOURCES,
                  excluded_integration_modules=sorted(EXCLUDED),
                  runner_resources=runner_resources())
    (output / "preflight.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"Preflight: exact head {expected}, {len(MODULES)} modules, {len(names)} declarations")
    print("Runner resources: " + json.dumps(record["runner_resources"], sort_keys=True))


def axiom_records(text: str, expected: set[str],
                  allowed: set[str] = ALLOWED) -> dict[str, list[str]]:
    pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
    pairs = re.findall(pattern, text, re.S)
    names = [name for name, _ in pairs]
    require(len(names) == len(set(names)), "Duplicate axiom audit records")
    records = {name: sorted({item.strip() for item in axioms.split(",") if item.strip()})
               for name, axioms in pairs}
    require(set(records) == expected,
            f"Incomplete axiom output: missing={sorted(expected - records.keys())}, "
            f"unexpected={sorted(records.keys() - expected)}")
    for name, axioms in records.items():
        require(set(axioms) <= allowed,
                f"{name}: disallowed axioms {sorted(set(axioms) - allowed)}")
    return records


def check(expected: str, output: Path) -> None:
    verify_checkout(expected)
    hashes, names = inventory()
    before = json.loads((output / "preflight.json").read_text())
    require(before["head_sha"] == expected, "Preflight belongs to another commit")
    require(before["source_sha256"] == hashes, "Sources changed during verification")
    require(before["declarations"] == names, "Audited declaration inventory changed")
    build = (output / "build.log").read_text()
    audit = (output / "axioms.log").read_text()
    for kind, log in (("BUILD", build), ("AUDIT", audit)):
        require(f"MOM_ENGINE_INDUCTION_{kind}_OK {expected}" in log,
                f"Missing successful {kind.lower()} completion marker")
        require(re.search(r"(?:^|\n)(?:[^\n]*?:\d+:\d+: )?error:", log) is None,
                f"Error diagnostic in {kind.lower()} log")
    records = axiom_records(audit, set(names))
    record = dict(before, status="passed", axioms=records,
                  allowed_axioms=sorted(ALLOWED),
                  build_log_sha256=digest(output / "build.log"),
                  axiom_log_sha256=digest(output / "axioms.log"))
    (output / "verification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"PASS: {len(MODULES)} modules and {len(names)} declarations at {expected}; "
          f"all axioms belong to {sorted(ALLOWED)}")


def skeleton_inventory() -> tuple[dict[str, str], list[str]]:
    hashes: dict[str, str] = {}
    declared: set[str] = set()
    for module in SOURCE_MODULES:
        path = TASK / (module + ".lean")
        subprocess.run(["git", "ls-files", "--error-unmatch", "--",
                        str(path.relative_to(ROOT))], cwd=ROOT, check=True,
                       stdout=subprocess.DEVNULL)
        forbidden = re.findall(r"\b(?:sorry|admit|axiom|sorryAx|native_decide)\b",
                               lean_code(path.read_text()))
        require(not forbidden, f"New proof shortcut in {path.name}: {forbidden}")
        hashes[str(path.relative_to(ROOT))] = digest(path)
        declared.update(declarations(path))
    names = sorted(declared)
    require(REQUIRED_SKELETON_TARGETS <= set(names),
            f"Missing source adapter targets: {sorted(REQUIRED_SKELETON_TARGETS - set(names))}")
    return hashes, names


def skeleton_preflight(expected: str, output: Path) -> None:
    preflight(expected, output)
    source_hash, names = skeleton_inventory()
    record = json.loads((output / "preflight.json").read_text())
    record.update(kind="skeleton-integration", skeleton_source_sha256=source_hash,
                  integration_declarations=names, upstream_probes=list(UPSTREAM_PROBES))
    (output / "preflight.json").write_text(json.dumps(record, indent=2) + "\n")
    # Generated audit commands and evidence stay outside the source checkout.
    audit = "\n".join("import " + PREFIX + "." + module for module in SOURCE_MODULES) + "\n\n"
    audit += "\n".join("#print axioms " + name for name in names) + "\n"
    (output / "SkeletonAudit.lean").write_text(audit)
    upstream = "import HeckeSkeleton.Moments\n\n"
    upstream += "-- Existing declarations; excluded from the new declaration inventory.\n"
    upstream += "\n".join("#print axioms " + name for name in UPSTREAM_PROBES) + "\n"
    (output / "UpstreamAudit.lean").write_text(upstream)
    print(f"Separate skeleton integration: {len(names)} declarations; "
          "inherited sorryAx is recorded, not accepted by the clean audit")
    print(f"Separate upstream probes: {len(UPSTREAM_PROBES)} existing declarations")


def skeleton_check(expected: str, output: Path) -> None:
    verify_checkout(expected)
    hashes, names = inventory()
    source_hash, integration_names = skeleton_inventory()
    before = json.loads((output / "preflight.json").read_text())
    require(before.get("kind") == "skeleton-integration", "Wrong preflight kind")
    require(before["head_sha"] == expected, "Preflight belongs to another commit")
    require(before["source_sha256"] == hashes and before["declarations"] == names,
            "Clean sources changed during integration verification")
    require(before["skeleton_source_sha256"] == source_hash
            and before["integration_declarations"] == integration_names,
            "Skeleton adapter changed during integration verification")
    require(before["upstream_probes"] == list(UPSTREAM_PROBES),
            "Upstream probe inventory changed")
    imports, printed = audit_commands((output / "SkeletonAudit.lean").read_text())
    require(imports == [PREFIX + "." + module for module in SOURCE_MODULES]
            and printed == integration_names,
            "Generated integration audit commands changed")
    imports, printed = audit_commands((output / "UpstreamAudit.lean").read_text())
    require(imports == ["HeckeSkeleton.Moments"] and printed == list(UPSTREAM_PROBES),
            "Generated upstream audit commands changed")
    for kind, filename in (("BUILD", "build.log"), ("AUDIT", "axioms.log"),
                           ("UPSTREAM_BUILD", "upstream-build.log"),
                           ("UPSTREAM_AUDIT", "upstream-axioms.log")):
        log = (output / filename).read_text()
        require(f"MOM_ENGINE_INDUCTION_SKELETON_{kind}_OK {expected}" in log,
                f"Missing successful skeleton {kind.lower()} completion marker")
        require(re.search(r"(?:^|\n)(?:[^\n]*?:\d+:\d+: )?error:", log) is None,
                f"Error diagnostic in skeleton {kind.lower()} log")
    integration_allowed = ALLOWED | {"sorryAx"}
    records = axiom_records((output / "axioms.log").read_text(),
                            set(integration_names), integration_allowed)
    upstream_records = axiom_records((output / "upstream-axioms.log").read_text(),
                                     set(UPSTREAM_PROBES), integration_allowed)
    inherited = sorted(name for name in integration_names if "sorryAx" in records[name])
    upstream_inherited = sorted(name for name in UPSTREAM_PROBES
                                if "sorryAx" in upstream_records[name])
    record = dict(before, status="integration-compiled",
                  axioms={name: records[name] for name in integration_names},
                  upstream_probe_axioms=upstream_records,
                  integration_allowed_axioms=sorted(integration_allowed),
                  declarations_with_inherited_sorryAx=inherited,
                  upstream_probes_with_sorryAx=upstream_inherited,
                  build_log_sha256=digest(output / "build.log"),
                  axiom_log_sha256=digest(output / "axioms.log"),
                  upstream_build_log_sha256=digest(output / "upstream-build.log"),
                  upstream_axiom_log_sha256=digest(output / "upstream-axioms.log"))
    (output / "verification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"PASS integration compilation: {len(integration_names)} declarations at {expected}; "
          f"{len(inherited)} inherit sorryAx. This is separate from the clean axiom gate.")
    print("Existing upstream probes depending on sorryAx: " + json.dumps(upstream_inherited))


def original_check(expected: str, output: Path) -> None:
    """Enforce the task's original-name acceptance gate after source compilation."""
    verify_checkout(expected)
    integration = json.loads((output / "verification.json").read_text())
    require(integration.get("head_sha") == expected
            and integration.get("status") == "integration-compiled",
            "Original targets require successful exact-head source integration")
    log = output / "upstream-axioms.log"
    require(digest(log) == integration["upstream_axiom_log_sha256"],
            "Original target axiom log changed after integration verification")
    records = axiom_records(log.read_text(), set(UPSTREAM_PROBES), ALLOWED | {"sorryAx"})
    targets = UPSTREAM_PROBES[:3]
    unexpected = {name: sorted(set(records[name]) - ALLOWED) for name in targets
                  if set(records[name]) - ALLOWED}
    result = dict(head_sha=expected, status="passed" if not unexpected else "blocked",
                  targets=list(targets), axioms={name: records[name] for name in targets},
                  allowed_axioms=sorted(ALLOWED), unexpected_axioms=unexpected,
                  upstream_axiom_log_sha256=digest(log))
    (output / "original-targets.json").write_text(json.dumps(result, indent=2) + "\n")
    for name in targets:
        print(name + ": " + json.dumps(records[name]))
    require(not unexpected,
            "Original target axiom gate failed: " + json.dumps(unexpected)
            + ". Conditional clean theorems do not satisfy this acceptance gate.")
    print(f"PASS original targets: {len(targets)} declarations at {expected}; "
          f"all axioms belong to {sorted(ALLOWED)}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    phases = {"preflight": preflight, "check": check,
              "skeleton-preflight": skeleton_preflight, "skeleton-check": skeleton_check,
              "original-check": original_check}
    parser.add_argument("phase", choices=tuple(phases))
    parser.add_argument("--expected-sha", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    require(not output.is_relative_to(ROOT), "Place verification logs outside the repository")
    phases[args.phase](args.expected_sha, output)


if __name__ == "__main__":
    main()
