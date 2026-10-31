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
MODULES = (
    "Order", "Recursion", "IntegralRecursion", "Reduction", "Family", "Terminal", "ExceptionalCounting",
    "TerminalCertificate", "Interface", "Centering", "Induction", "ChildStepCompatibility",
    "RootNormalization", "KernelReduction", "LogNormProfiles",
    "SourceData", "SourceAdapter", "ScheduleCompatibility",
    "BaseTerminal", "SourceConsumers",
    "LengthStages", "BaseUniformity", "BranchedIntegralRecursion", "BaseBranch",
    "StepOutputAdapter", "BranchAssembly", "MomentProfileScaling", "ProfileControlScaling",
    "ProfileScaling", "SourceReindex",
    "CoreGeometry", "ReflectionBranch", "ReflectedRoot",
    "CoreStages", "GeneralBaseTerminal", "RecipeRoot", "ProfileSupremum",
    "CoreRecursion", "RecipeInduction", "AnnularMellin", "AnnularReflection",
    "OrdinaryReflection", "OrdinaryGamma", "OrdinaryReflectionDecay",
    'OrdinaryReflectionUniformity',
    'OrdinaryReflectionTruncation',
    'OrdinaryReflectionSmooth',
    'OrdinaryGammaRight',
    'OrdinaryReflectionSmall',
    'OrdinaryReflectionDyadic',
    'OrdinaryDeletionReflection',
    'OrdinaryDyadicMass',
    'OrdinaryReflectionLines',
    'OrdinaryPowerWindows',
    'OrdinaryReflectionOperator',
    'OrdinaryRestorationOperator',
    'OrdinaryReflectionDensity',
    'RowNonNorm',
    'MaskDeletion',
    'MaskNorm',
    'WeightedReflectionMass',
    'ReflectionWeights',
    'ReflectionMask',
    'ReflectionConductor',
    'RowIntegralKernel',
    'OrdinaryReflectionWhole',
    'OrdinaryRestorationTail',
    'OrdinaryRowReflection',
    'ReflectionTailLedger',
    'PowerWindowSeminorm',
    'PowerWindowEnergy',
    'FiniteBranchMeasure',
    'FiniteRowKernel',
    'ReflectionGeometry',
    'ProfileOrderSchedule',
    'OrdinaryProfileNormalization',
    'NormalizedReflectionDensity',
    'RestorationRows',
    'NormalizedPowerWindowEnergy',
    'ActualReflectionRows',
    'ReflectionProfileBudget',
    'ActualReflectionDensity',
    'ReflectionTerminal',
    'PrimitiveReflectionCalibration',
    'UniversalNodeFamily',
    'ProfileTimeIndependent',
    'FixedLineKernel',
    'CommonKernelMass',
    'ActualCommonReflection',
    'SourceProfileAnnulus',
    'UniformOrdinaryReflection',
    'ReflectionChildGeometry',
    'RankedProfileControl',
    'CutoffReflectionLabels',
    'OrdinaryReflectionProduction',
    'RankedBaseBranch',
    'FiniteProfileConstants',
    'ReflectionPrimitiveFamily',
    'UniversalSourceRoot',
    'UniversalReflectionBranches',
    'ParameterTransport',
    'BranchParameterTransport',
    'RecipeReflectionParameters',
    'RankedReflectionAssembly',
    'RecipeReflectionRoot',
    'AnnularSchwartzControl',
    'RecipeReflectionFamily',
    'SchwartzEulerControl',
    'AnnularMellinSeparation',
    'PlainMellinProfiles',
    'CenteredMellinKernel',
    'AnnularMellinWindowControl',
    'MellinProfileNormalization',
    'MellinSeparationMass',
    'MellinPreprocessing',
    'RankedAnnulus',
    'RankedAnnulusPrimitive',
    'RankedAnnulusReflectionAssembly',
    'RecipeRankedAnnulusReflection',
    'MellinStrictTransfer',
    'ScalarRecursion',
    'MellinScalarStep',
    'MellinCoreRecursion',
    'RecipeMellinInduction',
    'OriginalMesh',
    'RankedMeshReflectionAssembly',
    'RecipeMeshReflectionFamily',
    'RecipeMellinFamily',
    'MellinUniversalLabels',
    'DataPrimitiveExtension',
    'RankedDataReflectionAssembly',
    'RecipeDataReflectionFamily',
    'CompleteRowAtoms',
    'ActualRecipeAtoms',
    'ActualAtomPhases',
    'OriginalAtomConsumers',
    'CompleteSourcePrimitive',
    'CompleteParentSource',
    'PrimeAnnulus',
    'PrimeAnnulusModel',
)
# Exact canonical single-step imports, including the complete-row atoms
# and genuine original positive source. These remain in the owner namespace.
PRODUCER_COMMIT = 'a8cf65cedd24ba4c71bbe754d1f8c5149123b20c'
PRODUCER_SOURCES = {'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualCapacityProduction.lean': '05d527ae105a5c0c73bfd48f589faf82897aa709de3ae4c6c78be6b64c99b9e4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualChildInvariants.lean': 'd4971513b7e4f38c8b6bcdb3595d75772ff3d7003e073f576050540720090cde',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualChildRows.lean': 'ab2f29c47f570f01c2e56ccab9de8c71197424d41f22d2f0b79c71a933973ad2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualChildren.lean': '71081ee5face3a8ba76d88a84eab5eaf8048fae36f0631ee072c92510ad9731d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualCorrelationBound.lean': '6fb4f2288c9a8620b72cf50bbfd488678b853048d0237632ea007714319a3e0e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualFamilyIntegrability.lean': '7ba63049fad1dcbcbd32f3f028ca471546708384fd9258b17bd28da6b85084ab',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualFirstCharacters.lean': '25cbf685cdfcfc72cbd0b44214ad389a8ebd2629d4a79328700dd9c109b22500',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualFirstZero.lean': '76f8766b5f4e9291f224d9f334a8cd6ea502ea03e97cb7de9a99fcecdec52ae7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualFrequencyPartition.lean': '63766d1efe81dfbf915d1cd3a6cf76083ee81485b13749dafd6dda1c493c5933',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualLengths.lean': '99f803cfd98ec2a3a124c1d7192a4df3141c18b7d51c9e22d6b2490e6ca550c2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualPool.lean': 'c0c43cf5dd688ee0ff777874def1fd75a87b5a5a1031f6cc0d51ab7dee940f33',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ActualScaleClipping.lean': 'b2ae32c5364c3881f5e014dee5642d69b39f8a3a39a00c73a7fcd68c36e8f180',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AllocatedCapacityProvider.lean': 'b2764f5265014ae9079c92838de514080072a6d874e23102cf48bf2e1f42d972',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AllocatedChildFamily.lean': 'e83d72f6b8c5bc3aad1d6e2114846096a7dcc4f3a3107329857d013cf7838765',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AllocatedChildProvider.lean': 'f2188eba24fcbdedcf1501285436c86de070977f55c9c2f597cb63006cfbaead',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AllocatedSubsupport.lean': 'e658a7d3667cc8908de48c552a4018ebb95624e89232898ae88b4c1ab7218012',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AllocationKernel.lean': '9b117cd06a5b2e81cc7c0d70eb17e681e70ef91478540dfd79a8ad808f1ed19e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AllocationMass.lean': 'ef3bf0bd41877b5a7daf978a460071ad42a4188fa98f1b28e9bd8edeefbbea84',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AmplifierDifference.lean': 'b55418917a8d44c399d90012bcb551278de171566ef023b7b874512718894b41',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AmplifierGaussExtraction.lean': '3f26ddec7c41a220fa96042800f6c4c82761724355fed4712d8dd165caccc649',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AmplifierResidualSupport.lean': '674a35ec9973fe56741298f1071bf2fafb0f0a03a6852ba5948306908ac3e7b0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/AmplifierValuationSupport.lean': '70141b981aa29341fe2f32ba2d845aaf2c5c38060833b082148f8016e186ea70',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ArithmeticPrimePool.lean': '01fdf4cd368703ac9d4a9de5dc4800790fd8e83a9807ffa1c8c9542bc9d9ed4a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalFirstBlocks.lean': '1efb4f6882214dae1879392657c59637d406d116bc0299d0e6d7ecbd4bf24d19',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalParentSource.lean': '61e49e1036145fed5d9f1c0d3c36936e2722982060c48379f96ebe540fa2c1e6',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CanonicalRowBallChart.lean': 'aecfc32b5b946927bddacb3998c694d6467ce315ac7c26b75325df4b2c14a479',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/Capacity.lean': 'afe8803e7fe57c56c163f5a2b84df6584ccf6efb9fbad611aa8b3594ba461109',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CenteredAllocatedChildren.lean': '97a0b0f16e7803a7eb6fe7198f1b78774c820cb475d304d06a6edc3006bd8d08',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CharacterRecipePreservation.lean': 'db9e8ae0048c6331f50f23a3e6fbddb6cfe109b0f785e581ada9bc74dca1b19b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ChildAssembly.lean': '8d3b7c785934789a837371ec2c6e7232a136a16c7763ad6f02f3c2060dd23bfb',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ChildMomentDataAdapter.lean': '1e7dcb1995557bc809b7a3f01bdddab942db6db538baf2f675a20546b3063086',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ChildTermDictionary.lean': '23103c46a6b76e190e43b710c88bcf46e4e13e25ca260a8629689e9534e599a5',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/Coefficient.lean': '18488694967da3d55b23c68a5df1be49096f4b5cccb30aeabbabfa9ca6970ecd',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CommonHarmonicMass.lean': '104d0c157d979dedd9534fc74ba79e039598f3c58ff9e94476b57e8d79d667b4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CommonRadical.lean': 'dea66dd26ae9e657fe8e8a8d8f20d620199dd24c4a3d860abdf16822e21bfe2f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CommonSupportPartition.lean': 'd4f4b603a71824855a5e009759599ccf85963fab82efa8eebc8753cae098852f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CompleteRowRecipe.lean': 'f3cf0b2faf1b7a2e5314c0633402b9861de4fd1b5e6c86533e2569acdaf7156c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CoprimeCoefficient.lean': '64ccd35ebf33d9ee2d262889696156c3a75067c8bba6e16fbecf9e056b833790',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/CorrelationKernel.lean': '75b953a93ca96be104ebfc6fb85162f7feecc7904eea35df6049f6e442c9dca0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/DerivedCapacity.lean': 'eb08e9f4e2a93b1848fc4c25b5ef3e3df7542ab3cd9a7e94f54d5f8dbf8740f0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FiniteNormalizedChildren.lean': '19a72a11d1f18cf6a9312e6af45a1456acca3baacd38b3ce8c3d0502d0a76452',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FinitePhase.lean': 'af748396b7a3267d03dbf7650cc31d73eb57ed8127d58a8852a5f27001c0779f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstActiveDictionary.lean': '364942cfa67cbf35ba4a2dd841c410493f3c0cf00dc249ca5c355d59713a5562',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstCharacterSource.lean': '59e91672ccaa4a018ac56e5cd8b4d2579e0d1280dac13a03c49d372fde6fa90e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstCommonMass.lean': '35705d812d04ab543ecf0733bd1a11b63a4957f78f3df57958a60e5450f30258',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstCommonSupportSource.lean': '00d317127abe58e1daca113d64beb167988becf8bed2e0dde28e302adf24b967',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstDivisorPool.lean': 'f4457c5eeca1bfe2dfac88c0c68477b7c052610e5d341bd67931ad8d36f5db5d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstFiniteSource.lean': 'fa3769152d5276be21e946bea879e83eddf8a7a89d27c166e0e8d5dbd5af89e2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstGaussPool.lean': 'a78b5ee229876fa68c248a0092ac2d9345ed719c1230d501a9dac6dc990b5059',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstGaussPoolKernel.lean': 'a6c4a14e5baa281ce941658e59729e12e5253675995ff972a1cc37ff1f5638b6',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstKernel.lean': '3145f698c16353708dde0e4975db6802927724dabd98b53cd1971e7a05a7228b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstPooledResidual.lean': '02356399db18c6506ae98ecffba18619f68ec59ea2552ef8c740bac7cc50b671',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstResidualSource.lean': '76f2e66a819cde4cc49febfc65aeac9ba32866d1f9033e441c718c71b2f1c93b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstStage.lean': 'dea93a1460ee0e3a24917d18f4b8c4c3b9282f5996f925e552bfb4844aaf1448',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstWeightedReduction.lean': '461f81ab7a698d59a3f773eb387ca5399f4ee7dd883e7911819d9bd4d5f05a9a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstZeroAmplitude.lean': '9ff72712351ab57f911065b9ddf8847a0f7e82b026366ec22b446dde3e837286',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstZeroDiagonal.lean': '5b0a78ab63fd1c2833beb6f386b7f8710099a05a1c0e9fbe6205ffb2ef7571ec',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FirstZeroSupport.lean': '591202f1693eb198a9e02d65ec303d393aa15f8d8c939693c93cec1c1904dc5e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/FixedChildFamily.lean': '09e34e8301c7998e0a5090e08a6516ce81df931a14c79200bbbae8754cb06d7f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/GaussEnergySource.lean': '507a9f71aad8871866d5e38843dbb7d4089b132cc40047e3c2137ddad309d1f4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/GaussPairTransform.lean': '7f8f7f1900a3b360cda1872ada6cbf033f123e12492b57636f7e3b2cc805b7aa',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/GaussPoolDictionary.lean': 'cad391bf04567ddc8556c7639af1ed0699ffd6b273a87c8d5867f055846c4468',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/GaussSource.lean': '6407f677714a58fee619d78f06542dae06725144fdd037bd2bec5703d030fb2e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/GaussStagePhaseTransport.lean': '08dbcc1ff365a388bb596a00bf97385633632bf2b22d04cc2c03e3ac6c45ad49',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/GeneratedCorrelation.lean': 'a9954a4895cd9b961f3dc11d887845af4c0f70b714797a0009eeb52aa3abdca9',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/GeneratedZeroGauss.lean': '0e38d05c180923881046fc14dfe66c062593bd54f1ac9c525d7615e08ab69b13',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/IdealPool.lean': '92535888ebd2a4156e709addfde0f559fa87674602bbbeed7848df159d6f22bc',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/JointKernel.lean': '086b04d6a986e56b54ae640d8c35a5ea74196bdb6a12c0b679500be7950b8b83',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/JointKernelBounds.lean': '3fdb156c2ce7dc0a4345207118702a140c713ad250e5a164fe6a85c3eaad3865',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/JointRowBudget.lean': 'fd2b8372edfacb687d68018aeca9be31c393742bdb53d2eb103e993d8803120b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/Ledger.lean': '54378988612a95e65e1275cd9652ff3a47f659db5df22192201aa87928381b40',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/LocalAmplifier.lean': '9ec335750270c2d8f711cde5cd1b5a3d7dc3ccb69558840369af5f6dba2475d5',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/LocalCRT.lean': 'e153ca3345dd682b7dd08307fb28150aa27805f40b497db1236da2f3b9bf4c50',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/LocalCorrelation.lean': 'd340279846d99ae441f66e26f126ebce65eba6641f9d166bef2c64a4310aaaad',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/MomentDataAdapter.lean': '4353d443440dee67c8b9b93adc4fce1f61361ae1ea830534c68af6b02d2f7c0d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NestedFourierMeasure.lean': '3c55a6dcb90d72e28d938a10c05313db9492f486947c910ba18fdd55e220d5b4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NestedHilbertPhase.lean': '8006594c929c936a3950f737920e9c89f9e44934a9fcdf846c982e0207811d0c',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NestedSecondClassProduction.lean': 'bc600f14b2e575e7d45c7443eb6cdd079076d3af52c889f708f285fb9bd3f5ed',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NestedSecondResidual.lean': 'e02e3642db93fd6139b6c7df4f73526b464bd58a37d384a43f5b955fc28d8345',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NonzeroQuotientSupport.lean': 'ec69fdf0d3f5090007d153a0df8f03752f2cab476965592a5b37c505fff41564',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormIndependentProfiles.lean': '9249e328eba671c88d0945222adc71bd649ee3ee03f4666d76f40d653808ac79',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedActualCapacityChild.lean': 'a8892531d70f51f211e1cfb08e06dc9f6c862dc569cb4c20d5e914efb232f900',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedCapacityChild.lean': '04a515f2864839a0386b23367a0af33fbed664a700d3db595f09213d15939387',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedChildKernel.lean': '56627b4d88c8037e53a39b26023b696a9301d421657d8758fbbacb5f3c44aae7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedMomentProfiles.lean': '3e256b726acf33c3cf4f8c1efc2a60696a683ac903cef7f4f8cd75c821c8cc26',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/NormalizedSlotRemoval.lean': '2c651ac42fb17f3e28fc13262e7e1ef8a7b9b2bcd829e6d8ca53651c29f69fed',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OrbitalCorrelation.lean': 'a5e050eec9f565c1d3e7d530437ce7e302fabbc97dae06558f815e2847db12a3',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/OriginalOrbitFibre.lean': '38fb5b056b417e0ebb5bdf41177a147e62e0f98751ca3cb40a6dedc2b061be84',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ParentArithmeticAtoms.lean': '9f8e87800ab32837144084c0bfc374984717706a0aa51931c5b0c5fc9944e2c8',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ParentColumnPhaseBinding.lean': '8cad470033dce4b997e3a174bf20f71270f548db268c5822efd1c25e7229be1d',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ParentConstantSource.lean': '57a32626c7f12925a77f0377d08a17c6096de68cb4fc160f1f68e038a1a98a24',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ParentMoment.lean': '2ad71b4fcede7f07ec9fd898dc154aa37597d94ac0ea1a0e40f4d25f9612e391',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ParentOrbitFibre.lean': '5fa92cb56397a08af6b4413058062a3669af40cbd37d5a401b6b09eeede8b2c5',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ParentOriginalAtlas.lean': '1718c4911900bb241eaaf88071a8cbe16f9e074a3354124ff29d262688e9c6e1',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ParentRawSourceInput.lean': '88ef307a32cb6b0b4447bbda60428461ca4dda39f559acfeb2e5b2b81e16f9ac',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ParentSource.lean': '1bc5e01adcb8b240a1de3ee0456871b292436b9414db5d7b2f18104476b3356e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ParentTruncation.lean': '7a76a06d433138afe0c8a178889a7013851ebdc3fc553bb57ce60b9556198707',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PhaseDictionary.lean': '3836cc54e1651a2ba786d32c1c6808054ffec893c851e1a74fb792c6ba1dcf65',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/Pool.lean': '98a8f2bc36a6c8095bf7a169cd66ad763875ddd0d27236bcf879804daf525601',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PoolGaussDecomposition.lean': 'e72ebb092b4487d2ad8b57b84ae4d92525daebff533c3a25ec8c2d1f59363b48',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PoolSecondStage.lean': '1b8db53310396fcb3abc1168a402cf1f35fc11038ada5b01bb9be80f05ddcc4f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PowerfulDiagonal.lean': 'b9c47f8550f6be598ff1c414e014b59c8120e35edd385cf00761ff9b37ec820e',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PowerfulProducts.lean': 'c5d8a333b6fbb4929066a47e0cc82a1075748d45fe3fe17e58c2a524ce2e2274',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PrimePool.lean': '4dc443e953823525a803d5cc24311903bb28de66582a839788164560074369c4',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PrimePowerGcd.lean': '22c17bc3ae50b86bc3947f790673ed74ad2ba19d7b0599b0b6c8417f75c0d2f7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PrimePowerQuotientSupport.lean': 'ba4d96eb6bfbf5b3a3667b2ece7dce23d68dc9d0dc593a52c2ed2a267acdf609',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/PrimeSupportMass.lean': 'a36fd44ed18275e4e2ce89e2e309c85328abf624579413d3fd940cbad8f9c8ce',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ProfileNormalizationInput.lean': '12c3de33520b5e21c05b7bc8048a6972649da20f404fedec7ab094f0f55bd9bc',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ProfileSeminormNormalization.lean': 'fc95b37ca712799b62951ef89afd85a90b3f8fcf3636053a901aec6d3fed9dec',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/RankinLabels.lean': '50b15b54b192a0ac3c84722a9caeae24469e95d821bbe70eb275cfa74d7a07cf',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ReductionOutput.lean': 'd575b59236c84b4cdb76f67930d4b5dc15e671f47811a18818afd9a9882f1b5f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ResidualTupleCount.lean': 'fd83c6bba5281de4f4100ed5dcb6e153cf6880b654dc3aa0cd6d790229786c73',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SIntegerFirstFourier.lean': '93baf7ceb54942b4810a234d2293bb49b0948b54a2280ef606fa1d58733c2cb2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondAllocatedSource.lean': '4de4ab89bb320756899229d59f055eb497ca29b5c43393f4174bd41e1bdbb7e7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondAllocationKernel.lean': 'fa5cf5d9bba21e5469b8027b6d1a2d19eb512b3e2f1cbf2770eed4ec5571ef43',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondBranchProduction.lean': 'e581be95029c4dbf08676e6d61548f6fe68ae396dff1a0d9b296467cc6fdf7a3',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondCenteredBinding.lean': '6883e61529307021b3498dea2cf8e91654bad15ec8ef658f7e3ccb1b381f1d92',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondChartAllocation.lean': '63f9222834d7b89bcd3a291f29d545c5629190ce89a7b0b7848543cf52cd42db',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondClassProduction.lean': 'd65b26868ce708e23b6a58a3a11018fbe522ffdccbe62bf7cd156e17cf0e1043',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondCoefficientBinding.lean': 'bf312c4fc2a264b23c0fdba380cfdebc200781e5314cdd3747ab658ca0a7613b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondCoefficientNormalization.lean': '1eecc40ec643be114284b63eb00df47f65e60490a227428b562fb10e16ae3a0f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondCommonSource.lean': '2cefea84d0e6e2f4b9d22bab52feafa493e26a34974d7034f8643eb250e3752b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondCorrelationSource.lean': 'f02f9e9b7b37098b96181b5d7153574ae4344a9f8465582ff25fba25f4b9f757',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondGeneratorSource.lean': '35695098f678a15f583fb2a8f195bf93e9b2aa209c7462f119a84075a9c2a005',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondResidualSource.lean': '1583d6a3b10d2800452dd7dd3649feb718625bb8e21fdf6977bb9cab3bb0b916',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondStage.lean': 'c004d250ec24cbb3db68a0968163f5df0ad9cc4cb0957dbf64f3a3d6c43fe6cd',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondTailBudget.lean': '565364e2ce241bdbff73803a4e6eef903b8b90dd332625ea3a61dcc45b8eec4f',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondZeroAmplitude.lean': 'f3cdd8169d09eb848756dcf680c7a246cb1cb385e645a129966cceda844b0bc9',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondZeroDiagonal.lean': 'd17c8b180bb11d75ae84854dc42fe53d8055ba259701c94b6fb43150abf8cadc',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SecondZeroSupport.lean': '47123d9778de5f1fdf4e873e354ff0d15f95ca253fa3dc399d17f7cd9e2b6ad7',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SlotRestriction.lean': 'c873f6367169dd9cda2e29582a1ecc24a203e3657b23091191c0464bd41772e2',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SourceCartesianAtlas.lean': '6718a4bd89d21596019a4cbcd9ac8a425105d44e9f494d1c4c61e4dfd830a82a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SourceFactorExtraction.lean': '7a305075ef11e206335c7ffe9cffc1ba0eef8fa379dcb70863288b747d61c160',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SupportCartesianReindex.lean': 'a8af4daa76a9752913dcb7626be52e15db9a473747434486782487d9221c7156',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/SupportKernelPartition.lean': '6f4431ce9df17ac8de7a3d0bd385ca2749cb54790ffe10c38cc3313bdabf1eb3',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/TailBudget.lean': 'b49aff8bea739d827096a0ad635815dc492b8283b1986ff5e700a4bb923fb5e0',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/TailFiberCount.lean': '1df0c2886f229f37de743a92d4466b63ddf40b71bcab82021b216f077f483f6b',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/UniformLengthCapacity.lean': 'cae19e238208c691da09df58b81afbbda8639d85f5b5388c6794f13b281c7040',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/ValuationAllocation.lean': '4099ec5ce0c3fcaf5b611a6b2c7a35c906321b130b7a1338f1d63a88edf9288a',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/WeightedNestedFourierMeasure.lean': '047684bf2d6ebd6e23ae0473787242d5602a85b0a9ea89af75e1bc9cf4d7ed47',
 'HeckeSkeleton/Moments/MOM_ENGINE_STEP/WholeAllocation.lean': '1447e7e84cfea07f65b9feeb2bc732ca380789f86d6155de0e11d6e93c3f03e5'}
SOURCE_COMMIT = 'acc0c254a8e9aef3d7e4b04c03782b28d81a8de8'
SOURCE_SOURCES = {'ExpansionInterfaces/DyadicCount.lean': 'a52681bd30d1e18c7c20b32165ddf11136870f357a21f267502caffb13f95331',
 'ExpansionInterfaces/DyadicShells.lean': 'a8330e7066ff7a3b3c53f9b4e8b6d6af137041a29cb6b0dab5d1bd31b3123610',
 'ExpansionInterfaces/ParameterChoices.lean': '371926930bf1e35af484c711c2e2d0668f4dd978f466ca34009c8c425fc86d61',
 'HeckeSkeleton/ExpansionModels/Core.lean': '537b4afd82871e007cb438518e663e9a45c064c3cefecaa81a7ce557eda0f6f4',
 'HeckeSkeleton/ExpansionModels/DyadicMomentEnvelope.lean': '63bd533c5a5b4bd2be880ceeb22ef5880f0753e01a2139dfd051bf98f899fcea',
 'HeckeSkeleton/ExpansionModels/RecipeSchedule.lean': '48b1838bd6aa0a1c7229424653ca47c8ca8ebba1abe850592c968964e41a3b48',
 'HeckeSkeleton/ExpansionModels/ScaleCutoff.lean': '98a5345a361d159a7d17d02b7953cf7f9e562402cda8d3eec912321fd43cad65',
 'HeckeSkeleton/ExpansionModels/SharedWitnessRecipe.lean': '78011ed1fb6076260b23abae7dc22ab40c34686ec032a9e5e39e2b7a83d9d611',
 'HeckeSkeleton/ExpansionModels/SourceData.lean': '4b40c6980a5cb1e4e4f6b5196c4034049b6c9af107b8bf21356ad7f681f8cdc3',
 'HeckeSkeleton/ExpansionModels/SourceGeometry.lean': '71cf993ca28b14f63ed4fe02456e0227a0affdb9dc02c1bff156cb2d048b6419',
 'HeckeSkeleton/ExpansionModels/WitnessHeightNormalization.lean': '31c92678b8e973f1c1ff65ae9e0ff3d43c17c2d440c2a90d5fea63204ed58520',
 'HeckeSkeleton/Moments.lean': 'ad32874b4e7f6da6d8ae670ccc5c588d26ca796041c4906a5ce0adad6db435ba',
 'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/ProfileControl.lean': '328a45dd8b9bea367aea65f9fd837482d3342c515550d3d1307c60bfe28c8ad1',
 'HeckeSkeleton/SourceData.lean': 'f8956f17c60594f51eb17349d0d94f55a9c412a54d764d1f5588d51f670f9345'}
REINDEX_COMMIT = '778b4220d3d4bc8538549bf74998a78e570d01d9'
REINDEX_SOURCES = {'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/FiniteSectorCore.lean': 'aec890cdfe84c6a6bb97fa3d48ac88117ced794a5ead2b5aded1b469d1d636eb', 'HeckeSkeleton/Moments/MOM_UNIFORM_AMPLIFY/FiniteSectorReindex.lean': 'c9cc4fb6c7156db541c69b1e50dd709cd198d9ab791572ffcb72e4857178de9b'}
# These integrated files preserve the canonical source and the already merged
# ThetaGlobal aligned choice / library configuration. They are deliberately
# audited separately from byte-for-byte canonical imports.
INTEGRATED_SOURCE_PARENTS = (SOURCE_COMMIT, "e66f7384bc08d1124d1a9a4e7dcc21e4facffab0")
INTEGRATED_SOURCES = {'HeckeSkeleton/Base.lean': '16cd8ba7fec2cc47da61f2d7310a49fe87acf53992885ac2377d4eaeb146586c', 'lakefile.toml': '2d4deb66cc8a08f069ce72e873ea53f0877ac8aa181a57b08676a7a73aad1af0'}
INTEGRATED_SOURCES['HeckeSkeleton/Moments/MOM_BASE/LocalGauss.lean'] = 'fd1552537104f93fb975803605bd53ab800861ba6162e1300476c40e3dd94567'
CANONICAL_SOURCES = PRODUCER_SOURCES | SOURCE_SOURCES | REINDEX_SOURCES | INTEGRATED_SOURCES
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
                f"Canonical imported source differs from its published pin: {relative}")
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
                  canonical_source_commit=SOURCE_COMMIT, canonical_source_sha256=SOURCE_SOURCES,
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
