HB-EULER：有限有理表、动态界与解析域核查
ChatGPT / GPT-6 Astra Pro，2026-10-31（UTC+8）

一、交付结论

本包包含指定环境下编译通过的五个新增 Lean 模块、原样依赖副本、
项目适配层、逐条定理声明、成功构建日志、一页报告和七页数学分析。

已完成：
  * 五行参数化分歧有限有理表及整指标标记版本；
  * 重复指数合并后的有限数据求值正确性；
  * 归一化有限有理表求值与闭式的精确恒等式；
  * 动态线上未标记误差与标记表的常数 9；
  * 未标记表保留额外扭曲分母时的常数 40；
  * 实际正则有理函数的代数审计和原解析域的参数反例。

原任务没有完整完成：通用 TRowEulerInput 在原 rowEulerRegion 上有反例。
分析稿第 3 节证明在 (s,w,z)=(9/10,4,1/100) 上可使实际乘积模长发散，
不是仅仅发现一个现有估计不够强。该全局发散论证是数学文本证明；
Lean 已核查实际有理式及区域运算，未声称完成全局 not_multipliable 定理。

本包没有定义 highEulerData，也没有证明工程中的 highInitialEulerControl
或 HighExceptionalEulerControl。一般数域的 Gauss/Fourier 校准仍需完成。
没有用这些目标自身作假设，没有为错误的原域结论加入占位证明。

二、文件与状态

code/HeckeSkeleton/HighEulerRegionAudit.lean
  已编译：18 条定理，直接导入原样 RowEulerRational，审计精确代数和实部区域。
code/HeckeSkeleton/HighEulerFiniteData.lean
  已编译：10 条定理（含 private helper），有限表和标记差的精确数据构造。
code/HeckeSkeleton/HighEulerScalarBounds.lean
  已编译：20 条定理，从 q>=2、b>=1/2、e>=0 和系数范数界推导常数 9。
code/HeckeSkeleton/HighEulerCheckedTable.lean
  已编译：20 条定理，把有限表求值接到标量界，并证明扭曲分母常数 40。
code/HeckeSkeleton/HighEuler.lean
  已编译统一入口，导入上述四个模块；没有新增定理声明。

上述新增模块共 68 条 theorem 声明。完整声明见 theorem_statements.txt。
所有证明体均在相应 .lean 文件中；声明目录不是另外加入的假设。

code/HeckeGeneral/Analysis/RowEulerRational.lean
  原上传依赖的逐字节副本，已编译，不计为新增源码。

integration/HeckeSkeleton/HighEulerTables.lean
  未在完整工程编译：逐字段转成真实 FiniteEulerRational，并运输已证求值和界。
  所需 PhysicalProbeRows 的传递项目依赖不在附件中。五个适配定理单独列于
  theorem_statements.txt，不计入已核验的 68 条声明。

reports/HB_EULER_report.pdf
  一页交付报告。
reports/HB_EULER_analysis.pdf
  七页完整数学说明、反例证明、五行表、动态估计和待接线接口。
reports/*.tex 与 reports/fonts/
  可编辑源稿、原始字体及 OFL 许可证；在 reports/ 中运行 XeLaTeX 两遍。
  需要可用的 XeLaTeX、常见 LaTeX 数学宏包和 DejaVu Sans Mono 字体。

verification/logs/
  六个实际成功构建日志，包含版本、编译命令、源码 SHA256、声明公理与退出码。
  仅 HighEulerFiniteData 有一条不影响正确性的 tactic 排版 linter 提示。
verification/verify_used.py
  产生上述日志时使用的原始脚本，保留当时的环境路径作为复现记录。
verify_one.py
  便携的单模块编译包装器，只使用已安装的 Lean/Mathlib 缓存，不下载依赖。
  该包装器不是 Lean 证明的一部分；仅做了语法及命令行入口检查。
manifest.json、SHA256SUMS.txt
  模块验证状态、源码散列和交付文件完整性记录。
proposed_region_fix.diff
  未应用、未进行全项目编译的区域修正建议；仅增加两个混合条件。
  用户原始文件没有改变，所有上传 ZIP 条目与解压副本都逐字节一致。

三、已证明的主要数学接口

令 q>=2、b>=1/2、e>=0，并设
  Re(s)=b+16e，Re(w)=1-b-6e，Re(z)=17/50。
PhaseData 的六个复系数 eta, alpha, c2, c31, c32, c4 均有显式范数 <=1 的字段。
它不包含待证的局部误差界；V、R、B 和各 D_j 的界都在模块内部推导。

normalizedFiniteFactor_value：
  归一化有限数据的求值等于 ramifiedTableValue（q>0）。
normalizedFiniteFactor_dynamic_bound：
  |rationalValue(normalizedFiniteFactor P q j false)-1| <= 9*q^(-10e)。
normalizedMarkedFiniteFactor_dynamic_bound：
  |rationalValue(normalizedFiniteFactor P q j true)| <= 9*q^(-10e)。
normalizedFiniteFactor_twisted_dynamic_bound：
  若 |d|<=1，则 |H_j/(1-d*q^(-s))-1| <= 40*q^(-10e)。

j : Fin 5 对应实际分歧估值类 j.val+1。上述界允许任意虚部和负的 Re(w)。
最后一个定理只处理未标记表增加扭曲分母，未声称校准实际 Hecke 系数。

四、目标版本与逐模块复核

Lean 4.35.0-rc3
Lean commit: 470d5ce1400764999581fd26d5d72b00d990b0f4
Mathlib commit: 0493595ecd5da8ef14742febab99728f98e948e8

本轮每次仅构建一个模块，没有运行全量项目构建，没有提交。
已编译源码没有 sorry、新 axiom 声明、native_decide。
记录的 #print axioms 输出只使用 propext、Classical.choice、Quot.sound。

如果已有同版本 Lean 和带 .olean 缓存的 Mathlib，可以在本包根目录运行：

  python verify_one.py HeckeGeneral/Analysis/RowEulerRational.lean --lean "/path/to/lean" --mathlib "/path/to/mathlib4"

然后每次只把第一个参数替换为以下一个文件，按顺序执行，等待上一次结束：

  HeckeSkeleton/HighEulerRegionAudit.lean
  HeckeSkeleton/HighEulerFiniteData.lean
  HeckeSkeleton/HighEulerScalarBounds.lean
  HeckeSkeleton/HighEulerCheckedTable.lean
  HeckeSkeleton/HighEuler.lean

参数支持 Windows 路径；请选用对应系统的 Lean 可执行文件。
该包装器只向 code/ 写编译产物，向 local_verification/ 写新的本地日志。
随附的历史验证日志不会被覆盖。锁文件防止同时启动两个编译。

若接入完整原项目，可复制五个新增源码到原 HeckeSkeleton/，保留项目已有的
RowEulerRational.lean；再单独检查 integration/ 中的适配层。
不要把当前入口误当成已满足 highEulerData/initial_identity 的最终替代。

五、后续必须解决的数学步骤

1. 修正正 w 区域：在原条件上增加 Re(w+6z)>1 与 Re(s+6z)>1。
   分析稿证明这给出正则因子的正常收敛；完整工程的解析性接线仍需实现。
   动态负 w 的部分沿用原项目已有 RowEulerNegativeStrip，不是本轮新缺口。
2. 从一般 K 的实际 finitePoissonFactor 识别本表的 Gauss 因子、单位相位、
   生成元和估值类；证明 PhaseData 的系数范数界。
3. 在分歧处使用实际乘积特征的素系数。不能把两条分歧特征分别置零后再相乘，
   因为其分歧可能抵消，实际扭曲系数可能非零。
4. 证明四理想初始级数的绝对收敛、互素乘法性与全局 Euler 恒等式。
5. 构造 RowEulerData 的实际算术字段，再接 presentation 层目标。

引用到的 Mathlib 引理均由上述实际编译核对。附件未给出的项目模块和
需核对的算术桥梁完整列在分析稿第 8 节；未编造那些模块中的引理名。
最不确定且尚未证明的步骤是一般 K 的有限 Fourier/Gauss 精确校准。
