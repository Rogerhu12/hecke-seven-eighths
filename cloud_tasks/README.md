# 云端任务

**仓库**：`Rogerhu12/hecke-seven-eighths`，分支 `dtests-handoff`。论文是根目录下的 `weil_seven_eighths_revised.tex`。顶层骨架在 `HeckeSkeleton/`，其中尚未完成的部分都标有 `-- OBLIGATION <ID>`。

**参考**：openai/math（https://github.com/openai/math ，路径 `lean/OAI/NumberTheory/DirichletL/`）。

**环境**：Lean 4.35.0-rc3，Mathlib `0493595ecd5da8ef14742febab99728f98e948e8`。

**持续工作**：领到任务后要一直做到完成标准全部达到才算结束，即目标定理编译通过、公理检查只含三条标准公理、PR 标为可审查。不要中途停下来汇报阶段性进展，也不要停在"草稿"状态。某一部分被卡住时，把原因记在 PR 里，转去做其他部分，全部能做的都做完才停。

**规矩**
1. 每个任务在自己的新分支上做，用 PR 交付到 `dtests-handoff`；不要直接推送 `dtests-handoff`。
2. 一个 PR 只做一个任务。
3. 不要改动已有的证明和定义。发现陈述有错或缺少必要的假设，就在 PR 说明里指出，并给出修正后的陈述。
4. 不要用 `sorry`、`axiom`、`native_decide`。
5. PR 说明写清楚四件事：
   - 主定理的陈述与假设；
   - 还差什么；
   - 编译了哪些模块、在什么环境下编译；
   - 公理清单。

## CI 预编译缓存

仓库的 release 里有 `lake-cache-<提交号>`，存放除 `HeckeSkeleton` 外所有项目库（DedekindZetaZeroFree、HeckeGeneral、HeckeAxiom、SkeletonInputs、GramCoreInputs、GramAssemblyInputs、CubicSieve、PrimeCancellation、HeckePort、OAI、FLTReuse、Zeta23、TauCetiReuse）以及 `vendor/class-field-theory`、TauCeti 两个包的 Lake 编译产物。Mathlib 及其依赖不在里面，仍由 `lake exe cache get` 下载。恢复缓存后 `lake build` 只重编分支自己改动过的模块及其下游。

**接入**：在 workflow 里 `actions/checkout` 和 `leanprover/lean-action`（`use-mathlib-cache: "true"`）之后、`lake build` 之前加一步：

```yaml
      - name: Restore precompiled project artifacts
        uses: Rogerhu12/hecke-seven-eighths/.github/actions/restore-lake-cache@ci/lake-cache-test
```

分支里已经有 `.github/actions/restore-lake-cache` 时也可以写 `uses: ./.github/actions/restore-lake-cache`。默认取最新的已发布（非草稿）`lake-cache-*` release，也可以用 `with: tag: lake-cache-xxxxxxx` 指定。只需要 `contents: read` 权限。如果同一个 job 还用 `actions/cache` 恢复 `.lake`，把这一步放在它后面。

**说明**
- 缓存在哪个提交上生成，记在 release 的 `lake-cache-manifest.json` 里。分支相对这个提交改过的 `.lean` 文件和它们的下游会正常重编，其余模块都是 `Replayed`。
- `HeckeSkeleton` 不在缓存里，CI 每次都重编它。SkeletonInputs、GramCoreInputs、GramAssemblyInputs 里有 44 个模块 import 了 `HeckeSkeleton.*`；下游的 trace 记录的是被 import 模块产物的哈希，CI 上重编出的 `HeckeSkeleton` 产物与本地的哈希对不上时，这些模块也会重编（实测 `HeckeSkeleton.Principal` 用到的 33 个里有 31 个重编，2 个直接复用）。
- 生成缓存时，工作区里源文件与目标提交不同的模块及其下游不打包，名单在 manifest 的 `skipped_stale_modules` 里。
- 实测（`lake-cache-76c696e`，ubuntu-24.04，`LEAN_NUM_THREADS=2`）：恢复缓存约 30–50 秒，`lake build HeckeSkeleton.Principal` 共 12540 个任务，只编译 106 个模块（73 个 `HeckeSkeleton.*`、31 个 import 了 `HeckeSkeleton` 的 `*Inputs` 模块、2 个 `skipped_stale_modules`），其余全部 `Replayed`，用时约 7 分钟；整个 job 约 10 分钟。
- 只打包 Lake 判断"已是最新"所需的文件：`.trace`、`.olean`、`.ilean`、`.c`，module 系统的模块还有 `.olean.server`、`.olean.private`、`.ir`、`.ir.sig`，以及这些文件各自的 `.hash`。`ir/**.setup.json` 每次编译前都会重新生成，不打包。缺任何一个必需文件（包括 `.c`）Lake 都会重编该模块。
- Windows 上编出的产物可以直接给 Linux CI 用：Lake 对 `.lean` 源文件按换行归一化（CRLF 转 LF）后取哈希，trace 里的路径只是说明文字，不参与哈希。

**底层库变了怎么重新生成**
1. 在要生成缓存的提交（通常是 `dtests-handoff` 的最新提交）上，本地把这些库完整编好：`lake build DedekindZetaZeroFree HeckeGeneral HeckeAxiom SkeletonInputs GramCoreInputs GramAssemblyInputs CubicSieve PrimeCancellation HeckePort OAI FLTReuse Zeta23 TauCetiReuse`。工作区可以是别的分支，脚本会跳过源文件与目标提交不一致的模块及其下游。
2. 在仓库根目录运行（需要 `zstd` 和登录过的 `gh`）：
   ```sh
   python3 scripts/build_lake_cache.py --ref origin/dtests-handoff --out <临时目录> --upload
   ```
   脚本只读 `.lake/build`，按每卷 1900 MiB 分卷压缩，建一个草稿 release `lake-cache-<提交号前 7 位>` 并上传。
3. 在 `ci/lake-cache-test` 上手动运行 workflow "Lake cache restore test"，`tag` 填新 release 的名字。确认 summary 里 "Built modules outside HeckeSkeleton" 只有 import 了 `HeckeSkeleton.*` 的 `*Inputs` 模块和 manifest 里 `skipped_stale_modules` 列出的模块，再发布：`gh release edit <tag> --draft=false`。发布之后各分支自动用上新缓存；旧 release 可以保留，也可以删掉。
