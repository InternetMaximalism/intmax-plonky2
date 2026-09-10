# 現行wire-v3 Lean監査更新レポート

2026-09-06 / source base `becfe98e37c76e62f02f1aa7a417c7b06840db67`。

## 結論

**現行の重要部分に対する実行可能モデルと決定論的証明を追加した。
「今の実装全部をLeanに直して安全性を証明する」という全体目標は未完了。**

全ソースを列挙したmanifestにより、未形式化のファイルを隠さず管理する。
ソースhash、型の整合性、既存テストの成功は、実装refinementや暗号健全性の代用にしない。

## この更新で得た実用的な結果

- canonical field演算、strict byte読取り、24byteのExt3符号化と表現変換を接続。
- Rustのzero-padded constituent foldとSolidityのsparse-prefix foldが、
  関数的loopモデルで任意のpadding/challengeについて同じ結果を返すことを証明。
- 同一の旧digestの下でtyped transcript frameのtag/payloadはhash前に曖昧でなく、
  両lane/全claimを吸収後に指定counterでchallengeを生成する関数の順序を証明。
- 外側compact grammarの切詰め・非canonical limb・誤header・余剰bytesに関する
  実byte上の検査条件を証明。opaque WHIR内部とは明確に分離。
- coupled roundsを実際の遷移列として定義し、長さと結果の一意性を帰納証明。
- 原子的verifyの受理には、同じderived contextに対するroots/claims照合、
  WHIR tail観測、norm/gate双方のterminal一致が必要であることを証明。
- WHIR終端行の限定モデルでは、認証に渡した同じ行のfold値と、導出したdomain点での
  最終多項式の評価が全queryで一致することを、成功条件から導出。
  WhirFinalで後続のfinal sumcheck・最終claim・EOFへ同一vectorを接続したが、
  認証/前段状態/decoder等の観測は残り、全WHIRの証明ではない。
- 同じ終端値に到達する候補/真のsumcheck chainで初期値が異なるなら、
  実challengeで異なるround関数の評価が一致することを証明。
  その事象の確率やcircuit witnessの存在までは導いていない。

正の通常例も含めて実行可能な受理経路を確認しているが、観測関数付き例は
実際に生成した暗号proofの代わりではない。

## 前回の継続更新（69516414時点）

この段階では6モデル・202定理を追加し、計14モデル・372定理へ拡張した。
以下の未対応記述は当時の状態であり、その後の更新を次節に記録する。

- **WHIR終端**: 実際のquadratic更新、最終randomnessの逆順fold、非零、具体的な
  norm/adjugate方式の逆元計算、全round constraints、全linear-form、両cursorのEOFを接続。
  逆元恒等式や、観測されたdecoderが全bytesを正しく読んだことまでは未証明。
- **Merkle**: raw byteのhint境界、paired/lone nodeの層別計算とoffset更新、computed root検査。
  同一index/depthでの異なるleaf hashの同root到達を、実際の64byte圧縮入力衝突へ還元。
  多重開示全体のbindingや衝突確率はまだ導いていない。
- **norm/logUp**: formal norm/adjugate、helper集計、固定ConfigのkIs/subgroup/PI map、
  順序・重複を保存したPI集計を具体化し、受理時の計算結果一致へ接続。
- **gate**: 14familyすべての設定検証、6familyの具体評価、selector/Horner、
  零差分と完全3limb一致の同値を証明。残る8familyのactive評価は未対応。
- **代数的同値**: 具体Nat.mod式からExt3の交換・結合・分配・加法逆元を証明。
  Rust/Solidityの別形eq/subgroup式とsquareのモデル内同値を解消した。
  PI cache全体の再結合・実bytecodeとの同値までは未証明。
- **統合入口**: packed/norm/eq/gateの4観測を具体化。checked preflightにより、
  未対応gateのnoneをzero fallbackで受理しない。非空のrouted wire/helperを使う
  通常成功例も検査した。WHIR/初期FS/hash観測付きであり、実暗号proofの生成例ではない。

追加6モデルは別担当による独立read-onlyレビューも実施。
Integratedのエラー分類/順序はモデル上のもので、実装の例外・slashing証拠との一致ではない。

## 第2チェックポイント（4422b4c7）

14モデルを追加し、既存統合入口への2定理追加と合わせて326定理増えた。
この時点のrootは計28モデル・698名付き定理。件数を安全性の達成率とはしない。

- **全14 gateの具体評価と統合**: 残る8familyの評価を完成し、GatesCompleteを
  Integratedへ接続した。valid設定と入力長から実評価結果Someが得られることを証明。
  旧partial gateの未対応Noneやzero fallbackを「健全性の証明」として扱わない。
  ただし全gateの多項式次数・回路意味論・集約の確率的健全性はまだ別課題。
- **実定数・全roundの確認**: Poseidon全1023語とCoset全124語を収録。
  全18表をSolidityと逐語比較し、PoseidonはRustとも比較する継続検査を追加。
  Poseidonの正常135-wire witnessは全30roundを実行し、123制約ゼロと
  既存Rust標準12出力を通常Lean kernelで検査した。これ自体はhash安全性の証明ではない。
- **norm/逆元の具体代数**: formal変数T³=2上で実Ext3係数のadjugate恒等式を証明。
  recomposition、inverse candidateとの積、binary冪乗の正確値・fuel条件を接続し、
  実inverse成功時の積をnorm^(p−1) mod pへ還元した。Fermatや非零normを仮定で埋めていない。
  WHIR最終sum-form foldとPacked difference-form foldのモデル内同値も証明した。
- **public input最適化の同値**: 実OR/XOR maskと共通bit分離、newest-first cache検索、
  同一row合算、順序・重複・最後のeta更新省略を具体化し、キャッシュ版PI集計が
  Rust直接和モデルと同じ値を返すことを仮定なしで証明した。
  無条件なのはrawモデルの関数等式で、実コードの入力shape/メモリ条件を不要とする意味ではない。
- **内側WHIR byte処理**: raw hash chain、BE counter、120byte一括challenge、
  24byte canonical read、geometric RLC、PoW、hint Vec prefixを具体化。
  初期phaseのroot/own-OOD/checked・unchecked claims/cross-OODから実初期sumまで接続し、
  272byteの非空初期処理例と、続くsumcheckを含む320byte例を検査した。
- **終端の観測を削減**: WhirFinalのreadMessage/checkPow/challengeを全て具体byte処理に置換。
  成功時は同じ状態で48byte、PoW有効時56byteを読み、120byteからchallengeを生成する。
  既読hint位置は保持し、受理時の正確なsuffix長とhint EOFを導出した。
  初期phase→最初のsumcheckも同じbytes・計算済みsum・spongeへ接続した。
  中間round・raw row認証・samplingから最終Contextまでの一体化は未完了。
- **体証明の準備**: p−1の因数積、基数7の6組のべき乗/gcd検査、
  `2^((p−1)/3) mod p = 4294967295` を具体証明書として保存した。
  素数性判定法の健全性・小因子の素数性・Fermat一般定理は未完了で、pが素数とはまだ結論しない。

新gate群・Poseidon定数/round・Spongefish・WhirInitial・WhirFinalSpongefish・
WhirPrefix・PI cache/shared bits・代数/冪乗/数値証明書・統合入口・定数検査は、
実装担当と別担当によるread-only対照を実施した。
必須修正の未解消事項は残っていないが、手動対照はformal refinementではない。
定数抽出器はコメントを除去して文字列を保持する限定lexerであり、コンパイラではない。
PI cacheの正常例はPI集計部分の計算例で、完全なNorm terminal/verifierの受理例ではない。

このチェックポイントでは実装本体・依存設定・main・親pinを変更していない。公開/pushも行わない。
成果は専用ローカルブランチ `codex/lean-wire3-audit-20260906` にチェックポイント保存する。
全体目標は引き続き進行中であり、この段階で完了としない。

## 第3チェックポイント（f7236217）

現行のraw hint/Merkle処理を接続し、6モデル・184定理を追加した。
この時点のrootは34モデル・882定理。全体目標は引き続き未完了。

- **実multiproofからのpath抽出**: paired/lone双方の実層処理をたどり、全入力leafから
  実チェックrootまでのdepth長pathを導出。独立した認証pathの正しさを仮定しない。
- **元の行bytesからのbinding**: Vec要素数、連続hint slice、raw hash、既存Merkleの
  同root/indices/cursorを接続。実openGroupの同root/depth/index行について、bytes・同Layoutの
  canonical復号値・同weightsの全列dotが一致するか、具体的hash衝突があることを証明。
  これは衝突確率の評価や、全WHIRの受理健全性ではない。
- **sampling**: hashをbyteごとに呼びcounterを進める実raw query生成、BE順、mask、
  特殊分岐、上限を具体化。並べ替えは挿入sortの実行可能な基準版とし、sourceの
  in-place quicksort同値は明確に未証明。基準版でのsortednessを実装証明へ流用しない。
- **逆元の条件付き接続**: 明示したFermatAt(norm)から実inverseの実行・左右逆元・
  消去・除算を証明。7の具体証明書から無条件の逆元例も得た。
  全非零値のFermat/非零norm/既約性を証明済みとはしない。
- **folding schedule**: 実設定guardの投影から、初期＋全中間＋終端が元の変数数に
  等しいこと、各roundのnumVariablesが残suffixと一致すること、減算の安全性、
  interleaving/最終サイズを証明。domainや点配列を含む完全設定検証ではない。

raw認証成功とcanonical decode成功は別条件。final splitのdecode/集計がMerkleに先行する
分岐順も隠さず、今のopenGroupをその完成モデルとは呼ばない。
追加モデルは実装担当と異なる担当が全文・元ソース・主要定理を対照した。
手動レビューは言語間のformal refinementの代用ではない。

## 独立レビューで修正したモデル対応差

1. **設定検査のタイミング**:
   Solidityのconstructor-only検査をcall-timeガードのように扱わないよう、
   複合境界とcall境界を分け、deployment invariantを明示した。
2. **WHIRの変数順序**:
   論理MLE順 `row ++ index` とnative WHIR順を分離し、
   実際に `Packed.whirPoint` を呼んで全体反転するモデルへ修正した。

これらはモデルの対応精度の問題であり、今回新しい実装脆弱性を実証したという報告ではない。

## 主要定理の入口

| テーマ | 定理 |
|---|---|
| canonical arithmetic | `Arithmetic.emul_canonical`, `Arithmetic.canonical_equality_iff` |
| zero padding | `Packed.sparse_fold_equals_zero_padded_fold`, `Packed.full_table_final_shape` |
| bytes / framing | `Transcript.fromLe_le_roundtrip`, `Transcript.frame_tag_and_payload_are_unambiguous` |
| exact outer parsing | `Compact.validation_requires_exact_exhaustion`, `Compact.strict_validation_all_fields_canonical` |
| sumcheck reduction | `Sumcheck.mismatch_requires_evaluation_collision` |
| verification boundary | `Verifier.acceptance_exact_whir_and_terminal_binding`, `Verifier.call_acceptance_yields_checked_acceptance` |
| concrete model connection | `Connections.verifier_transcript_roundtrip`, `Connections.packedFold_padding_invariant` |
| WHIR terminal row slice | `WhirTerminal.successful_each_query_exact_equality`, `WhirTerminal.verified_groups_authenticate_each_pair` |
| final sumcheck / claim | `WhirFinal.end_success_same_vector_and_all_checks`, `WhirFinal.end_success_final_fold_is_singleton` |
| Merkle bytes / reduction | `Merkle.accepted_opening_stays_in_slice`, `Merkle.same_root_same_leaf_or_path_collision` |
| concrete norm / PI | `Norm.acceptance_requires_computed_terminal`, `Norm.public_inputs_all_processed` |
| gate configuration / formulas | `Gates.every_configured_gate_checked`, `Gates.arithmetic_constraints_exact` |
| concrete algebra | `Algebra.emul_assoc`, `Algebra.norm_eq_loop_matches_rust`, `Algebra.norm_subgroup_loop_matches_rust` |
| checked integration | `Integrated.accepted_concrete_terminal_equations`, `Integrated.unavailable_gate_never_uses_zero_fallback` |
| all gate families | `GatesComplete.combined_has_output_iff_valid`, `Integrated.valid_decoded_gate_configuration_evaluates` |
| formal adjugate / inverse | `NormIdentity.formal_adjugate_identity`, `ModularPower.inverse_success_product_is_fermat_power` |
| inner transcript / PoW | `Spongefish.verifier_ext3_exact_cursor_and_bytes`, `Spongefish.pow_success_checks_actual_digest` |
| concrete WHIR initial | `WhirInitial.initial_all_roots_and_checked_claims`, `WhirInitial.initial_exact_read_count` |
| concrete WHIR sumcheck / EOF | `WhirFinalSpongefish.round_success_actual_sequence`, `WhirFinalSpongefish.end_success_exact_transcript_and_hint_eof` |
| connected initial prefix | `WhirPrefix.successful_prefix_is_one_execution`, `WhirPrefix.successful_prefix_exact_consumption` |
| cached PI equivalence | `PiCache.cached_binding_equals_direct_norm`, `PiSharedBits.actual_varying_mask_factoring` |
| numeric field certificate only | `GoldilocksCertificate.all_factor_checks_accept`, `GoldilocksCertificate.base_two_third_exponent_value` |
| actual multiproof extraction | `MerkleExtraction.accepted_nonempty_opening_extracts_paths`, `MerkleExtraction.accepted_raw_rows_bind_or_hash_collision` |
| bytewise sampling / reference boundary | `WhirSampling.raw_nontrivial_success`, `WhirSampling.reference_sampling_output_properties` |
| raw row / cursor connection | `WhirRows.group_success_same_merkle_inputs`, `WhirRows.empty_group_consumes_exactly_eight` |
| actual decoded row / dot binding | `WhirRowBinding.accepted_decoded_rows_bind_or_collision`, `WhirRowBinding.accepted_full_column_dot_binding` |
| conditional inverse units | `FermatBridge.norm_fermat_gives_actual_two_sided_unit`, `FermatBridge.actual_division_equation_iff` |
| folding schedule projection | `WhirSchedule.accepted_schedule_partitions_original_variables`, `WhirSchedule.accepted_round_annotations_equal_remaining_suffix` |

上表の名前は共通prefix `Audit.Wire3.` を省略。
全名付き定理は[manifest](wire3-manifest.json)で管理し、検査は抜粋ではなく全件に対して行う。

## 全ソースの対応状況

| このcheckout内のRust/Solidityファイル | 合計 | 部分的なモデル対応あり | モデル対応なし |
|---|---:|---:|---:|
| MLE Rust (`mle/src/`、旧実装を含む) | 35 | 10 | 25 |
| MLE Solidity (`mle/contracts/src/`、旧実装を含む) | 33 | 18 | 15 |
| その他（テスト・example・別crateを含む） | 222 | 2 | 220 |
| 合計 | 290 | 30 | 260 |

「部分的なモデル対応あり」はファイル全体の翻訳・証明を意味しない。
行数ベースのcoverageや安全性の達成率でもない。
外部WHIR依存はrevisionを固定した依存情報を追跡するが、その全ソースをこの表で
列挙・形式化したわけではない。全実装を形式的に証明済みのファイルは認定していない。

## 旧監査の扱い

7月のrootは `HistoricalAudit.lean` に保存し、旧README/REPORT/SCOPEは
`HISTORICAL-*.md` に保存。旧モデルの数学・所見・公理は歴史資料として保持するが、
current rootからはimportしない。`Poly.roots_le_degree` を含む旧公理を
current proofの根拠として流用しない。

## 検査と再現

```sh
python3 -B mle/audit/test-check-wire3.py
python3 -B mle/audit/check-wire3.py
git diff --check
```

Lean 4.10.0の `lake` がPATHに必要。guardはbuild前後のhash、全source inventory、
全current root到達性、全名付き定理の型と推移的公理を検査する。
許容するglobal axiomsはLean標準3件だけ。
**Engineや定理引数の明示的仮定はこれとは別に残る。**

前回69516414時点でこの作業checkoutにおいて以下を実行した。

| 検査 | 結果 |
|---|---|
| 現行Lean rootのbuild | PASS — 14モデルとrootの計15ファイル |
| 全名付き定理の解決・推移的公理検査 | PASS — 372件、独自公理・未証明穴なし |
| source inventoryとbuild前後のhash検査 | PASS — 290ソースを含む356ファイル |
| guardの単体テスト | PASS — 21件 |
| CI workflowのYAML構文 | PASS |
| 差分の空白エラー検査 | PASS |
| 対象baseからのRust/Solidity・依存設定の差分 | なし |

356ファイルにはモデル・文書・検査器・歴史資料も含む。
CI jobは現行rootとguardを検査するが、リモートCIはこの作業では未実行。
実装を変更していないため、全Rust/Solidity試験も今回は再実行していない。
これらのLean検査を、全体暗号監査の完了とはしない。

### 第2チェックポイントの検査

2026-09-06にこの作業checkoutで統合guardを実行し、以下を確認した。

| 検査 | 結果 |
|---|---|
| 現行rootのbuild | PASS — 28モデルとroot |
| 全名付き定理の解決・推移的公理 | PASS — 698件、標準3公理のみ |
| source inventoryとbuild前後のhash | PASS — 290ソースを含む370ファイル |
| Poseidon/Coset定数の逐語照合 | PASS — 18表・1147語、PoseidonはRustとも一致 |
| guard単体テスト | PASS — 27件 |
| CI workflowのYAML構文・差分の空白検査 | PASS |
| 対象baseからの実装本体・依存設定の差分 | なし |

独自公理・未証明穴・native評価による証明代替はない。
ただし定理引数/Engineの残る前提、未接続のWHIR段階、言語refinementと暗号健全性は
このPASSとは独立した未完了事項である。リモートCI・全Rust/Solidity試験は今回未実行。

### 有限体証明の依存調査

第2チェックポイント時の現監査・親の2監査はLean4.10、依存packagesなし。利用可能な4.10互換Mathlib
checkoutや具体Goldilocks素数性証明は見つからなかった。別版由来と思われるbinary cacheは
対応source/toolchain/lockを確認できないため採用せず、この時点ではネットワーク利用もなかった。

第3継続では公式Mathlib v4.10.0を一時領域で調査した。commitは
`a719ba5c3115d47b68bf0497a9dd1bcbb21ea663`、公式lockの6推移依存のHEADも一致。
LucasPrimality/Finite.Basic/NormNum.Primeとその依存1333 build targetは成功した。
Mathlib cache getは使っていないが、ProofWidgetsはpackage設定によりrelease archiveを取得した。
**このビルドを全依存source-onlyと記載しない。** 素数性/Fermat候補はまだcurrent root外の実験で、
882定理へ含めない。監査lakefile/lockや本番の依存設定への採用もまだ行っていない。
隔離候補の10定理はcompile成功し、主要6定理の公理は標準3件のみだった。
Lucasから具体pの素数性、一般Fermat、立方根2の排除、実inverse成功時の左右逆元を導出するが、
この候補の採用前にcurrent rootの未証明範囲を「解消済み」へ変更しない。
採用前に完全pin/実ファイル内容/未追跡source/import/search path/公理の検査と、
release artifactの信頼境界またはソース再生成手順を明確にする。

この時点で残っていた素数性・Fermat・全非零canonical Ext3の逆元と体構成は、
次の第4継続更新で取り組む。上記は候補調査時点の記録であり、後段の検査結果と区別する。

### 第3チェックポイントの検査

2026-09-06に現行rootの統合guardを実行した。

| 検査 | 結果 |
|---|---|
| 現行rootのbuildと全名付き定理の推移公理検査 | PASS — 34モデル・882件、標準3公理のみ |
| source inventoryとbuild前後hash | PASS — 290ソースを含む376ファイル |
| 実定数逐語照合 | PASS — 18表・1147語、PoseidonはRustとも一致 |
| guard単体テスト | PASS — 27件 |
| CI YAML構文・差分の空白検査 | PASS |
| 対象baseからのRust/Solidity/実行依存差分 | なし |

Mathlib候補・採用準備中の依存checkerはこの結果に含めない。この時点のrootはStd-only。
リモートCI・全Rust/Solidity試験は再実行していない。main/push/親pinも変更しない。

## 第4チェックポイント（da3df4ed）

3モデル・55定理を追加し、37モデル・937定理へ拡張した。
本番のRust/Solidity依存には触れず、監査専用のLean数学依存を導入した。

- **具体的な素数性とFermat**: p−1の全prime-divisorを6小素因子へ分解し、
  既存の実binary冪乗証明書を証明済みLucas基準へ渡してpの素数性を導出。
  Fact instanceはその定理から構成し、素数性を仮定へ移していない。
  全非零residueのFermatと立方根2の不存在も具体Nat.modへ接続した。
- **全非零Ext3の実inverse**: 基底ZMod上のdouble-adjugate恒等式からnormの非退化を導き、
  実norm式・canonical座標の同値へ戻した。実WhirFinal.inverseの成功 iff 非零と、
  canonical出力・左右の積=1を証明。形式normのoff-cube Ext3係数へ一般化していない。
- **実演算による有限体**: Verifier.Ext3のwrapper上に実add/sub/neg/mulと実inverseを使う
  Fieldを構成。別の抽象体から演算を置換せず、失敗時inverse=0という全域化も明示。
  三座標との全単射、標数p、要素数p³、有限体Fermat/Frobeniusを証明した。
  θ³=2および実θ逆元の正の計算例も含む。

主要入口は `GoldilocksFoundation.modulus_prime`、`general_fermat_nat`、
`GoldilocksNorm.actual_inverse_has_output_iff_nonzero`、`nonzero_actual_inverse_exists`、
`GoldilocksExt3Field.field_inverse_executes_when_nonzero`、`cardinality_exact`。
共通prefixは `Audit.Wire3.`。全体のWHIR/回路/言語refinement/暗号確率は未完了。

### 固定した監査依存と再現手順

Mathlib v4.10.0 `a719ba5c3115d47b68bf0497a9dd1bcbb21ea663` と、その公式lockの
6依存を全てcommit固定した。正確なURL/SHAは追跡する `lake-manifest.json` と
`check-proof-dependencies.py` の独立policyで照合する。直接外部importはFoundationの3名称、
NormのRingだけに限定した（第5継続でWhirPolynomialのRootsを追加）。
無制限なMathlib importや歴史資料の公理は許可しない。

```sh
python3 -B mle/audit/test-check-wire3.py
python3 -B mle/audit/test-proof-dependencies.py
python3 -B mle/audit/test-provision-proof-dependencies.py
python3 -B mle/audit/provision-proof-dependencies.py
python3 -B mle/audit/check-wire3.py
```

provisionは既存全依存の検査後に未存在分だけを固定origin/SHAから取得し、
既存の変更・不完全repoをreset/削除/修復しない。検査器は全5601 tracked files・
64,398,270 bytesの実Git blob、HEAD/origin/indexを検査する。通常statusが隠す
assume-unchanged/skip-worktreeの変更、追加Lean/config source、symlink、外部search pathも拒否。

初回fresh buildでは `--no-tags` によりProofWidgetsのrelease選択に必要なタグがなく失敗した。
公開元で `v0.0.40` が固定commitを指すことを確認し、新規取得にそのタグ1件だけを追加。
既存repoはタグ集合とpeeled targetも検査し、別release名への変更は受け入れない。
この修正でsource/HEADのpinを緩めていない。

**依存のsource照合は生成済み.oleanやrelease archiveの出自認証ではない。**
通常LakeビルドはProofWidgets releaseを使うため、全依存source-only再生成とは呼ばない。
Mathlib cache getや互換性不明の既存バイナリcacheは使っていない。
標準3公理と全定理検査は維持するが、Lean toolchain・imported object・実行環境の信頼は別境界。
別途fresh出力でのsource再生成手順を調査しており、この調査結果を現行PASSへ混ぜない。

### 第4チェックポイントの検査

依存guardの34件、provisionの20件、main guardの33件の単体テストはPASS。
7依存の実source pin照合とCI YAML/空白差分・実行コード無変更も確認した。
採用した37モデル・全937定理の統合検査もPASS。全定理を実環境で解決し、
`.thmInfo` と推移的公理依存を確認した。独自公理・未証明穴はなく、許容した標準3公理のみ。
384 reviewed hashes、290 runtime sourceの完全inventory、18表1147語の定数逐語照合、
build前後の7依存5601 tracked fileの照合もPASS。これらは言語refinementやPCS確率の証明ではない。
独立レビューでPythonの `-B` は既存pycの読み込みを禁止しない点も確認し、
helperは検査済みsource bytesを明示compileして読み込む形へ変更した。
cache loaderを使わないことを単体検査する。依存source pinやLeanの公理条件は緩めていない。
リモートCI・全Rust/Solidity試験は未実行。main/push/親pinを変更していない。

## 第5継続更新（da3df4ed以降）

3モデル・82定理を追加し、40モデル・1019名付き定理へ拡張した。

- **最終多項式の意味と一致点数**: 実reverse-Hornerと具体Ext3体上のPolynomial.evalが
  同じraw値を返すことを証明。係数を反転せず、全canonical raw係数を損失なく持ち上げる。
  同長・不同の2つの固定vectorなら、その評価が一致する相異点数は高々長さ−1。
  空列・singleton zero、異なる長さでも同じ多項式になる例も明示する。
  根の個数はMathlibの証明済み定理から導出し、旧Polyの根個数公理は使わない。
  これは固定性/FS/query分布/適応選択/PCS確率の証明ではない。
- **evalL0の実逆元接続**: 実specialized squareの反復からx^(2^bits)を導出。
  degreeBits<64から0<n<pとuint64範囲を証明し、実denominator inverseを使った有理式一致へ接続。
  出力存在 iff bits<64かつx≠1。x=1を数学的な補間値1に置換せず実sourceどおりnoneとする。
  ほかのn次根における正当なzero出力と、逆元が存在しない場合を区別する。
- **中間WHIRの同一実行**: 実WhirPrefixから始め、new root/全OOD challenge/全answers/PoW、
  reference sampling、前rootの実raw Merkle、実RLC、canonical decodeと全列dot、
  constraint保存、具体sumcheck、previous root更新を一つの状態列へ接続。
  初段3 base roots×1vectorから後段single Ext3 rootへの切替えも実装する。
  成功時の全query/全group/全column、同RLC index、rootの元32byte slice、
  乱数prefix・constraint数・transcript/hint cursorを証明。
  初期処理＋最初のsumcheck＋2中間roundの通常toy例は736 transcript bytes/128 hint bytesを消費する。
  toy hashの実行例であり、production暗号proofの生成例ではない。

WhirIntermediateのProfileShapeはVK/config由来のprevious-round設定の投影で、
sourceに存在しないguardを追加したものではない。domain pointのNat.powは_glPowの
数学的結果のモデルであり、binary loopの言語refinementはまだ別課題。
純粋decode→dotとsourceの逐次decode/算術の命令対応、in-place quicksortも未証明。
最終vector/read/Merkleから元prefix由来のFinal.Context、finalsumcheck/claim/EOFへの
接続は次工程であり、今回の中間round証明だけで全WHIRを完了としない。

WhirPolynomial/GoldilocksLagrangeは別担当が全文・実ソース・前提を独立レビューしてPASS。
WhirIntermediateもrootが全定義・定理・元の各source phaseを対照した。
外部importはWhirPolynomialのMathlib.Algebra.Polynomial.Rootsだけを追加許可する。
統合guardと全1019定理の検査はPASS。40モデル・387 reviewed hashes、runtime 290/部分対応28、
18表1147語、build前後の7依存5601 tracked fileの照合もPASS。
main guard33件、CI YAML/空白差分、実行コード無変更も再確認した。
これは通常Lake成果物を用いた検査であり、fresh source再生成の検査結果はまだ含めない。
実装・main・push・親pinは変更しない。

相異なる評価点の前提を実queryへ接続する際、_validateDomain単独はgeneratorの位数を
検査しない点を静的に確認した。固定VK/configのgenerator生成経路から位数を証明する必要があり、
単なる形状検査を原始根の証明へ読み替えない。これは攻撃の実証や、全固定configの
安全/不安全の判定ではなく、今後の健全性証明で閉じるべき設定生成の境界である。

## 第6継続更新（88d8a135以降）

5モデル・172定理を追加し、45モデル・1191名付き定理へ拡張した。
以下はモデル内の決定論的証明であり、全実装の健全性の完了ではない。

- **終端までの同一実行**: WhirTail.runがinit/実prefix/実中間列の結果を保持し、
  final vectorの一回の読取り、PoW/reference sampling、終端両分岐、Horner比較、
  同vectorの最終fold、同じ導出Contextでのsumcheck/全claim/両EOFを接続する。
  final splitはhash→canonical dot→vector RLC加算→cursor→各root Merkle、
  standardはraw認証→各row decode/Hornerというsource順を保持する。
  rootの32byte射影は無損失。全初期claimをcheckedにした通常toy例は336/72、488/128bytes。
  任意のrunTail Stateを前段由来とみなさず、run成功のprovenance定理を使う。
- **実重複除去**: 現在のbuffer[i]/[i−1]を比較し、write位置へ上書きする実loopを形式化。
  全read/write境界、n−1回の終了、未読suffix保存、最終write長と基準dedupの一致を証明。
  sorted入力の仮定はこの同値には不要で、strictnessの系だけで使う。quicksortは未証明。
- **固定評価点の位数**: 6素因子の具体証明書からorder(7)=p−1を導き、k≤32で
  7^((p−1)/2^k)の位数2^kと冪の単射性を証明。transpose指数の範囲・逆変換・単射と合成する。
  任意のshape-valid generatorやdigest-accepted configへ無条件に適用しない。
- **実sumcheckの次数**: 実c1復元、Horner、実端点和=claim、次数≤2を具体体上で証明。
  異なる固定canonical claimを持つ2つの実quadraticの一致点は高々2点。
  成功roundの同じmessage/challenge/stateを保存し、既存の二本のchainの条件付き不一致にも接続。
  比較側chainの真の回路意味論、固定性/FS/query分布/確率は未証明。
- **全typed設定検査**: 全source scalarとraw評価点を保持し、初期fold/domain、各round、
  final remainder/size、single/multi-pointの順に検査。canonical確認後も元のlimbを変えない。
  bound/deployment入口を区別し、成功から既存Schedule・全domain・全点・正確な件数と
  WhirInitial.validatedParamsを導く。sourceが検査しないsamples/threshold/mask末尾bitsを追加制約しない。
  ABI/uint幅/overflow・固定VKからの完全投影・3×1 profileは引き続き別境界。

追加5モデルは実装者と異なるrootが全文・source・明示前提を確認した。
WhirDedup/WhirTail/WhirParametersはさらに別担当の独立read-onlyレビューもPASS。
期待評価値はtyped callerが既にcanonicalな入力を渡す境界であり、設定点のraw検査から
期待値自体のcanonical性も導いたとはしないことを、該当定理のdocにも明記した。
採用名へ置換した5モデルの直接buildと全統合guardはPASS。
全1191名の実定理/型/推移的公理、392 reviewed hashes、18表1147語、7依存5601fileを検査した。
現行source inventoryは290file中29部分対応/261未対応で、全fileの形式的対応は認定しない。
guard33件・dependency34件・provision20件、CI YAML、空白差分、runtime無変更の検査もPASS。
ここでの45モデル検査は通常Lake出力であり、次節の40モデルfresh検査とは範囲を区別する。

## 40モデルcheckpointのfresh Leanソース再生成検査

45モデルの追加前、`88d8a1356eb1a83eda1b7fa8784e5570eca9a507`を凍結し、
既存の非toolchain `.olean` を参照しない別検査を実施した。結果はPASS（777.405秒）。

- manifest SHA256: `f11c4729b3bb077bf11b333fd95e70e6adcddc1fcc9e7e923e87fc0be9b3e6c9`。
- 1370非toolchainモジュール: audit/root 41、Mathlib 1091、Batteries 99、Aesop 108、
  Qq 11、ProofWidgets 18、ImportGraph 2。全て新規出力先へsourceから再生成。
- 全1019定理について、fresh出力だけの検索パスで`.thmInfo`、型、推移的公理を再検査。
  独自公理/未証明穴なし、許容は標準3公理のみ。新規5モデルをこの件数へ混ぜない。
- 開始/終了時に387 reviewed hashes、全source inventory、18表1147語、7依存5601ファイルを照合。
  実compileごとにimport解決が既存source graphと一致し、全生成artifact/source/JSを再hash。
- Lean 4.10 commit `c375e19f6b656fcd594cdca3a38b8578634df8cd`、binary SHA256
  `2af8d3dec15cf5a79a9521cbdf692fa3fdf3110704c4fac2e7fe3c92b36d415b`。
  `--trust=0`だけで古いimported artifactのsource再検証ができるとは主張しない。

当該ローカル検査の保存先は `/private/tmp/wire3-fresh-source-build.497h73wc/`。
receipt SHA256は`bfa4ec60d782fc0de20d6ff9f3462e353801eb2d8b1e09021390aae13648299f`、
graph SHA256は`edb9a9d17980ae0d298e7a48d1ad6d58b3c75c58373f71c6268c914a3c152cb1`。
使用した一時runnerは `/private/tmp/wire3-fresh-source-runner.iXATos/fresh_audit.py`、
SHA256は`9128f90b80becc4a43cae970567362887ce42da1970debad150e196fea0b46ed`。
この一時パスの保持を別環境での再現可能性の代用にしない。

runnerは全sourceと失敗経路を独立レビューし、補助self-check12件もPASS。
ただし無効`.pyc` fixtureの検査は通常importへの退行を検出できないという弱点を記録する。
現loaderは実source bytesをcompile/execし、既存bytecode cacheは読まない。
途中失敗時も終了時source検査を試行する。ネットワーク、Lake、release取得、既存成果物への書込みは行わない。

**主張は「固定JSデータを使ったLeanソース再生成と全定理検査」に限定する。**
11個のProofWidgets表示用JSは既存bytesを固定して用い、そのsourceから再生成していない。
Lean toolchain/core artifact・Python/Git・固定metaprogramと競合する悪意あるFS変更がないことは
信頼境界に残る。実装refinement、暗号健全性、後続モデルのfresh検査を証明したことにはしない。

## 第7継続更新（ac3476bb以降）

2モデル・59定理を追加し、47モデル・1250名付き定理へ拡張した。

- **実評価点での一致query数**: WhirIntermediate.domainPointの同じraw Ext3値を
  具体Fieldへ包み、固定生成元由来のtranspose後の点との一致を証明。
  k≤32、実generatorと固定値の一致、正のcoset次元と積=2^kの明示条件下で単射を導き、
  同長・不同の固定canonical vectorの一致する相異query数≤長さ−1を証明した。
  実raw Hornerと正規化比較の双方へ接続。実query範囲や設定生成の証明ではない。
- **実剰余変換を含む条件付き上界**: 全120byte入力と3個の40byte LE整数の全単射を
  証明し、同じ入力の実reduceChallengeへ接続。商/剰余の単射を使い、d点に還元される
  入力の個数≤d・ceil(2^320/p)³を、巨大な全入力空間の列挙なしで導いた。
  全120byte入力を等確率と定義した有限uniform lawでは、固定した不同WHIR quadraticの
  一致確率≤2(ceil(2^320/p)/2^320)³。これは実Keccak/FSの分布や独立性を証明しない。
  外側MLEは3×32byte squeeze/異なる係数復元式なので、この内側定理とは区別する。

追加2モデルはrootが全文・実source・依存モデル・明示前提を対照し、採用名で直接buildした。
別担当の独立read-onlyレビューでも必須修正なし。内外のchallenge分布を混同しない説明を
WhirChallenge冒頭にも追加した。統合guardは全1250名の実定理/型/推移的公理、394 hashes、
18表1147語、7依存5601fileを検査してPASS。source inventoryは290file中29部分対応/261未対応。
guard33件・dependency34件・provision20件、空白差分とruntime無変更の検査もPASS。
全体の実装/PCS健全性は未完了であり、
40モデルfresh検査を、この47モデルのfresh再生成実績へ読み替えない。

## 第8継続更新（6642bd83以降）

5モデル・181定理を追加し、52モデル・1431名付き定理へ拡張した。

- **単一設定から全相へ**: checkBound済みの同じpから初期/前round opening/当round/終端を
  投影。別の形状仮定なしで、実行成功と明示3×1条件から全到達中間相・終端Contextの形状、
  同一stateの連続、fold分割、正確な件数・両EOFを導く。raw generatorはcanonical検査により保持。
  generic Paramsを受ける型であっても、source対応を3×1外へ拡大しない。
- **実indexed sortの一般証明**: midpoint pivotの実scan/swapからsentinel・partition分類を維持し、
  最初のswapがiを増やしjを減らすことから再帰幅の厳密縮小と全終了を証明。
  範囲外不変・区間内要素保存を使って全再帰の整列を導き、最後にだけ基準sortとの一致を結論する。
  大きなfuelを与えた例や外部sortedness仮定で一般性を代用しない。
- **実samplingでの全実行**: 実sort→indexed compaction→raw queryを接続し、count=0とsingleleafの
  早期分岐を保持。基準版とOption全体・全State・失敗が一致し、両sampling箇所を差替えた
  初期→中間→終端の全結果も一致する。単一checked設定入口とそのcontextShapeも接続。
- **実bitwise冪乗との接続**: 64bit mask、low-bit分岐、右shift、各mulmodのscalar loopを
  既存冪乗runnerへ同一化。全Fin64入力/Fin256指数で256fuel以内の終了と正確値、返却値<p<2^64、
  同じ範囲内transpose queryでの既存domainPoint一致を証明。任意generatorの位数は結論しない。

追加全候補の全文・source・依存モデルはrootと別担当で対照し、必須修正は残らなかった。
採用namespaceへの移行で生じた曖昧なimport名を完全修飾へ修正し、全model/root buildを再検査した。
統合guardは全1431名の実定理/型/推移的公理、399 reviewed hashes、18表1147語、
7依存5601fileの検査にPASS。source inventoryは290file中29部分対応/261未対応を維持。
guard33件・dependency34件・provision20件、CI YAML、空白差分とruntime無変更もPASS。
これらは手動モデル内の対応であり、source/compiler/Yul/EVM・メモリ・gasの形式的refinement、
immutable VK由来、真の回路多項式、ROM/PCS健全性の証明ではない。40モデルfresh検査とも区別する。

## 第9継続更新（4063db74以降）

6モデル・140定理を追加し、58モデル・1571名付き定理へ拡張した。

- **外側の実更新式**: evaluateRoundの係数和・具体inverse-two・逆向きHornerと、
  具体Ext3体上多項式の評価を同一化。端点和=claim、送信非定数係数数による次数上界、
  固定した不同claimの多項式の一致点数を証明した。coupled roundの両実更新・stateも保持する。
  log sourceの固定5係数loopには既存係数長preflightが必要で、任意長helperを代用しない。
- **外側challengeの区別**: 実3×32byte squeezeの同digest・連続counter・剰余を接続。
  両係数列吸収後のlog 0..2/gate 3..5を同じ更新多項式へつなぐ。明示uniform triple law下で
  固定多項式の一致確率≤d(ceil(2^256/p)/2^256)³。log 5/gate q+2は別々の上界で、
  実Hash/FSのuniform性・独立性・適応的fixednessや確率の積増幅は証明していない。
- **7familyの実次数**: 全14familyのzero-filter分岐を同じ具体制約/Hornerへ同一化した上で、
  IDs 0,1,2,3,5,6,7の実制約式と多項式評価の一致を証明した。両wire/constant列がaffineなとき
  次数は0,1,1,3,1,3,3以下。local constantも変数として保持し、Ext2の非剰余7とMDSの実定数・順序も保持。
  実設定検査/入力長から選択行寄与≤q+1、明示affine重み後≤q+2を導く。
  残7familyはsymbolic NONEとし、gate truth・全行和・認証endpoint・補間係数を仮定で埋めない。

追加6モデルはrootと別担当が全文・実source・依存モデル・仮定を対照した。
採用namespaceの直接buildと全統合guardはPASS。全1571名の実定理/型/推移的公理、
405 reviewed hashes、18表1147語、7依存5601fileを検査した。
source inventoryは290file中30部分対応/260未対応（coefficients.rsの部分対応を追加）。
guard33件・dependency34件・provision20件、CI YAML、空白差分とruntime無変更もPASS。
通常Lake検査と40モデルfresh検査の範囲は区別し、全実装/PCS健全性の完了とはしない。

## 第10継続更新（80b63289以降）

5モデル・145定理を追加し、63モデル・1716名付き定理へ拡張した。

- **形式Normの実次数**: denominatorの3座標もExt3係数のaffine多項式として扱い、
  formal adjugate≤2/norm≤3/helper≤4/logUp≤3、eq重み込み行・有限和≤5、PI≤2を導く。
  実Norm.wireStepの1寄与と評価一致、実lambda/eta乗算回数に一致する重みbuilderも証明。
  canonical Ext3非零norm定理をoff-cube形式座標へ流用しない。X^5−Xとなる次数5の代数例も確認。
  round_evaluation_actualは候補内行/PI式への一致で、mutable arraysからのendpoint抽出、
  全重みbuilder適用、PI suffix/column/prefix由来、補間/送信係数への完全接続ではない。
- **12familyまでのgate次数**: Exponentiation≤4、BaseSum≤固定base、Reducing2種≤2、
  RandomAccess≤bits+1を追加。高位bit順、全range積、可変alpha wireとclaimed-nextへのreset、
  再帰的scratch折畳み、trailing extra constantsの順序を保持。Boolean性・制約成立を仮定しない。
  実validateGate/全設定/両列長から実寄与≤q+1、明示affine重み後≤q+2へ接続する。
  nonlinear Poseidon4/Coset13はsymbolic NONEのまま。全14familyの実評価と次数証明を混同しない。
- **WHIRの実RLC**: 実geometricPowersと増順row dotを同じ具体Field多項式へ同一化。
  固定同長不同canonical vectorの一致点数≤n−1、実120byte/3×40LE還元に対する明示uniform lawの
  偏り込み上界を証明。count0/1は無消費、2以上は同じfour blocksとcounter+4。
  全claim/cross読取り後vector RLC→次stateのconstraint RLCという実相順序とサイズを保持する。
  Hash uniform性/2RLC独立性、rootからのvector抽出、適応的fixedness、nested全和の健全性は未証明。

追加全5モデルはrootが全文・source・依存・仮定を対照し、別担当の独立read-onlyレビューもPASS。
採用namespaceでの直接buildと全統合guardはPASS。全1716名の実定理/型/推移的公理、
410 reviewed hashes、18表1147語、7依存5601fileを検査した。
source inventoryは290file中30部分対応/260未対応を維持。
guard33件・dependency34件・provision20件、CI YAML、空白差分とruntime無変更もPASS。
実装・main・push・親pinは変更せず、全実装/PCS健全性を完了したとはしない。

## 第11継続更新（c2b3684a以降）

10モデル・322定理を追加し、73モデル・2038名付き定理へ拡張した。

- **全14familyのgate次数**: Poseidon4の実状態（swap/delta、各S-box前のfresh wire、partial最終roundの
  定数省略、circulant/sparse MDSとpartial-initial行列）を既存の実定数表で実行し、制約消失を仮定せず
  123制約・次数≤7を導く。Coset13はold-product評価→更新、中間claimed E/P制約→reset、clamped next
  count≤D−1から、実metadataのD≥2で次数≤D、4+4·intermediates制約。全14familyの実validateGate成功から
  symbolic term listの存在、GatesComplete.evaluateUnfilteredとの評価一致、family別上界
  0,1,1,3,7,1,3,3,4,base,2,2,bits+1,D、選択行寄与≤q+1、明示affine重み後≤q+2を証明する。
  12family dispatcherのNONEはこの全family wrapperには残らないが、gate truth・endpoint由来は別境界。
- **全行集約とBoolean suffix和**: 実combineRows全行が同じwires/constants/publicHash/alphaを使う順序付き
  集約を評価点の前に固定した1多項式へ接続し、validateRowsから次数q+1、完全なevalCombinedとの一致、
  実設定包絡q≤8から重み後≤10を導く。2s/2s+1の実読取り・同一challengeの実行可能補間・
  0..2^remaining−1の増順suffix和（remaining=0を含む）も同じ多項式で証明し、明示TableShape下では
  fallback読取りが起きない。Rustのslot-first/forward alphaとの可換、mutable grid転置、
  DenseMle endpoint由来、補間との接続は未証明。
- **外側補間の実Gauss消去と全域性**: coefficients.rsの自然node・増順冪・RHS列n・pivot交換なし・
  対角inverse・pivot..=n正規化・pivot行clone・書込み前factor捕捉・増順列減算・係数順抽出・空入力拒否を
  添字付きで模し、全accessがn×(n+1)内、nodeのu64適合を証明。証明専用ghost RHSで到達pivot=∏_{j<p}(p−j)を
  同定し、n≤pで全prefix/全n段が成功、実WhirFinal.inverseが実行され、非空入力で全域。degree<pで
  0..degreeのsampleから正確な係数と省略定数message、実Verifier.evaluateRoundがf(r)を返す。
  norm次数5とchecked gate q+2（q>0、q+2≤10）へ特殊化する。
- **添字付きDenseMle bind**: ext3.rsのbind loopで各iが2i/2i+1を書込み前に読み、増順に書き、最後に
  truncateすること、未書込suffix不変、Valid長=2^numVars、source numVars>0 guard、全bindMany実行と
  Packed.layer/foldの一致、affine Normへの橋を証明。constructor/from_base/usize/memory refinementは残る。
- **外側初期transcriptとadapter**: 16frameの実順序（circuit digest、raw PI、15語u64-LE metadata、
  bytes32-BE config digest、64/32byte識別子、preprocessed/witness root）、eta→beta/gamma後の
  norm-inverse root吸収→xi→lambda/rho/kappa→log tau→gate alpha→gate tauの正確なcounter、d≤13で
  全checked squeeze成功、識別子長guard、toInitial往復、40byte内部snapshotの無損失性を証明。
  OuterAdapterは実coupledRoundの6limb/counter、5claim+空第6cell→index domain→log/gate index列
  （既存constituentIndicesと全limb一致）、Verifier.roundStepと定義的に同じchecked loop、
  初期→coupled rounds→claim/index→packed fold→whirContextのOption prefixを接続し、
  envelope/shape/InputSizesからの成功と任意Hashでの非空例を持つ。malformed decodeをzero/defaultへ
  全域化しない。既存total Engineとの一致はCommitAgrees/SamplesAgree/初期/fold一致を明示した条件付き。
  PI hash再計算・config digest・VK/config意味論・Hash安全性・完全受理・PCS/WHIR接続は未証明。

追加10モデルは候補段階でrootと別担当の独立read-onlyレビューをPASS（OuterInterpolation/Totalと
OuterAdapterのsource対照レビューは本更新で実施し、必須修正なし）。
採用namespaceでの直接buildと全統合guardはPASS。全2038名の実定理/型/推移的公理、420 reviewed hashes、
18表1147語、7依存5601fileを検査した。
source inventoryは290file中31部分対応/259未対応（sumcheck/ext3.rsの部分対応を追加）。
guard33件・dependency34件・provision20件、CI YAML、空白差分とruntime無変更もPASS。
実装・main・親pinは変更せず、全実装/PCS健全性を完了したとはしない。

この73モデル・2038定理の状態について、40モデル時点と同じ一時runner
（`/private/tmp/wire3-fresh-source-runner.iXATos/fresh_audit.py`、SHA256
`9128f90b80becc4a43cae970567362887ce42da1970debad150e196fea0b46ed`）で
全非toolchain依存を空の新規出力先へsourceから再生成し、その出力だけで全定理を検査した。

- 1403非toolchainモジュール: audit/root 74、Mathlib 1091、Batteries 99、Aesop 108、
  Qq 11、ProofWidgets 18、ImportGraph 2。全て新規出力先へsourceから再生成。
- 全2038定理の`.thmInfo`、型、推移的公理をfresh出力だけで再検査。errorなし、
  許容は標準3公理のみ。経過1072.292秒。
- 開始/終了時に420 reviewed hashes、全source inventory、18表1147語、
  7依存5601file/64,398,270byteを照合し、一致。
- 保存先 `/private/tmp/wire3-fresh-source-build.g45kkble/`。receipt SHA256
  `d7404564544658ad1a1958ca2530eaa540e376976139bc6a90c2cf1b9bdcd437`、graph SHA256
  `8ef2043045aa89602b5e84ffbe2cbffeca9d4f49a8a46841f8cd455d3b4b2c89`。実行時のmanifest SHA256は
  `1522e8c7afe3e7e43706fd4a073b2e275ab32c474886c218c016243f9d8b5fbe`で、その後の差分は
  この記録の追記に伴うREPORT/manifest hashのみ。
- 11個のProofWidgets JSは固定既存bytes。Lean toolchain/core、Python/Git、固定metaprogram、
  非adversarialなFSは信頼境界に残る。この一時パスの保持を別環境での再現可能性の代用にせず、
  fresh PASSを実装refinementやPCS健全性の証明に読み替えない。

## 第12継続更新（daa945d1以降）

4モデル・137定理を追加し、77モデル・2175名付き定理へ拡張した。

- **Rust slot-first順序との可換**: gate_ext3.rs 543-608の各gate評価（filter零でも評価）、出力数ensure、
  accumulated[slot]+=filter·valueの固定幅buffer書込み、forward alpha powersによる還元を添字付きで模す。
  範囲外writeはsourceのpanicどおりnoneとし、totalizedなList.setをsource挙動と主張しない。
  validateRows/validateConfigurationから全writeが範囲内で、slot-first結果が実combineRows/evalCombinedと
  一致し、同じ固定多項式（≤q+1、affine重み後≤q+2）を持つことを証明する。
- **current_roundのgrid転置**: gate_ext3_v2.rs 105-134のnumVars>0 ensure、half=len/2、zero初期化の
  degree+1 cell、suffix外側・integer内側のmutable累積、(1−x)·t[2s]+x·t[2s+1]の実読取りを同じslot評価器で
  模し、iteration bodyがGateSuffixPolynomialのslice値、実行されたmutable loopがlockstep形、転置loopが
  整数ごとのsuffix優先和currentRoundValueに一致、Valid eq表でhalf=2^(numVars−1)、TableShape下で全cellが
  1多項式（≤q+2≤10）の値であることを証明。補間呼出し（136）とdegree構成検査（80-83）は別。
- **Norm/logUpのprover round**: 前回compile失敗だった候補を採用済みDenseMleIndexed/OuterInterpolationTotal
  上で修復し拡張。norm_logup.rsのline_value、evaluate_target_from_values（幅assertはnone、単一loopの2累積、
  xi·ZERO項保持）、round_sum_at（4 scratch vector、suffix loop、shift/mask PI loop、sum+xi·binding）、
  current_round（is_complete→Err、cache、Field64_3::from(0..=5)のsample、採用済み補間、coefficients[1..]）、
  bind（旧bound_variablesでprefix更新→+1→全表bindBuffer、num_vars=0はnone）、prover stateの
  Err/panic/Consistent/PrefixProvenanceを模す。Shape∧0<remaining下でroundSumAt=roundValue、6 sampleが
  次数5のroundPolynomialのsample、省略定数=coeff 0=verifierの半和復元、送信5係数を実Verifier.evaluateRoundが
  端点和claimからround値へ復元、全読取り境界、bind後のShape保持、prefix=booleanRowEq(bound point)保持を
  証明する。from_baseのbase→Ext3転置・eq_evals_ext3・重み由来、不正prover、round連鎖、PCSは未証明。

GateSlot 2候補は別担当の独立レビューで、totalizedなslot書込みがsourceより全域である点（必須）と
docstring/行番号を指摘され、修正のうえ新規GateSlotRoundとともに再レビューでPASS。
NormDenseRoundは修復後の独立レビューで、Shapeのみを前提とする6定理がremaining=0かつbindings非空で
Rustのpanic入力に到達しうる点を指摘され、0<remainingを前提に加えてPASS。
採用namespaceでの直接buildと全統合guardはPASS。全2175名の実定理/型/推移的公理、424 reviewed hashes、
18表1147語、7依存5601fileを検査した。source inventoryは290file中31部分対応/259未対応を維持。
guard33件・dependency34件・provision20件、CI YAML、空白差分とruntime無変更もPASS。
実装・main・親pinは変更せず、全実装/PCS健全性を完了したとはしない。

この77モデル・2175定理の状態についても、同じ一時runner（SHA256
`9128f90b80becc4a43cae970567362887ce42da1970debad150e196fea0b46ed`）で全非toolchain依存を
空の新規出力先へsourceから再生成し、その出力だけで全定理を検査した。

- 1407非toolchainモジュール: audit/root 78、Mathlib 1091、Batteries 99、Aesop 108、
  Qq 11、ProofWidgets 18、ImportGraph 2。全て新規出力先へsourceから再生成。
- 全2175定理の`.thmInfo`、型、推移的公理をfresh出力だけで再検査。errorなし、
  許容は標準3公理のみ。経過1439.640秒（wall clockは実行中のホストsleepを含むため参照しない）。
- 開始/終了時に424 reviewed hashes、全source inventory、18表1147語、
  7依存5601file/64,398,270byteを照合し、一致。
- 保存先 `/private/tmp/wire3-fresh-source-build.kmfety_9/`。receipt SHA256
  `3375f2b18dc8202529dc49c1339ccb78c615da78a80acddba15c1d409ad13714`、graph SHA256
  `2527787b924c4722988e0ad648814e3145e2a0b2968629fe4187f19d303979a7`。実行時のmanifest SHA256は
  `60b7a4a3879ea565bc3279dae8b80f8863ea3cbf6811e3b513a939a431ee933d`で、その後の差分は
  この記録の追記に伴うREPORT/manifest hashのみ。
- 信頼境界（固定ProofWidgets JS、Lean toolchain/core、Python/Git、固定metaprogram、
  非adversarialなFS）と、fresh PASSを実装refinement/PCS健全性に読み替えない点は前節と同じ。

## 第13継続更新（71338df0以降）

再起動で`/private/tmp`のworktree・候補・一時runner・fresh receiptが消失したため、
worktreeを`/Users/andropov/repos/intmax-plonky2-lean-wire3`へ再作成し、7依存を再provision、
全rootを再buildして通常guardがPASSすることを確認した（77モデル・2175定理・424 hashes）。
コミット`daa945d1`/`71338df0`はsubmoduleのobject storeに残っており内容は同一。

- **WHIR期待claimと全表評価**: OpenedClaimFoldは採用済みPacked.fold/packedFold/bindManyの
  row++index分割を同じ関数の結合則として証明し、pack_mlesの列優先padded tableの全表評価が
  各列row openingのpacked foldに等しいこと、Solidity cell/Rust slotの対応、native点=dense点の
  反転を接続する。5個のclaimed cellが各列のrow foldに等しいという明示的honest-prover仮定の下で
  expectedClaimsの各cellがpadded tableのWHIR点でのdense評価に一致し、OuterAdapter.execute成功時の
  contextにも適用される。第6 cellはnoneでlogNormInverseをgate点に結び付けない。
  不正cellで一致しない具体例を持ち、PCS binding/WHIR受理/FSは主張しない。
- **fresh source runnerの再実装と追跡**: 消失した一時runnerをREPORTの記録どおりに再実装し、
  `mle/audit/fresh-source-audit.py`（self-check29件）として追跡対象に加えた。独立レビューで
  既存`.lake/build`の混入経路・失敗の握り潰し・pre/post guard省略がないことを確認し、
  指摘の任意改善（`lean --deps`必須化、Lean panicの失敗化、comment内include_strの除外、
  audit dirの`__file__`由来化）を採用した。出力先は再起動で消える`/private/tmp`を拒否する。

再実装runnerの採用前版（SHA256 `0b7e3ad8b2b3f51bf2224dbf0e6d507fb73e5292940bf82ae5b56ca2a2bb0493`）で
コミット`71338df0`の77モデル・2175定理を再検査し、PASS（763.171秒）。
1407非toolchainモジュール（audit/root 78、Mathlib 1091、Batteries 99、Aesop 108、Qq 11、
ProofWidgets 18、ImportGraph 2）をsourceから再生成し、公理分布は消失した旧runnerの記録
（807/689/428/248/2/1）と一致。実行時manifest SHA256 `9bca4717c0b7633cf18a325f71889b5b7ede95fefeacf129acc1ab018efe08ab`、
receipt `fd517c5fedbb09692667fa223cdb279bcdb2556134050f329637d3ca147de55e`、graph
`fa644927bfc7048f06cf083a1a0cc999a35cad3d80b5c4ab45a3a3b00944f1da`、保存先
`/Users/andropov/.local/share/wire3-fresh-source/wire3-fresh-source-build.g6r0xrb1/`。
OpenedClaimFold追加後の78モデル・2214定理と追跡版runnerでの再実行は次の記録に持ち越す。

OpenedClaimFoldは別担当の独立read-onlyレビューで必須修正なし。採用namespaceでの直接buildと
全統合guardはPASS。全2214名の実定理/型/推移的公理、427 reviewed hashes（runner 2fileを追加）、
18表1147語、7依存5601fileを検査した。source inventoryは290file中31部分対応/259未対応を維持。
guard33件・dependency34件・provision20件・fresh runner self-check29件、CI YAML、空白差分と
runtime無変更もPASS。実装・main・親pinは変更せず、全実装/PCS健全性を完了したとはしない。

## 第14継続更新（9e960c70以降）

追跡版runner（SHA256 `56237ada14b4a29015199a6b3c9566d72bd3a175921cecb813f9f821fc4c744a`）でコミット`9e960c70`の
78モデル・2214定理を再検査し、PASS（758.152秒）。1408非toolchainモジュール（audit/root 79、Mathlib 1091、
Batteries 99、Aesop 108、Qq 11、ProofWidgets 18、ImportGraph 2）をsourceから再生成し、全定理の公理は
標準3公理の部分集合（818/703/436/254/2/1）。実行時manifest SHA256は当該コミットと同一の
`f74472f78c43f5facdb42e474bd380055096c5d5599fc4430131ea0d592ac8ec`、receipt
`5542843f1d9ca96d2542a4077cd1eb877b628cd7162cd4840d70567f9792a2eb`、graph
`ce4e6ffd93eab565895f80cfa3942c1dccbb8b17e2fa86a5fcd548aa02f62d3f`、保存先
`/Users/andropov/.local/share/wire3-fresh-source/wire3-fresh-source-build.jvklnsxi/`。

- **gate proverの終端接続**: GateTerminalBindingはbind_challenge（degree ensure→eq/全wire/全constantの
  採用済みbind→rounds/point push）とinto_proof_and_pointを模し、ProverShape（構成子ensure 70-79）から
  全変数bind後の各列が単一cellで採用済みpacked foldに等しいこと、最終roundのeq·aggregateが
  GatesComplete.evalCombinedに一致し、eq cell=eqEvaluation(gateTau,gatePoint)・claimed cell=prover cell・
  alpha=gateAlphaの明示仮定下でVerifier.gateTerminalとIntegratedの受理式に一致することを証明。
  Integrated.verify成功から必要なmetadata検査を導くhonest prover限定定理も持つ。
  eq表のtau由来、係数補間、transcript、WHIR/PCSは未証明。
- **norm proverの終端接続**: NormTerminalBindingは全変数bind後の表をNormTerminalInput（constants++sigma、
  routed wire cells++非routed tail、identity/sigma helper、PI値）へ明示的に対応させ、proverのtargetValueと
  verifier側Norm.evaluate/checkedEvaluate/Engine.logTerminalの項ごとの一致（lambda running product、eta冪、
  PI eq_row、kappa/xi重み、helper半分の順序を対照）、各bound cell=採用済みpacked fold、bind成功と
  全列単一cell、最終roundのroundValue=bind後表のterminal target、honest proverのend-to-end定理を証明。
  独立レビューでwitnessがrouted cellのみでnumWires=numRoutedに限定されていた点（必須）を指摘され、
  非routed tailを加えて全定理を保ったまま修正、numWires>numRoutedの具体例も追加した。
  eq/subgroup cellのtau由来、lambda/eta/wire-map/kIsの由来、shapeValid、PCS claimed値=prover cellは
  可視の仮定。
- **honest proverのclaim連鎖**: OuterClaimChainは採用済みVerifier.roundStep/runRoundsをproverの
  currentRound→bindChallengeと同じcommit引数で駆動し、各round後のlogClaim=直前表のroundValue、
  次表のf'(0)+f'(1)=前表のroundValue(r)（NormDenseRoundが残していたround間恒等式、2≤remainingと
  全読取り境界を証明）、初期零claim⇔端点和零、intoProofAndPoint=verifierが消費したmessage/challenge、
  derivedRounds/OuterAdapter.runCheckedとの一致、n=1の具体例を証明。gate laneは明示仮定で
  parameteriseし偽のgate proverを置かない。任意messageの健全性・FSは主張しない。

追加3モデルは別担当の独立read-onlyレビューをPASS（GateTerminalBindingは引用行番号の修正のみ、
NormTerminalBindingは上記必須修正後の再レビュー、OuterClaimChainは必須修正なし）。
採用namespaceでの直接buildと全統合guardはPASS。全2402名の実定理/型/推移的公理、430 reviewed hashes、
18表1147語、7依存5601fileを検査した。source inventoryは290file中31部分対応/259未対応を維持。
guard33件・dependency34件・provision20件・fresh runner self-check29件、CI YAML、空白差分と
runtime無変更もPASS。実装・main・親pinは変更せず、全実装/PCS健全性を完了したとはしない。

## 第15継続更新（f9ada18b以降）

追跡版runnerでコミット`f9ada18b`の81モデル・2402定理を再検査し、PASS（771.879秒）。1411非toolchain
モジュール（audit/root 82、Mathlib 1091、Batteries 99、Aesop 108、Qq 11、ProofWidgets 18、ImportGraph 2）を
sourceから再生成し、公理分布は919/729/482/269/2/1。実行時manifest SHA256は当該コミットと同一の
`5b772df15b2273893cde7e77841ebc41059d6b378ac68b5e6c80301fc4d3f113`、receipt
`39367c53af192fd1bcc648a4aeb1ca44a50194cbfad499e4a057f1ff0a0b01f7`、graph
`0ca3fba58ae89cd0a3526cb0933a0ad70bcf2e8e30c07ebeae1d6a68071e848f`、保存先
`/Users/andropov/.local/share/wire3-fresh-source/wire3-fresh-source-build.vvt12tjv/`。

- **終端連鎖の統合**: IntegratedTerminalChainは採用済み4モジュールを再実装せずにVerifier.verify/
  Integrated.verifyへ接続する。名前付き仮定構造（honest norm prover、norm terminal provenance、
  gate chain仮定、honest openings）の下でhonest proverのlogTerminal=derivedRoundsの最終logClaim、
  gateTerminal=最終gateClaim、5 WHIR期待claim=padded tableのdense評価・第6はnoneを導き、
  verify_success_checksの逆向き補題でVerifier.verify/Integrated.verifyの受理を示す。残る前提は
  ObservationOnly（chain/config hash/envelope/deployment/shape/4長さ/verifyWhir/7 challenge/normShape）
  として列挙する。Rust順（WHIR→norm）とSolidity/Lean順の受理同値をProp水準で証明。
  採用済みInteger例（exampleEngine/Config/Proof）上で全仮定構造を実際のhonest prover実行から充足し、
  既存のpositive経路を接続経由で再導出した。gridはgate running claimの端点和一致を含意するhonest
  prover仮定で、eq/subgroup cellのtau由来・claimed値=prover cell・PCS/WHIR健全性は仮定のまま。

追加1モデルは別担当の独立read-onlyレビューで必須修正なし（gridの含意をdocstringに追記）。
採用namespaceでの直接buildと全統合guardはPASS。全2445名の実定理/型/推移的公理、431 reviewed hashes、
18表1147語、7依存5601fileを検査した。source inventoryは290file中31部分対応/259未対応を維持。
guard33件・dependency34件・provision20件・fresh runner self-check29件、CI YAML、空白差分と
runtime無変更もPASS。実装・main・親pinは変更せず、全実装/PCS健全性を完了したとはしない。

## 第16継続更新（03e69a20以降）

追跡版runnerでコミット`03e69a20`の82モデル・2445定理を再検査し、PASS（750.355秒）。1412非toolchain
モジュール（audit/root 83、Mathlib 1091、Batteries 99、Aesop 108、Qq 11、ProofWidgets 18、ImportGraph 2）を
sourceから再生成し、公理分布は936/735/490/281/2/1。実行時manifest SHA256は当該コミットと同一の
`ccafd4b71c310c4f7491662044aa4fb073da8df9048517dc79b6341554bd4fa5`、receipt
`81e79f8c8a8e3dfe3c959e6340bf5b233bb8fb5581cd7172ced0adac2592c548`、graph
`501e10c44cc9dfe8ad9e941a6545b2c9286e597a7bc2c7d1ceb8f9a5c2c52d71`、保存先
`/Users/andropov/.local/share/wire3-fresh-source/wire3-fresh-source-build.jso0ljtj/`。

- **eq/subgroup表の由来**: EqTableProvenanceは実eq表builderのloop nest（tau順の外側loop、index内側loop、
  左側累積、(i>>j)&1による因子選択）を模し、各entryが採用済みNorm.booleanRowEqであること、
  採用済みbindBufferの2i/2i+1 pairingから低位bitが先にbindされることを証明する。全点bind後の
  eq cellはNorm.eqEvaluation(tau,point)に等しい。subgroup列は等比列で、verifierはこれをfoldせず
  (1-r_j)+r_j·g^(2^j)の積を取るため、その積が全bind後のcell/Packed.foldに等しいという正確な関係を
  証明した。これによりNormTerminalBinding/GateTerminalBindingの主要定理から、これまで可視の仮定だった
  eq cell/subgroup cellの由来を取り除いた系（honest prover版を含む）を与える。
  VKのsubgroup_gen_powersが表の生成元の反復二乗であることは、採用モデルにtwo_adic_subgroupと
  VK生成元導出のモデルがないため述語として書くのみで解消せず、可視の仮定として残した。

追加1モデルは別担当の独立read-onlyレビューでLean側に欠陥なし。指摘された文書の必須修正2件
（3つのeq builderはbyte一致ではなく同一loop nest／eq_poly.rsは旧経路、subgroup仮定が解消できない
本当の理由）と、系の結論から落ちていたPrefixAt連言の復元を適用した。
採用namespaceでの直接buildと全統合guardはPASS。全2500名の実定理/型/推移的公理、432 reviewed hashes、
18表1147語、7依存5601fileを検査した。source inventoryは290file中31部分対応/259未対応を維持。
guard33件・dependency34件・provision20件・fresh runner self-check29件、CI YAML、空白差分と
runtime無変更もPASS。実装・main・親pinは変更せず、全実装/PCS健全性を完了したとはしない。

## 第17継続更新（c3719e61以降）

追跡版runnerでコミット`c3719e61`の83モデル・2500定理を再検査し、PASS（727.034秒）。1413非toolchain
モジュールをsourceから再生成し、公理分布は971/744/500/282/2/1。実行時manifest SHA256は当該コミットと
同一の`cc7b67fbcf0b2969aa2099146ee36acb9627e0e4db33797b8f31d489b8823ea5`、receipt
`05760f64b72b2529ef93bea6b4df3a45cbe19fbee45dea19b0a1255707bae119`、graph
`24ced6ff907622b015cc3dee2b1ccc175a05e5555090da8c37696d125f4c83ba`、保存先
`/Users/andropov/.local/share/wire3-fresh-source/wire3-fresh-source-build.5imen0_t/`。

- **public input hashの具体化**: PublicInputHashBindingは採用済みPoseidon置換の上に実hash-no-pad
  スポンジを構築し、absorb順・overwrite mode・chunk数・末尾短chunk・4要素digest・空入力の
  置換0回を実装と対照する。Ext3モデル上で全30roundにわたりc1=c2=0が保たれること、
  c0読出しが無損失であることを層ごとに証明した（採用済みzeroInputWitnessとの一致はrfl、
  外部test vectorのzero入力行も再現）。raw public inputsのpreflight（256語上限、各語<p、
  拒否時に無言のreductionをしない）も新たに模した。これによりgate terminal定理から
  hash長仮定を除き、GateChainHypothesesのhashLengthフィールドを埋める系を与える。
  Solidity/Rustの差（Rustは型でcanonicalなため範囲検査なし、256語上限はSolidityのみ、
  hashはcalldataを読むため`PoseidonGate.sol:77`が外部library入口を守り、verify内では
  多重防御）はheaderに明記した。

追加1モデルは別担当の独立read-onlyレビューでLean側に欠陥なし。指摘された必須修正2件
（calldata読取りの正確な言い換え、採用済みLean/Solidityの引用行番号）を適用した。
採用namespaceでの直接buildと全統合guardはPASS。全2579名の実定理/型/推移的公理、433 reviewed hashes、
18表1147語、7依存5601fileを検査した。source inventoryは290file中31部分対応/259未対応を維持。
guard33件・dependency34件・provision20件・fresh runner self-check29件、CI YAML、空白差分と
runtime無変更もPASS。実装・main・親pinは変更せず、全実装/PCS健全性を完了したとはしない。

### 第17継続更新の追補（3d5880ed以降）

- **transcript由来の解消**: TranscriptProvenanceは単一前提DerivedInitial（engineの初期transcriptが
  実導出そのもの。採用済みOuterAdapterが既に取る仮定と同一でwithInitialならrfl）から、
  challengesFromInitialが導出7 challengeを返すこと、log/gate tau列とgate alphaが導出値であること、
  各challengeがsourceのdigest/counter位置に載ることを証明する。ObservationOnlyは12項から9項へ、
  NormTerminalProvenance/GateChainHypotheses/NormColumnProvenanceも各1項減る。
  hashの性質は一切使わないため、これは順序と受け渡しの同一性でありFiat-Shamir健全性ではない。
  独立レビューの必須修正2件（gateのhptは解消ではなく同値な言い換えであること、
  honest prover表示は6件でなく5件）を適用した。DerivedInitial自体とprover側challenges一致は残る。

### 第17継続更新の追補その2（5dd688a6以降）

追跡版runnerでコミット`5dd688a6`の85モデル・2617定理を再検査しPASS（873.732秒、1415モジュール、
manifest `ce2c6d30aa01e8b12716bd0eee1ad4e7940a4f2b7d08d637fe2848104683a802`、receipt
`ef28bde84e33e38daafa476a610f7f1da76741b75300ae807bada83787657f40`）。

- **VK生成元由来の解消**: VkSubgroupProvenanceはplonky2のtwo_adic_subgroupとVK生成元導出を模し、
  固定two-adic生成元の位数2^32を核が実際に評価した冪証明書から確定したうえで、
  verifier_v2.rs 130-147の再計算検査が「VKのpowersが導出生成元の反復二乗である」ことと
  同値であることを両方向で証明する。これにより、以前のレビューが「採用モデルでは解消できない」と
  記録していたSubgroupPowersProvenanceが仮定から定理になった。採用済みGoldilocksDomainの生成元7は
  plonky2のtwo-adic生成元とは別値であるため、位数はここで独立に証明している。
  残る仮定はdegreeBitsと変数幅の一致、prover側subgroup列の由来の2つで、いずれも可視フィールド。
  独立レビューは必須修正なし。指摘に従い、n_log>32でsourceがpanicする一方Leanの切詰め減算は
  受理するためiffが忠実なのはdegreeBits≤32（envelopeがdegreeBits≤13を強制するため到達不能）である旨と、
  引用行番号を追記した。

### 第17継続更新の追補その3（1c2bc096以降）

追跡版runnerでコミット`1c2bc096`の86モデル・2688定理を再検査しPASS（858.808秒、1416モジュール、
manifest `d89e078087f53f5d3b8c6c3bec9b70cc5f485585b9f3fe304c2b86b85ed9a839`、receipt
`5d41b90d3490e861906f854f552b6183a544fef60884965523faf04a4a8fb3c8`）。

- **明示的暗号仮定下の条件付き健全性**: ConditionalSoundnessは18個の仮定を可視フィールドとして
  列挙し、Integrated.verifyが受理しlog laneのbad eventが起きていなければ、抽出した表の
  endpointSumが0であることを導く。これはIntegratedTerminalChainがzeroSumとして仮定していた命題で、
  どのフィールドもendpointSumを値として言及しないことを確認したうえで循環なく導出している。
  定理の形は「endpointSum=0、またはどこかのroundでdrawn challengeがbad setに入った」であり、
  これはsumcheck健全性の正しい形である。bad set濃度上界195·⌈2^256/p⌉³は、受理から導いた
  degreeBits≤13とquotientDegree+2≤10から195を出しており、仮定ではない。

  **この定理が証明していないこと**を明記する。gate laneは証明していない。初稿はgate側の
  cube和も結論していたが、gateTruths:=[]で任意の受理proofに対し仮定が成立してしまう退化した
  連言であることが敵対的レビューで判明したため、採用済みgate proverに係数補間・Boolean cube和・
  round連鎖・eq表由来のいずれも無いことを確認したうえで削除した。
  195·(⌈2^256/p⌉/2^256)³≒2^-184は外側sumcheckの一致事象のみを数えた値であり、
  支配項であるWHIR/Merkleを含まない。設計点は約100 bitであるから、この数値を系の
  健全性誤差として引用すると約80 bit過大になる。failureは自由な有理数で上界しか与えられておらず、
  実確率との橋渡しはどのフィールドも供給しない。第1連言と第4連言は合成されておらず、
  実行に関する確率空間はこのファイルに存在しない。Assumptions全体の充足可能性も示していない。
  抽出とcommitmentの接合（terminalのclaimed値=prover cell）は仮定のままである。

  2回の敵対的独立レビューを通した。初回は上記の退化connective、未使用の2仮定と自由変数による
  空虚化、scalarに留まる最終round橋、充足可能性の誇張、数値の誤引用リスクを指摘し、
  すべて修正（gate連言と2仮定を削除、最終round橋を構造化して値等式を導出、
  §12を部分的非空虚性検査に改題、警告を3箇所へ）。再レビューで修正の実効性を確認し、
  残る4件の誇張表現（failureが実確率を上から抑えると読める記述など）も修正した。

### 第17継続更新の追補その4（746ed942以降）

追跡版runnerでコミット`746ed942`の87モデル・2742定理を再検査しPASS（801.944秒、1417モジュール、
manifest `bbc6dd9d869a7cb4ec7eba545f3dcac20a9a1e5e0acbfa4a761033a62a82febe`、receipt
`6b2b46bae6e8bffe40a5c4417ad0deb151d1104033d0b09d9b288c46b01a8b97`）。

- **gate側のround模型**: GateDenseRoundはNormDenseRoundのgate版として、current_roundを採用済み
  gridと採用済み補間で端まで模し（再実装なし）、送信messageの長さがbind_challengeの再検査値と
  一致すること、省略された定数係数がverifierの半和復元と一致すること、実Verifier.evaluateRoundが
  round値を再現することを証明する。Consistent不変量とround間の端点恒等式、および単一indexで
  定義したBoolean cube和と第1roundでの端点和一致も証明した。多round帰納は未実施であり、
  cube和=0は主張しない（それは回路truthである）。これによりcapstoneが挙げたgate障害4つのうち
  3つが解消した。残る5点（多round帰納、向き、抽出/transcript、terminal橋、重み付き和と
  各制約の区別）はSCOPEに列挙した。
- **openingのbinding**: OpeningBindingは同root/index/depthの2つの受理openingが同じraw row・
  復号値・dotを返すことを、実行から計算した有限listに対するhashの単射性のみへ還元する。
  この述語は自由変数ではなく呼出しの結果から計算され、Merkle cursorも採用済み定理で固定される。
  仮定17は双条件で書き換わるが、残余はfold水準であって列の同定より弱い。
  さらに、限界そのものを定理として証明した。不透明engineのWHIR検査は任意のcontextを受理し、
  opening関係は3つのrootを差し替えても成立する。したがってbindingから抽出は導けない。

追加2モデルはいずれも敵対的独立レビューを通した。GateDenseRoundは必須修正なし（文書2件を適用）、
OpeningBindingは必須修正2件（fold水準の残余を列の同定と書いていた点、双条件の数学的内容を
過大に述べていた点）を適用し、復号rowとp.usedの未接続という未記載の欠落も明記した。
採用namespaceでの直接buildと全統合guardはPASS。全2834名の実定理/型/推移的公理、
438 reviewed hashes、18表1147語、7依存5601fileを検査した。

### 第17継続更新の追補その5（118caab2以降）

追跡版runnerでコミット`118caab2`の89モデル・2834定理を再検査しPASS（1427.517秒、1419モジュール、
manifest `17a71c4a1c340b182a88bd184c5f8dc5f862d9944131d6e4c5ef28554aa23ea4`、receipt
`63cb1cc80dd9b9d25ee32b3429e9c5d66724579c1886940d7362f5366ee42ec5`）。

- **意味論的段階**: ZeroCheckSemanticsは採用済みeqによる多重線形拡張がcube上でgを補間すること、
  非零値があれば拡張が恒等的に零でないこと、零点の密度が n/|F| 以下であること
  （Schwartz-Zippel、総次数≤n、帰納法は仮定段なしで完遂、n=0の端も証明）を示す。
  bad set外のtauに対しGateDenseRoundの各行値が0になる系を、採用済み導出tauと
  EqTableProvenanceが解消する eq 仮定のもとで与える。
  採用済みbadSetsとは合成しない（単一challenge対n組）。
- **gate laneの連鎖と向きの転換**: GateClaimChainは実Verifier.roundStepでgate laneを多round連鎖し、
  gate row数・hash長・validateConfigurationを受理から導出してterminal橋を渡し、
  受理とgate lane bad eventなしから抽出表のcube和=0を導く。採用済みbad event機構を再利用し
  二重定義を作らない。gate lane固有の上界(q+2)·degreeBitsも再具体化した
  （ConditionalSoundnessの195はこのlaneには適用されないことを明記）。
  以前gate連言を退化させた`gateTruths := []`は、truth chainが実行に束縛されるため充足不能である
  ことを定理で示した。

  **正直に記録すべき限定**: この定理には敵対的供給者への棄却力がまだない。
  仮定はeq表の1つの線形汎関数しか固定せず、cube重みの行和は独立なので、正しいbound cellを
  持ちつつ行和0のeq表を選べる。同種の退化として`numGateConstraints=0`があり
  （envelopeは下限を課さず、採用済みexample configがこれを設定している）、これは
  レビューが発見し定理として証明したうえで可視の仮定4で除外した。網羅ではなく、
  selector filterを全て零化する経路も残る。これらはheaderと本文に明記した。

追加2モデルはいずれも敵対的独立レビューを通した。ZeroCheckSemanticsは必須修正なし（文書3件を適用、
badSetsと合成するという誤りの訂正を含む）。GateClaimChainは必須修正4件
（過大な表現の削除、上界の再具体化、退化の証明と可視の仮定による除外、棄却力なしの明記）を適用し、
検証レビューで再確認したうえ、退化が2つだけと読める記述も訂正した。
このとき採用済みConditionalSoundnessのgate lane記述が陳腐化していたためコメントのみ更新した。
採用namespaceでの直接buildと全統合guardはPASS。全2923名の実定理/型/推移的公理、
440 reviewed hashes、18表1147語、7依存5601fileを検査した。

### 第17継続更新の追補その6（c89d8ea7以降）

追跡版runnerでコミット`c89d8ea7`の91モデル・2923定理を再検査しPASS（1129.262秒、1421モジュール、
manifest `2470b854fbca0265d5e3acea62c4cd915f4bb6cdf77aec7c68253ea4c28a5d06`、receipt
`bbcebcc6d799c6b14e1fac5184299e46855dbf9a1f8db136b9b91d19c86ec97f`）。

「健全性に問題があるシナリオを特定し、そうでないと示す過程で健全性を証明する」方針で2モジュールを追加した。

- **攻撃シナリオの列挙と棄却力**: GateRejectionPowerは攻撃シナリオを定義として列挙し、それぞれが
  実在することを定理で示す。特にeq列をゼロにすると、任意の表に対して採用済みの結論が成立し、かつ
  各行のgateValueは不変であることを証明した（旧定理が何も棄却していなかったことの形式的証明）。
  そのうえで採用済みeqの単位分解（cube上の行和が恒等的に1）を証明し、eq列を全行で固定すれば
  行和ゼロのeq表は存在しえないことを導く。強化仮定のもとで各行の集約が0であることを
  ZeroCheckSemanticsと合成して示し、対偶により棄却力があることを述べ、旧仮定が受理していた
  偽造状態2つを新仮定が棄却する具体例を与えた。
- **alphaのzero-check**: AlphaZeroCheckは行の集約をalphaの多項式として扱い、係数が採用済みslot値
  そのものであることを同定する（次数上界だけではない）。根の個数上界をenvelope由来の
  numGateConstraints≤123から≤122として導き、bad set外のalphaで各slot値が0、filterが非零のgateは
  制約自体が0であることを示す。tauとalphaの両zero-checkの合成を、採用済みtranscriptのalphaとtau
  （alphaはgate tauより前のcounterで引かれる）に対して証明した。

  **未解決として明記した攻撃面**: selectorの部分的零化（全零化はactiveFilterで除外されるが、
  重要な行だけ零化して他所にgateを残す攻撃は残る。constants列の由来、すなわち抽出接合の問題）。
  tauは両モジュールで自由変数でありtranscriptに束縛されていないため、表を固定した後にtauを
  選ぶ適応的攻撃はhgood仮定でしか排除されない。確率は未計算で、alphaのbad setは行ごとなので
  cube全体には2^n行のunion boundが要る。

追加2モジュールはいずれも敵対的独立レビューを通した。AlphaZeroCheckは必須修正なし（推奨4件を適用）。
GateRejectionPowerは必須修正1件（tauを「引かれた」と書いていたが自由変数である）と、
selector偽造の範囲の訂正（例示した状態はactiveFilterで除外され、残るのは部分的零化）を適用した。
採用時に、定理名の`?`と末尾プライムが採用済みguardの識別子正規表現と衝突することを発見し、
2件を改名した（guardは`get?_append_cons`を`get`と誤読し、`x'`と`x`を重複と誤認する）。
採用namespaceでの直接buildと全統合guardはPASS。全3021名の実定理/型/推移的公理、
442 reviewed hashes、18表1147語、7依存5601fileを検査した。

## 第18継続更新（f5424f98以降）

追跡版runnerでコミット`f5424f98`の93モデル・3021定理を再検査しPASS（1279.663秒、1423モジュール、
manifest `83a68fcedb8deb2ad9cb2c4568c5525defeb649b41b2b60fe7d55ccb32cebdf5`、receipt
`3a48e1165b0466016fe20a3cbadc0ac60618e9a6e6f5172579df67f198f8ab2a`、graph
`e43331323b2d7e39d37198ba817c5663fa8dc489117bfa98947d816a64d16114`）。

本更新からloop方式に移行した。計画と結果検証をFable 5.1、実装をOpus 5が担当し、
各候補は採用前に独立の敵対的レビューを通す。この回は「表を固定した後にchallengeを選ぶ」
余地と、確率的読みへの橋の2点を対象にした。

- **challengeのtranscript束縛**: GateDerivedRejectionは棄却定理と合成定理をtranscript導出の
  gate tau/alphaで再述し、bound cell仮定を全表eq由来と構造的binding fieldから導いて、
  自由なchallenge値を含まない9フィールドの縮約仮定集合を与える。§2は例外で自由alphaを保持する。
  残るchallenge側の仮定は、導出tau/alphaに関する2つのhgoodと、sumcheck roundの採用済み
  BadEventFreeの3つである。
- **適応性の決定論的半分**: CommitmentOrderはgate alpha/tauのsqueeze前のprefixが22 frameで
  採用済みrelationStateと一致し、3つのrootが13/15/19番目、最終rootとsqueezeの間は固定domain tag
  2つだけであることを実装と照合して証明する。gateのbad setはeq列に依存せず、表を変えつつ
  prefix digestを保つには具体的なtranscript衝突が要る（衝突耐性は仮定しない）。
  確率的半分は定数hashに対する反例で否定され、順序論法では得られないhash仮定として残る。
- **union bound**: ChallengeUnionBoundはtauのbad setをn個の独立digest tripleの積事象へ、
  alphaの行ごとbad setを2^n行のunionへ持ち上げ、外側sumcheck項と合わせて3つの質量の和を
  上界化する。envelope極値で等式に展開し、有理数の厳密計算で≤2^-172を証明した。
  **この数値はWHIR/Merkle項を含まず系の健全性誤差ではない**。独立検算で総和は2^-172.07、
  余裕は約0.07 bitでenvelopeぎりぎりである。3項は別々の標本空間上の質量の和であり、
  結合事象は形式化していない。積事象と行unionのパラメータは受理実行の表に束縛されていない。

追加3モデルはいずれもFable側の敵対的検証を通した。GateDerivedRejectionは文言の必須修正3件
（§2の自由alpha、「challenge仮定は2つだけ」の過大主張、binding fieldがchallenge列の等式を
含む点）、CommitmentOrderは引き締め2件、ChallengeUnionBoundは必須修正3件（「disjunctionの質量」
という誤った表現、自由パラメータの明示、余裕の定量化）を適用した。
採用namespaceでの直接buildと全統合guardはPASS。全3129名の実定理/型/推移的公理、
445 reviewed hashes、18表1147語、7依存5601fileを検査した。

## 第19継続更新（d937d15f以降）

追跡版runnerでコミット`d937d15f`の96モデル・3129定理を再検査しPASS（1483.923秒、1426モジュール、
manifest `29d29f182cbcda02a269ec76b782b0252aac9744c7b67211563f9d527c7bfb06`、receipt
`0af02e6adc74c31dc52405ac55438683bc354b2010e595277abda0f2bbb5bc71`、graph
`74a4b58940642560ced5a047d92f700d61ee3e440bfa73a46272d330a02ccac7`）。

loop方式の2回目。前回残した「union boundの自由パラメータ」「selector部分零化の由来」
「3項が別々の標本空間上にある」の3点を対象にした。

- **受理実行への束縛**: AttachedUnionBoundはChallengeUnionBoundの自由パラメータ（n、g、係数族）を
  受理実行に束縛する。tau arityはdegreeBitsから導出、行値はgateValue、係数族は受理由来の
  slotCoefficients、制約数≤123は受理から導出し、attached tupleがtranscriptの導出tau列そのもので
  あること（attached_tau_tuple_ofFn）を示す。combinedBoundは4引数すべてで単調で
  （⌈2^256/p⌉·p≥2^256）、envelope下で≤combinedBound 13 8 13 123≤2^-172。attached_seamが
  計数上界と「導出tau/alphaがattached bad set外なら全行で選択gateの制約が零」を1定理に結合する。
  **数値はWHIR/Merkle項を含まず系の健全性誤差ではない**。余裕約0.07 bitは制約数128まで持ち、
  129で初めて破れる（SCOPEの旧記述「125」は誤りで訂正した。envelopeは123で頭打ち）。
- **selector部分零化の由来鎖**: ConstantsProvenanceはselector値←供給constants列←導出gate点での
  bound cell←gatePreprocessed claim←committed列のbound cell←preprocessed root下のopening←
  deployment pinの6リンクを、pin（Verifier.shape、verifier_v2.rs 184-187、MleVerifierV2.sol 563）を
  起点に証明する。攻撃定理partial_zeroing_forces_one_of_threeは、供給列とpinned列のbound cellが
  導出gate点で異なれば、root不一致（pinで閉鎖）・抽出接合CellsMatchClaimsの破れ・opening関係
  OpensCommittedTableの破れのいずれかが必ず起きることを示し、具体的偽造例で旧仮定は検知せず
  新鎖が接合で捕捉することを示す。残余は「bound cell一致は列同定より弱い」（反例つき）、
  engine不透明性R1、opening関係R2、root→列写像R3で、いずれも可視仮定のまま。導出gate点で
  不可視な列改変を除外するにはsumcheck challengeによるzero-checkが要り、未着手である。
- **結合事象の形式化**: JointChallengeSpaceは3つの質量を1つの標本空間に載せる。squeeze schedule
  （gate alpha、gate tau×d、外側log/gate round×d、計3d+1座標）で添字づけた`Draw d → DigestTriple`上の
  一様計数測度を定義し、座標事象・tau積事象の質量を計数で証明、真のdisjunction事象の質量
  ≤combinedBound（外側項は両laneの2d座標を被覆）を証明した。2^-173≤bound 13 8 13 123≤2^-172。
  seam `DrawEncodesRun`はhash仮定ではなく座標符号化の主張で、全hash・全受理実行で可住であることを
  補題として示す。Fiat–Shamir半分(B)「符号化drawがjointProbability分布」は未形式化のままで、
  合成定理composed_gate_constraints_vanish_on_the_joint_spaceは暗号仮定を一切持たない。外側bad setは
  実現challenge/messageに相対的でprefix定数ではない。**数値はWHIR/Merkle項を含まず系の健全性誤差ではない**。

追加3モデルはいずれもFable側の敵対的検証を通した。AttachedUnionBoundは必須修正（「125で破れる」
の誤記→129、SCOPEの同記述も訂正）、ConstantsProvenanceは文言3件（残余の列挙、旧定理の
「真」→「結論が成立」、verifyCallもshapeを検査）、JointChallengeSpaceは必須修正3件（当初
`TranscriptIsUniform`と名付けた seam がhash仮定ではなく全hashで可住である点、外側bad setを
「prefix定数」とした誤り、合成定理の確率的読みの過大表現）と注記5件（合成定理の改名、log lane
比較値の束縛、余裕表現、schedule写像の性格、maxHeartbeats 2箇所）を適用した。健全性欠陥は
3モデルとも検出されなかった。
採用namespaceでの直接buildと全統合guardはPASS。全3268名の実定理/型/推移的公理、
448 reviewed hashes、18表1147語、7依存5601fileを検査した。

## 次工程

[SCOPE.md](SCOPE.md)の未完了一覧を順に進める。
特にtyped設定/実sampling経路から外側入口への接続を進め、全gateの意味論・次数、
実行意味論・有限体証明の全体接続・確率的健全性を証明することが必要。
この更新のみを根拠に本番利用や「criticalな健全性問題なし」を宣言しない。
