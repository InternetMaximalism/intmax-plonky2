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
| MLE Rust (`mle/src/`、旧実装を含む) | 35 | 9 | 26 |
| MLE Solidity (`mle/contracts/src/`、旧実装を含む) | 33 | 18 | 15 |
| その他（テスト・example・別crateを含む） | 222 | 2 | 220 |
| 合計 | 290 | 29 | 261 |

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

## 次工程

[SCOPE.md](SCOPE.md)の未完了一覧を順に進める。
特にtyped設定/実sampling経路から外側入口への接続を進め、全gateの意味論・次数、
実行意味論・有限体証明の全体接続・確率的健全性を証明することが必要。
この更新のみを根拠に本番利用や「criticalな健全性問題なし」を宣言しない。
