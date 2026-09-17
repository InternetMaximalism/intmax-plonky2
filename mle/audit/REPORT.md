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
初期モジュールの見出しだけをここに置き、後続は各「第N継続更新」に記録する。
直近バッチ40・41の見出しは次のとおり。

| テーマ | 定理 |
|---|---|
| installed WHIR の具体成功 | `WhirTailWitness.configured_six_claim_execution_example`, `WhirTailWitness.installed_whir_pair_accepts_a_full_verification` |
| 配備主張数での tailRun | `WhirTailWitness.installed_tail_succeeds_at_a_six_claim_context`, `WhirTailWitness.six_verify_whir_is_true` |
| マスクは主張数までは一致 | `WhirTailWitness.configured_run_mask_congruent`, `WhirTailWitness.the_two_masks_agree_below_three` |
| toy hash / 非 derivedConfig | `WhirTailWitness.the_witness_hash_ignores_every_input`, `WhirTailWitness.the_accepting_configuration_is_not_the_derived_one` |
| `numRouted = 80` での受理 | `RoutedAcceptance.routed_acceptance`, `RoutedAcceptance.routed_integrated_acceptance` |
| digest 無視と衝突 | `RoutedAcceptance.routed_hash_is_a_transcript_collision`, `RoutedAcceptance.rho_ignores_the_statement` |
| ゲート7は根の差を区別しない | `RoutedAcceptance.alt_proof_is_also_accepted`, `RoutedAcceptance.routed_wire_loop_runs_eighty_times` |
| digest を読む routed 受理 | `DigestRoutedAcceptance.fixed_acceptance`, `DigestRoutedAcceptance.fixed_initial_transcript_separates_the_two_proofs` |
| 旧ハッシュは2つのproofを分離しない | `DigestRoutedAcceptance.routed_initial_transcripts_do_not_separate_the_two_proofs` |
| chain は1バイト幅 | `DigestRoutedAcceptance.derive_digest_tail_is_thirty_one_zero_bytes`, `DigestRoutedAcceptance.fixed_hash_is_still_a_transcript_collision` |

全名付き定理は[manifest](wire3-manifest.json)で管理し、検査は抜粋ではなく全件に対して行う。

## 全ソースの対応状況

| このcheckout内のRust/Solidityファイル | 合計 | 部分的なモデル対応あり | モデル対応なし |
|---|---:|---:|---:|
| MLE Rust (`mle/src/`、旧実装を含む) | 35 | 14 | 21 |
| MLE Solidity (`mle/contracts/src/`、旧実装を含む) | 33 | 23 | 10 |
| その他（テスト・example・別crateを含む） | 222 | 3 | 219 |
| 合計 | 290 | 40 | 250 |

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

## 第20継続更新（15d2ee8f以降）

追跡版runnerでコミット`15d2ee8f`の99モデル・3268定理を再検査しPASS（790.780秒、1429モジュール、
manifest `6aab14eb581a8fd56c27e41423d6504bba7e98c6c83a6430c0dd4cbf1de4056a`、receipt
`0aeac5a0e2ac6914bf9f4866f3eb8ab99a3aedd7a6eb833233372048d41a88e3`、graph
`07321f04a0fc2f950c3217445b4eeebb740ae441fed24be1e8dd4f12a53708e3`）。

loop方式の3回目。前回残した「bound cell一致は列同定より弱い」と「外側bad setはprefix定数ではない」
の2点を対象にした。

- **gate点上のzero-check**: GatePointZeroCheckはConstantsProvenanceの残余を導出gate点上の
  Schwartz–Zippelで閉じる。bound cellと多重線形拡張の橋渡しは2^|point|≤|col|で成立し（短い列では
  bindColumnの切り詰めとextensionのゼロ埋めが食い違う反例を証明）、2列の一致集合は差分列の零点集合で
  密度≤n/|F|、一様質量≤tauTerm。合成定理は、列が異なり導出gate点が一致集合外なら受理下で抽出接合か
  opening関係が破れることを示す。レビューで、橋渡しの仮定が等式でなく不等式で足りること、committed列の
  幅仮定がopening関係から導出できること、供給列の幅が採用済みConsistent+EqCellBindingで固定されることが
  判明し、幅仮定を全て落とした。gate点列がgate laneのround challenge列であることを抽象engineで証明し、
  JointChallengeSpaceの第4族（outerGate座標）として質量≤tauTerm dを得た。残余は、供給列が結論の2分岐
  以外でrootに束縛されないこと（colを点より前に固定した読みでのみ密度が意味を持つ）、round digest連鎖が
  具体engineのみで文書化されていること、R1–R3、half (B)。
- **逐次条件付け**: OuterSequentialConditioningは外側座標のadaptive性を扱う。有限積空間上の一般エンジン
  （Nodup座標列、PrefixDependentなbad set族、Fubiniの剥ぎ取り）で質量≤Σ c_k/|A|を証明し、round messageを
  先行challengeの関数とする`Lane`で両laneに具体化した。走査順は実装どおりroundごとにlog→gate（両challengeは
  同一round digestのcounter 0/3、両messageは1回のcommitで固定。モデルの敵対者は実物より強い＝安全側）。
  adaptive外側事象の質量≤outerTermでprefix凍結版と同じ数値、adaptive結合bad事象≤combinedBound、凍結版
  laneEventはエンジンの特殊例で採用済みjoint_union_boundを同じ型で再導出する。レビューでは`ownsNext`
  （旧`active`）が交互走査の位相ビットでありgate laneのbad setが全gate座標に現れることをd=1で展開して
  確認した。Lane水準の凍結比較はDrawEncodesRunを要し未証明。法則は依然として理想一様分布で、half (B)は
  未形式化、**WHIR/Merkle項を含まず系の健全性誤差ではない**。

追加2モデルはいずれもFable側の敵対的検証を通した。GatePointZeroCheckは必須修正3件（橋渡し仮定の
不等式化、committed列幅仮定の除去と供給列幅の採用済み仮定からの導出、half (A)段落の過大表現）、
OuterSequentialConditioningは文書修正3件（`active`→`ownsNext`と位相ビットの説明、凍結族がLaneではなく
エンジンの実例である旨、message順序の誤記）を適用した。健全性欠陥は両モデルとも検出されなかった。
採用namespaceでの直接buildと全統合guardはPASS。全3390名の実定理/型/推移的公理、
450 reviewed hashes、18表1147語、7依存5601fileを検査した。

## 第21継続更新（1f3ffbf1以降）

追跡版runnerでコミット`1f3ffbf1`の101モデル・3390定理を再検査しPASS（799.855秒、1431モジュール、
manifest `1a3f5013728838f9d1e4a087ed58dedff2f0143e4611f6d44c1319e8f90422dd`、receipt
`5498858df20a074cfe5ad952d763ede2638a1ff82e7dfb58669f6b66bb41b1e4`、graph
`d1e15da16349989dca5ba0f1e273caf6f8769fcd52c6fc3a74505a7cd86a7cd5`）。
loop方式の4回目。残余R1（engine不透明性）と、iteration 3で残した「供給列は点より前に固定」という読みの
形式化、OuterSequentialConditioningが未証明としたLane水準の凍結比較を対象にした。

- **engine不透明性**: InstalledWhirTailは採用済みの手動WHIR tailモデル`WhirConfigured.run`を
  Integrated.modelEngineの`whirTail`に据え付ける。受理から具体tail実行の成功と3 rootの一致、初期評価値が
  bound cellのpacked foldであることを導き、配備プロファイル（numRounds≥1）では3 rootが中間round 1で
  開かれて各rowがMerkle認証されること、2受理実行の同root同leaf行が一致するか衝突することを証明した。
  レビューは2巡した。1巡目で「numRounds=0を本番経路とする」誤り（fixtureは全てnumRounds≥1）、R1b述語が
  WHIRと無関係に可住である欠陥、`wp`が自由である点を指摘し、round-1経路の定理群を追加、R1bを実行結果に
  対して再定式化した。2巡目で再定式化した`extract`がcommitment rootを無視し異なるcommitment間で
  cell一致を強制する（正直な実行でも偽になる）欠陥を指摘し、root引数とroot一致仮定を加えた。
  R1bはper-column形でR3を包含するため、fold水準の変種も併記した。R2は変わらない。
- **adaptiveな供給列**: AdaptiveAgreementFamilyはGatePointZeroCheckの一致集合を座標ごとの
  Schwartz–Zippelに分解してOuterSequentialConditioningのadaptiveエンジンに載せ、供給列を最初の`cut`座標のみの
  関数として質量≤tauTerm d、第5族込みの結合bad事象≤combinedBound+tauTerm d（envelope極値で≤2^-171）を得た。
  Lane水準の凍結比較もDrawEncodesRun下でlaneごとに両方向同値として証明し、OSCの未証明項目を閉じた。
  レビューは「adaptiveに選んだ列も覆われる」という見出しが過大であることを反例構成で示した。偽造者は
  1座標を見ただけで残差を恒等的に零にする列（cc+(x0 / −(1−x0))型）を作れ、第5族は空になる。したがって
  閉じているのは二分法（slice上で恒等零＝R2/R3の残余類、または質量≤tauTerm）であり、見出しを改め、
  脱出構成を形式的残余証人として追加、cut=dの空事象とcut=0の固定列一致も定理化した。

追加2モデルはいずれもFable側の敵対的検証を通した（InstalledWhirTailは2巡、必須修正計8件；
AdaptiveAgreementFamilyは1巡、必須修正1件＋注記）。健全性欠陥は両モデルとも検出されず、指摘は
いずれも被覆範囲・可住性・見出しの正確さに関するものであった。
採用namespaceでの直接buildと全統合guardはPASS。全3508名の実定理/型/推移的公理、
452 reviewed hashes、18表1147語、7依存5601fileを検査した。

## 第22継続更新（70eed7fa以降）

追跡版runnerでコミット`70eed7fa`の103モデル・3508定理を再検査しPASS（809.497秒、1433モジュール、
manifest `66894f315b3846e4e86e18d511eea0586f4afce43148cc45570893637df092d5`、receipt
`dcbd788f0e98ee3e9e43aebf33ec4cdb1336e52ab09e1034f783595bec8cafbc`、graph
`8ce127fc76aa71e44913d54c1fb756e15a14df9f2d6485924970cff743b813cf`）。
loop方式の5回目。InstalledWhirTailが残した「`wp`が自由」「index点のsamplerが観測」の2点を対象にした。

- **WHIRプロファイルの固定**: PinnedWhirProfileは`CanonicalWhirProfileV2.validateCanonical`の4制約を
  `deploymentValid`の具体化として据え付け、受理から復号wpの正準性とtail実行レコードの一致を導く。
  ソースは`inDomainSamples>0`を構文的に強制しないため、正値性とnumRounds≥1は表の意味論仮定の下で
  転記済み2行（n=10、n=21）に対してのみ導出し、round-1認証定理のhsamples/hroundsを消した。レビューは
  4制約の忠実性と2行のkeccak再計算一致を確認し、「whirTailはconfigにアクセスできない」という誤った
  設計根拠（実際はctx.parameters=c.whirEncoding）と「配備次元」という過大表現を修正させた。
- **index点samplerの具体化**: InstalledIndexSamplerは採用済みの検査付きsamplerをdecode上で全域化して
  installed engineに据え付け、index squeeze前のprefixがround状態++claim frames（6 frame、counter 3i／
  3·indexBits+3i）であること、index digestの一致がused claimsの一致か具体的衝突を強制すること、両laneの
  長さがindexBitsであることを証明し、「indexはcellの後に引かれる」（R3の順序面）を定理化した。
  確率的段階（偽造cell族が新鮮なindex点で失敗する）は未証明のまま。レビューはソース忠実性を確認し、
  decode仮定が実行上で可住であることの証明（採用済みCommitAgrees下、fixtureでも）を追加させ、
  schedule上のblock番号がラベルにすぎない点を明記させた。

追加2モデルはいずれもFable側の敵対的検証を通した（必須修正はいずれも文書と可住性補題の追加で、
健全性欠陥は検出されなかった）。
採用namespaceでの直接buildと全統合guardはPASS。全3575名の実定理/型/推移的公理、
454 reviewed hashes、18表1147語、7依存5601fileを検査した。

## 第23継続更新（bdfa02e2以降）

追跡版runnerでコミット`bdfa02e2`の105モデル・3575定理を再検査しPASS（808.547秒、1435モジュール、
manifest `a9e492060bd42f74a1b51d81f2edf3f61c6ab5d56964b9ad821890db757313f6`、receipt
`d9e26bb39f4f278c246f82575e3d86b62640a97ab4524786e34e193e8f227f3b`、graph
`ce026c0feebded75d5819c5b84bb3d623459f3348a94d265495b702d74804af8`）。
loop方式の6回目。engineに残る観測のうち初期transcript／公開入力hashとround commitを対象にした。

- **初期transcriptの据え付け**: InstalledInitialTranscriptはsampler engineの上に`OuterInitial.derive`と
  `hashNoPad`を置き、8フィールドが同時に具体化された1つのengineを与える。`DerivedInitial`自体は採用済み
  `withInitial_derived`がrflで与えていたため新規性は合成にあり（レビューで過大な新規性主張を修正）、
  この engine では下流36箇所の`hderiv`とPublicInputHashBindingの`hsub`が無条件化する。主要定理を
  `hderiv`なしで再述し、prefixがCommitmentOrderの22 frameであることをengine自身のtranscriptに対して
  示した。受理proofの公開入力がSolidityのcapと語検査を満たすことも定理化した。
- **round commitの据え付け**: InstalledRoundCommitは採用済みの検査付きround commitを全域化して据え付け、
  `CommitAgrees`を定理化、導出roundが採用済みexecuteと一致すること（残る仮定は初期transcript観測と
  degreeBits≤13）、decode仮定の無条件化、round digestが22 frame prefixの後に5 frameずつ連鎖して
  counter 0/3から引かれること、round messageの非可鍛性を証明した。RES-4とJCSのcounterラベルはこの
  engineでは定理になり、実digestを座標とするdrawでのDrawEncodesRunの実例も証明した。レビューはenvelopeがwidth c=1でindexBits=0を許す点を指摘し、その設定では
  decode失敗経路をindex長guardが通す限界（ただし本モジュールの定理では到達不能）を定理として明記させた。

追加2モデルはいずれもFable側の敵対的検証を通した（必須修正はいずれも新規性・被覆範囲・限界の記述と
補題の追加で、健全性欠陥は検出されなかった）。
採用namespaceでの直接buildと全統合guardはPASS。全3659名の実定理/型/推移的公理、
456 reviewed hashes、18表1147語、7依存5601fileを検査した。

## 第24継続更新（3efafd4c以降）

追跡版runnerでコミット`3efafd4c`の107モデル・3659定理を再検査しPASS（810.778秒、1437モジュール、
manifest `3e92472ca8f048d02592429233f36e9021d3909c0bb9c6321a2435d6c38ecc6c`、receipt
`b9f35b7157061f3ebda7c2ae15ab35bebc4bbbf88eb547058cdd9312c04b060e`、graph
`5d78a9de153572488476087bf45923df70c353168779e71dab70af815d1f9de9`）。
loop方式の7回目。据え付け済みフィールドの合成と、最後に残る観測の1つparseWhirを対象にした。

- **engineの合成**: ComposedEngineは10フィールドを具体化した1つのengineを与え、観測はparseWhirと
  configurationHashのみになった。5つのrfl同一性で各据え付けengineと一致し、InstalledRoundCommitの
  初期transcript仮定はrflで消え、degreeBits≤13と形状仮定は受理から導かれる。要約定理は受理から16連言を
  導く（各連言は採用済み定理の適用のみ）。抽象parseWhirが誤ったrootを通せないことも定理化した。レビューは
  16連言をそれぞれ元定理とbase engineまで追跡して正しいことを確認し、文書上の不正確（採用済みmoduleを
  「staged」と記載、`hi`を担ぐ定理数、「pinned triple」の表現）を修正させた。
- **parseWhirの据え付け**: InstalledWhirParseは採用済みWhirInitialのprefix読み取りの射影としてparseWhirを
  具体化し、verifyWhirの同値、root条件の冗長性、transcriptバイト列上のroot位置、誤ったrootの棄却、parseと
  tailが同じprefix実行を読むことを証明した。レビューはソース忠実性（stride、root 2本の順序、OOD回答の
  位置、mask）を確認し、非推奨補題の警告4件の除去と、prefixが中間roundまで含む点・derivedContextの先頭
  rootがproof側である点（pinとの一致はshape経由で追加）の明記を求めた。合成後に残る観測はconfigurationHash
  のみである。

追加2モデルはいずれもFable側の敵対的検証を通した（必須修正は文書と警告除去で、健全性欠陥は
検出されなかった）。
採用namespaceでの直接buildと全統合guardはPASS。全3726名の実定理/型/推移的公理、
458 reviewed hashes、18表1147語、7依存5601fileを検査した。

## 第25継続更新（327d52da以降）

追跡版runnerでコミット`327d52da`の109モデル・3726定理を再検査しPASS（818.525秒、1439モジュール、
manifest `6f4ffcd8465c06a2c2a3999fb60bd8f91a0b8d68a3b7b46ae2ae699fe91187e6`、receipt
`98d903428b68d3d5ff67a3249f9845864a3c2fc1e1984feeb8c485b08efc2f50`、graph
`8df8d7d544dc4cbfc3c6e8e3b67b25b88e132025213f85db48b42b6aaf9ea319`）。
loop方式の8回目。engineの最後の観測configurationHashと、R3の確率的段階を対象にした。

- **index点上のzero-check**: IndexPointZeroCheckはR3の二分法を与える。packed foldと多重線形拡張の橋渡し
  （反転なし、indexBits=2の数値probeで確認）、一致集合の密度≤indexBits/|F|、fold水準の関係の下で
  per-column同定が成立するか導出index点が上界された集合に入るか、同じ幅なら残余類が空であることを証明した。
  レビューはcommitted幅が導出できない（capacityは≤のみ）ため残余は「幅の不一致（末尾零を除く同定）」で
  あることを明確化させ、存在しない定理の引用と無限定の表題を修正させた。
- **明示的engine**: ExplicitEngineは最後の観測configurationHashを`khash ∘ encodeConfig`として据え付け、
  抽象base engineを持たないverifierモデルを与えた（12フィールド全てが明示的パラメータの関数）。符号化は
  coreの13フィールドで単射で、digest一致はcore一致か具体的khash衝突を強制し、PinnedWhirProfileの理想化仮定は
  衝突を除き定理になった。レビューは符号化のフィールド順の忠実性を確認し、gateRowsが受理で固定される
  ことから残余をcircuitDigest/circuitConfigDigestの2つに訂正させ、gate評価器の検証が受理の帰結として
  残ることと、配備検証の扱いがSolidity経路のみのモデルであること（RustはcallごとにkIs等を再検証）を
  明記させた。

追加2モデルはいずれもFable側の敵対的検証を通した（必須修正は分類と文言、可住性補題の追加で、
健全性欠陥は検出されなかった）。これで採用モデルのengineには観測フィールドが残っていないが、それは
「hash類を任意の決定的関数、WHIR tailを手動モデルとした上で検査経路が全て明示的である」という意味に
とどまり、R1b（WHIR近接性＋sumcheck健全性）、R2（抽出）、Fiat–Shamir半分(B)、回路真理、Rust/Solidity
refinementは未解決である。
採用namespaceでの直接buildと全統合guardはPASS。全3864名の実定理/型/推移的公理、
460 reviewed hashes、18表1147語、7依存5601fileを検査した。

## 第26継続更新（c2141566以降）

追跡版runnerでコミット`c2141566`の111モデル・3864定理を再検査しPASS（828.666秒、1441モジュール、
manifest `5fe36c22f984e419977de0a973408e862ca4e0ffe231f7f74ab482c5b184dbb7`、receipt
`84c157199baad093b2d86da3331f91f1e2feb4d80b499902b8de393f7f1a1cb7`、graph
`072d5962e491dd939676706e1eedd675f78068f472afaee95b6aff983da8b52f`）。
loop方式の9回目。監査の残余目録を1定理の仮定として固定する組み立てと、gate評価器の被覆を対象にした。

- **gate評価器の被覆**: GateEvaluatorCoverageは、Integratedが使う完全dispatcherが14 family全てを評価し
  次数上界も揃うことを定理として固定し（「id 0,1,2,3,6,7のみ」は基礎Gatesの部分dispatcherについてのみ
  正しい）、宣言表の転記と一致証明、形状検査付き評価器、124制約行の排除、BaseSum大基数の設定不能を
  示した。レビューは「次数にRust側の対応物がない」という記述が誤り（validate_gate_ext3_contextが
  Gate::degree()で同じ不等式を検査）であることを指摘し訂正させた。
- **組み立て**: SoundnessAssemblyは受理＋残余仮定構造体＋good draw条件から制約消失・per-column同定・
  profile行・core一致を導く1定理を与える。初稿はindex bad eventが無ガードで結論が仮定と矛盾し、偽造前提が
  残余に紛れていたためFable側の検証でFAIL（Leanで仮定からFalseを導出）となり、ガード付きに修正して攻撃を
  条件付き系に分離、再レビューで反駁が型検査を通らないことと正直な抽出でbad eventが空になることを確認して
  PASS-WITH-FIXESとなった。受理と残余の同時充足可能性は未提示で、名前も「good draw」とした。

追加2モデルはいずれもFable側の敵対的検証を通した。SoundnessAssemblyの初稿棄却は、レビュー工程が
「主定理が空虚である」という最も重い欠陥を検出した例であり、本更新の最重要の記録である。
採用namespaceでの直接buildと全統合guardはPASS。全3962名の実定理/型/推移的公理、
462 reviewed hashes、18表1147語、7依存5601fileを検査した。

## 第27継続更新（2016206f以降）

追跡版runnerでコミット`2016206f`の113モデル・3962定理を再検査しPASS（833.92秒、1443モジュール、
manifest `f15c914f43bfbdc698c28ea01516e58fc9ad6b866dd2b9cbb46347e59a696ca5`、receipt
`1c16975af9aa7fef557a922bab3bf3cd7b1d7accc409f9376807fdb153aa9330`、graph
`864d79f348c8413b23faa055d438874b20d89dad94554efd87c285e4435237ce`）。
loop方式の10回目。ExplicitEngineに残った2つのdigest残余と、抽出接合（R2）の構成的消化を対象にした。

- **正準proof検査**: CanonicalProofCheckはSolidityの`_requireCanonicalProof`をモデル化し、未モデルだった
  circuitDigestのimmutable比較とtranscriptに吸収されるcircuitConfigDigestを配備値に固定した。受理は
  全19フィールドについてc = c₀か具体的khash衝突を強制し、Configに自由フィールドは残らない。レビューは
  10比較表と19フィールドの由来を追跡し、verifyCall読みでの位置づけとdigest語の正準性検査の引用を
  求めた。
- **抽出器の構成**: ExtractorConstructionは抽出状態を受理proofのused claimsとR1b抽出器の出力から定義し、
  TruthChainが定義的であることを確認して、SoundnessAssemblyの残余19のうち10を構成またはR1bから定理化した。
  残る仮定は受理・R1b・表と行・配備digestと有界性・gate復号・制約数正・active filterのみである。
  レビューはfitColumnがhop.fullの下で恒等であること、laneの具体化の整合、反駁不能を確認し、初期状態の
  rounds/pointを空にすること（採用済み意味論では束縛済み履歴）とroundBadSetの対角の記述を修正させた。

追加2モデルはいずれもFable側の敵対的検証を通した（必須修正は定義の衛生と文書で、健全性欠陥は検出されな
かった）。この更新で、Configに自由フィールドは残らず、抽出接合の大半は構成により消化された。残るのは
R1b（WHIR近接性＋sumcheck健全性）、Fiat–Shamir半分(B)、回路真理、hash、Rust/Solidity refinement、
および受理と残余仮定の同時充足可能性の提示である。
採用namespaceでの直接buildと全統合guardはPASS。全4024名の実定理/型/推移的公理、
464 reviewed hashes、18表1147語、7依存5601fileを検査した。

## 第28継続更新（917e2cde以降）

追跡版runnerでコミット`917e2cde`の115モデル・4024定理を再検査しPASS（836.35秒、1445モジュール、
manifest `9052117b5b14fc5f9f6bc5d090c8427343e2616e887e3268bee021bb18630629`、receipt
`66cfeff187cba129d908bdd75567cedf4bf19ec9099af82d6f8faa21bc505d7c`、graph
`e0d7e1c579f195daf593899226630c55a665a282f5eb0be6a3f0c127b718d988`）。
loop方式の11回目。Rust側の呼び出し境界と、Fiat–Shamir半分(B)の最初の形式化を対象にした。あわせて
採用済みSoundnessAssemblyのcommittedWidth注記（HonestOpenings.openedから導出可能）とExplicitEngineの
被覆注記（完全dispatcherは14 family）を文書修正した（定理の変更なし）。

- **Rust側境界**: RustCallBoundaryはRustのcallごとの検査を対応付け、kIs正準連鎖とcircuit_config_digest
  再計算をモデル化して、Solidity側受理からRust検査が従うこと、逆は成り立たないこと（VKが配備）、配備
  config上で両engineが一致することを示した。レビューはkIs近似の向き（ソースより厳しい下近似）と、
  rustEngineがverify骨格経由でSolidityのpinも読む点を明記させた。
- **衝突述語の局所化**: LocalizedCollisionsは`TranscriptCollision`等の大域的衝突述語が鳩の巣の
  トートロジーであることを証明し、影響する採用済み定理54件を文として自明であると明示した上で、局所化
  した反証可能な述語で主要定理を言い直した。レビューはRowCollision系も表に含めること、
  `ConditionalSoundness.no_row_collision_binds_opened_dot`が仮定充足不能で空虚であること（採用木側の
  要修正として記録）、ConditionalSoundness 685-692の先行注記の引用を求めた。本更新のREPORT／SCOPEに
  おける「具体的衝突」の記述は局所述語の意味に読み替える。
- **random oracleのsqueeze**: RandomOracleSqueezesはhashを有限集合上の一様ランダム表とし、block digestを
  固定した条件付きでスケジュールsqueezeが一様でbad draw質量≤combinedBoundであること（d=13の閉じた実例
  つき）、frame/challenge入力の分離によるcongruence補題、frame fibre上のFubiniによるrun水準の上界
  P[bad draw] ≤ combinedBound + P[round digestの局所的衝突]を示した。初稿の非適応定理はレビューが仮定の
  矛盾（全digestがzeroDigestに強制される）をLeanで導いてFAILとなり、再定式化後の再レビューで「大域衝突
  述語がトートロジー」という横断的所見と「最小の閉包証人では加算項が1」という限定が指摘され、局所述語
  への置換と、加算項<1となるQの存在証明・正直な記述で収束した。小さい上界と適応的proverは未解決。

追加3モデルはいずれもFable側の敵対的検証を通した（RandomOracleSqueezesは4巡、うち1回はFAIL；
LocalizedCollisionsは1巡；RustCallBoundaryは1巡）。本更新で検出された採用木側の要修正は
`ConditionalSoundness.no_row_collision_binds_opened_dot`の空虚性（仮定¬RowCollisionが充足不能）と、
「具体的衝突」記述の局所述語への読み替えである。
採用namespaceでの直接buildと全統合guardはPASS。全4292名の実定理/型/推移的公理、
467 reviewed hashes、18表1147語、7依存5601fileを検査した。

## 第29継続更新（2d8de2d1以降）

追跡版runnerでコミット`2d8de2d1`の118モデル・4292定理を再検査しPASS（894.88秒、1448モジュール、
manifest `1a98c5af11f6728ef9ba023b3c56aad6f8b4dcd6005bbd1b93722cde05bf3094`、receipt
`c0bcbb4407930c4f14f846e5d2318e74d9d1d25844194a1fe466b90dbc6301e0`、graph
`bab5f012649fef549d25ae80d3fe2cb8c412496a6602962d8670eca65ad5c1e3`）。
loop方式の13回目。LocalizedCollisionsが指摘した空虚な採用済み定理の修復と、RandomOracleSqueezesに残った
加算項（round digest衝突確率）のbirthday型上界を対象にした。

- **空虚定理の修復**: OpenedDotBindingは`no_row_collision_binds_opened_dot`に利用箇所が無いことを棚卸しで
  確認し、実行から計算される有限リスト上の単射性を仮定とする置き換え定理と葉衝突への局所化形、非退化な
  実例と反証例を与えた。レビューは仮定の範囲の記述（多index openingでは他のrow/pathも含む）を正確化させた。
- **birthday型上界**: BirthdayClashBoundはfresh query補題とadaptive版、因果的chainの衝突確率上界、
  有界長の問い合わせ集合上でのround fold chainモデルの衝突確率≤5d(5d+1)/2/|Block|を証明した。レビューは
  計数の核が健全で非空虚であることを確認し、Check.leanの被覆不足、chainモデルと実行の接続が未了である
  こと、局所化定理の文が大域衝突述語のままである点を修正させた。修正でprefix 22 frameを繋いだchainの起点が
  deriveのdigestと一致することまで証明され（87段で≤3828/|Block|）、concreteChainの帰納のみが残る。
  run水準の加算項は依然仮定であり、2145/|Block|を実行の値として引用してはならない。

追加2モデルはいずれもFable側の敵対的検証を通した。採用木側の修正として、空虚な
`ConditionalSoundness.no_row_collision_binds_opened_dot`のdocstringを非推奨化しOpenedDotBindingを
参照させた（定理の変更なし、利用箇所なし）。
採用namespaceでの直接buildと全統合guardはPASS。全4431名の実定理/型/推移的公理、
469 reviewed hashes、18表1147語、7依存5601fileを検査した。

## 第30継続更新（94989dd5以降）

追跡版runnerでコミット`94989dd5`の120モデル・4431定理を再検査しPASS（1116.97秒、1450モジュール、
manifest `988316051e4fa86ff372fd3b430b39f682acb4e10f73fbb31d3475cc7902bbd4`、receipt
`d546da99ae1a2948b8fc020e66519438b72c823a1ebf8a6576bd69d404c629ac`、graph
`ed485185cd626206d3ef8ded95c2c4df8bdf7646a260c7677eeebf0e82a5bb9e`）。
loop方式の14回目。BirthdayClashBoundが残したchainモデルと実行の接続、およびindex laneのROM法則下での扱いを対象にした。

- **chainの実行への同定**: ConcreteChainThreadingは`chain_model_is_the_run_chain`（帰納法）で
  chainの22+5r段目のdigestを採用済み`concreteFinal`の先頭rメッセージ後のdigestに同定し、採用済み
  `sourceDigest`をchainの22+5r+5段目として読み、`clashEvent`と`prefixRoundDigestClashEvent`が同じFinsetで
  あることを示した。これによりRandomOracleSqueezesのrun水準上界に残っていた加算項の仮定は放棄され、
  `run_bad_draw_probability_le_birthday`は固定（非適応）プローバのROM下で確率的側条件を残さないrun水準上界
  （≤ combinedBound + (22+5d)(22+5d+1)/2/|Block|、d=13で3828/|Block| ≤ 2^-244）になった。長さ予算の閉じた証人
  （L=381）と閉じた実例、そのRHS<1（`closed_bound_lt_one`）、非空性（定数表∈clash事象、frame-freeでない）を添えた。
  レビューは数学を完全に再現し（独立に再構築したoleanが作者のものと一致）、absorbが入力counterを読まないこと、
  getDの退化分岐が採られないこと、事象等式が真の等式であることを確認した。修正は参照SHA、見出し文への
  「固定プローバ・ROM」限定句の明記、frame計数（statementベクトル2 + root 3）、RHS<1定理の追加、公理なし定理数。
- **index laneのROM法則**: IndexLanesOracleは採用済みclaim frame 8個を足した拡張chainの22+5d+8段目が採用済み
  `indexDigest`であることを示し、レビュー要求の橋渡し補題で拡張chainの22段目・22+5i+5段目を採用済みderive/
  roundCommitted digestに同定した。固定index digest下で`actualIndexDraw`の押し出しは採用済み`indexProbability`に厳密に
  等しく（3 squeeze/座標、mod pの偏りは採用済みtauTerm側に既に計上）、guard付きindex bad事象は≤2·tauTerm、joint族と
  index族の和集合は固定digest下で≤combinedBound+2·tauTerm（索引カウンタは外側カウンタと数値的に重なるため、分離は
  digestのみ。和集合上界が消費するのは各族の単射性のみで、交差の相異は充足性経路でしか使われないことを明記）、
  拡張chainのbirthday上界はd=13で4560/|Block|。レビューはLeanモデルとSolidity/Rustの両方で22+5d段目が索引サンプラに
  渡されるsnapshotであること（最後のround commitと索引absorbの間に他のtranscript操作がない）、押し出し等式が可除性
  仮定なしに厳密であることを確認した。未実施は和集合のrun水準Fubiniと、`hst`のLean上の接続（ConcreteChainThreadingが
  同じ事実を証明するが相互importはない）。
  両モジュール合わせて122モデル・4530定理。今回もROMの法則下・固定プローバの結果であり、keccakの性質でも系の健全性
  誤差でもない。適応的プローバ、R1b（WHIR近接性+sumcheck健全性）、回路の真値、受理証明と残余の同時充足性は未着手。

## 第31継続更新（5e55b602以降）

追跡版runnerでコミット`5e55b602`の122モデル・4530定理を再検査しPASS（854.581秒、1452モジュール、
manifest `d880585491d008e94f5b39a4cfeba31441f20373e89e122435be788954104346`、receipt
`e06033d3d393f681e975e820cf3ce362ad1deb36250ed2ef1a5bb4365a10ec8a`、graph
`65480d4334a2ee54b091f5c44bf8526dc910427ab4c95f0b0fec98be5d84ee3f`）。
loop方式の15回目。ConcreteChainThreadingとIndexLanesOracleの接合（run水準の和集合上界）と、適応的プローバへの第一歩（chainのbirthday項）を対象にした。

- **run水準の和集合上界**: RunLevelUnionBoundはILOの`hst`をCCTで放棄し（拡張chainの22+5d+8段目 = 組立の実索引digest、rfl）、
  RandomOracleSqueezesのframe fibre Fubiniを2族同時に1回再実行して P[jointBad ∪ guardedIndexBad] ≤ combinedBound + 2·tauTerm +
  P[拡張chainのclash]（d=13で4560/|Block|）を得た。閉じた実例（L=381）でRHS<1、good tableの存在も示した。explicit engineの
  組立結論の失敗集合はhash添字付き和集合事象に含まれる（無条件）。レビューは分割と接頭辞分離の実使用、clash外での結合
  単射性（block 0のdigest = derive digestを含む）、厳密なfibre計数、≤の総和を確認した一方、初稿の質量系が依存した被覆仮定
  （∀hashで固定事象が支配）は固定プローバでも非退化な実行で充足が知られない（hashはgate alpha座標と外側row点経由でのみ
  bad事象に入る）と判定し、空虚性方針により被覆定理と質量系を削除させた。残る橋渡しは2段階条件付き計数であり適応性の
  問題ではないことを見出しに明記した。`hlenI`の追加コスト（p.usedの幅上界、L=381は幅≤13のみ）と閉証人の索引半分が∅である
  ことも開示。
- **戦略に対するbirthday上界**: StrategyChainBoundはfresh-query帰納を戦略（既出digestとそのchallenge回答から次frameを
  選ぶ関数。因果性は型に組込み）に対して再実行し、任意の戦略でchainのclash確率 ≤ n(n+1)/2/|Block|（87段で3828/|Block|、
  固定プローバと同じ定数）を得た。鍵は採用済み`frame_ne_challenge_input`（frame回答の書換えはchallenge回答を動かさない）と
  no-clash下でのdigest相異。chain自身のno-clash事象で条件付けたchallenge回答の一様性（単一・有限集合版）、戦略的外側
  プローバのchainが表ごとの実現メッセージでconcreteFinalに一致することも示した。レビューは戦略が自前の神託問合せを持たないtranscript制限付きモデルであること（grindingプローバは対象外、質量は問合せ数に比例）を見出しに明記させ、「履歴で条件付け」の表現をno-clash事象での条件付けに正した。未達は適応的プローバの和集合上界
  （OuterSequentialConditioningの逐次条件付け計数の神託表への輸送）で、見出しで明示している。
  両モジュール合わせて124モデル・4637定理。RunLevelUnionBoundの初稿の被覆仮定と、StrategyChainBoundの「Fiat–Shamirプローバが持つ
  情報そのもの」という表現は、いずれもレビューで退けられた（前者は非退化な実行で充足が知られない仮定、後者は自前の神託問合せを
  持つgrindingプローバを黙って除外していた）。今回もROMの法則下の結果であり、keccakの性質でも系の健全性誤差でもない。
  残るのは固定プローバの2段階条件付き計数、適応的プローバの和集合上界（逐次条件付けの神託表への輸送）、grindingプローバの
  問合せ計数、R1b、回路の真値、受理証明と残余の同時充足性。

## 第32継続更新（c2b5bc53以降）

追跡版runnerでコミット`c2b5bc53`の124モデル・4637定理を再検査しPASS（875.055秒、1454モジュール、
manifest `a42ad65a94eb376744257475a45bc82f565ab22adde7422a2d5a8bebe50b2f34`、receipt
`baf9c8f84601c50fffa062a2d9d0733f8b3179bfb64302af71079bd0b9f18af2`、graph
`ca1b2c730dee823ab5a50a75eda72564f9fc51b443d8e37769706164d2102972`）。
loop方式の16回目。RunLevelUnionBoundが契約として残した固定プローバの2段階条件付き計数と、StrategyChainBoundが除外したgrindingプローバを対象にした。

- **2段階条件付き計数の外側段**: TwoStageConditionalCountはexplicit engineのouter bad事象がgate alpha座標経由でのみhashに依存すること
  （engine自身の依存も吸収）を示し、対角事象を一座標条件付き計数で採用済みcombinedBoundのまま評価してRLUBのfibre Fubiniで神託表へ
  輸送した（`run_outer_stage_mass_le`）。レビューは条件付けの正当性（各固定alpha事象がalpha座標から独立な柱であることが実効仮定で、
  敵対的族{w | w_α = a}は排除される）と定数の一致を確認した一方、索引段の「row点は外側drawの関数でない（log-tau列）」という障害主張を
  採用済み補題で反証した。修正後はrow点が外側drawの関数であることを定理化し、索引段の条件付き計数は`RowPointFixed`を明示仮定として
  払い出し（定数列で非退化に充足、payoffは定数committed列のみと明記）、閉実例の索引半分が∅であることを定理で記録して、guardが生きる
  第二の閉実例を追加した。
- **grindingプローバのchain上界**: GrindingQueryBoundは各段q回の自前probe問合せを持つプローバを定式化し、採用済みCausalが再問合せ
  に耐えないことを見出してfreshness事象で条件付けるFreshCausalへ置き換え、異なる文字列間の回答一致事象の上界を経由して
  chainの衝突質量 ≤ N(N+1)/2/|Block|（N=(q+1)n、q=0で3828/|Block|）を得た。probeの回答を読む戦略の提示、q=0でのSCBとの表ごとの
  一致を示した。レビュー要求でchallenge入力の読み取りを任意digestに一般化し（列の位置のみframe形）、上界がqについて2次で
  先頭項が≈(q+1)倍緩いこと（SCBの「q·n」は発見的）を明記した。
  両モジュール合わせて126モデル・4780定理。今回もROMの法則下の結果であり、keccakの性質でも系の健全性誤差でもない。残るのは
  索引段の細分割（3段契約）、適応的/grindingプローバの和集合上界、grinding上界のq線形化、R1b、回路の真値、受理証明と残余の
  同時充足性。

## 第33継続更新（3a5fedba以降）

追跡版runnerでコミット`3a5fedba`の126モデル・4780定理を再検査しPASS（883.049秒、1456モジュール、
manifest `b04b24cb68d71f05e5a74468b0f1d8311bfb204e368a8accaf59347b22bda9cc`、receipt
`6e0cf2860eaa8c94a2923190a2a5039ba12c0827eba57b53b41372232a96d7f7`、graph
`c600a127f60b34f5ab9eba36e01d894a5f5b8491cb72f590b56e0c1730077cb5`）。同コミットに対する先行2回の実行は、並行して動いていた実装エージェントが
`pkill -f "[l]ean --root"`を発行してrunnerのleanプロセスを外部から停止させたため失敗（`lean exited -15`、出力なし）しており、
監査上の所見ではない（記録は候補ディレクトリのfresh-run-3a5fedba-FAIL-run1/2.logとreceipt写し）。
loop方式の17回目。TwoStageConditionalCountが契約として残した索引段の細分割と、StrategyChainBoundが残した適応的プローバの和集合上界を対象にした。

- **索引段の細分割**: IndexStageFinerSplitは結合scheduleのclash外単射性、結合selectorでのrestrict_ratio、2群条件付き計数、frame fibre
  Fubiniの3段を構築し、`RowPointFixed`を計数で放棄した。見出しは`run_index_stage_mass_le ≤ 2·tauTerm + P[拡張clash]`と
  `assembly_failure_mass_le_unconditional`（committed列に条件なし、RHSはcombinedBound + 2·tauTerm + P[拡張clash]、d=13で4560/|Block|、
  閉実例でRHS<1）。レビューは対角計数（uは補完のK1半分であってfibre定数ではない、F uは文字通りrow点でのguard付き索引bad事象）、RLUBのhash添字付き族との
  文字単位の一致、単一のFubiniによる加算項1つ、仮定がTSCCから`RowPointFixed`（と`committed0`）を除いただけであることを確認し、PASSとした。
  文言上の指摘（未使用引数、派生形の限定句、「放棄」は計数による仮定の除去であり述語の証明ではない）を反映した。
- **外側laneの条件付けの輸送**: OuterLaneTransport（初稿名AdaptiveUnionTransport）は対角fresh step（条件付け事象をtargetの値で分割）と
  入れ子no-clash事象でOSCの各round条件付けを神託表へ輸送し、任意の戦略駆動chainに対して ≤ outerTerm + chain衝突項を得た。レビューは
  計数の正しさ（採用済みlaneBad_card_leの天井上界、和がouterTermに厳密一致）を確認する一方、一般形の見出しが**戦略と独立に量化された
  laneのbad集合**を扱っており（判定 iii）、SCB (iii)の「roundのbad集合はプローバが選んだメッセージで決まる」を閉じていないこと、
  閉実例のbad集合が早いroundで空であるのに非空を主張していたことを指摘した。修正でモジュールを改名し、構成不能性（定義域と損失）を
  見出しに明記、非空性を両方向の定理にし、縮約履歴部分クラス（ReducedStrategy）でlane messageと実現メッセージの一致を証明して、
  その部分クラスに限る真の適応的和集合上界`reduced_outer_lane_bad_draw_probability_le`を追加した。再検証は結合補題が真の恒等式であること（lane側のbad集合の入力 = 戦略がround rで吸収したメッセージ、gate側のtake帳簿も一致）を
  確認し、部分クラス定理を判定 (i)（真の適応的上界）、一般形を判定 (iii) と評価してPASSとした。truth関数と主張が自由なのは∀量化で
  正しい形（正直なメッセージではbad集合が空）。
  両モジュール合わせて128モデル・4895定理。IndexStageFinerSplitにより、固定プローバのROM下でexplicit engineの組立結論の失敗集合に
  committed列の条件なしの質量上界が付いた。今回もROMの法則下の結果であり、keccakの性質でも系の健全性誤差でもない。残るのは
  raw block読みの戦略への適応的上界、tauTerm/alphaTermの輸送、grindingの和集合上界、非定数列でのguard生存性、R1b、回路の真値、
  受理の提示。

## 第34継続更新（63722788以降）

追跡版runnerでコミット`63722788`の128モデル・4895定理を再検査しPASS（900.365秒、1458モジュール、
manifest `80c5a0ac065ce87206d173e1136033167eac1fd4a95c1f9179c54234ecf6b61d`、receipt
`1b84c594fd49c83780b75d77ef449323949a65e5da1ba314c94e5a0efa6a9623`、graph
`605078e3db6f3659a66ee5baad7fcacdd4c8975f0096c00a024761ee82b5cc7e`）。
loop方式の19回目。OuterLaneTransportの縮約部分クラス上界の定数拡張、grinding上界のq線形化、索引guardの生死の説明を対象にした。

- **縮約部分クラス上界の完成**: ReducedFullTransportはderive digestでのgate tau/gate alpha事象を固定targetとして加え（採用済みtau/alpha
  bad事象はg/coeffsOfのみに依存し表を読まない）、3dカウンタの同時剥離と入れ子no-clashによる共有衝突項で
  `reduced_full_bad_draw_probability_le ≤ combinedBound + chain衝突項` を得た（閉実例でRHS<1）。索引laneは適応的プローバでは使用claim
  が表の関数になるため含まず、その理由を明記。レビューはgate tau/gate alphaの読み取りが採用済みsourceCounter（12+3d+3i, 9+3d）でderive digestを読むこと、事象が採用済みtauBadEvent/alphaBadEventの引き戻しであること、衝突項が1つであることを確認しPASS-WITH-FIXESとし、「22段目 = derive digest」と2つの引き戻しを散文でなく定理にさせた（`derive_stage_is_derive_digest`、`gate_tau_bad_event_is_pullback`、`gate_alpha_bad_event_is_pullback`）。
- **grinding上界の線形化**: GrindingLinearBoundは押し下げを問合せ文字列上で言い直し、形成済み段digestを位置依存targetとして
  (q+1)n(n+1)/2/|Block| を得た。ただしprobeが形成済み段digestでframeするstate-framedプローバに限り、probe予算内で候補chainを
  模擬する攻撃者は除外（GQBの2次上界は覆う）と明示。q=0では制限なしで採用済み定数に一致。レビューは包含（後段についての強帰納法。段rは段r−1のabsorbで形成されるため進行は自動）、計数、戦略水準仮定、残差形、数値を確認しPASS-WITH-FIXES（文言: defs数、StateFramedは「以後のabsorbが問う文字列」に限る制約、残差項は「ほぼ全空間」）とした。
- **索引guardの生死**: IndexGuardLivenessはguardが共通幅で「主張cell = committed cell」のときに限り死ぬこと（正直な場合。索引事象は∅）と、
  非定数列（spikeColumn）ではdead ↔ eqAtZero(row) = (x−v)/(w−v) という単一の体方程式であることを定理化し、ISFSの未解決項目を
  説明として閉じた（上界は不変）。レビューは特徴づけと拡張の索引規約を確認しPASS-WITH-FIXESとし、「下流の消費者は皆1cell形」（誤り: ISFSのindexBadAtは幅の一致を仮定しない。dead条件は0詰め一致）と見出しの「非空」主張（未証明）を訂正させた。
  三モジュール合わせて131モデル・5002定理。今回もROMの法則下の結果であり、keccakの性質でも系の健全性誤差でもない。残るのは
  索引laneの適応的扱い（対角形）、raw block読み戦略、probe予算内でchainを模擬する攻撃者、g/coeffsOfと配備表の結合、R1b、回路の真値、
  受理の提示。

## 第35継続更新（a5f73b35以降）

追跡版runnerでコミット`a5f73b35`の131モデル・5002定理を再検査しPASS（1394.096秒、1461モジュール、
manifest `cfb7c94f799310747fb97688a054d4d49ce5cf348c078d9197aa40d120e2f779`、receipt
`3ac5415e12fab3d64d2292dfbeb76adf25440108595e02054588262cc4abfd8f`、graph
`a31ef1dcf2b4e847e7b686811bb7bb2a9c71cecd861fe370743039ae9378ba59`）。
loop方式の20回目。縮約履歴適応プローバの索引laneと、grindingプローバの問合せグラフによる見方を対象にした。

- **縮約適応プローバの索引lane**: ReducedIndexLanesは履歴依存のused-claims選択を8 claim frameとして吸収する拡張戦略のchainの22+5d+8段目が
  実現claimsでの採用済みindexDigestであることを示し、索引digestでの対角fresh step（分離はno-clash下のdigest）と密度補題、6·bitsカウンタの
  同時剥離で、索引項2·tauTermを加えた `≤ combinedBound + 2·tauTerm + (22+5d+8)(22+5d+9)/2/|Block|` を得た（閉実例でRHS<1）。committed cell
  は履歴の関数のパラメータであり実現proofへの転送は未実施、索引項は1 bound cell分と開示。レビューは拡張chainの同定（claim frame 8個、Uが読むのは縮約round履歴のみ）、no-clash下のdigestによる分離、密度補題と6·bitsカウンタの剥離の厳密性、単一の衝突項を確認しPASS-WITH-FIXES（文書のみ）とし、HONESTY (iii) を「転送に必要なのはprefix合同補題・OLT §6の実現draw同定・TSCCのrow点定理と列が固定データであるという既存の仮定であり、RowPointFixedは不要」に正させた。
- **grindingの問合せグラフ**: GrindingGraphBoundは段の衝突をabsorb経路上の位置対の衝突に帰着し、GQB/GLBを実例に持つ統一charging定理を
  与えた上で、chain模擬プローバでは eligible 集合が全対に一致してこの方式では定数が改善しないことを定理として記録した（否定的結論、
  衝突質量の下界は主張しない）。レビューは統一定理がGQBのfresh位置帰納の位置依存target版であり3実例が採用済み定理と項単位で一致すること、到達上限がnでなくmであること、混入痕跡がないことを確認しPASSとした（docstring 2点を補足）。
  両モジュール合わせて133モデル・5115定理。今回もROMの法則下の結果であり、keccakの性質でも系の健全性誤差でもない。残るのは
  committed cellの実現proofへの転送、複数bound cellの索引項、raw block読み戦略、一般grindingプローバの線形上界（charging方式の外）、
  g/coeffsOfと配備表の結合、R1b、回路の真値、受理の提示。

## 第36継続更新（d523eecd以降）

追跡版runnerでコミット`d523eecd`の133モデル・5115定理を再検査しPASS（1181.923秒、1463モジュール、
manifest `cfd8dc008e434a455cd787bd2d38d2fcc94e4b35ddf81a5066b93f62fef31ffa`、receipt
`4a3b0a6fdd5fa05305cf86d39f0658849700aad9d4289242170d5ba2b84e2ac5`、graph
`73765b5d7ce76b9f3365fc820fb3e48620185de65eac0bb1eaf2218459767d77`）。
loop方式の21回目。ReducedIndexLanesが残した転送と、reduced-history制限の解除を対象にした。

- **engine自身の索引事象への転送**: ReducedEngineIndexは二戦略・同一表の合同補題、OLT §6のdraw同定、TSCCのrow点定理を実現proofで
  組み合わせ、committed cellが縮約履歴の関数であることを示してengine自身の索引bad事象とのFinset恒等式を得、縮約適応上界
  ≤ combinedBound + 2·tauTerm + chain衝突項をengine自身の事象上で成立させた（多cell版は5·2·tauTerm、衝突項1つ。RILのhstも放棄）。
  レビューはFinset恒等式の左辺が`explicit_good_draw_assembly`のhidxが消費する事象そのものであること（probeで実際にhidxを放棄）、三つの同定が全て定理であること、合同補題の関数水準の量化、realizedRunの側条件、多cell版の単一衝突項を確認し、PASS-WITH-FIXES（REPORTの行数のみ）とした。
- **reduced-history制限の解除**: RawBlockLanesは対角fresh stepに必要なのがRoundCausalのみであることを使い、OSCのLaneを経由しないraw lane
  （rawメッセージ、縮約challengeでの評価）で任意のRoundCausal戦略の外側+block-0上界 ≤ combinedBound + chain衝突項を得、OLT §8を特例として
  回収し、OLTが対応づけられなかったchallengeTruncatedMessageで閉実例を与えた。索引半分のraw版は未達と明記。レビューはraw laneの1段が採用済み検証器の段（縮約challengeでの多項式評価）と一致すること、結合、OLT §8の回収、単一衝突項、閉実例を確認しPASS-WITH-FIXES（文言）とし、見出しを「SCB (iii) の**各round分解の半分**をcombinedBound laneで閉じる（run水準の輸送は未着手）」に正させた。
  両モジュール合わせて135モデル・5223定理。今回もROMの法則下の結果であり、keccakの性質でも系の健全性誤差でもない。残るのは
  索引半分のraw版、grindingプローバの和集合上界、列・g/coeffsOfと配備表の結合（CommitmentOrder）、R1b、回路の真値、受理の提示。

## 第37継続更新（d6603b5c以降）

追跡版runnerでコミット`d6603b5c`の135モデル・5223定理を再検査しPASS（1401.11秒、1465モジュール、
manifest `675137424184c1cd832a5056d58563def95cadc9aabc5b2ad12963dda487e079`、receipt
`f407c41b37cc38204335d5871b5819e881d7e363c31c0c0b63368444ec6124f7`、graph
`01d65a87670b039fa86501fbbac7ecd75cfa5340302213b86d2e7e6f56b948ef`）。
loop方式の22回目。raw戦略の索引半分と、SCB HONESTY (iii) 末尾のrun水準輸送の決着を対象にした。

- **raw索引半分とengine転送**: RawIndexLanesはClaimsCausalなused-claims選択を持つraw拡張chainを定義し、RILの計数スタックとREIの転送補題を
  逐語的に再利用して（新規は不変性補題2本）、任意のRoundCausal S・ClaimsCausal Uに対しexplicit engine自身の事象上で
  ≤ combinedBound + 2·tauTerm + chain衝突項（5 cell版は5·2·tauTerm）を得た。閉実例はraw blockを読む戦略と claims 選択で
  RHS<1。レビューはClaimsCausalがRoundCausalのd段目版と定義的に一致すること、claim frameとindexDigestの同定、no-clash下のdigest分離（全カウンタで不変）、RIL計数スタックの戦略非依存性、engine事象とのFinset恒等式（probeでhidxを放棄）、単一衝突項と5 cell版を確認しPASS-WITH-FIXES（文書のみ）とした。
- **run水準輸送の決着**: RunLevelTransportAuditは採用済み`jointBadEvent`の外側部が凍結LaneRoundリストを取り、claimの再帰が各roundの
  challenge欄で進むことから、RBLのraw全事象が実現proofでの`actualDigestDraw`のrun水準bad事象とFinsetとして等しいことを示し、
  適応的run水準上界を固定プローバ定理と同じ形で得た（閉実例でRHS<1）。whole-schedule一様性は不要と定理化し、積法則は主張しない。
  提案された修正文をSCB (iii)/OLT (vi)/RBL (vi) のdocstringに反映した。レビューは`jointBadEvent`の外側部が凍結LaneRoundリストを取り自身のchallenge欄で再帰すること、実現laneが採用済み`DrawEncodesRun`のseam述語を実現drawで満たすこと、座標ごとの輸送、事象が固定プローバ族の対角であること（同じ文の形）を確認しPASS-WITH-FIXES（散文）とした: 「no-clash事象は内側段の再割当で閉じない」という未証明の否定を「閉性は既知でなく、積法則の成否はここでは未決」に改め、提案修正文に範囲（外側+block-0、transcript制限付き因果的プローバ、claimed start 0、索引はRawIndexLanes、ROM、grinding除外。OLT側は縮約部分クラスの見出しに限る）を明記させた。
  両モジュール合わせて137モデル・5317定理。これでROMの適応的上界はtranscript制限付き（自前問合せなし）の因果的プローバに対して、
  外側・block-0・索引の全laneでexplicit engine自身の事象上に成立し、run水準の形でも述べられた。今回もROMの法則下の結果であり、
  keccakの性質でも系の健全性誤差でもない。残るのはgrindingプローバの和集合上界、列・表と配備との結合（CommitmentOrder）、R1b、
  回路の真値、受理の提示。

## 第38継続更新（2cf506f6以降）

追跡版runnerでコミット`2cf506f6`の137モデル・5317定理を再検査しPASS（1534.183秒、1467モジュール、
manifest `4a84b12770f6c6ec43f9d20dd9c90bf32de3ba99e64526570eb62fffdd16e977`、receipt
`1b1cfb8725f8aef6f143ca50496a1df0019b6972e60cdbf03ea0d86e94c05ec8`、graph
`e1eb1d0e3cdedded09f0ea7b35b9941b7fc0e01aaa4c2f51c66a3fb5e1d71b16`）。
loop方式の23回目。「固定データ」残余の分類、grindingプローバの和集合上界、そして分類が露わにしたtau事象のalpha対角を対象にした。

- **固定データ残余の分類**: CommitmentOrderSurveyはgate alphaがderive digestのsqueeze（challenge座標）であり、assemblyのtau表gがそれを
  読むことを示した。レビューは初稿がalphaを「prefixデータ」に分類していた点を退け（prefix digestの決定的関数であっても神託法則の
  外側で束縛された値ではない）、ROM系列の固定gのtau事象がengine自身のtau事象のalpha固定スライスに過ぎず対角が未評価であること、
  REI/RXLが「engine自身の事象」と呼べるのは索引事象のみであることを確定させた。committed列はround-one openingに依存し（索引squeeze
  の後に吸収）prefixデータではなく、「固定」はR1b型のrootDetermined仮定と判明。採用済み6ファイル12箇所（RFT・JointChallengeSpace・
  OuterSequentialConditioning・RIL・REI・RXL）の過大な文言を修正した。
- **grindingの和集合上界**: GrindingUnionBoundはChallengeRestricted（challengeは自身の段digestでのみ読む）なgrindingプローバに対して
  外側+block-0の和集合上界 ≤ combinedBound + N(N+1)/2/|Block| を得た（抽象段digest族上の剥離、probe回答も読めるGrindLane）。レビューは
  初稿のpreReadGrinderが名指した攻撃を行っていないこと（tag不一致）と「より広いクラス」の包含未証明を指摘し、selector版と包含定理で
  修正させ、bad集合がgrinder自身のメッセージを運ぶ結合は未了と見出しに明記させた。orchestratorの「拡張clash事象」案は
  probe→absorbが同一文字列である点で反証され、pre-read（FS challenge grinding）はこの方式の外側にあると確定した。再検証は拡張laneの因果節がroundのchallenge段より厳密に下の cut（probeをroundの5 frameの間に挟むプローバは未モデル。緩い cut でも対角stepは通る）であること、selector版preReadGrinderが好都合な読みで実際にpre-read digestへ移ること、包含定理、結合が未了である旨の正直さを確認しPASS-WITH-FIXES（docstring 1箇所）とした。
- **tau事象のalpha対角**: EngineTauDiagonalはalpha三つ組で条件付け事象を分割し、各ブロックでRFTの同時剥離を適用して engine自身のtau事象
  の質量 ≤ tauTerm d を任意の戦略・任意のGについて示し（対角は定数を増やさない）、RXL経路を再構築してengine自身のtau+索引事象上で
  ≤ combinedBound + 2·tauTerm + chain衝突項を得た。最終定理で∀-lane形のまま残るのは外側（適応系列でのalpha依存外側対角は未解決）と
  alpha（対角不要）であることを明記。レビューは対角計数（alpha三つ組による分割、各ブロックの段安定性、値ごとの採用済み密度上界）とRXL経路の再構築（仮定はRXLと同一、衝突項1つ）を確認しPASS-WITH-FIXESとし、`alphaRead`が実現proofの`gateAlphaElement`に等しいという同定（RLTAから導出）を定理として追加させた。これで未証明の残余は tables = s0.tables（CommittedTables結合）のみ。
  三モジュール合わせて140モデル・5469定理。CommitmentOrderSurveyの分類とEngineTauDiagonalにより、transcript制限付き因果的プローバの
  ROM適応的上界は engine 自身の tau・索引事象上で述べられ、外側（alpha依存の対角、適応系列で未解決）とalpha（対角不要）は∀-lane形。
  今回もROMの法則下の結果であり、keccakの性質でも系の健全性誤差でもない。残るのは適応系列の外側alpha対角、pre-readプローバの
  問合せ計数、grinder自身のメッセージとの結合、CommittedTablesJoin（rootDetermined・preprocessedPinned・configDeployed）、R1b、
  回路の真値、受理の提示。

## 第39継続更新（be012e44以降）

追跡版runnerでコミット`be012e44`の140モデル・5469定理を再検査しPASS（1433.378秒、1470モジュール、
manifest `47e3a0c1cac5e6bc0573c674762d9a8a8ac1e521e0015b12a47c8a039b0dca59`、receipt
`0130324cafcff44a7b19a8160e9f44205924a4e55df008caa03aaed0ac067e33`、graph
`049d621b851d3edd1345b324fd008517201392ce5383f9547dbc9610d851e974`）。
loop方式の24回目。適応系列の外側alpha対角と、pre-read grinding の問合せ計数を対象にした。

- **外側alpha対角**: EngineOuterDiagonalはalphaが外側事象にgate laneの初期truth claim経由でのみ入ることを示し、alpha索引のraw lane族で
  engine自身の外側事象を定義、alphaがround cellより厳密に前の段で読まれるためOLTの対角fresh stepが無変更で適用できて ≤ outerTerm を
  得た。これで4事象すべてがengine自身のものとなり ≤ combinedBound + 2·tauTerm + chain衝突項（閉実例でRHS<1）。組立失敗集合への系は
  DrawEncodesRunの実現drawでの成立とlane列の同定の2脚が残るため未到達と明記。レビューは全証明を確認し（alpha依存のrfl分解、22 < 27+5rによる不変性、一様基数ゆえ分割不要、ETDと同一仮定の全所有和集合）、「残る2脚」の診断を退けて（DrawnAtは実現laneで構成的に成立）lane列同定1本に縮め、要約文の過大表現（tables = s0.tables だけでない）を正した。PASS-WITH-FIXES。修正でDrawnAt/frozen walkの定理4本を追加（45定理）。
- **pre-readのcharge**: PreReadChargeはprobeをchargeする二段fresh peelで、GUBが除外したpre-readプローバを含むクラスに (q+1)·outerTerm を
  証明した。好都合な分岐ではroundのchallenge digestがprobeのdigestそのものであることを示し、absorb（反復）をchargeしない理由と、
  probeのchargeが攻撃をchargeする理由を定理化した。結合（grinder自身のメッセージ）と他laneは未達。レビューは二段peelの健全性と算術を確認した上で、結合の隙間が「decoder不在」ではなく**構造的**（GrindLaneは段digestのcellしか読めず、pre-readの実現メッセージ・running claimを表現できない）であること、「bounds it」が候補族サロゲートの上界であること、absorbスロットが被験プローバでは空であることを正させた。修正で二分補題と緩いcutを追加（60定理）。
  両モジュール合わせて142モデル・5574定理。EngineOuterDiagonalにより、transcript制限付き因果的プローバのROM適応的上界は4事象すべてを
  engine自身のものとして述べられた（組立失敗集合への系は2脚が残る）。PreReadChargeにより、FS challenge grindingは予想通り係数(q+1)で
  評価された（結合は未了）。今回もROMの法則下の結果であり、keccakの性質でも系の健全性誤差でもない。残るのはlane列同定（適応系列の組立系）、grinderのメッセージとの結合、CommittedTablesJoin、R1b、回路の真値、受理の提示。

## 第40継続更新（ac1fb665以降）

追跡版runnerでコミット`ac1fb665`の142モデル・5574定理を再検査しPASS（1362.576秒、1472モジュール、
manifest `ceca92d3edcf8dc73203c659e4f6cd71321628596569308a57a3e8a8dc72d53b`、receipt
`50176f39ed12391bb75edbefe9ce91e6c580b8b7eaeb274739bc03997ddd01bc`、graph
`82d864633ee6423d5f8c76e9934c678e6a195337c3137f73c5ab16e49bed6cd3`）。
loop方式の25回目。EngineOuterDiagonalが残したlane列の同定と、`CommittedTables`結合の節ごとの判定を対象にした。

- **適応系列の組立失敗上界**: AdaptiveAssemblyFailureは実現lane列と採用済みengine lane列が`frozenLane`の読む射影で一致することを示して
  EODの最後の脚を閉じ、全所有事象が実現runでの`SoundnessAssembly.outerBadEvent`とFinsetとして一致することを証明した。これにより
  組立失敗集合は仮定なしにその事象と索引事象の和に含まれ、質量は ≤ combinedBound + chain衝突項 + P[索引事象]。索引半分の質量は
  運搬のままで、採用済み索引モジュールの評価地点（拡張shapeのchain・異なるused記録）への証明記録の輸送が残る一歩である旨を見出しに
  明記した。レビュー（Opusによる敵対的検証）はfrozenLaneが`.message`/`.truth`しか読まないこと、truth列に添字のずれがないこと、engineが自由であること、`thash`が`gateAlphaElement`以外の経路で入らないこと（公開入力ハッシュはhash非依存）、payoffが採用済み組立定理の対偶そのものであることを独立に再導出し、PASS-WITH-FIXESとした。閉実例の見出しが**最初の2項のみ**を覆う（索引項を含めると mass < 1 + P[索引事象] しか従わない）ことを明記させた。
- **`CommittedTables`結合の節ごとの判定**: CommittedTablesClausesはpreprocessedPinnedを受理から任意のengineで導出し、configDeployedを
  Solidity経路で局所的な構成符号化衝突1つまで導出し、rootDeterminedがR1bそのものであるばかりか、開示を読む抽出器では節を満たす表写像が
  存在しないこと（従ってCOSの退化した証人は強制されていたこと）を示した。採用済みbinding補題が届くのは開かれたcellだけで、そこでは
  局所leaf/path衝突までroot決定性が成り立つ。結論として「tablesは固定データ」はR1b + 2つの局所衝突に還元され、`g`は依然として
  固定データではない（block-0のalphaを読む）。レビュー（Opusによる敵対的検証）は節1・節2の導出が厳密であること、節3の不可能性が採用済み抽出器で真正（`0 < numWires`が実効的）であることを確認しPASS-WITH-FIXESとし、tau表系の受理・衝突仮定が不活性であること（R1bのみから従う）、fixture定理が自明に真であること、「2つの異なるhint buffer」が消費されない末尾バイト差でしかないこと、修正文がSolidity経路の限定と局所衝突の但し書きを落としていたこと、「何も再掲していない」が誤りであることを正させた（35定理）。
  両モジュール合わせて144モデル・5642定理。これで適応系列の組立失敗集合には（索引半分の質量を運搬したまま）上界が付き、ROM系列が
  一貫して「固定データ」と呼んでいた残余はR1bと2つの局所衝突に分解された。今回もROMの法則下の結果であり、keccakの性質でも系の
  健全性誤差でもない。残るのは索引半分の輸送、R1b（全列のroot決定性）、回路の真値、受理の提示、そしてgrindingプローバの結合。

## 第41継続更新（cf5154da以降）

追跡版runnerでコミット`cf5154da`の144モデル・5642定理を再検査しPASS（976.283秒、1474モジュール、
manifest `c73e62e7fede78e845ce185f280ea96bfd89b1bef20e3b26dabc4ac250daa4a6`、receipt
`dc57d67e22ea1d701164a0b9f09dd0d366c8710b7886e95877e1ec063385f6d6`、graph
`1999c10334e6cd13ded4f935811c1dc7a9c67fd1df3eca43591d498d276629f7`）。
## 第42継続更新（cf5154da以降）

反復27では索引半分の輸送と2つの局所化衝突の質量計算を採用した。いずれもOpusによる敵対的レビューを経ており、
**両方のレビューが実質的な欠陥を指摘した**。

`Audit.Wire3.IndexHalfTransport`（38定理・8定義）: AdaptiveAssemblyFailureが未評価の`oracleProbability`として
運搬していた索引項を評価し、適応系列の組立失敗上界を単一定数にした。要は2つの`rfl`である —
`realized_run_proof_used`（実現runの`used`は`defaultClaims`）と、鎖の比較`raw_extended_no_clash_subset`
（拡張shapeの無衝突事象は採用済みstrategic shapeの`22+5d`段のそれに含まれる）。補集合は1つだけ課金され、
結果は`combinedBound + 2·tauTerm + indexStage(indexStage+1)/2/|Block|`、右辺に`oracleProbability`は残らない。
**レビューが採用済みツリーに遡る空虚性を発見した**: `adaptiveAssemblyFailureEvent`は受理を連言項に持つ
（含意の否定でその前件が`Integrated.verify … = .ok ()`）。採用済み`Integrated.verify`は`Verifier.verify`に終わり
（`Integrated.lean:59-66`）、`Verifier.shape pin c p = true`でなければ拒否し（`Verifier.lean:415`）、shapeは
`p.used`の3つの長さを構成に固定する（`Verifier.lean:139-141`）。ところが実現runの`used`はfixtureの
`Verifier.testProof.used`（長さ`1, 1, 0`）のままである（`Verifier.lean:596-600`、`RunLevelTransportAudit.lean:582-587`）。
したがって受理は`numRouted = 0 ∧ numConstants = 1 ∧ numWires = 1`を強制し、**それ以外のあらゆる構成で失敗事象は空**、
採用済みAAFの閉実例`adaptive_assembly_bound_at_thirteen`を含め上界は空虚に真だった。`degreeBits`と`numPublicInputs`は
固定されない（`logRounds`/`gateRounds`/`publicInputs`は上書きされる）、退化構成では`Verifier.width c = 1`なので
`constituentWidth := 1`は追加の固定を与えない。本モジュールは両方向で処理した。第一に空虚性を定理として記録する
（`shape_forces_degenerate_config_at_fixture_claims`、`acceptance_forces_degenerate_config_at_fixture_claims`、
`adaptive_assembly_failure_event_is_empty_at_nondegenerate_config`）。第二に`used`をパラメータにして障害を除去する:
`realizedRunProofWith u`は`defaultClaims`で採用済み`realizedRunProof`と、`constantClaims u`で採用済み`rawRealizedRun`と
**定義的に一致**する（ともに`rfl`）ので採用済み補題がそのまま転送し、外側半分は`used`を読まないため無改修である
（`outer_bad_event_at_claims`）。payoffは`shape_satisfiable_at_matching_claims` — `matchingClaims c`ではshapeの
**5つの`used`連言すべて**が`c`自身で成立し、長さによる障害は消える。受理が提示されたとは主張しない（残るshape連言と
`Verifier.envelope`は未決として明示）。適応プローバの自由度は結合round messageと statement 5欄のみであり、
`used`/`whirTranscript`/`whirHints`/`protocolVersion`/`constituentWidth`はfixture定数である。

`Audit.Wire3.LocalizedCollisionMasses`（80定理・19定義＋4略記）: CommittedTablesClausesが残した2つの局所化衝突の
ROM質量を計算した。固定ペアの衝突質量は**ちょうど**`1/|Block|`である（`adaptive_fresh_step_card`自体が等号で標的が単集合。
片側版は`fresh_coordinate_probability`）。退化枝は実在し、ROM oracleの`Q`外既定値が`zeroDigest`であるため両文字列が`Q`外なら
質量は1になる（`degenerate_branch_has_mass_one`）。**レビューはより強い定理を証明して返し、それを採用した**:
和集合のサロゲートは構成の族`F`ではなく**クエリ集合**である。符号化クエリが`Q`内に落ちる構成は`Q.erase (configQuery c₀)`で
添字付けられ各項は`≤ 1/|Block|`、`Q`外に落ちる構成はoff-`Q`既定値により**単一の固定事象**へ潰れる。よって
`any_config_collision_mass_le`は「**何らかの**構成が配備済み`c₀`と衝突する」質量を`≤ (Q.card + 1)/|Block|`で抑える —
`Verifier.Config`全体で量化し、族を一切名指ししない。前提は`configQuery c₀ ∈ Q`のみである。
`any_config_collision_mass_le_at_the_bounded_queries`が`Q := boundedQueries L`を代入して既存の
`config_query_mem_bounded_queries`で仮定を落とし、和集合項は採用済みのクエリ長モデルが所有する量になる。行側も
`hR : R ⊆ Q`から同様に従う。`F`版は「粗い族ごとの読み」として残置し、`config_family_collision_event_subset_any`により
損失なく捨てられることを示した。**負の結果も記録した**: `joinFailureEvent`は`CanonicalProofCheck.DeployedFacts`を
連言項に持ち、その`pinnedDigest`欄が表座標を`configQuery c₀`に固定するので、**任意の**述語`X`に対して
`deployed_facts_alone_costs_the_whole_birthday_term`が質量`≤ 1/|Block|`を与える。`X := True`でも看板は成り立つ以上、
`fixed_tables_costs_a_birthday_term`の数値はbirthday項ではなく条件付けから来ており、その節の実質は包含
`join_failure_event_subset`の側にある。R1bは常に仮定のままで証明も弱化も供給もせず、joinは主張せず、`joinFailureEvent`が
非空とも主張しない。`hc₀ : configQuery c₀ ∈ Q`は採用済み対応物のない**追加仮定**である（採用済み
`committed_tables_join_up_to_collisions`はkhashにクエリ集合側の条件を課さない)。

本バッチは採用済み2モジュールの文言も訂正した。`RunLevelTransportAudit`の honesty 項目(vii)は
「以下のすべての定理はproofを`Verifier.statement`と`roundMessages`経由でしか読まない……`Verifier.shape`はこれに対して
一度も主張されない」と述べていたが、これは当該モジュール自身の定理については真でも**下流では破れている**。破れは2種類あり、
(a) fixture欄が読まれる（AAFの`suppliedCellsAt`が`p.used`を読む）、(b) shapeが主張される（失敗事象が受理を連言項に持ち、
受理はshapeを含意する）。(vii)を全面差し替えし、fixture継承欄を読むか shape/受理を主張する下流モジュールは当該欄を
パラメータ化するか空虚性を開示せよと明記した。`AdaptiveAssemblyFailure`には空虚性の項目を追加し、
`adaptive_payoff_hypotheses_satisfiable`の「したがって上記のどれも空虚ではない」という**推論そのものが無効**である
（仮定の充足可能性は上界を付けた事象の非空性ではない）ことを明記した。

両モジュール合わせて146モデル・5760定理。今回もROMの法則下の結果であり、keccakの性質でも系の健全性誤差でもない。
残るのはR1b（全列のroot決定性）、回路の真値、受理の提示、そしてgrindingプローバの結合である。

## 第43継続更新（9c52fd74以降）

追跡版runnerでコミット`9c52fd74`の146モデル・5760定理を再検査しPASS（1001.957秒、1476モジュール、
manifest `4da8af10a07d7d36376d43c85863112e52f0c4e19939fd293c3e62bb6420f95a`、receipt
`595a8b2ff9be2ca8ba49a9cf3aa8e24b3a2bce2cc8d68479e1c90e50ddb5c480`、graph
`10ab26d5cd043f6b9096a619648f4e645ef28f0bff86034ca1949252dadf3fc2`）。

この更新の時点で、適応系列の受理前件について**退化の原因が2つ独立にある**ことが分かっている。
第一は`used`主張のfixture（本バッチのレビューが発見）で、shapeが3つの主張リスト長を構成に固定するため
`numWires = 1 ∧ numRouted = 0 ∧ numConstants = 1`を強制する。これはIndexHalfTransportの`realizedRunProofWith` /
`matchingClaims`で除去した。第二は自明なengineの索引サンプリングであり、こちらは未除去である:
`Verifier.testEngine.sampleIndices = fun _ _ _ => ⟨[], []⟩`（`Verifier.lean:605`）で
`derivedIndices e c p = e.sampleIndices … c.indexBits`（`:389-391`）であるところ、`verify`は
`idx.log.length = c.indexBits ∧ idx.gate.length = c.indexBits`でなければ拒否する（`:420-421`）ので`c.indexBits = 0`が強制される。
ところが`envelope`は`width c ≤ 2 ^ c.indexBits`を要求する（`:104`、`:413`で検査）ので、`indexBits = 0 ⇒ width c ≤ 1 ⇒ numWires ≤ 1`と
なり、`used`に一切触れずに同じ退化へ到達する。したがって非退化構成での受理の提示には、パラメータ化された`used`記録と、
`c.indexBits`長のリストを返すengineの**両方**が要る。`sampleIndices`は`c.indexBits`を引数として受け取るので、
モデルengineについては第二の原因は安価に外れる見込みである。採用済みの唯一の受理実例`positive_model_verification`
（`Verifier.lean:612`）は`testConfig`（degreeBits 1・numWires 1・indexBits 0）での成立であり、明示engine
（`SoundnessAssembly.engine`）での受理はWHIR tailとgate評価を要する別格の目標である。

## 第44継続更新（9c52fd74以降）

反復28では受理の提示とgrindingプローバのlane対応付けを採用した。いずれもOpusによる敵対的レビューを経ており、
**両方のレビューがモジュール自身より強い定理を証明して返し、同時に誤りを指摘した**。

`Audit.Wire3.NonDegenerateAcceptance`（68定理・15定義）: 適応系列の受理前件が現実的な構成で充足不能だった理由は、
第43継続更新の時点では2つと見ていたが、**実際には4つあった**。(1) `used`のfixture、(2) 自明engineの索引サンプリング、
(3) fixtureの`initialObservation`が1要素の`logTau`/`gateTau`を返すこと（`verify`は`i.logTau.length = c.degreeBits`でなければ
拒否する（`Verifier.lean:420`）ので`degreeBits = 1`が強制される）、そして(4) integrated経路では`Norm.checkedNormEvaluation`が
`logChallenges.length = 7`を要求する（`Norm.lean:353`）一方でfixtureのリストは空なので、
`Integrated.verify Verifier.testEngine … = .error .configuration`が**無条件に**成立する。(4)は既知のどの原因よりも強い事実である。
(1)(2)(3)は任意のengine・pin・chain・構成・proofで定理化した。

payoffは`model_acceptance_at_the_maximal_config`（`rfl`）である。動かしたengine欄は`sampleIndices`と`initialObservation`の
**2つだけ**で、`degreeBits 13`・`numConstants 80`・`numRouted 80`・`numWires 160`・`numSelectors 4`・`numGateConstraints 123`・
`quotientDegree 8`・`gateRows 255`・`indexBits 8`（width 160）という**`Verifier.envelope`の上限そのもの**の構成で
`Verifier.verify`が受理する。`degreeBits + indexBits = 21`は`PinnedWhirProfile.maxProfileVariables`にちょうど一致する。
この実例は同時に、動かさなかったfixture欄のどれも`Verifier.verify`内で構成量を固定していないことの**構成的**証明でもあり、
欄ごとの列挙よりも強い。採用済みツリーにあった destructor `Verifier.verify_success_checks`に対する**構成子**`verify_of_checks`を
新設し、それにより上限内の全WHIRトランスクリプト・ヒント列に対するパラメトリック受理も与えた。`Integrated.verify`も
同じengineと同じ代用デコーダのまま15 wiresまで届く。

限定は厳格である。これらはモデルengineであり、採用済み`SoundnessAssembly.engine`ではない。`Verifier.verify`の9ゲートのうち
§5で**実計算は3つだけ**（envelope、shape、tau/index長）であり、6つはfiatである（chainId、`configurationHash`は定数`testRoot`、
`deploymentValid`は定数`true`、log/gate terminalは任意の引数で定数`zero`、`whirTail`は定数`true`）。さらにどのゲートも見ない退化が
2つある: 導出トランスクリプトは任意の構成・proofで**空のバイト列**であり、この実例にはFiat–Shamir依存性が一切ない。
また修復後のサンプラは**全ゼロの索引点**を返す — 修復したのはlaneの**長さ**であって**中身**ではない。§6は11ゲート中7つが
実計算で、`normResult`と`gateResult`は実際に計算され、ゼロのnorm helperでは実際に失敗した（`Norm.one`が現れる理由である）が、
そのWHIRゲートは構成上反証不能である（echoする`parseWhir`は任意のcontextと任意のproofで`verifyWhir`を真にする）。
したがって本モジュールは採用済み`AdaptiveAssemblyFailure.adaptiveAssemblyFailureEvent`を非空にはせず、
`IndexHalfTransport`が記録した空虚性も解除しない。主張は「**`Verifier.shape`の長さ固定と`Verifier.envelope`だけでは、
非退化構成での受理を不可能にしなくなった**」ことに限る。残る障害を明示engineについて局在化することも主張しない:
その`deploymentValid`（`PinnedWhirProfile.canonicalProfileCheck`）は`1 ≤ numVariables ≤ 21`という**数値**制約を含んでおり、
envelopeと同種の算術だからである。レビューは9ゲートの内訳を数え上げ、「独立に証明した」（実際は採用済み定理の定義的な転記で、
採用済みツリーに何も足していない）と「パラメトリック版はLeanの再帰深度を超えるため出せない」という**2つの偽の主張**を
指摘して撤回させた。後者はレビュア自身が`set_option`なしで証明して反証した。**Leanに証明できないという否定的主張は
kernelで検査されない** — 「自分のスクリプトでは閉じなかった」はスクリプトについての証拠であって、証明可能性についての証拠ではない。

`Audit.Wire3.GrindLanePairing`（102定理・15定義）: 採用済み`GrindingUnionBound`が自ら「未提供」と明記していた2つの穴を閉じた。
**(A) q=0の同一性**: probeを行わないgrindingプローバは採用済みraw戦略と一致し、GUBの見出しから採用済み
`RawBlockLanes.raw_full_bad_draw_probability_le_combined`が**導出される**（衝突項は`(22+5d)(0+1) = 22+5d`に潰れる）。
無衝突事象の一致は合同ではない: 採用済み`stageNoClash`は鎖の`n`個の**答ブロック**の`noClash`に`avoidBase`節を加えたものであり、
`grindingNoClash`は`n+1`個の**段ダイジェスト**の対ごとの相異であって、両者は添字シフトと`digestBlock`の単射性を経て初めて一致する。
この還元が循環していないことは、保存された証明項に対する**推移的定数依存走査**で確認した: 採用済みraw上界には到達せず、
GUBの見出しには到達する（触れる`RawBlockLanes`の定数は文中に現れる`rawFullBadEvent`だけである）。
**(B) 対応付け**: 採用済みの部分デコーダ`Spongefish.decodeCanonicalExt3`を全域化した`elementOfBytes`により、
laneのround `r`メッセージがgrinderの段`22+5r`における吸収ペイロード**そのもの**であることを示した。走行が実際に問うバイト列の
中身であって再符号化ではない。しかも**条件付け事象を要しない**: 段`j`の列は段`j`ダイジェストに沿ったoracleの引き戻しであり（`rfl`）、
ダイジェストが衝突しても情報は失われないからである（ハッシュ衝突とは構造が異なる）。ダイジェスト添字と段添字の型の不整合は
`digestLookup`の全域性が定義だけで閉じるが、その**正しさ**は`grinder_table_view_determined`が担っており、反例によりそれが
本質的であることも示した。

適用範囲は正確に確定した: `ChallengeRestricted`であって全段で吸収ペイロードが`min 120 (24*(quo+2))`バイト以下のgrinderである。
採用済み`quo = 8`では120バイト、すなわち**5個の符号化元**であり、予算は採用済みの次数予算そのものである。6個を吸収する
`longMessageGrinder`はちょうど1元だけ外側で、そのペアlaneの質量は何も抑えていない。ペイロード上界は**結合段でのみ**必要であり、
非結合段で144バイトを吸収する`mixedGrinder`は一様な仮定では除外され結合段限定の仮定では覆われる — 非結合段でWHIRのMerkle rootや
最終多項式を吸収する現実的なプローバがこれに当たる。**バイト予算より大きな制限**も記録した: `grinderLane`が入れるメッセージは
段`22+5r`の唯一のペイロードなので、log laneとgate laneは**同一の**roundメッセージを運ぶ。プロトコルではこの2つは別個の
結合プローバメッセージである。`truth`と`claim`は採用済み`RawBlockLanes`と同様に自由なままである。デコーダの採用済み部分デコーダとの
一致は**一方向**であり、その定義域（長さがちょうど24かつ3つのlimbすべてがmodulus未満）の外では全域化が値を発明する:
配備パーサが拒否する2つの異なるペイロードが同一の非空メッセージを得る。これは保守的であって不健全ではないが、
定義域外でのlaneメッセージはモデル上の選択であってverifierの読みではない。`selectorGrinder`は**攻撃ではない**:
probe 0を読んで2つの定数メッセージに分岐するだけで、再探索も検索もしない（GUB自身が自らの`probeGrinder`について同じことを
述べている）。検索するプローバ`preReadGrinder`を除外しているのはバイト予算ではなく`ChallengeRestricted`であり、
GUBのpre-readの穴はそのまま残る。

両モジュール合わせて148モデル・5930定理。今回もROMの法則下の結果であり、keccakの性質でも系の健全性誤差でもない。
残るのはR1b（全列のroot決定性）、回路の真値、明示engineでの受理、そしてFiat–Shamirのchallenge grindingの課金である。

## 第45継続更新（d0f31900以降）

追跡版runnerでコミット`d0f31900`の148モデル・5930定理を再検査しPASS（997.077秒、1478モジュール、
manifest `5a9f257ef5c0cd88f5b0182aa54df1bca5639a09d90ae71b1480453adaa41c5e`、receipt
`eb84d036965584f4e411e8587db562c73f9234e5989045fc18e08c6fb78636c6`、graph
`8d2eb3616f040965d20fbcaef6c4e6843e832f37887506515e64e16976c93017`）。

この更新の時点で、受理はenvelopeの上限構成で提示されているが、**修復されたのはlaneの長さであってlaneの中身ではない**。
受理実例の導出トランスクリプトは任意の構成・proofで空のバイト列であり、Fiat–Shamir依存性が一切ない。また索引サンプラは
全ゼロの索引点を返す。したがって次の実質的な一歩は、`initialTranscript`と`sampleIndices`がproofの真の関数であるengine
（明示engineでなくてよい）で受理を出し直すことであり、そのうえで初めてWHIR tailと実gate評価を要する明示engineでの受理が
射程に入る。明示engineの`deploymentValid`のうち数値部分（`1 ≤ degreeBits + indexBits ≤ 21`）は上限構成で充足可能と
分かっている。

## 第46継続更新（d0f31900以降）

反復29では受理実例を明示engineまで押し上げ、grindingのlane対応付けを2本に分けた。いずれもOpusによる敵対的レビューを経ており、
**両方のレビューがモジュール自身より強い結果を証明して返し、同時に誤りを指摘した**。

`Audit.Wire3.DerivedAcceptance`（104定理・16定義）: 第45継続更新は「修復されたのはlaneの長さであってlaneの中身ではない」と記した。
本モジュールはそれを解消する。受理しているengineは`ExplicitEngine.explicitEngine`から`parseWhir`と`whirTail`の**2欄だけ**を
fixtureに戻したものであり、これは`rfl`で成立する（`derived_engine_is_the_explicit_engine_minus_the_whir_pair`）。12欄中10欄が
採用済みの実コンポーネントである。見出し`derived_acceptance`は`thash`と`khash`を**全称量化**し、ハッシュの性質を一切使わない。
`Integrated.verify`経由の版も成立する。依存性は4つの定理で記録した。うち`derived_transcript_depends_on_the_proof`は
「または`thash`が衝突する」形で出荷しており、無条件版が`constantHash`で**反証される**ことをwitnessによって**肯定的に**記録する
（否定を主張として書かないための作法であり、レビューはこれを本監査で最良の開示実践と評した）。

**誠実なゲート数は9中4である。** 実際に失敗し得た算術を持つのは(3)envelope、(5)shape、(6)tau/index長、(9)gate dispatcherだけである。
(2)と(4)は`rfl`で閉じる: `derivedPin`が`khash (encodeConfig derivedConfig)`として**定義されている**以上、構成ハッシュのゲートは
失敗しようがなく、配備ピンも`c = derivedConfig`では反射的である。さらに(2)の束縛性には**本モジュール自身の量化子の内側に抜け道**が
あり、定数`khash`では`derivedConfig`から計算したpinが**異なる構成**を受理する。(7)は`numRouted = 0`のため`Norm.runWires`が
0回しか走らず、`denominatorTerms`・`formalNorm`・`formalAdjugate`・logup対・λ梯子のいずれも実行されない。結果として終端は
**あらゆる**観測・点・主張記録でゼロであり、**どの2つのproofも区別できない** — 2つのproofを区別できないものはガードではない。
(9)は実際に走るが最小である（14 gate族中1、255行中2、123制約中1）。全称量化は論理的には任意の代入より強いが、
同時にハッシュ依存ゲートを**非束縛**にする。「あらゆるトランスクリプト・構成ハッシュで」は受理の一般性についての主張であって、
ガードの強度についての主張ではない。

構成は`degreeBits 13`・`numWires 160`・`numConstants 80`・`indexBits 8`・`quotientDegree 8`（envelope上限、採用済み
`maximalConfig`と同値）まで達するが、**`numRouted = 0`**である。これは元の退化が強制した3つのピン
（`numWires = 1 ∧ numRouted = 0 ∧ numConstants = 1`）の1つへの**復帰**であり、採用済みツリーが特に修復した退化に戻っている。
したがって**本実例は採用済み`maximalConfig`を支配せず、両者は比較不能である**。本モジュールはengineで優り、採用済み実例は
`numRouted`・`numSelectors`・`numGateConstraints`・`gateRows`で優る。両者を組み合わせて結論を導くことはできない。
レビューは後退がむしろ**過大申告**であることも示した: 同じengine・同じ全ゼロ主張記録のまま`numPublicInputs = 3`でも
`quotientDegree = 8`でも受理が再提示され、後者は`derivedConfig`自体に取り込んだ。実コンポーネントが強制するのは`numRouted = 0`
だけで、`numPublicInputs = 0`は`Integrated.verify`に限り、しかも`numRouted = 0`の**下流の帰結**として強制される
（`Norm.shapeValid`の`column < c.numRouted`が0では充足不能）。`gateRows`・`numSelectors`・`numGateConstraints`は
**代用デコーダ**由来であって実コンポーネント由来ではない。

`numRouted = 1`での受理は「実例が見つからなかった」ではなく**定理**にした: `matchingClaims`の全ゼロ列により
`idHelper = sigmaHelper = 0`、よって`idZero = sigmaZero = -1`、`logupSum = 0`となり、終端は`eq(τ,point)·(-(1+ρ))`で
恒等的にゼロではない。ゆえに受理は**導出challenge間の偶然の一致と同値**である。抜け道（`denominatorTerms.1`を反転する非ゼロ列）は
ゲート8が導出索引点で`packedFold p.used.logNormInverse (width c) idx.log = zero`を強制するため塞がれており、修復には
`thash`依存の点で消えるpacked foldを持つ非ゼロ列が要る。

残る障害はWHIR parse/tailのみである。採用済みツリーには`InstalledWhirTail.tailRun`が呼ぶ`WhirConfigured.run`の具体的な
`rfl`成功例が**実在する**（`WhirConfigured.lean:637,646`、`WhirTail.lean:902,921`）。ただしそれらはマスク`[⟨7⟩]`・3主張で走っており、
`tailRun`のマスクは`[⟨31⟩]`に固定され本文脈は5主張を担うので**再利用できない**。欠けている補題を名指しした。加えて重要な緊張も
記録した: `WhirInitial.readClaims`はトランスクリプトを当の検証器自身の`packedFold`値（導出索引点での値）に束縛するので、
そのようなwitnessは`thash`依存であり、**WHIR完全な実例は本モジュールの`thash`全称量化を保てない**。
本モジュールは採用済み`AdaptiveAssemblyFailure.adaptiveAssemblyFailureEvent`を非空にはせず、`IndexHalfTransport`が記録した
空虚性も解除しない。当該事象は明示engineと fixture used-claims の**両方**で添字付けられており、本モジュールは`matchingClaims`を
使い、WHIR対はfixtureのものなので、**両方の添字を外している**。

`Audit.Wire3.TwoLaneMessages`（91定理・13定義）: 採用済み`GrindLanePairing`のhonesty項目(v)を撤去する。ただし本モジュールが
運ぶ最も重要な内容は**採用済みgrindingモデルについての発見**である。トランスクリプト鎖では2つの結合セルは別個の吸収であり
（`BirthdayClashBound.roundShapeAt`のframe 2が段`22+(5r+2)`のLOG、frame 3が`22+(5r+3)`のGATE）、しかしlane層では両者は
同一の`S r ch : CoupledMessage`の射影である。そして`GrindCausal`の切断は round `r`のlaneに**どちらのセル段も読ませない**。
したがってgrindingのlineはプロトコルより**厳密に粗い粒度**にあり、単一ペイロードをどう分割してもそれは直らない — 分割はそれを
モデル化できるだけである。欠けている補題は`roundStage r * (q+1)`で切るGUB見出しであり、GUB自身の注記が
`grind_run_view_reassign_lower`は`22+5r < j`しか要らないと記録しているので対角段は生き残る。切断のどの部分が効くかも特定した:
履歴側は段`22+5r+1`を許容し、challenge側（`digestLookup`）が、そして`0 < q`ではprobe側も、切断を強制する。

分割自体は`logHalf = take 120`・`gateHalf = drop 120`で、両laneの対応付けを**条件付け事象なしで**全表について証明する。
`hfitlog`は**消滅**し（log側の半分は構成上120バイト以下）、予算は`p ≤ 360`に**上がる**（5元から15元へ。半分どうしが互いに素なため）。
定数はGLPと項ごとに同一で、結合段限定の`hp`も維持する。**ただし2 laneが分離するのは120バイト超のときだけである。**
それ以下ではgate側のメッセージが**空**になり、すなわちGLPが覆うクラス全体（GLP自身のwitnessを含む）では、2 laneが異なるのは
gate側を**黙らせている**からであって、プロトコルの第二メッセージを与えているからではない。空のgateセルは合法なroundメッセージでは
ない（受理からgate roundは長さ`quotientDegree + 2`、log roundは5が従う）。両方が合法長になるのは360バイトちょうどのときだけで、
そこでの閉実例も出した。この長さ不正はGLPからの**継承**であって本モジュールが開いたものではない（`GrindLaneBounded`は`≤`である）。
因果性についての否定は**全称ではなく存在**の主張に直した: `blindGrinder`ではあらゆる段関数で因果的なので、後段を読むlaneが
因果的でないという全称主張は偽である。存在の形でも一様構成を採用済み見出しに渡せないことを示すには十分であり、障害は特定の
オフセットの人工物でもない（段24以上すべて、gateセル自身の段を含む）。witnessは検索しない（probe 0の答えのみの関数であることを
定理化した）。

両モジュール合わせて150モデル・6125定理。今回もROMの法則下の結果であり、keccakの性質でも系の健全性誤差でもない。
残るのはWHIR tailの成功witness、R1b（全列のroot決定性）、回路の真値、`numRouted > 0`での受理、そしてFiat–Shamirの
challenge grindingの課金である。

## 第47継続更新（175c8a4e以降）

追跡版runnerでコミット`175c8a4e`の150モデル・6125定理を再検査しPASS（1340.382秒、1480モジュール、
manifest `55fc196a60662092fcdd3f40c68b8570f716a5b6629df39fa26c07e8c682f773`、receipt
`e6288e36a10df0e5736f29ac0957ea34208e01935845f1837fec7c4f9f3469d4`、graph
`36e5aea3a308a618d6f68274883f857edd23da4d028183e47699712f1f298823`）。

この更新の時点で、受理ラインに残る障害は**WHIR parse/tailただ1つ**である。次工程はその成功witness、すなわちマスク`[⟨31⟩]`で
5主張を担う文脈での`InstalledWhirTail.tailRun … .isSome = true`（`InstalledWhirTail.lean:1122-1130`の`= none`の双対）である。
既知の障害は、両ストリームの厳密なEOF（`WhirFinal.exhausted`）、3つのpinされたrootがトランスクリプトにliteralに現れ
`Merkle.verify`を通ること、そして配備プロファイルの実PoW閾値が実際のnonceを要することである。
**あらかじめ記録しておくべき緊張がある**: `WhirInitial.readClaims`はトランスクリプトを当の検証器自身の`packedFold`値
（導出索引点での値）に束縛するので、そのようなwitnessは必ず`thash`依存になる。したがってWHIR完全な実例は
DerivedAcceptanceの`thash`全称量化を**保てない**。次の反復では両者のどちらを取るかを選び、その選択を明示することになる。

反復30は両方を取り、どちらを取ったかを定理として記録した。

`Audit.Wire3.WhirTailWitness`（56定理・11定義）: installed水準のWHIR成功を初めて具体的に示す。採用済みの具体評価はすべて
否定（`InstalledWhirTail.example_empty_hints_fail_the_concrete_tail` の `tailRun = none`、
`InstalledWhirParse.example_concrete_parse_rejects_the_empty_transcript`）だった。成功は仮説か受理前提の存在結論だけだった。

**段1–2。** 3主張では `installed_tail_succeeds_on_a_concrete_transcript` と `witness_verify_whir_is_true` が
`InstalledWhirTail.tailRun … .isSome = true` と `Verifier.verifyWhir = true` を出す。6主張（`Verifier.expectedClaims` の配備Arity）では
`configured_six_claim_execution_example` が `WhirConfigured.run` の成功を `rfl` で出す（408トランスクリプトバイト、72ヒントバイト、
両ストリーム exact EOF。レイアウトはコミット認証192ゼロバイト + 6主張144バイト + 初期sumcheck `(1,0)` + 終端ベクトル `1`）。
それを `installed_tail_succeeds_at_a_six_claim_context` / `six_verify_whir_is_true` が `tailRun` と `verifyWhir` へ持ち上げる。
`six_context_is_the_derived_context_of_the_installed_engine` により6主張文脈は `Verifier.testConfig` 上で outer verifier が導出する
`derivedContext` そのものであり、`installed_whir_gate_is_true_at_its_own_derived_context` は手渡し文脈ではなく
エンジン自身の WHIR ゲートが `true` を返す。

**段3。** `installed_whir_pair_accepts_a_full_verification` は `parseWhir` と `whirTail` の両方を installed にした
`Verifier.verify (sixEngine …) ⟨1, testRoot, testRoot⟩ 1 Verifier.testConfig sixProof = .ok ()` を `rfl` で出す。
`set_option maxRecDepth 8192` / `maxHeartbeats 1000000` を当該宣言だけに狭めた（採用済みの同種定理は 65536）。

**前提の訂正。** マスク `[⟨31⟩]` 対 `[⟨7⟩]` はブロッカーではない。`WhirInitial.readClaims` は `0..expected.length-1` しか見ず、
0,1,2 でビット一致する（`the_two_masks_agree_below_three`）。`configured_run_mask_congruent` が一般形で、マスクが
`WhirConfigured.run` に入るのは `checkBound` の長さガードと `readClaims` だけだと示す。実障害は主張数で、
`the_two_masks_do_not_agree_below_six` が6主張では一致が壊れること、`configured_six_claim_execution_example` がそれを外すことを示す。

**これは明示engineでの受理ではない。** `accepting_engine_field_ledger` が欄を列挙する: `sixEngine` は `testEngine` に
`parseWhir` / `whirTail` / `commitRound` / `sampleIndices` を載せたもので、`foldClaim`・`normEvaluation`・`eqEvaluation` も具体だが、
`initialObservation`・`publicInputsHash`・`configurationHash`・`deploymentValid` の4欄は抽象観測のまま。これは
`DerivedAcceptance`（10欄具体、WHIR対が fixture）の**補集合**であり、どちらも12欄すべてではない。
構成は `Verifier.testConfig`（`degreeBits = 1`、`indexBits = 0`）であり `DerivedAcceptance.derivedConfig`（21変数）ではない
（`the_accepting_configuration_is_not_the_derived_one`）。ハッシュは定数 toy（`the_witness_hash_is_constant`、
`the_witness_hash_ignores_every_input`: 追加72バイトの claim は sponge digest を動かせない）。
プロファイルは `exampleNoRounds`（PoW閾値はすべて `maxCounter`。`the_witness_profile_is_not_the_deployed_shape`）。
`thash` は供給文脈（`witness_verify_whir_is_true` / `six_verify_whir_is_true`）では `e`・`gdec`・`thash` を全称量化し、
導出文脈では `InstalledRoundCommit.toyHash` にインスタンス化する。21変数の witness は未構成で、不可能とも主張しない。
敵対的レビューは PASS-WITH-FIXES（見出しに NOT derivedConfig / NOT explicitEngine を先に書くこと、
`the_witness_hash_ignores_every_input` の追加）。

`Audit.Wire3.RoutedAcceptance`（111定理・13定義）: `numRouted = 80`（envelope 上限、採用済み `maximalConfig` と同値）での受理を、
採用済み `DerivedAcceptance.derivedEngine` と採用済み `IndexHalfTransport.matchingClaims` のまま示す。見出しは

    Verifier.verify (DerivedAcceptance.derivedEngine routedHash khash P) (routedPin khash) 1
      routedConfig routedProof = .ok ()

（`routed_acceptance`。`khash` とプロファイル `P` は全称、後者は `profileOk` 仮説の下。仮説は stand-in と sharp プロファイルで放電:
`routed_acceptance_at_the_profile_witness` / `routed_acceptance_at_the_sharp_profile`）。`Integrated.verify` 版もある
（`routed_integrated_acceptance`）。`routedConfig` は `derivedConfig` の `numRouted` だけ 0→80 し `kIs` を揃えたもので、
他欄は動かしていない（`routed_config_agrees_with_the_derived_config_off_the_routed_wires`）。
`numPublicInputs = 3` の第二実例（`routedPublicConfig`）は `numRouted > 0` でのみ可能で、`Norm.shapeValid` の
`column < numRouted` を `routed_public_targets_are_in_range` が放電する。

経路は(b): 採用済み `probe_acceptance_at_one_routed_wire_forces_a_challenge_coincidence` の第2因子 `1+ρ` を消す。
`routedHash` は challenge 入力の末尾8バイト（カウンタ）だけを見て、カウンタ3で `modulus-1`、4と5で0、それ以外で2を返す。
関係状態のカウンタ3,4,5が `ρ` なので、あらゆる構成・statement で `ρ = -1`（`routed_rho_is_minus_one`）。
digest chain は評価されない。経路(a)（非ゼロ norm-inverse 列が導出索引点で fold 0）は未発見で不可能とも主張しない。

ゲート7は80回の wire loop（`routed_wire_loop_runs_eighty_times`）、160回の `denominatorTerms`、80段の λ 梯子
（`routed_lambda_ladder_runs`）を実行する。組み立ては `NonDegenerateAcceptance.verify_of_checks` でゲートごと、`set_option` なし。

**ただしこれは最後の退化ピンの除去ではない。** 敵対的レビュー（PARTIAL。見出しの「last pin removed」読みは偽）が確認し、
モジュールへ採用した事実: `routed_hash_is_a_transcript_collision`（digest を無視するので同じカウンタの異なる digest が衝突）、
`rho_ignores_the_statement`、および `routed_lambda_is_two_everywhere` / `routed_kappa_is_two_everywhere` /
`routed_beta_is_two_everywhere`（いずれも構成と statement で全称なので導出 challenge は statement に依らない）、
`alt_proof_is_also_accepted`（`normInverseRoot` だけが異なる第2の proof も受理。`Verifier.shape` が pin するのは
`preprocessedRoot` だけ）。`dependence_implication_holds_because_the_hash_collides` は採用済み依存含意の衝突選言がここで真だと示す。
`DerivedAcceptance` が `constantHash` を依存の**反証 witness** として使ったのと同じ退化したハッシュ族を、本モジュールは
**受理ハッシュ**として使っている。**見出し: 受理ラインはいま routed wires と proof依存challengeの両方を持っていない。**
3実例はすべて比較不能: derived は `thash` 全称で本実例は collapsing hash を受理に使う。maximal は fixture engine で
`numSelectors`/`numGateConstraints`/`gateRows` が上。WHIR対は依然 fixture。ゲート2は `routedPin` が `khash` から定義されるため
依然 `rfl` で閉じる。

両モジュール合わせて152モデル・6292定理。今回もROMの法則下の結果であり、keccakの性質でも系の健全性誤差でもない。
残るのは21変数のWHIR成功witness（derivedConfigへの接続）、digestを実際に使う`thash`での`numRouted > 0`、
ゲート7が2つのproofを区別する具体的拒否例、R1b（全列のroot決定性）、回路の真値、そしてFiat–Shamirの
challenge grindingの課金である。

## 第48継続更新（84e7c54c以降）

追跡版runnerでコミット`84e7c54c`の152モデル・6292定理を再検査しPASS（1054.723秒、1482モジュール、
manifest `fdeb30545b31e6e7387c0eaea9789c11a3e60e0b8a990ca3e18855abfdb26469`、receipt
`1762988f8561a9e65fa340383a3ed2eda1b56d6c004dbdb87c1d8e62ce0a6d06`、graph
`7be1b47866c711e4c5f9d813917ed8cc00167bd2125c64ea657b7682cf3b1854`）。

この更新の時点で、受理ラインは routed wires と proof依存challengeの両方を持っていない。
バッチ40の定理名・段・engine欄・ハッシュの定義は第47継続更新と「主要定理の入口」の直近表に書いた。
WHIR成功は installed 水準で具体化されたが、構成は`Verifier.testConfig`（1変数）、ハッシュは定数toyであり、
`DerivedAcceptance.derivedConfig`（21変数）への接続は未構成である。次工程は digest を実際に使う
`thash`での`numRouted > 0`、ゲート7が2つのproofを区別する具体的拒否例、21変数のWHIR成功witness、
R1b、回路の真値、そしてFiat–Shamirの challenge grinding の課金である。

## 第49継続更新（057d4b98以降）

反復31は利用者の指示（RoutedAcceptanceの取引を実際に修復せよ）による単一候補で、
`Audit.Wire3.DigestRoutedAcceptance`（119定理・12定義）を採用した。Opusによる敵対的レビューを経ており、
レビューは修復の核が本物であることを確認したうえで、散文の較正欠陥3件を指摘して直させた。

**修復の中身。** `fixedHash`は採用済み`framePrefix`（長さ20）と`challengePrefix`（長さ24）がバイト15で異なることを使って
フレーム/チャレンジ入力をドメイン分離する（`challenge_mark`/`frame_mark`は任意のdigest・タグ・payload・カウンタで`rfl`）。
チャレンジ側はカウンタ3/4/5（受理の消滅論法が必要とするρ = −1とその隣接値）だけ固定し、それ以外は`mixFrom`がdigestを
実際に読む。フレーム側は常にdigestを読む。設計中に2つの事実が確定した: (i) 旧`routedHash`の退化の本体はフレーム側であり、
実質すべてのフレームが定数`twoDigest`に写るので**連鎖全体が定数**だった（`routed_hash_on_a_long_frame`。ラウンド3の
コミットフレームは例外的に`minusOneDigest`へ潰れることも証明された）。(ii) カウンタ符号だけで分岐すると`commitRound`が
吸収する`le 8 round`の末尾8バイトがちょうど`counterTag round`なのでラウンド3–5で連鎖が崩壊する — バイト15の判別子は
装飾ではなく必要である。

**見出し`fixed_acceptance`**: 採用済みの`routedConfig`・`routedProof`・`routedPin`・`matchingClaims`を一切変えず、
ハッシュだけ差し替えて`numRouted = 80`で`Verifier.verify`が受理する。`khash`とプロファイル`P`は全称（stand-in/sharp両方で
放電）、`Integrated.verify`版と`numPublicInputs = 3`構成も継承。組み立ては`verify_of_checks`でゲートごと、`set_option`なし。

**修復が本物であることの対比定理対**: 旧ハッシュでは`routedProof`と`normInverseRoot`だけ違う`altProof`の導出初期
トランスクリプトが**一致**し（`routed_initial_transcripts_do_not_separate_the_two_proofs`）、新ハッシュでは**分離**する
（`fixed_initial_transcript_separates_the_two_proofs`、任意の構成・`khash`・`P`）。digest単射性は両枝とも定理
（`fixed_hash_is_injective_in_the_digest`、`frame_hash_is_injective_in_the_digest` — mixByteはmod 256加法で左簡約可能、
`clip 31`はちょうど31バイトのリストに適用され情報を落とさない。レビューが検証した）。

**残余の台帳（レビューが検証の結果「正しい」と確認）**: 導出102回＋ラウンド78回＋索引48回 = 228回の絞り出しのうち、
digest盲目なのはカウンタ3/4/5の48回（ρ・γと各段の3/4/5）で、180回がchainを読む（旧`routedHash`: 0/228）。
最初の2つの和は定理化した（`derive_squeeze_counts`、`a_round_squeezes_six_from_counter_zero`）。カウンタ盲目性の記述は
8バイトLE符号化にスコープする: `counterTag (2^64+3) = counterTag 3`だが（`le 8`はmod 2^64）、そのエイリアスは
squeezeのカウンタ上限の外で到達不能（`the_aliased_counter_is_out_of_squeeze_range`）。

**chain状態は1バイト幅である（見出しの重みで開示）**: `mixFrom`は32バイト読むが1バイトしか書かず、末尾31バイトは
入力digestのものをそのまま持ち越す。開始状態は全ゼロなので、任意の構成・statementで導出chainのdigestは可変1バイト＋
ゼロ31バイト（`derive_digest_tail_is_thirty_one_zero_bytes`）— 連鎖は高々**256個**のdigestしか通らない。
「228中180がchainを読む」はその1バイト状態を読むという意味である。復元されたのはFiat–Shamir依存の**構造**
（どのchallengeがどの吸収の関数か）であって量的衝突耐性ではない（`fixed_hash_is_still_a_transcript_collision`を
敢えて証明し、衝突フリー性は主張しない）。

**分離はfold特異的（対比の対の真隣に配置）**: 分離定理は fold 34対35の一対についての事実である。foldが等しい対
（`normInverseRoot` 1と256、どちらもfold 35）は新ハッシュでも導出初期トランスクリプト全体が一致する
（`fixed_hash_does_not_separate_the_other_root_pair`）。どの対が分離するかは1バイトfoldの性質であってstatementの
相異の性質ではない。

**正直な否定**: `alt_proof_is_still_accepted` — ゲート7はnorm-inverse列（両proofでゼロ）とρ（両方−1）しか読まず、
ゲート8は`normInverseRoot`を比較するはずだがfixtureの`parseWhir`が文脈rootをechoする
（`fixture_parse_echoes_the_context_roots`）。2つのproofの分離は経路(a)（非ゼロnorm-inverse列）かinstalled WHIR parseを
要する — 構成していないし不可能とも主張しない。

**取引台帳**: RoutedAcceptanceよりハッシュで厳密に良く、それ以外は同一（`same_instance_as_the_adopted_routed_acceptance`、
全`rfl`）。DerivedAcceptanceとは依然比較不能（`thash`はここでは代入、あちらでは全称 — その量化子が依然価格であることを
見出しの重みで明記）。maximalConfig台帳は再輸出のまま。**最後の退化ピンが除去されたとはどこにも書いていない**:
正直な主張は「routed wiresと（228中180の）proof依存challengeが両立するようになった。残余48回と1バイト状態幅と
fixture WHIR対を名指しのうえで」である。

1モジュールで153モデル・6411定理。今回もROMの法則下の結果であり、keccakの性質でも系の健全性誤差でもない。
残るのは、状態幅を広げたハッシュ（またはρの盲目性も外す具体連鎖プログラミング）、ゲート7が2つのproofを区別する
具体的拒否例（経路(a)かinstalled WHIR parse）、21変数のWHIR成功witness、R1b、回路の真値、
Fiat–Shamirのchallenge grindingの課金である。

## 第50継続更新（c0572083以降）

追跡版runnerでコミット`c0572083`の153モデル・6411定理を再検査しPASS（1018.227秒、1483モジュール、
manifest `898d80048d4b1ef366f5f401053ea9c130f80eab38d16eb47901b442022c8476`、receipt
`a42b3766ced743fb5efd8c2990495aa78e70dda143b4535787c3f3f46866c169`、graph
`b5bd65577bee19cab4d8b751e5947749102e344b0719583a93eb8d96d233ca5c`）。

この更新の時点で、受理ラインの誠実性の弧は次の段階にある: 検証器が**実行する**（済）、検証器がproofに**依存する**
（済 — ただしchain状態は1バイト幅で、復元されたのはFiat–Shamir依存の構造であって量的衝突耐性ではない）、
検証器が誤ったproofを**拒否する**（未了）。次工程はその最後の一歩 — 経路(a)（導出索引点でpacked foldが消える
非ゼロnorm-inverse列）またはinstalled WHIR parseによる、2つの具体的proofの分離 — と、状態幅を広げたハッシュ、
21変数のWHIR成功witness、R1b、回路の真値、Fiat–Shamirのchallenge grindingの課金である。

## 第51継続更新（c7d285b0以降）

反復32は利用者の指示（「実務上必要」な3証明を終わらせる）による3候補並列で、いずれもOpusによる敵対的レビューと修復を経た。
方針は利用者と確定済み: WHIRプロトコルの数学は文献が担保し、Lean監査は実装忠実性を担う。

`Audit.Wire3.RejectionWitness`（29定理・7定義）: **このツリー初の拒否定理。**
`installed_engine_rejects_the_wrong_root_proof`は、WhirTailWitnessの`sixEngine`（parse/tail両方が採用済みの実物インストール）で、
`sixProof`の`normInverseRoot`だけを変えた偽proofが`.error .invalidProof`になることを`rfl`で示す。locator定理が
`Verifier.verify`の他の全ゲート通過を1連言で特定し、失敗はWHIRゲート、その内部ではparseのroot照合である
（installed parseはトランスクリプトのliteralなcommitmentバイトを文脈のrootと比較する — fixtureのparseは文脈のrootを
echoしており、それがDigestRoutedAcceptanceの`alt_proof_is_still_accepted`の原因だった）。交絡の不在は定理:
`runPrefix`に渡る引数のうちrootリスト以外のすべてが受理時と文字通り同一で、rootを戻すとparseは復活する。もう1つの
非固定root（`witnessRoot`）でも拒否され、fixture対はそれも受理する。**帰属はレビューにより先鋭化した**: WHIR対の各半分が
単独でも偽proofを拒否して正直proofを受理し（4つのhalf-install定理）、偽造の受理には両方の半分がfixtureであることを要する。
量化版として、このengineで受理される任意のproofについて読まれたroot（actualとbound）が
`[testRoot, p.witnessRoot, p.normInverseRoot]`のdigestに固定されることも示した（`rootDigest`は単射）。
r族形（root値の全域で拒否）は未了で、欠落補題を名指しした: `WhirInitial.receiveOne`はexpected = rootを強制するが
`receive_one_success`がそのバイト等式を輸出していない。スコープ: `Verifier.testConfig`（1変数）・定数toyハッシュ・
4欄は抽象観測のまま・installed parseのモデルについての言明であり配備Solidityについてではない。

`Audit.Wire3.R1bBridge`（28定理・15定義＋2構造）: R1b（`rootDetermined`節）を**証明ではなく橋として**閉じる。
初版は無衝突要求を構造の中に全実行∀量化で置いたが、**その形はレビューが本ツリー自身の深さ1 fixtureで`decide`により反証した**
（`Merkle.exampleHash`は`take 32`で、奇数索引1の圧縮入力は`sibling ++ current` — 深さ1のrootは葉に依存せず、同じrootに対して
第2の行が開き、2走行の実行入力が衝突する）。修復後の形が計算論的に正しいスコープである:
`RunPairNoCollision r₁ r₂`（**比較する2つの走行**が実際にハッシュした入力上の無衝突。`Run`構造がhints/startを露出する —
existentialな隠蔽が誤った∀形を強制していた）を各橋定理のper-pair仮説として可視的に運び、構造は1欄の
`WhirDecodeUniqueness`（列は開示をその行バイト経由でしか読まない。走行上で量化。文献引用付き・仮定であり証明せず・
Leanのaxiomではない）に縮む。反証された旧形は削除せず§7に定理として保存し、per-pair形もその特定のfixture対では反証される
ことを注記した — そのcommitmentは実際に束縛的でないのだから、そうあるべきである。橋の実質は
`opened_rows_determined_of_pairwise_no_collision`（採用済み`opened_cells_root_determined_or_collision`のセル単位の一致を、
`group_success_contiguous_rows`の長さ等式と`List.ext_getElem`で行リスト全体の一致に閉じる）。消費は採用済み
`committed_tables_join_up_to_collisions`のhr1b枠に**引数単位で一致**して差し込まれ（レビューが署名を読んで確認 — 当該枠は
1つのopeningを取り、OpeningFreeExtractorを要求しない）、tau表の2枠も単一の`tablesOf`から放電される。帰結の条件文:
同一rootの2つの受理済み走行についてRunPairNoCollisionと復号一意性の下で、受理されたSolidity呼び出しごとに
`CommittedTablesJoin`全体を満たす`tablesOf`が存在する — 例外は`ConfigEncodingCollision`と、実際に開かれた2行上の
`OpenedLeafCollision`のみ。価格付けは一部接続した（サンプル表自身の`leafHashOf Q T`での実例化＋`boundedQueries L`での
クエリ所属）。未確立と明記: 配備ハッシュとサンプル表ハッシュの同定、配備行の行長上界。root命名の但し書き
（`opening_relation_is_root_blind`）・非走行opening・単一rootのスコープは継承。

`Audit.Wire3.DeployedWhirWitness`（49定理・31定義）: WHIR実行witnessが**完全な21変数**（配備の変数数）に達した。
`configured_twenty_one_variable_execution_example`は、実転写`canonicalRow21`のスケジュール（4 | 4,4,4,4 | 1、残差17/13/9/5、
interleaving深さ16）での実折り畳み4ラウンド、配備マスク`[⟨31⟩]`下の6主張、1904トランスクリプトバイト
（shapeの上限ちょうど）/1976ヒントバイト・両ストリーム厳密EOFで、`WhirConfigured.run`の成功を`rfl`で示す。
`installed_tail_succeeds_at_twenty_one_variables`と`deployed_verify_whir_is_true`（parse/tail両方実物）が続く。
パラメータ許可は実物の転写行そのもので行い、非空虚対照も定理化した: 転写行はpointsが空で出荷されるため6主張では
rejectされ、実2^23ドメインと29クエリ数は全構造検査を通過する — 障害はpointsだけである。

**規模の開示（見出しの重み、定理として）**: 正典row-21のin-domainクエリ予算は5段で84（29/19/14/12/10）、本witnessは5 —
16.8倍の削減であり、WHIRのlist-decoding健全性余裕については何も述べない。代用ドメインは`merkleDepth = 0`/
`codewordLength = 1`で、1976ヒントバイト中のMerkle認証パスは**すべて空**である（正典なら深さ23/22/21/20/19で約54kBの
兄弟ハッシュ＋実パス検証）。代用はこの2族のみで、全6 PoW閾値を含む他の全欄は転写値である。

**モデル忠実性の確定（レビューの最重要問への答え）**: 中間sumcheckラウンドが等式を課さないのはモデルの欠落ではなく
配備ワイヤ形式の忠実な転写である。プローバは3つの二次係数のうち2つ（c0, c2）だけを送り、検証器が
`c1 = claim − 2c0 − c2`を**再構成**する（`WhirFinal.lean:144-146`・`SpongefishWhirVerify.sol:454`・vendored
`whir/sumcheck.rs:124` — 3層照合、48バイト/ラウンドの一致まで）。よって`h(0)+h(1) = claim`は恒等的に成立し、検査対象が
存在しない。健全性は係数の自由度が3→2に減ることで保たれる。唯一の照合は最終RLC等式（`sol:737`／
`WhirFinal.finalClaim`）である。`roundStep`の成功がrunning claimに証明可能に非依存であることも定理化した。

PoW: 実正典閾値5つ（非sentinel）を運び40 nonceバイトを実際に消費するが、定数ハッシュでは`powValue = 0`で比較は
証明可能に空虚（別の定数ハッシュではgrindingが効く対照付き — 空虚性はモデルではなく`toyHash`の性質）。
`derivedConfig`の導出文脈との同定は7欄中5欄（6主張セル・protocol id・session id・encoding・変数数・3root、
全thash/khash/Pで）。残る2欄はpacked pointsで、これはheartbeat予算の記録であって証明可能性の主張ではなく、欠落補題
（`derived_expected_claims_are_zero`のpoints版）を名指しした。6主張セルはゼロproof由来で全てゼロである（採用済み
DerivedAcceptanceから継承する玩具性 — 非自明な主張と読んではならない）。正直な一行要約: 配備検証器が検査する唯一の
等式を、退化ハッシュ・空パスドメイン・84中5クエリで満たすトランスクリプト — 真正の実行witnessでありそれ以上ではない。

3モジュール合わせて156モデル・6517定理。受理ラインの誠実性の弧は完結した: 検証器は実行し、proofに依存し、
**誤ったproofを拒否する**。今回もROMの法則下の結果であり、keccakの性質でも系の健全性誤差でもない。
残るのは、r族の拒否形（receiveOneのバイト等式の輸出）、配備ハッシュとサンプル表ハッシュの同定、packed pointsの2欄、
状態幅を広げたハッシュ、回路の真値、そしてFiat–Shamirのchallenge grindingの課金である。

## 第52継続更新（644326a0以降）

追跡版runnerでコミット`644326a0`の156モデル・6517定理を再検査しPASS（1057.088秒、1486モジュール、
manifest `144da1b5e3f82f5cf5bf26520aff8f96c256e50dd819010566c0b3754315e0d0`、receipt
`631c7824d1044b392781ed68cd99a582601558841ab066f0ca8909f17a35b6f5`、graph
`058bac9228d4253e81196a1fb8171900e78022ab83ce697f5ce6a27d20d3e2b6`）。

## 第53継続更新（5b1d26f2以降）

反復33は利用者の指示（回路の真値を進める）による単一候補で、`Audit.Wire3.CircuitTruth`（25定理・10定義＋1構造）を採用した。
Opusによる敵対的レビューと修復を経ている。レビューは証明がすべて正しいことを確認したうえで、**見出しのコミットメント側の
連言が恒真である**ことをコンパイルで示した: `CommitmentOrder.CommittedTables`は`rfl`で埋まる2欄しか持たないため
`∃ tablesOf, CommittedTables tablesOf s t`は無仮定で証明可能であり、橋を全部削除しても旧結論形が成立する。両事実は削除
ではなく記録定理として保存した（`committed_tables_existential_is_a_tautology`、
`the_former_conclusion_shape_holds_without_the_bridge`）。

修復後の見出し`extracted_tables_satisfy_the_selected_gate_constraints_and_are_pairwise_run_independent`は、受理・
`AssemblyResidue`（R1bBridgeの抽出状態で）・good draw・`WhirDecodeUniqueness`・`gates.Nodup`の下で、
(i) **対ごとの走行非依存性** — `RunPairNoCollision r rp`なる任意の第2走行rpについて、rpの抽出表はrの抽出表と等しい、
または実際に開かれた2行上の`OpenedLeafCollision` — これが「コミットメントが表を決定する」の計算論的に正直な意味であり、
(ii) 全行（< 2^degreeBits）×全選択gateで`GateEvaluatorCoverage.evaluateGateFull`の全constraint項がゼロ、を結論する。
一様`tablesOf`への強化案（`∀ r, RunPairNoCollision r r₀`）は出荷前に検査し、深さ1 fixtureで反証されることを定理として
記録した（`the_uniform_no_collision_family_fails_at_the_depth_one_fixture`）— R1bBridgeで反証した∀-全実行の罠が
「一様抽出器」の顔で再入場する実例であり、本監査はこの罠を二度捕まえ、二度とも反証を定理として保存したことになる。

**一意選択はツリーから証明した。** `unique_selection_of_plonky2_selector_row`は採用済み`Gates.other_row_zero_filter`／
`unused_selector_zero_filter`の合成であり、ツリーにないもの（定数列が行に何を持つか）だけを5欄構造`SelectorRowIsPlonky2`
に分離した。その中身はplonky2の実装に照合済みである: 未使用セレクタ定数`4294967295 = u32::MAX`は`mle/src/gate_ext3.rs:33`
（filter計算は`:629-647`）とSolidityミラー2箇所に一致し、`manySelectors`を落とすと一意選択が壊れる反例、および構造が
結論を密輸していないことの検査もレビューが済ませた。列の同定は`ConstantsProvenance`で未放電のまま継承（明記）。

**意味論**は全14 familyが`evaluateGateFull`形に載る（`validateConfiguration`は受理から、幅は`extractedStateConsistent`
から、`numSelectors ≤ numConstants`はenvelopeから）。完全な体等式展開はid 0–3のみで、id 13はcoset layout形状ゲートで
`none`があり得る。転写の但し書き（監査済みRustへの照合であってPlonky2本体への照合ではない）は逐語継承。

**追加配備仮定を1つ名指しした**: `gates.Nodup`。採用済みの単一gate定理はpre/postの全要素のfilter消滅を要求するため、
選択gateと構造的に同一の重複はそこに覆われず残る。`Gates.validateConfiguration`に相異検査はなく、`distinctRows`は重複に
対して空虚である（反例定理つき）。誠実な弱形は選択gateごとの`count = 1`である。

**最深の条件層を明記した**: `AssemblyResidue`の実例はこのツリーで一度も提示されていない。最寄りは
`ExtractorConstruction`§8（19欄中10欄を放電。keccak2欄・配備/ABI4欄・`gatesDecode`・`gateConstraintsPositive`・
`activeFilter`・R1bが仮定のまま）で、`SoundnessAssembly`自身が「`hacc`と`AssemblyResidue`が両立し得ることを示すものは
ここにはない」と述べている。すなわち`{hacc, H, hdraw, hidx}`の同時充足は未提示であり、本文はその条件の下の文である。
12項目の台帳: copy/routing（欠落文は正確に「コミットされた表が回路のroutingの各置換軌道上で一定」）・公開入力束縛
（PublicInputGateの行等式まで）・truth列と`coeffsOf`の自由・root盲目性・セレクタ列の中身・未選択行は全く無拘束・
coset layoutゲート・転写但し書き・質量側・`hdec`・`Nodup`・同時充足。

1モジュールで157モデル・6542定理。今回もROMの法則下の結果であり、keccakの性質でも系の健全性誤差でもない。
残るのは、copy/routing制約の意味論（置換軌道上の一定性）、公開入力束縛、`AssemblyResidue`の実例（受理との同時充足）、
r族の拒否形、packed pointsの2欄、そしてFiat–Shamirのchallenge grindingの課金である。

%%B45%%













## 次工程

[SCOPE.md](SCOPE.md)の未完了一覧を順に進める。
特にtyped設定/実sampling経路から外側入口への接続を進め、全gateの意味論・次数、
実行意味論・有限体証明の全体接続・確率的健全性を証明することが必要。
この更新のみを根拠に本番利用や「criticalな健全性問題なし」を宣言しない。
