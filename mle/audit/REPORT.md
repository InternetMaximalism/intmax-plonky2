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

## 今回の継続更新（69516414以降）

14モデルを追加し、既存統合入口への2定理追加と合わせて326定理増えた。
現行rootは計28モデル・698名付き定理。件数を安全性の達成率とはしない。

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

本ターンは実装本体・依存設定・main・親pinを変更していない。公開/pushも行わない。
成果は専用ローカルブランチ `codex/lean-wire3-audit-20260906` にチェックポイント保存する。
全体目標は引き続き進行中であり、この段階で完了としない。

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

上表の名前は共通prefix `Audit.Wire3.` を省略。
全名付き定理は[manifest](wire3-manifest.json)で管理し、検査は抜粋ではなく全件に対して行う。

## 全ソースの対応状況

| このcheckout内のRust/Solidityファイル | 合計 | 部分的なモデル対応あり | モデル対応なし |
|---|---:|---:|---:|
| MLE Rust (`mle/src/`、旧実装を含む) | 35 | 8 | 27 |
| MLE Solidity (`mle/contracts/src/`、旧実装を含む) | 33 | 18 | 15 |
| その他（テスト・example・別crateを含む） | 222 | 2 | 220 |
| 合計 | 290 | 28 | 262 |

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

### 今回の検査

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

調査した現監査・親の2監査はLean4.10、依存packagesなし。利用可能な4.10互換Mathlib
checkoutや具体Goldilocks素数性証明は見つからなかった。別版由来と思われるbinary cacheは
対応source/toolchain/lockを確認できないため採用せず、新規依存・ネットワーク利用もまだない。
次は素数性判定基準と小因子の証明→Fermat→成功時inverse正当性を閉じる。
三次式の既約性は、その後に非零Ext3のnorm非零と体全体の構成へ接続する。
Mathlib採用なら対応版・全推移依存を固定し、guardの許可対象を限定して標準公理検査を維持する。

## 次工程

[SCOPE.md](SCOPE.md)の未完了一覧を順に進める。
特にWHIR中間round・sampling・raw opening/Plan/Contextを接続し、全gateの意味論・次数、
実行意味論・有限体の基礎・確率的健全性を証明することが必要。
この更新のみを根拠に本番利用や「criticalな健全性問題なし」を宣言しない。
