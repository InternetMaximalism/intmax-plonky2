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
  認証関数は観測のままで、後続のfinal sumcheck/最終claimまで含む全WHIRの証明ではない。
- 同じ終端値に到達する候補/真のsumcheck chainで初期値が異なるなら、
  実challengeで異なるround関数の評価が一致することを証明。
  その事象の確率やcircuit witnessの存在までは導いていない。

正の通常例も含めて実行可能な受理経路を確認しているが、観測関数付き例は
実際に生成した暗号proofの代わりではない。

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

上表の名前は共通prefix `Audit.Wire3.` を省略。
全名付き定理は[manifest](wire3-manifest.json)で管理し、検査は抜粋ではなく全件に対して行う。

## 全ソースの対応状況

| このcheckout内のRust/Solidityファイル | 合計 | 部分的なモデル対応あり | モデル対応なし |
|---|---:|---:|---:|
| MLE Rust (`mle/src/`、旧実装を含む) | 35 | 6 | 29 |
| MLE Solidity (`mle/contracts/src/`、旧実装を含む) | 33 | 10 | 23 |
| その他（テスト・example・別crateを含む） | 222 | 0 | 222 |
| 合計 | 290 | 16 | 274 |

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

2026-09-06にこの作業checkoutで以下を実行した。

| 検査 | 結果 |
|---|---|
| 現行Lean rootのbuild | PASS — 8モデルとrootの計9ファイル |
| 全名付き定理の解決・推移的公理検査 | PASS — 170件、独自公理・未証明穴なし |
| source inventoryとbuild前後のhash検査 | PASS — 290ソースを含む350ファイル |
| guardの単体テスト | PASS — 21件 |
| CI workflowのYAML構文 | PASS |
| 差分の空白エラー検査 | PASS |
| 対象baseからのRust/Solidity・依存設定の差分 | なし |

350ファイルにはモデル・文書・検査器・歴史資料も含む。
今回追加したCI jobは現行rootとguardを検査するが、リモートCIはこの作業では未実行。
実装を変更していないため、全Rust/Solidity試験も今回は再実行していない。
これらのLean検査を、全体暗号監査の完了とはしない。

## 次工程

[SCOPE.md](SCOPE.md)の未完了一覧を順に進める。
特に全WHIRとnorm/gate多項式を `Engine` 観測から具体的実装へ置き換え、
実行意味論・field laws・確率的健全性を接続することが必要。
この更新のみを根拠に本番利用や「criticalな健全性問題なし」を宣言しない。
