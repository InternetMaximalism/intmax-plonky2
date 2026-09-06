# 現行 wire-v3 Lean 監査

対象: submodule main `becfe98e37c76e62f02f1aa7a417c7b06840db67`。
実装本体は `b569e0d7`、プロトコルは `MLEWHIR3` です。
ファイル名の `V2` はAPI世代名で、旧wire v2を受理する意味ではありません。

**状態: 部分的な実行可能モデルと決定論的性質を証明済み。
実装全体のLean化・Rust/Solidityとの形式的同値性・暗号健全性の証明は未完了です。**

旧監査を現行実装の証明として流用しません。通常の `lake build` とCIは現行
`Audit.lean` を検査します。7月のモデル・根の個数公理・旧所見は
[歴史資料](HISTORICAL-README.md)および明示的な `HistoricalAudit` targetに分離しています。

## 追加した現行モデル

| モジュール | 実装に対応する範囲と証明 |
|---|---|
| [Arithmetic](Audit/Wire3/Arithmetic.lean) | Goldilocks/Ext3の具体的mod演算、canonical値の保存。素数性・拡大体の既約性・逆元・機械語実装の証明ではない |
| [Packed](Audit/Wire3/Packed.lean) | LSB-first隣接fold、任意のゼロ末尾paddingとの結果一致、配列長、全座標反転 |
| [Transcript](Audit/Wire3/Transcript.lean) | 実byteのLE符号化、同一の旧digestの下でのhash前tag/payload一意性、counterと両round/全claim吸収順 |
| [Compact](Audit/Wire3/Compact.lean) | 実byteの外側grammar、canonical limb、読取り境界、headerと完全消費。完全Proof decoderではない |
| [Sumcheck](Audit/Wire3/Sumcheck.lean) | 意味的round関数に対する決定論的collision reduction。確率評価や実coefficientsとの全接続ではない |
| [Verifier](Audit/Wire3/Verifier.lean) | 設定/shape境界、coupled round履歴、3 roots・2 points・6 claims、terminal条件とWHIR観測への束縛 |
| [Connections](Audit/Wire3/Connections.lean) | canonical subtypeとFin3表現の双方向変換、実Packed.foldをVerifierへ接続 |
| [WhirTerminal](Audit/Wire3/WhirTerminal.lean) | WHIR終端query/最終多項式比較の限定slice。全WHIRやMerkle暗号健全性ではない |

[スコープと未証明事項](SCOPE.md)、[結果・再現手順・次工程](REPORT.md)、
[全ソース対応表](wire3-manifest.json)を参照してください。
対応表はこのcheckoutに属する全Rust/Solidityファイルを列挙し、
モデルとの部分対応があるファイルと未対応のファイルを区別します。
依存ライブラリ・コンパイラを含む全コードを形式化したという意味ではありません。

## 実行

Lean 4.10.0の `lake` をPATHに入れ、リポジトリrootから実行します。

```sh
python3 -B mle/audit/test-check-wire3.py
python3 -B mle/audit/check-wire3.py
```

検査は全current moduleのbuild、全名付き定理の実Lean環境での解決、推移的公理依存、
ソース/モデル/文書のhash、列挙漏れを確認します。空の検査リストは失敗です。
`sorry`、`admit`、独自公理、`native_decide` による穴埋めは認めません。
許容するglobalな論理公理は `propext`、`Classical.choice`、`Quot.sound` のみです。

**公理リストが短くても、定理の引数やEngine観測は仮定として残ります。**
hash照合は変更検知であり、コードとLeanモデルの形式的同値性を証明しません。
未証明のWHIR健全性を `Engine.whirTail = true` で証明済みにすることもありません。
