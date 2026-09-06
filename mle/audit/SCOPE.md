# wire-v3 監査スコープと信頼境界

対象コミット: `becfe98e37c76e62f02f1aa7a417c7b06840db67`（2026-09-06）。
この作業は現行MLE/WHIR経路を優先します。全Rust/Solidityファイルは対応表に
列挙しますが、旧V1、Plonky2の再帰回路全体、独立したStarky、全依存実装を
形式化済みとはしません。

## 「証明済み」が意味するもの

Lean kernelが、**記述されたLean関数・型と明示的前提**から定理の結論が
導かれることを検査しました。次の3層は別物です。

1. Leanモデル内部の性質 — この更新で扱う。
2. 実Rust/Solidity/Yulの全実行がモデルに対応すること — 手動対照のみ。形式的refinementは未証明。
3. 受理された証明に正しいwitnessが存在する確率的健全性 — 未証明。

同じ初期claim・同じchallenge・同じroots/points/claimsを使ったという条件は、
それらが暗号学的に健全に生成・認証された証明ではありません。

## 明示的な境界

- ArithmeticはNatによるmod演算。uint64/uint256のwrap、addmod/mulmod、メモリ、
  Rust fieldの非canonical内部表現、コンパイル結果との対応は別課題。
  Goldilocks素数性、X^3-2の既約性、inverse/exp/evalL0はここで証明しない。
- Packedは関数的なloopモデル。paddingとの結果一致を証明するが、実in-placeメモリ操作
  の安全性は含まない。Rustの配列実装への適用には入力長・width・次の2冪・point長の接続が必要。
- Transcriptのhashは任意の決定的関数。同一の旧digestの下でのhash前tag/payloadの
  一意性から、hash後の単射性・ランダム性は導かない。
  counterの結果はcheckedで成功する呼出しが対象。
  `commitClaims` 等のraw helperは、preflightでcanonical値・payloadのu64長上限が
  保証された環境を対象とし、そのpreflight接続自体は未証明。
  初期statement/root吸収の全手順と全Engineへの接続は残る。
- Compactはtyped Proofを返す完全decoderではなく、byte grammarを走査してchunksを返す。
  trusted Shapeの全検証、Rustのより厳しい可変cap、debug WHIR pattern再構成、
  opaque WHIR bytes内部、EVM構造体メモリ配置は未対応。
  strict canonicalityは外側field chunkのみ。deferred canonical mode単独では保証しない。
- Sumcheckのcollision reductionは意味的なmessage/truth関数を対象とする。
  honest truth chainとの対応が前提で、production verifierがtruthを検査するわけではない。
  coefficient復元・gate/norm多項式との完全な接続、次数・根の個数・確率・FS変換は残る。
- Verifierは正規化済みtyped入力に対する成功境界モデル。
  configuration、decoder、initial transcript、gate/norm/eq評価、hash、WHIR tail等を
  入力付き関数観測として残す。例外・gas分類は実EVMの全分類ではない。
- Solidityのenvelope/deployment検査はconstructorで行い、callでは設定hashを照合する。
  `verify` はdeployment+callの複合境界、`verifyCall` は前者の検査を除いた境界。
  両者の一致にはdeployment invariantを明示的前提とする。hash一致だけからその前提を導かない。
- WHIRへの座標は `reverse(index) ++ reverse(row)`。Rust入口の `row ++ index`
  からnative adapterが反転する境界とSolidityが反転する境界を区別する。
- 6個のclaimのうち外側terminalで使う5個を拘束する。第6セルは外側では未拘束で、
  WHIR内の処理対象であることと外側期待値との一致を混同しない。
- WhirTerminalは終端比較のslice。Merkle/hash/FS/OOD/前段sumcheck/PoW/全bytes消費を
  含むWHIR verifier全体の証明ではない。全query数ゼロを独自に禁止するモデルにはしない。
- ConnectionsはLeanモデル間の具体的な型・foldの接続。全Engineを具体的に実装したわけではない。

## 未完了の全体証明（優先順）

1. WHIR全round・Merkle path・OOD・PoW・終端・EOFを具体化し、固定VK/root/pointへの
   認証を全経路で接続。native dependencyの対象revisionも形式化する。
2. norm/logUp、public-input wire map、全14 gate families、selector/lookup拒否、
   degree boundsを具体化し、意味的sumcheck定理に接続。
3. setup/VK/config生成、immutable store、全compact decoder、初期transcript、
   真のchallenge計算・packed foldを一つの実行可能なverifierに接続。
4. 有限体の数学的基礎とRust/Yulの実行意味論を検証し、手動対照を形式的refinementへ置換。
5. honest proverの全段階、completeness、再帰回路/親statementとのcompositionを証明。
6. 暗号仮定を明記したPCS/Fiat–Shamir/grindingの定量的健全性を証明。
   全てのhashに無条件の数学的安全性があると仮定しない。

現target105の約101.5-bit値はリポジトリのgeneric-work見積もりで、Leanが証明した
128-bit/end-to-end安全性ではありません。実装変更・デプロイ承認もこの更新には含みません。
