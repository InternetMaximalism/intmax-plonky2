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
| [WhirFinal](Audit/Wire3/WhirFinal.lean) | 同一finalVectorを最終sumcheck・逆順fold・非零・全線形形式・EOFへ接続。前段WHIR/decoder等は観測 |
| [Merkle](Audit/Wire3/Merkle.lean) | 実byteの層別multiproof処理、cursor範囲、同じindex/depthのpathに対する圧縮衝突への還元 |
| [Norm](Audit/Wire3/Norm.lean) | formal norm/adjugate、helper/logUp・PI集計、固定Configと同一statementを使う具体terminal |
| [Gates](Audit/Wire3/Gates.lean) | 全14familyの設定検証と基礎6family、selector/Horner。単独の旧部分dispatcherは追加8family未対応だが、統合入口では使わない |
| [Algebra](Audit/Wire3/Algebra.lean) | 具体mod演算から交換・結合・分配・加法逆元を証明し、eq/subgroup/squareの異なる式を接続 |
| [GatesAdditional/Coset](Audit/Wire3/GatesAdditional.lean) | 残る6familyの全評価式、Cosetの実124定数、chunk/Ext2/bit順序と具体正常例 |
| [Poseidon/Constants](Audit/Wire3/Poseidon.lean) | Poseidon/MDSの全評価、123/24制約、実1023定数、全30roundを通る正常witnessとRust標準出力 |
| [GatesComplete](Audit/Wire3/GatesComplete.lean) | 全14familyの具体dispatcher。valid設定・入力長なら全familyが実計算結果を返すことを証明 |
| [Integrated](Audit/Wire3/Integrated.lean) | packed/norm/eq/全gateの4観測を具体化。checked preflightで不正設定やdecoder失敗のzero fallback受理を防ぐ部分統合入口 |
| [NormIdentity](Audit/Wire3/NormIdentity.lean) | 実Ext3係数上のformal adjugate恒等式、逆元candidateとの積、WHIR sum-formとPacked difference-formの同値 |
| [ModularPower](Audit/Wire3/ModularPower.lean) | 実binary冪乗の正確値とfuel条件、inverse成功時の積をnorm^(p−1)へ還元。一般Fermatは後段GoldilocksFoundationで解消 |
| [Spongefish](Audit/Wire3/Spongefish.lean) | 内側WHIRのraw byte hash chain、BE counter、120byte challenge、canonical read、PoW、hint Vec長。Hashの安全性は仮定しない |
| [WhirInitial](Audit/Wire3/WhirInitial.lean) | 実root/own-OOD/全claim/cross-OOD読取りから2種のRLCと初期sumを生成し、同一データ・読取り量・checked maskを証明 |
| [WhirFinalSpongefish](Audit/Wire3/WhirFinalSpongefish.lean) | 最終sumcheckの3観測を実byte処理へ置換。1roundあたり48/56byte、120byte challenge、受理時の正確なsuffix長とhint EOF |
| [WhirPrefix](Audit/Wire3/WhirPrefix.lean) | 初期処理→最初のsumcheckを同一source・初期sum・spongeで接続。中間以降の全WHIR接続ではない |
| [PiSharedBits/PiCache](Audit/Wire3/PiCache.lean) | 実OR/XOR共通bit分離・逆順検索・重複行合算・eta末尾更新省略を含むキャッシュと直接PI和の同値 |
| [GoldilocksCertificate](Audit/Wire3/GoldilocksCertificate.lean) | 体証明で使う具体べき乗/gcd証明書。単独では素数性を結論せず、GoldilocksFoundationのLucas証明に渡す |
| [MerkleExtraction](Audit/Wire3/MerkleExtraction.lean) | 実multiproof成功から全leafの深さ付きpathを抽出。同root/index/depthの開示を一致または具体的hash衝突へ還元 |
| [WhirSampling](Audit/Wire3/WhirSampling.lean) | byteごとの実hash/counter・BE query・mask。挿入sort基準版の順序/集合を証明するがsource quicksortとの同値は未証明 |
| [WhirRows](Audit/Wire3/WhirRows.lean) | Vec要素数→元の連続hint行→raw hash→既存Merkleのcursor接続。canonical decoderは実行順を保つため別操作 |
| [WhirRowBinding](Audit/Wire3/WhirRowBinding.lean) | 実openGroupの同root/depth/index行についてraw bytes・同Layoutの復号値・同weightsの内積が一致するか、具体的hash衝突があることを証明 |
| [FermatBridge](Audit/Wire3/FermatBridge.lean) | 明示したFermat等式から実inverseの左右逆元・消去・除算を証明。後段Foundation/Normが一般Fermatと非零norm条件を解消 |
| [WhirSchedule](Audit/Wire3/WhirSchedule.lean) | 実folding検査の投影から全変数の分割・各roundの残suffix・underflowなし・最終サイズを証明。domain/点を含む完全設定検査ではない |
| [GoldilocksFoundation](Audit/Wire3/GoldilocksFoundation.lean) | 具体証明書と証明済みLucas基準からpの素数性、一般Fermat、立方根2の不存在を導出。新しい体公理を置かない |
| [GoldilocksNorm](Audit/Wire3/GoldilocksNorm.lean) | 実normが0 iff canonical Ext3が0。全非零入力で実WhirFinal.inverseが成功し、左右の積が1になることを証明 |
| [GoldilocksExt3Field](Audit/Wire3/GoldilocksExt3Field.lean) | 実演算・実inverseを包む型にFieldを構成。標数p、三座標との全単射、要素数p³、Fermat/Frobeniusを証明 |
| [WhirPolynomial](Audit/Wire3/WhirPolynomial.lean) | 実constant-first Hornerと具体体上Polynomial.evalの一致。同長・不同の固定canonical vectorの一致点数≤長さ−1。query分布や適応選択の確率ではない |
| [GoldilocksLagrange](Audit/Wire3/GoldilocksLagrange.lean) | 実反復squareと2冪乗、guardとscalar範囲、実inverseを通るevalL0の有理式一致。x=1はsourceどおり失敗 |
| [WhirIntermediate](Audit/Wire3/WhirIntermediate.lean) | 初期prefixからnew root/OOD/PoW/前rootのraw Merkle/RLC/dot/constraint/sumcheckまで同じ実状態で接続。3 base roots→単一Ext3 root。設定投影・reference sortの境界は残る |
| [WhirDedup](Audit/Wire3/WhirDedup.lean) | 実indexed隣接重複除去の上書き・読書き境界・最終長と基準dedupの一致。quicksort自体の証明ではない |
| [WhirTail](Audit/Wire3/WhirTail.lean) | 同じ初期/中間実行から終端の両分岐、同一final vector、derived Context、最終claim・両EOFまで接続。3×1設定投影とsource refinementの境界は残る |
| [GoldilocksDomain](Audit/Wire3/GoldilocksDomain.lean) | 固定生成元7の位数p−1、k≤32で派生根の位数2^k、transpose指数と相異点の証明。任意shape-valid generatorや設定生成の証明ではない |
| [WhirQuadratic](Audit/Wire3/WhirQuadratic.lean) | 実sumcheckのc1復元/Horner、端点和、次数≤2と固定不同claimの一致点数≤2。比較側のtruth/FS/確率は別条件 |
| [WhirParameters](Audit/Wire3/WhirParameters.lean) | 実順の全typed設定guard、bound/deployment入口の区別、raw点の損失なしcanonical化と既存WhirInitial.validatedParamsへの接続 |

現行rootは45モデル・1191件の名付き定理です。直近の検査結果はREPORTとmanifestで管理します。
件数は暗号安全性の達成率ではありません。

[スコープと未証明事項](SCOPE.md)、[結果・再現手順・次工程](REPORT.md)、
[全ソース対応表](wire3-manifest.json)を参照してください。
対応表はこのcheckoutに属する全Rust/Solidityファイルを列挙し、
モデルとの部分対応があるファイルと未対応のファイルを区別します。
依存ライブラリ・コンパイラを含む全コードを形式化したという意味ではありません。

## 実行

Lean 4.10.0の `lake` をPATHに入れ、リポジトリrootから実行します。

```sh
python3 -B mle/audit/test-check-wire3.py
python3 -B mle/audit/test-proof-dependencies.py
python3 -B mle/audit/test-provision-proof-dependencies.py
python3 -B mle/audit/provision-proof-dependencies.py
python3 -B mle/audit/check-wire3.py
```

検査は全current moduleのbuild、全名付き定理の実Lean環境での解決、推移的公理依存、
ソース/モデル/文書のhash、列挙漏れを確認します。空の検査リストは失敗です。
Mathlib 4.10と公式lockの6依存は全てcommit固定です。provisionのみが公開元から取得し、
既存依存の変更・不完全な取得は自動修復しません。guardはビルド前後に全5601 tracked fileを
Git blobと照合し、外部search path、追加Lean/config source、固定タグの不一致を拒否します。
通常LakeビルドのProofWidgets release成果物・生成済み.oleanの出自は、このsource検査では
証明しません。ソースのみからの全依存再生成とは区別します。
別途、40モデル時点の全非toolchain依存1370モジュールをfresh出力へ再生成し、全1019定理を
その出力だけで検査した記録をREPORTに保存しています。固定した11個の表示用JSデータと
Lean toolchainはその検査でも信頼境界に残り、後続追加モデルの検査範囲とは区別します。
`sorry`、`admit`、独自公理、`native_decide` による穴埋めは認めません。
許容するglobalな論理公理は `propext`、`Classical.choice`、`Quot.sound` のみです。
Poseidon/Cosetの全18表・1147語をSolidityと逐語比較し、PoseidonはRustとも比較します。
これは定数抽出の継続検査であり、コンパイラやソース全体の形式的同値性ではありません。

**公理リストが短くても、定理の引数やEngine観測は仮定として残ります。**
hash照合は変更検知であり、コードとLeanモデルの形式的同値性を証明しません。
未証明のWHIR健全性を `Engine.whirTail = true` で証明済みにすることもありません。
