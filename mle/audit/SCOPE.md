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
  Goldilocks素数性、X^3-2の既約性、全非零値に対するinverse/evalL0はまだ証明しない。
  Algebraでは実際のc0/c1/c2式から加法・乗法の交換/結合/分配、加法逆元と取消を証明。
  ring法則を仮定するレコードは使わない。NormIdentityはformal adjugate/norm恒等式、
  ModularPowerは具体binary exponentiationの値と成功fuel条件を証明する。
  inverse成功時の積はnorm^(p−1) mod pへ還元できるが、これが1であるFermat証明と
  非零Ext3のnormが非零である証明は残る。有限体性を前提レコードへ隠さない。
- Packedは関数的なloopモデル。paddingとの結果一致を証明するが、実in-placeメモリ操作
  の安全性は含まない。Rustの配列実装への適用には入力長・width・次の2冪・point長の接続が必要。
- Transcriptのhashは任意の決定的関数。同一の旧digestの下でのhash前tag/payloadの
  一意性から、hash後の単射性・ランダム性は導かない。
  counterの結果はcheckedで成功する呼出しが対象。
  `commitClaims` 等のraw helperは、preflightでcanonical値・payloadのu64長上限が
  保証された環境を対象とし、そのpreflight接続自体は未証明。
  初期statement/root吸収の全手順と全Engineへの接続は残る。
- Spongefishはこれと別の内側WHIRのchain。state||squeeze||BE64counterの47byte入力、
  120byteを一括生成して3個のLE40byte値に還元するchallenge、24byteの厳密canonical読取り、
  PoWのchallenge32＋nonce8＋zero24とLE先頭8byte判定、hint Vec prefixを具体化。
  生の定数Hash引数はRO・衝突耐性・entropyの仮定ではない。実wordload/uint256/IO-patternは別境界。
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
  含むWHIR verifier全体の証明ではない。WhirFinalでは同じfinalVectorを後続の最終
  sumcheck・逆順fold・非零・逆元計算・全constraint差引き・全linear-form・両EOFへ接続。
  WhirFinal単独のdecoder/PoW/challengeは観測だが、WhirFinalSpongefish.engineは3つとも
  具体Spongefish呼出しへ置換し、各roundの48/56byte消費と受理時suffix長を証明する。
  Contextはなお前段で生成すべき信頼状態で、既読hint位置を保持したままEOFを照合する。
  このadapterはhintを一切読み足さず、前段のhint認証を独自に証明したことにはならない。
  NormIdentityでsum-form最終foldとPacked difference-formの完全table上の同値も証明済み。
  全query数ゼロを独自に禁止するモデルにはしない。
- WhirInitialはroot→OOD challenge→own answers→boundRootの各commitment処理、
  全claimのmask照合、cross行列、vector/constraint RLC、初期sumを具体化。
  WhirPrefixはその実結果・同一byte列を最初のsumcheckへ渡す。
  Params/form配列はvalidated callerからの投影で、runtimeで新しく保存するfieldではない。
  中間round/sampling/row bytesから最終Contextまでの接続、外側WHIR引数との型変換は残る。
- Merkleはraw32byte digest、左右64byte圧縮、厳密昇順と層別sibling処理を具体化。
  読取りがある場合のcursor境界と、same-index/same-depthの2本のpathが異なるleaf hashを
  同じrootへ送るなら圧縮入力の衝突があることを証明。hashの単射性は仮定しない。
  多重開示から個々のpathを抽出する証明、row serialization/hashとの接続、
  WhirTerminal.authenticateの置換、衝突確率、Yulの配列操作は未完了。
- Normはformal-coordinate式とhelper/logUp集計を具体化。PIはRustの順序付き直接和で、
  PiSharedBits/PiCacheでSolidityのrow-cache/shared-bit最適化とのモデル内同値を証明。
  OR/XOR mask、newest-first検索、重複/順序、eta最後更新省略も具体化している。
  無条件同値は両モデルのraw totalization上の定理で、不正shapeの実装受理を保証しない。
  EVMのポインタ・aliasing・in-place書込みとRust executionの形式的対応はまだ別課題。
  Algebraによりeq/subgroupのSolidity最適化式とRust式、およびsquare=mulはモデル内で証明済み。
  formal adjugate/normの恒等式はNormIdentityで証明済みだが、helperの正しさや
  PI個別一致への確率的還元は残る。
- Gatesは14familyの設定検証、GatesAdditional/CosetとPoseidon/Constantsは残る8familyを具体化。
  GatesCompleteは全14familyを実計算し、valid設定と入力長ならSomeが得られることを証明する。
  Integratedはこのcomplete dispatcherを使う。基礎Gates単独のpartial dispatcherと混同しない。
  全1147定数はソースと逐語比較するが、抽出検査をformal refinementとは呼ばない。
  zero-filter skipは保持する。degree budget検査から式の多項式次数証明は導かず、
  集約値0から全制約0への逆方向も主張しない。
- Integrated.verifyはchecked norm形状と7challenge layout、同じ入力での全gate計算の
  Someを検査後、packed/norm/eq/gateを具体化したVerifier.verifyへ進む。
  modelEngineだけの利用にはこの保証がなく、getD zeroは旧interfaceへの全域化にすぎない。
  metadata decoderは固定Config.gatesEncodingだけを受ける観測であり、初期FSや
  public-input hash、configuration hash、WHIR tailを具体化したわけではない。
  追加preflightの失敗分類/順序はモデル上のもの。実装の例外・slashing証拠とは未接続。
  Gates.rustAdmissionのlookup拒否もこの入口には未接続。
- ConnectionsはLeanモデル間の具体的な型・foldの接続。全Engineを具体的に実装したわけではない。

## 未完了の全体証明（優先順）

1. 具体化済みWHIR initial/最初のsumcheck・内側byte/PoWを中間round・samplingへつなぎ、
   Plan/ContextとfixedVK/root/pointへの認証を接続。raw row bytes→leaf hash→multiproof→
   各queryの開示path→終端比較を一つの実行経路として証明。native依存revisionも対象に含める。
2. 全14 gate評価の式から実多項式次数・gate意味論・sumcheckへの接続を証明。
   PI cacheの証明済み同値、selector/lookupの入口接続も全体経路へ反映。
3. setup/VK/config生成、immutable store、全compact decoder、metadata decoder、
   初期transcript・真のchallenge・public-input hashをIntegratedへ接続。
   現在別モジュールのWhirFinal/Merkleを、全whirTailの代替と誤認しない。
4. 具体代数/adjugate/冪乗証明を基に素数性・既約性・乗法逆元とRust/Yulの実行意味論を検証し、
   手動対照を形式的refinementへ置換。
5. honest proverの全段階、completeness、再帰回路/親statementとのcompositionを証明。
6. 暗号仮定を明記したPCS/Fiat–Shamir/grindingの定量的健全性を証明。
   全てのhashに無条件の数学的安全性があると仮定しない。

現target105の約101.5-bit値はリポジトリのgeneric-work見積もりで、Leanが証明した
128-bit/end-to-end安全性ではありません。実装変更・デプロイ承認もこの更新には含みません。

GoldilocksCertificateはp−1の因数積・基数7の6組のべき乗/gcd・三乗非剰余候補値を
kernelで確認した数値証明書にすぎない。素数性判定基準の健全性、小因子の素数性、
一般Fermatをまだ証明していないので、これをGoldilocks素数性の証明として使わない。
現依存はLean4.10/Stdのみ。互換性を確認できない既存Mathlibバイナリcacheは採用しない。
Mathlibを導入する場合は対応版・全推移依存を固定し、import/hash検査を限定拡張したうえで
標準3公理allowlistと全定理の検査を維持する必要がある。
