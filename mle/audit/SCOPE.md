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
  GoldilocksFoundationは具体pの素数性・一般Fermat・立方根2の不存在を証明する。
  GoldilocksNormは全非零canonical Ext3で実inverseの成功・左右逆元性を証明する。
  GoldilocksExt3Fieldは実演算/実inverseのwrapperにFieldを構成し、標数pと要素数p³を証明。
  X^3-2のPolynomial.Irreducibleとしての明示定理やevalL0の完全接続はまだ別課題。
  Algebraでは実際のc0/c1/c2式から加法・乗法の交換/結合/分配、加法逆元と取消を証明。
  ring法則を仮定するレコードは使わない。NormIdentityはformal adjugate/norm恒等式、
  ModularPowerは具体binary exponentiationの値と成功fuel条件を証明する。
  inverse成功時の積をnorm^(p−1) mod pへ還元し、Foundation/Normがこれを1へ接続する。
  有限体性を前提レコードへ隠さず、実Algebraのring法則と実inverseから構成する。
  FermatBridgeはFermatAt(norm)を可視の定理引数として、実inverseの左右逆元・
  canonical消去・除算を接続する。基数7の実例は数値証明書からこの仮説を解消するが、
  それ以外の入力の条件は後段Foundation/Normが解消する。canonical性は引き続き明示条件。
  raw Nat値の非零や、Ext3係数を持つoff-cube formal normへの同じ非零主張は導かない。
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
- WhirSampling.challengeRawは1byteにつき1hash/counter更新、BE query、power-of-two maskを具体化。
  count=0/numLeaves=1の無消費分岐、counter上限、raw rangeを証明する。
  challengeIndicesReferenceは実行可能な挿入sortと隣接dedupの基準版であり、sourceの
  in-place quicksortそのものではない。sortedness・membership・件数・非空性を証明しても、
  source quicksortのswap/partition/termination/メモリとの同値を得たことにはしない。
  原始query集合からこの基準出力へ移る差は、全WHIR接続時にも可視の未証明境界とする。
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
  MerkleExtractionはこの同じ成功executionから各leafのdepth長pathを抽出する。
  WhirRowsは元hint行のread/hashと既存Merkleへ直結し、WhirRowBindingは実openGroupの
  同root/index/depth行を、raw bytes・同Layoutの復号値・同weightsのdotが一致するか、
  実raw leaf入力または64byte圧縮入力のhash衝突へ還元する。
  独立leaf hash/pathやserialize単射性を前提として代入しない。
  WhirTerminal.authenticateの全入口での置換、衝突確率、Yulの配列操作は未完了。
- WhirRows.openGroup/openGroupsはraw phaseのみ。base8/Ext3-24のcanonical decodeは別操作で、
  raw認証成功だけからcanonical値の存在を導かない。実final splitのrow loop内decode/集計は
  この順序のまま未実装とし、先読みdecodeへ組み替えて同値としない。
  空queryも8byteのVec=0 prefixを読み、Merkleの空openingはその後offsetを維持する。
  Layout/weights/indicesの前段導出とfull tailへの接続は別課題。
- WhirScheduleは既存_validateParametersのfolding guardのみの投影。初期・中間・終端の
  変数数の完全分割、各roundのremaining/suffix、underflowなし、最終2冪サイズを証明する。
  domain/generator/coset/点配列/ABIの全検証は未実装。成功を完全設定検証済みとしない。
  値はstored VK/config由来である必要があり、proverが自由に変更できるfieldとはしない。
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
   各queryの開示path→終端比較を一つの実行経路として証明。raw row→multiproof→path→
   復号/dotのbindingは接続済みだが、samplingのquicksort同値と中間round全体は残る。
   native依存revisionも対象に含める。
2. 全14 gate評価の式から実多項式次数・gate意味論・sumcheckへの接続を証明。
   PI cacheの証明済み同値、selector/lookupの入口接続も全体経路へ反映。
3. setup/VK/config生成、immutable store、全compact decoder、metadata decoder、
   初期transcript・真のchallenge・public-input hashをIntegratedへ接続。
   現在別モジュールのWhirFinal/Merkleを、全whirTailの代替と誤認しない。
4. 証明済みの素数性・具体Ext3有限体/逆元を、Rust/Yulの実行意味論へ接続し、
   手動対照を形式的refinementへ置換。evalL0等の残る演算にも適用する。
5. honest proverの全段階、completeness、再帰回路/親statementとのcompositionを証明。
6. 暗号仮定を明記したPCS/Fiat–Shamir/grindingの定量的健全性を証明。
   全てのhashに無条件の数学的安全性があると仮定しない。

現target105の約101.5-bit値はリポジトリのgeneric-work見積もりで、Leanが証明した
128-bit/end-to-end安全性ではありません。実装変更・デプロイ承認もこの更新には含みません。

GoldilocksCertificate単独は数値証明書であり、素数性の根拠はGoldilocksFoundationの
Lucas適用・全prime-divisor列挙・小因子の素数性の証明と組み合わせたものに限る。
Mathlib v4.10.0のcommitと公式lockの6依存を監査専用に固定し、直接importは特定の
モジュール/名称だけ許可する。標準3公理allowlistと全名付き定理の検査は維持する。
依存guardは全tracked sourceの実Git blob・HEAD・origin・固定release tagと追加sourceを検査。
この検査は生成済み.oleanやProofWidgets release archiveの出自を認証しない。
通常Lakeビルドにはそれらの成果物とLean toolchainの信頼境界があり、全source-only再現とは呼ばない。
