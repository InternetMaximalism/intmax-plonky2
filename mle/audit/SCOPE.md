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
  GoldilocksLagrangeは実square反復を2冪乗へ接続し、evalL0の出力存在 iff
  degreeBits<64かつx≠1と、実inverse成功後の有理式一致を証明。x=1の失敗は保持する。
  X^3-2のPolynomial.Irreducibleとしての明示定理、機械語のshift/cast/memoryは別課題。
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
  WhirChallengeは同じ120byteの0/40/80 sliceと3個のLE整数との全単射を証明し、
  実reduceChallengeのd点への入力数をd・ceil(2^320/p)³以下に制限する。
  全120byte文字列を等確率と定義した有限uniform lawの下では、固定した不同の内側WHIR
  quadraticの一致確率は2(ceil(2^320/p)/2^320)³以下。これは実Keccak/FSのuniform性、
  前のmessageからの独立性・適応選択の固定性を導いた定理ではない。
  外側MLEの3回の32byte squeezeと別の係数復元式には、この内側WHIR定理を適用しない。
- WhirSampling.challengeRawは1byteにつき1hash/counter更新、BE query、power-of-two maskを具体化。
  count=0/numLeaves=1の無消費分岐、counter上限、raw rangeを証明する。
  challengeIndicesReferenceは実行可能な挿入sortと隣接dedupの基準版であり、sourceの
  in-place quicksortそのものではない。sortedness・membership・件数・非空性を証明しても、
  source quicksortとの同値をこの基準版単独から得たことにはしない。
  WhirQuicksort/Correctnessは実indexed scan/swap/左右再帰から
  partitionのsentinel・分類・範囲外不変・要素数保存を証明し、最初の実swapから再帰幅の
  厳密縮小と十分なfuelでの全終了を導く。整列と重複数保存を証明した後にだけ基準sortと同一化する。
  WhirSamplingExecutionは実sort/compactionをraw samplingへ接続し、count=0→singleleafの
  分岐順を保ち、全Option結果・全state・失敗を基準版と一致させる。両sampling箇所を差替えた
  全WHIR実行と単一checked設定入口にも接続した。これにより数学的sort置換の境界は解消したが、
  配列メモリ・uint256/overflow・gas・source/compiler refinementは証明していない。
  WhirDedupはquicksort後の実indexed compactionをモデル化し、現在のbuffer[i]/[i−1]比較、
  条件付き上書き、全read/write境界、n−1回の終了、最終長と基準dedupの同値を証明する。
  その同値にsortednessは不要で、strict ascendingの系だけがsorted入力を要求する。
- Compactはtyped Proofを返す完全decoderではなく、byte grammarを走査してchunksを返す。
  trusted Shapeの全検証、Rustのより厳しい可変cap、debug WHIR pattern再構成、
  opaque WHIR bytes内部、EVM構造体メモリ配置は未対応。
  strict canonicalityは外側field chunkのみ。deferred canonical mode単独では保証しない。
- Sumcheckのcollision reductionは意味的なmessage/truth関数を対象とする。
  honest truth chainとの対応が前提で、production verifierがtruthを検査するわけではない。
  WhirQuadraticは実WhirFinal.quadraticのc1復元とHornerを具体体上多項式へ接続し、
  実端点和=claim、次数≤2、不同canonical claimを持つ固定二組の一致点数≤2を証明する。
  成功roundの実message/challenge/stateを保ち、明示的な二本のchainの不一致にも接続するが、
  比較側chainが実回路の真値であること、gate/norm多項式との全接続、確率・FS変換は残る。
  WhirPolynomialは終端の実constant-first Hornerだけを具体Ext3体上Polynomialへ接続し、
  同長・不同の固定canonical最終vectorの一致する相異点数≤長さ−1を証明する。
  Finsetは重複のない点集合であり、query listやsource domain mapの単射性を仮定せず代入しない。
  異なる長さだけでは末尾zeroにより同じ多項式になり得る。symbolic Polynomialのnoncomputable性と
  実Hornerの実行可能性を区別し、FSで固定される時点・分布・適応的選択の確率は別課題とする。
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
  WhirIntermediateはこの同prefixから中間round列へ同じsum/roots/vector RLC/randomness/cursorsを渡す。
  new root→全OOD challenge→全answers→PoW→sampling→前rootのraw Merkle→round RLC→
  OOD/全queryのdecoded dot→constraint保存→sumcheck→previous root更新を具体化。
  round0は3 base roots×1vector、以後single Ext3 rootだけを対象とする。全query/全group/全columnと
  実RLC index、根の32byte slice、読取り量、constraint数を成功実行から導出する。
  ProfileShapeはvalidated callerのprevious-round設定投影であり追加runtime guardではない。
  source quicksort、domainPowのbinary loop、decode/算術の命令順の形式的対応は残る。
  WhirTail.runは同じinit/prefix/中間実行を保持し、final vectorを一回だけ読み、
  final splitまたはstandard認証、Horner比較、同vectorの最終fold/claim/両EOFへ接続する。
  Contextはその実prefixのforms/初期RLCと実中間stateから導出し、独立観測を受け取らない。
  runTail/finishの任意Stateには前段由来保証はなく、run成功の定理を使う必要がある。
  3×1 ProfileShapeを完全VK/ABI検証と同一視しない。外側WHIR引数と全設定投影の接続は残る。
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
  raw認証成功だけからcanonical値の存在を導かない。WhirTailの専用final splitは
  slice/hash→canonical decode/dot→vector RLC加算→hint cursor→各root Merkleの順を保つ。
  standardはraw認証を先に行い、その後各rowを復号して直ちにHorner比較する。
  空queryも8byteのVec=0 prefixを読み、Merkleの空openingはその後offsetを維持する。
  Layout/weights/indicesとtailはWhirTailの限定3×1経路で接続したが、言語間の命令対応ではない。
- WhirScheduleは既存_validateParametersのfolding guardのみの投影。初期・中間・終端の
  変数数の完全分割、各roundのremaining/suffix、underflowなし、最終2冪サイズを証明する。
  WhirParametersは全source scalarを保持するtyped Paramsから、実順序のfold/domain/点配列guardを
  具体化し、raw座標を検査後そのままSubtypeへ移す。bound入口の件数/mask/roots検査と
  deployment入口の正のform件数検査は区別し、後者にnc/nv検査を追加しない。
  成功から既存Schedule、全domain、全点の長さ/canonical性、正確なevaluation件数、
  WhirInitial.validatedParamsを導く。expectedの値をbound guardがcanonical検査したとはしない。
  samples/PoW threshold/末尾mask bitsはsource sliceに検査がないため独自に制約しない。
  WhirParameters単独ではABI・整数幅/overflow・immutable config由来と3×1 profile・全相への投影を扱わない。
  全typed相への投影は後段WhirConfiguredで接続済み。単一checkBound済みpから全phase引数を導き、
  実行成功と明示CallerProfile(nc=3,nv=1)だけから全中間ProfileShapeと終端contextShapeを導く。
  別のshape仮定や新runtime guardを追加しない。generic Params型でもsource対応は3×1内に限定。
  immutable VK由来・ABI/整数幅/overflowとgeneric nc/nv profileへの拡張は別境界のまま。
  sourceの_validateDomain単独はgeneratorの非零/canonical性と形状だけを検査し、位数は検査しない。
  query indexを相異なる評価点へ写すには、固定VKのgenerator生成から必要な位数を別途導出する。
  この条件をshape検査の成功やFinsetの重複なし条件から暗黙に得たことにしない。
  GoldilocksDomainは6素因子証明書からorder(7)=p−1、k≤32で固定根7^((p−1)/2^k)の
  位数2^kと相異indexの冪/transpose後のcanonical値の単射性を証明する。
  この固定生成式へのArk/native WHIR/codegenの形式的対応、digest bindingは別課題。
  WhirDomainBridgeは実WhirIntermediate.domainPointそのもののc0を、このtranspose後の
  canonical値へ接続する。k≤32・実generatorの固定値との一致・正のcoset次元と積=2^kを
  明示したときだけ、実点の単射、query像のcardinality保存、同長・不同の固定canonical
  最終vectorの一致query数≤長さ−1を導く。raw Hornerと正規化比較の両方を扱う。
  queryはFinset (Fin (2^k))であり、重複sample列・実query range/configへの接続・
  _glPowの機械語対応・FS確率を、この定理から暗黙に得たとはしない。
  WhirDomainPowerは別のbitwise scalar loopで、64bit mask・実low-bit条件・右shift・mulmodを
  既存binary powerへ接続。uint64入力とuint256指数のFin境界で256fuel以内の成功・正確値・
  出力<p<2^64を導く。同じtranspose指数が2^k内ならk≤32で実domainPointと一致する。
  初期baseがp以上でもuint64内なら保持し、zero exponentでは1を返す。fuelはgasではない。
  手動scalarモデルであり、Yul/parser/compiler/bytecodeとの形式的対応を得たことにはしない。
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

1. 具体化済みWHIR initial/最初のsumcheck・中間round・内側byte/PoWから終端へつなぎ、
   Plan/ContextとfixedVK/root/pointへの認証を接続。raw row bytes→leaf hash→multiproof→
   各queryの開示path→終端比較を一つの実行経路として証明。raw row→multiproof→path→
   復号/dotのbinding、中間round列、限定3×1 tailのderived Contextは接続済み。
   indexed quicksort/compactionの全実行同値、単一typed設定から全phaseの投影は接続済み。
   source/compiler refinementと外側統合入口への接続は残る。
   固定generatorの数学的位数は証明済みだが、native依存/codegenからの生成対応も対象に含める。
2. 全14 gate評価の式から実多項式次数・gate意味論・sumcheckへの接続を証明。
   PI cacheの証明済み同値、selector/lookupの入口接続も全体経路へ反映。
3. setup/VK/config生成、immutable store、全compact decoder、metadata decoder、
   初期transcript・真のchallenge・public-input hashをIntegratedへ接続。
   現在別モジュールのWhirFinal/Merkleを、全whirTailの代替と誤認しない。
4. 証明済みの素数性・具体Ext3有限体/逆元を、Rust/Yulの実行意味論へ接続し、
   手動対照を形式的refinementへ置換。evalL0のモデル内証明も全呼出し経路へ適用する。
5. honest proverの全段階、completeness、再帰回路/親statementとのcompositionを証明。
6. 暗号仮定を明記したPCS/Fiat–Shamir/grindingの定量的健全性を証明。
   全てのhashに無条件の数学的安全性があると仮定しない。

現target105の約101.5-bit値はリポジトリのgeneric-work見積もりで、Leanが証明した
128-bit/end-to-end安全性ではありません。実装変更・デプロイ承認もこの更新には含みません。

GoldilocksCertificate単独は数値証明書であり、素数性の根拠はGoldilocksFoundationの
Lucas適用・全prime-divisor列挙・小因子の素数性の証明と組み合わせたものに限る。
Mathlib v4.10.0のcommitと公式lockの6依存を監査専用に固定し、直接importは特定の
モジュール/名称だけ許可する（Foundationの3import、NormのRing、WhirPolynomialのRoots、
WhirChallengeのFintype.Card、WhirQuicksortのList.Perm、CorrectnessのList.Sort）。
標準3公理allowlistと全名付き定理の検査は維持する。
依存guardは全tracked sourceの実Git blob・HEAD・origin・固定release tagと追加sourceを検査。
この検査は生成済み.oleanやProofWidgets release archiveの出自を認証しない。
通常Lakeビルドにはそれらの成果物とLean toolchainの信頼境界があり、全source-only再現とは呼ばない。
別途40モデル/1019定理のcheckpointで、固定7依存の非toolchain Lean source全1370モジュールを
空の新規出力先へ再生成し、その出力だけで全定理を検査した。実行前後のsource/hash/依存/JSを
照合し、既存の依存.oleanは使わない。ただし11個のProofWidgets JSは固定した既存データで、
JS source再生成・Lean toolchain/core artifactの再現・全実装/PCS証明を主張しない。
その記録は後続追加モデルのfresh検査済みという意味でもない。詳細はREPORTを参照する。
