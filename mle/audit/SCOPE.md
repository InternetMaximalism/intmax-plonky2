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
  DenseMleIndexedはext3.rsのbind loopを添字付きmutable bufferとして模し、各iで2i/2i+1を書込み前に読み、
  増順に書き、最後にtruncateすること、未書込suffixの不変、Valid表長=2^numVars、source numVars>0 guard、
  全bindMany実行とPacked.layer/foldの一致、affine Normへの橋を証明する。
  constructor/from_base/trailing_zeros、usize/メモリ/compiler refinement、endpoint由来の完全接続は残る。
- Transcriptのhashは任意の決定的関数。同一の旧digestの下でのhash前tag/payloadの
  一意性から、hash後の単射性・ランダム性は導かない。
  counterの結果はcheckedで成功する呼出しが対象。
  `commitClaims` 等のraw helperは、preflightでcanonical値・payloadのu64長上限が
  保証された環境を対象とし、そのpreflight接続自体は未証明。
  初期statement/root吸収の全手順と全Engineへの接続は残る。
  OuterInitialは外側初期transcriptの16frame（初期化domain、statement domain、circuit digest、
  raw public inputs、packed schemaと15語u64-LE metadata、config digest、64/32byteのWHIR識別子、
  preprocessed/witness root）と、eta→beta/gamma→norm-inverse root吸収→xi→lambda/rho/kappa→
  log tau→gate alpha→gate tauの順序・counterを具体化し、d≤13で全checked squeezeの成功と同一結果、
  識別子長guardのnone、toInitialの往復を証明する。40byte snapshotは内部adapterでproof wire fieldではなく、
  PI hash再計算・config digest計算・VK/config意味論・Hashの衝突耐性/uniform性・下流Engineの全埋め込みは未証明。
  OuterAdapterは40byte内部snapshotの無損失decode（長さ40以外はnone）、実coupledRoundへのcheckedな委譲
  （round domain→u64-LE round→log vec→gate vec→challenge domain→log limb 0..2/gate limb 3..5、結果counter 6）、
  5個のclaim vectorと空の第6cell→index domain→log index列→gate index列（counter 3i/3·bits+3i）、
  既存Transcript.constituentIndicesとの全limb一致、Verifier.roundStepと定義的に同じchecked loop、
  初期識別子guard→checked導出→coupled rounds→claim/index→packed fold→whirContextのOption prefixを具体化する。
  malformed decodeをzero/defaultへ全域化しない。既存total Engineとの一致はCommitAgrees/SamplesAgree/初期一致/
  fold一致を明示した条件付き定理であり、任意Engineのsource同値・完全受理・PCS/WHIR接続ではない。
  shape外ではraw zipが不等長listを切詰めるため、source対応の結論はenvelope/shape/InputSizes前提下に限る。
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
  WhirRlcは同じgeometricPowersと実dotRowを具体多項式へ接続し、固定同長不同canonical
  vectorの一致点数≤n−1、明示uniform120byte lawの偏り込み上界を導く。
  count0/1はsourceどおり無消費、2以上は同じ120byte/four blocks/counter+4。
  初期phaseの全claim/cross吸収→vector RLC→次stateのconstraint RLCを接続するが、
  2つのHash出力の独立性・commitmentからの固定vector抽出・適応的fixednessは未証明。
  任意rowの式はzero-totalizationであり、実statement rowには別の検証済み境界定理を使う。
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
  OuterRoundは同じevaluateRoundの前向き係数和、具体inverse-two、逆向きHornerを
  具体Field上多項式へ接続し、端点和・次数・固定不同claimの一致点数を証明する。
  外側logのsource固定5係数loopへの適用には既存preflightの係数長5が必要。
  OuterChallengeは内側とは別に実3×32byte squeeze、同digestと連続counterを接続し、
  coupledRoundの両message吸収後log 0..2/gate 3..5と同じ多項式を保持する。
  明示uniform triple lawの固定多項式上界はd(ceil(2^256/p)/2^256)³であり、
  実hashの独立性・uniform性・適応的fixednessや両lane確率の積を主張しない。
  OuterInterpolation/Totalはcoefficients.rsのGauss消去（自然node、増順冪、RHS列n、pivot交換なし、
  対角inverse、pivot..=n正規化、pivot行clone、pivot以外の増順対象行、書込み前factor捕捉、増順列減算、
  係数順抽出）を添字付きで模す。証明専用のghost RHSで到達pivot値∏_{j<p}(p−j)を同定し、n≤pなら全prefix/
  全n段が成功して実WhirFinal.inverseが実行され、非空入力で全域、空入力は拒否する。degree<pで0..degreeの
  sampleから正確な係数と省略定数messageを得て、実evaluateRoundがf(r)を返す。norm次数5とchecked gateの
  q+2（q>0、q+2≤10）へ特殊化する。Vec/メモリ/compiler refinement、実current_roundのdataflow、
  回路truth、FS/PCSは含まない。
  configuration、decoder、initial transcript、gate/norm/eq評価、hash、WHIR tail等を
  入力付き関数観測として残す。例外・gas分類は実EVMの全分類ではない。
- Solidityのenvelope/deployment検査はconstructorで行い、callでは設定hashを照合する。
  `verify` はdeployment+callの複合境界、`verifyCall` は前者の検査を除いた境界。
  両者の一致にはdeployment invariantを明示的前提とする。hash一致だけからその前提を導かない。
- WHIRへの座標は `reverse(index) ++ reverse(row)`。Rust入口の `row ++ index`
  からnative adapterが反転する境界とSolidityが反転する境界を区別する。
- 6個のclaimのうち外側terminalで使う5個を拘束する。第6セルは外側では未拘束で、
  WHIR内の処理対象であることと外側期待値との一致を混同しない。
  OpenedClaimFoldは採用済みPacked.fold/Connections.packedFold/DenseMleIndexed.bindManyの
  row++index分割（同じ関数の結合則で、再実装ではない）、pack_mlesの列優先padded table
  （row bit下位・index bit上位、2^indexBitsまでzero列）の全表評価=各列row openingのpacked fold、
  Solidity cell 0-2/log index点・3-4/gate index点・cell 5 noneとRust slot point·3+groupの一致、
  native点=dense点の反転を証明し、5個のclaimed cellが各列のrow foldに等しいという明示的
  honest-prover仮定の下でのみ、expectedClaimsの各cellがpadded tableのWHIR点でのdense評価に
  一致することを導く。不正なcellでは一致しない具体例も持つ。opened値が真のPCS開示であること、
  WHIR受理、FS、Rust/EVM refinementは主張しない。
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
  NormPolynomialは実denominator/formal adjugate/norm/recomposition、wireStepの1寄与へ
  concrete Field上のaffine入力多項式を接続。formal座標もExt3係数なので、canonical
  Ext3の非零norm定理を使わない。helper≤4、eq重み込み行≤5、logUp≤3、PI≤2、有限和≤5。
  lambda/etaの実乗算回数への重みbuilderも証明するが、全行builderへの一括適用は未接続。
  round_evaluation_actualの右辺は捕捉endpoint上の候補内行/PI式であって、Norm.checkedEvaluateや
  Rust mutable arrays全体への同値ではない。
  NormDenseRoundはnorm_logup.rsのline_value、evaluate_target_from_values（幅assertはnone、単一loopの
  2累積、xi·ZERO項保持）、round_sum_at（wires.len()幅の4 scratch vectorをindex loopで書き、suffix loop、
  row>>(bound+1)/(row>>bound)&1のPI loop、sum+xi·binding）、current_round（is_complete→Err、cache、
  Field64_3::from(0..=5)のsample、採用済みOuterInterpolation.interpolate、coefficients[1..]）、
  bind（旧bound_variablesでprefix更新→+1→全表のbindBuffer、num_vars=0はnone）、prover stateの
  Err/panic/Consistent/PrefixProvenanceを添字付きで模す。Shape下でroundSumAt=roundValue、6 sampleが
  次数5のroundPolynomialのsamplePolynomial、省略定数=coeff 0=verifierの半和復元、送信5係数を実
  Verifier.evaluateRoundが端点和claimからround値へ復元、全読取り境界、bind後のShape保持、
  prefix=booleanRowEq(bound point)の保持を証明する。Shapeは構成子assertの呼出し側不変条件で
  新runtime guardではなく、from_baseのbase→Ext3転置・eq_evals_ext3・PreparedChallengesの重み由来、
  scratch書込みのinterleave順、不正prover/transcript/round連鎖、PCSは未証明。roundSumAt自体は
  totalized読取りなので、Shape下の各round定理は0<remainingを前提にして境界定理の範囲に留め、
  state定理はConsistent∧¬isCompleteからこれを導く。
  NormTerminalBindingは全変数bind後（remaining=0）の表をNormTerminalInput（constants++sigma cells、
  routed wire cells++非routed tail extra、identity helper cells++sigma helper cells、bindingsのPI値）へ
  明示的に対応させ、proverのtargetValueとverifier側Norm.permutationTerminal/evaluate（eq/subgroup値を
  引数化したevaluateWithはrflで同じ）の項ごとの一致、各bound cell=採用済みDenseMleIndexed.evaluate/
  Packed.fold/Connections.packedFold、|point|=remainingでのbind成功と全列単一cell、最終round
  （remaining=1）のroundValue=bind後表のterminal target、honest proverのend-to-end定理を証明する。
  eq cell=Norm.eqEvaluation(tau,point)、subgroup cell=subgroupEvaluation、lambda running product、
  eta冪、wire mapのbyte由来、kIs一致、shapeValid、normTerminalInput proof=対応表、challengesFromInitial=
  prover challengesは可視の仮定であり、eq_evals_ext3(tau)・from_baseの転置・PCS claimed値=prover cell・
  不正prover・transcript・Rust/EVM refinementは主張しない。
  OuterClaimChainはhonest proverのlog laneを、採用済みVerifier.roundStep/runRoundsに同じcommit引数で
  proverのcurrentRound→bindChallengeを組み合わせて駆動し、各round後のlogClaim_i=roundValue(t_i,p,r_i)、
  最終claim=最後にround_sum_atが走った表での値、次表のf'(0)+f'(1)=前表のroundValue(r)（2≤remainingと
  全隣接/PI読取り境界を証明）、初期零claim⇔端点和零（零性は仮定しない）、intoProofAndPoint=verifierが
  消費したmessage列/challenge列、Verifier.derivedRoundsとの一致、OuterAdapter.runCheckedとの一致を証明する。
  gate laneは採用済みgate proverにbind_challengeモデルがないため「復元が整数grid上の次数≤d多項式と
  一致する」明示仮定でparameteriseし、gate proverを偽造しない。任意messageの健全性・FSは主張しない。
- Gatesは14familyの設定検証、GatesAdditional/CosetとPoseidon/Constantsは残る8familyを具体化。
  GatesCompleteは全14familyを実計算し、valid設定と入力長ならSomeが得られることを証明する。
  Integratedはこのcomplete dispatcherを使う。基礎Gates単独のpartial dispatcherと混同しない。
  全1147定数はソースと逐語比較するが、抽出検査をformal refinementとは呼ばない。
  zero-filter skipは保持する。degree budget検査から式の多項式次数証明は導かず、
  集約値0から全制約0への逆方向も主張しない。
  GatePolynomialは全14familyのzero-filter分岐を同じ具体term/Hornerへ同一化し、
  selectorの実因子と固定alpha Hornerの次数を導く。GateBasicPolynomial/Mdsは
  IDs 0,1,2,3,5,6,7の実制約式へ評価一致を証明し、両wire/constant列のaffine入力から
  それぞれ次数0,1,1,3,1,3,3を導く。Arithmeticのlocal constantも変数なので上界は3。
  GateCheckedPolynomialはこの7familyだけで、実validateGate/両入力長/全設定の検査から
  選択行寄与≤q+1、明示affine重み後≤q+2を証明する。残る7familyはsymbolic NONE。
  重みの実eq列由来、全行和、補間/送信係数、各gate真偽・認証endpointは別境界。
  GateLoopPolynomial/Random/TwelveはIDs8〜12を追加し、Exponentiation≤4、BaseSum≤base、
  Reducing2種≤2、RandomAccess≤bits+1を実計算から導く。Reducingのaccumulatorは毎回
  claimed-next wireへresetし、制約成立を次数の前提にしない。RandomAccessのscratchは
  実際に再計算し、bitごとに次数上界が増える。Boolean性・range truthは仮定しない。
  実metadata/全設定/両入力長から12familyの寄与≤q+1/affine重み後≤q+2を証明する。
  前段7family dispatcherとこの12family dispatcherを区別し、Poseidon4/Coset13のNONEは残す。
  GateCoset/Poseidon/AllPolynomialはPoseidon4の全30round（swap/delta、各S-box前のfresh wire、partial最終
  roundの定数省略、circulant/sparse MDS）を制約消失を仮定せず123制約・次数≤7、Coset13のold-product評価→
  更新/reset/中間claimed E-Pを4+4·intermediates制約・D≥2で次数≤Dとして証明し、全14familyの実validateGate
  から寄与≤q+1、affine重み後≤q+2を導く。この全family wrapperにsymbolic NONEは残らない。
  GateAggregate/SuffixPolynomialは実combineRows全行の順序付き集約を1多項式へ接続して次数q+1、実設定包絡
  q≤8から重み後≤10、2s/2s+1の実読取りと同一challenge補間、0..2^remaining−1のBoolean suffix和
  （remaining=0を含む）を同じ多項式で証明する。TableShapeは供給表への明示条件で新runtime guardではない。
  GateSlotAlgebra/Commutation/RoundはRustのgate_ext3.rs 543-608（各gateをfilter零でも評価し、
  出力数ensure後にaccumulated[slot]+=filter·valueを固定幅bufferへ書き、forward alpha powersで還元）を
  添字付きで模し、範囲外writeはsourceのpanicどおりnoneとする（totalizedなList.setをsource挙動と
  主張しない）。validateRows/validateConfigurationから全writeが範囲内で、slot-first結果が
  実combineRows/evalCombinedと一致、同じ多項式（≤q+1、重み後≤q+2）を持つことを証明する。
  gate_ext3_v2.rs 105-134のcurrent_round（numVars>0 ensure、half=len/2、zero初期化のdegree+1 cell、
  suffix外側・integer内側のmutable累積、(1−x)·t[2s]+x·t[2s+1]の実読取り）を同じslot評価器で模し、
  実行された累積が整数ごとのsuffix優先和GateSuffixPolynomial.currentRoundValueに一致、
  Valid eq表でhalf=2^(numVars−1)、TableShape下で全cellが1多項式（≤q+2≤10）の値であることを証明。
  ext3_evaluations_to_coefficients呼出し（136）とdegree構成検査（80-83）、DenseMle構成、
  tau由来のeq表、canonical publicHash preflight、reduced emitter、Rust validate_gate_ext3_context成功から
  Lean validateConfigurationへの橋、回路truth/PCS/FSは未証明。
  GateTerminalBindingはgate_ext3_v2.rs 142-161のbind_challenge（degree ensure→eq表→全wire→全constantの
  採用済みbindVariable、rounds/point push、失敗はnone）とinto_proof_and_point（eq.num_vars=0 ensure）を模し、
  構成子ensure 70-79をProverShapeとして全変数bind後に各列が単一cellで採用済みpacked fold/
  DenseMleIndexed.evaluateに等しいこと、最終round（half=1）のeq·aggregateがGatesComplete.evalCombinedと
  一致し、eq cell=Norm.eqEvaluation(gateTau,gatePoint)・claimed cell=prover cell・alpha=gateAlphaを明示仮定
  したときVerifier.gateTerminal/Integratedの受理式に一致することを証明する。honest prover限定の定理は
  そのように表示する。degree ensure 80-83、eq表のtau由来、係数補間、transcript、WHIR/PCSは未証明。
- Integrated.verifyはchecked norm形状と7challenge layout、同じ入力での全gate計算の
  Someを検査後、packed/norm/eq/gateを具体化したVerifier.verifyへ進む。
  modelEngineだけの利用にはこの保証がなく、getD zeroは旧interfaceへの全域化にすぎない。
  metadata decoderは固定Config.gatesEncodingだけを受ける観測であり、初期FSや
  configuration hash、WHIR tailを具体化したわけではない。
  public input hashはPublicInputHashBindingで具体化した。採用済みPoseidon置換の上に
  実hash-no-padスポンジ（rate8/capacity4/width12、overwrite mode、⌈len/8⌉ chunk、
  末尾短chunkは占有slotのみ上書き、4要素digest、空入力は置換0回）を構築し、全30roundで
  c1=c2=0が保たれること、c0読出しが状態を失わないことを証明する。raw public inputsの
  preflight（256語上限と各語<p、拒否時にreductionを行わない）も模し、受理語では恒等であることを
  示す。これによりgate terminalのhash観測を具体関数へ置換し、GateChainHypothesesのhashLength仮定を
  除去した系を与える。Solidityは`MleVerifierV2.sol:382`でcalldataをhashするため、
  `PoseidonGate.sol:77`の検査は外部library入口を守るものであり、verify内では
  `_copyCanonicalBase`が先に同じcalldataを走査するため多重防御である。2つの走査の順序は未モデル化。
  Rustは型でcanonicalなため範囲検査を持たず、256語上限もSolidityのみである。
  置換の値としての正しさは採用済みPoseidonConstantsの主張と外部test vector 1行に依存する。
  追加preflightの失敗分類/順序はモデル上のもの。実装の例外・slashing証拠とは未接続。
  Gates.rustAdmissionのlookup拒否もこの入口には未接続。
  IntegratedTerminalChainは採用済みのOuterClaimChain/NormTerminalBinding/GateTerminalBinding/
  OpenedClaimFoldを再実装せずにVerifier.verify/Integrated.verifyへ接続する。名前付き仮定構造
  （HonestNormProver: shape/fresh/positive/bindings/rounds/零cube和、NormTerminalProvenance: eq/subgroup
  cell・challenges・rounds・claimed cell=prover cell、GateChainHypotheses: gate表のshape/bind/cellsと
  OuterClaimChainのgrid一致仮定、HonestOpenings: claimed cell=各列row fold）の下で、honest proverの
  logTerminal=derivedRoundsの最終logClaim、gateTerminal=最終gateClaim、5 WHIR期待claim=padded tableの
  dense評価・第6 cellはnoneを導き、verify_success_checksの逆向き補題verify_of_checksで
  Verifier.verify/Integrated.verifyが受理することを示す。残る前提はObservationOnlyとして列挙した
  観測（chain/config hash/envelope/deployment/shape/4長さ/verifyWhir/7 challenge/normShape）だけである。
  Rust順（WHIR→norm terminal）とSolidity/Lean順の受理はProp水準の同値で、revert理由やgasは扱わない。
  grid仮定はgate running claimの端点和一致を含意するhonest prover仮定であり、claimed値とprover cellの
  一致・PCS/WHIR健全性は依然として仮定である。
  EqTableProvenanceは実eq表builder（gate_ext3_v2.rs 26-39とnorm_logup.rs 360-374の同一loop nest。
  byte一致ではなく束縛子名のみ異なる。eq_poly.rsは旧経路の基底体版）を、tau順の外側loop・index内側loop・
  左側累積・(i>>j)&1による因子選択まで模し、各entryが採用済みNorm.booleanRowEqであること、
  採用済みbindBufferの2i/2i+1 pairingから低位bitが先にbindされることを証明する。
  全点bind後のeq cellはNorm.eqEvaluation(tau,point)に等しく、subgroup列は等比列でverifierは
  これをfoldせず(1-r_j)+r_j·g^(2^j)の積を取るので、その積が全bind後のcell/Packed.foldに等しいことを
  証明する。これによりNormTerminalBinding/GateTerminalBindingのeq/subgroup由来仮定を除いた系を与える。
  VKのsubgroup_gen_powersが表の生成元の反復二乗であることはVkSubgroupProvenanceで解消した。
  transcript由来の対応はTranscriptProvenanceで扱う。
- VkSubgroupProvenanceはplonky2のtwo_adic_subgroup（TWO_ADICITY=32、固定two-adic生成元、
  exp_power_of_2による位数2^k根、powers()の列挙順）とVK生成元導出（verifier_v2.rs 134-143、
  prover_v2.rsの同一loop）を模す。採用済みGoldilocksDomainの生成元7はplonky2のtwo-adic生成元とは
  別物なので、固定生成元の位数2^32は核が実際に評価した2つの冪証明書から確定した。
  そのうえでverifier_v2.rs 130-147の再計算検査が「VKのpowersが導出生成元の反復二乗である」ことと
  同値であること（両方向）を証明し、EqTableProvenanceのSubgroupPowersProvenanceを仮定から定理へ移す。
  Base側の乗算は新しいinstanceを足さずArithmetic.mulで扱い、canonical limb上の単射性で逆向きを閉じる。
  verifier_v2.rs 136のunwrap_orは1≤nLogでは到達せず、nLog=0では導出値と一致することも示す。
  残る仮定はdegreeBitsが норм stateの変数幅と一致すること、およびprover側subgroup列が
  埋め込まれたtwo_adic_subgroupであることの2つで、いずれも可視のフィールドである。
  ソースはn_log>32でpanicするがLeanの切詰め減算は受理するため、iffが実装に忠実なのは
  degreeBits≤32の範囲であり、envelopeがdegreeBits≤13を強制するため到達不能である旨を明記する。
- TranscriptProvenanceは「engineの初期transcriptがOuterInitialの実導出そのものである」という
  単一前提DerivedInitial（採用済みOuterAdapter.execute_matches_existing_derived_contextが既に取る
  仮定と同一で、withInitialならrfl）から、Norm.challengesFromInitialが導出した7 challengeを
  そのまま返すこと、log tau列・gate tau列・gate alphaが導出値であること、各challengeが
  sourceのdigest/counter位置（eta 0、beta 0、gamma 3、xi 0、lambda 0、rho 3、kappa 6、
  log tau 9+3i、gate alpha 9+3d、gate tau 12+3d+3i）に載ることを証明する。
  これによりIntegratedTerminalChainのObservationOnlyは12項から9項へ減り、
  NormTerminalProvenance・GateChainHypotheses・NormColumnProvenanceの各仮定も1つずつ減る。
  hashは任意の決定的関数のままで、単射性・uniform性・random oracle性は一切使わない。
  すなわちこれは順序と受け渡しの同一性であって、Fiat-Shamir健全性ではない。
  gateのhptは解消ではなく同値な言い換え（hpoint）であり、依然として仮定である。
  DerivedInitial自体と、prover側のchallenges一致は残る仮定である。
- ConnectionsはLeanモデル間の具体的な型・foldの接続。全Engineを具体的に実装したわけではない。

## 未完了の全体証明（優先順）

1. 具体化済みWHIR initial/最初のsumcheck・中間round・内側byte/PoWから終端へつなぎ、
   Plan/ContextとfixedVK/root/pointへの認証を接続。raw row bytes→leaf hash→multiproof→
   各queryの開示path→終端比較を一つの実行経路として証明。raw row→multiproof→path→
   復号/dotのbinding、中間round列、限定3×1 tailのderived Contextは接続済み。
   indexed quicksort/compactionの全実行同値、単一typed設定から全phaseの投影は接続済み。
   source/compiler refinementと外側統合入口への接続は残る。
   固定generatorの数学的位数は証明済みだが、native依存/codegenからの生成対応も対象に含める。
   installed 水準の具体成功は WhirTailWitness が初めて示した: 3主張と配備Arityの6主張の両方で
   `WhirConfigured.run` / `InstalledWhirTail.tailRun` が成功し、`parseWhir` と `whirTail` を両方 installed にした
   `Verifier.verify` も `rfl` で受理する（`configured_six_claim_execution_example`、
   `installed_whir_pair_accepts_a_full_verification`）。ただし定数 toy hash・`exampleNoRounds`・
   `Verifier.testConfig`（1変数）であり、`DerivedAcceptance.derivedConfig`（21変数）への接続と
   配備プロファイルの実 PoW は未構成。マスク `[⟨31⟩]` 対 `[⟨7⟩]` はブロッカーではなく主張数が実障害だった。
2. 全14 gate評価の式から実多項式次数・gate意味論・sumcheckへの接続を証明。
   全14familyの実式/設定済み行次数、全行和とBoolean suffix和、外側係数復元と補間全域性は
   接続済みで、Rust slot-first順序との可換とcurrent_roundのgrid転置も接続したが、
   補間呼出しの一本化・DenseMle endpoint由来・回路truth chainへの接続を完成したとはしない。
   PI cacheの証明済み同値、selector/lookupの入口接続も全体経路へ反映。
   GateEvaluatorCoverageで被覆を定理として固定した。Integratedが使う完全dispatcherは14 family全てを
   評価し次数上界も揃う（基礎Gatesの部分dispatcherはid 0,1,2,3,6,7のみ。ExplicitEngineの注記はこの
   区別を誤っており、次回のdoc更新で訂正する）。宣言表はgate_ext3.rsとPlonky2GateEvaluatorExt3.solから
   転記し採用済みrequirementsと一致、plonky2の各gateのnum_constraints/num_wires/degreeとも一致する。
   次数はRustでもvalidate_gate_ext3_contextがGate::degree()で同じ不等式を検査するので乖離はない。
   形状検査付き評価器で短い行の既定値評価を内在的に排除し、検証済み行では完全dispatcherと一致する。
   所見: RandomAccessGateの124制約行（bits 1・copies 18・extra 70）は個別検査を通るが設定検証と
   envelope 123（MAX_GATE_CONSTRAINTS_V2）で排除される（sumcheckのround次数には影響せず、alpha-Hornerの
   根上界を1増やすだけ）。BaseSumのbase 16以上は次数＝baseの会計で設定不能。Lookup系はgate idを持たない。
   回路真理（制約消失＝実witnessによる充足）は依然主張しない。
3. setup/VK/config生成、immutable store、全compact decoder、metadata decoder、
   初期transcript・真のchallenge・public-input hashをIntegratedへ接続。
   現在別モジュールのWhirFinal/Merkleを、全whirTailの代替と誤認しない。
4. 証明済みの素数性・具体Ext3有限体/逆元を、Rust/Yulの実行意味論へ接続し、
   手動対照を形式的refinementへ置換。evalL0のモデル内証明も全呼出し経路へ適用する。
5. honest proverの全段階、completeness、再帰回路/親statementとのcompositionを証明。
6. 暗号仮定を明記したPCS/Fiat–Shamir/grindingの定量的健全性を証明。
   全てのhashに無条件の数学的安全性があると仮定しない。
   ConditionalSoundnessはこの方向の最初の一歩であり、完成ではない。
   18個の仮定（適応的固定性、challenge law、抽出した表とその形状・truth chain・
   最終roundの構造的対応、eq/subgroup/lambda/wire-map/transcriptの由来、
   terminalのclaimed値=prover cellという抽出接合）を可視フィールドとして列挙し、
   Integrated.verifyが受理しlog laneのどのroundでもdrawn challengeがbad setに入らないなら、
   抽出した表のendpointSumが0であることを導く。これはIntegratedTerminalChainが
   HonestNormProver.zeroSumとして仮定していた命題であり、循環なく導出されている。
   bad setの濃度は195·⌈2^256/p⌉³以下（degreeBits≤13とquotientDegree+2≤10から195を導出）。
   **重大な限定**: gate laneは証明していない。初稿のgate結論は退化しており削除した。
   GateDenseRoundが障害3つを解消し、GateClaimChainが(1)多round帰納・(2)向きの転換・
   (4)terminal橋を、ZeroCheckSemanticsが(5)意味論的段階を扱った。
   GateClaimChainは受理とgate lane bad eventなしから抽出表のcube和=0を導き、
   gate lane固有の上界(q+2)·degreeBitsも再具体化する（ConditionalSoundnessの195はこのlaneには
   適用されない）。ZeroCheckSemanticsは採用済みeqの多重線形拡張の零点密度≤n/|F|を証明し、
   bad set外のtauで各行値が0になる系を与える。
   **ただしgate健全性は完成していない。** 現時点でGateClaimChainの定理には敵対的な供給者に対する
   棄却力がない。仮定はeq表の1つの線形汎関数（bound cell）しか固定せず、cube重みの行和は独立なので、
   正しいbound cellを持ちつつ行和が0のeq表を選べる。同種の退化は他にもあり、
   `numGateConstraints=0`（envelopeは下限を課さず、採用済みexample configがこれ）は
   可視の仮定4で除外したが、selector filterを全て零化する経路は残る。
   さらにZeroCheckSemanticsのbad setは採用済みbadSetsと合成しない（単一challenge対n組で、
   n重積事象が未構築）。bad setがprover自身の表で添字付けられるため、適応的選択の扱いも要る。
   eq表のgateTau由来を全行で固定することはGateRejectionPowerで扱った。
   採用済みeqの単位分解（cube上の行和が恒等的に1）を証明し、eq列を全行`eqTable tau`へ
   固定すれば行和ゼロのeq表が存在しえないことを導く。攻撃シナリオ（eq列ゼロ、行和ゼロ、
   制約数ゼロ、形状不一致、selector全零化）はそれぞれ定理として提示し、
   強化仮定が旧仮定の受理していた偽造状態を棄却することを具体例で示した。
   AlphaZeroCheckは行の集約をalphaの多項式として係数を同定し（係数はslot値そのもの）、
   根の個数≤numGateConstraints−1≤122をenvelopeから導き、bad set外のalphaで各slot値が0、
   filterが非零のgateは制約自体が0であることを示す。tauとalphaの両zero-checkの合成も
   採用済みchallenge上で証明した（alphaはgate tauより前のcounterで引かれる）。
   selectorの部分的零化はConstantsProvenanceで由来鎖として明示した。selector値←供給constants列
   （source-boundedなget?読み、getD既定値なし）←導出gate点でのbound cell←gatePreprocessed.take numConstants
   のclaim←committed列のbound cell←preprocessed root下のopening←deployment pin（Verifier.shapeの
   `p.preprocessedRoot = pin.preprocessedRoot`、verifier_v2.rs 184-187、MleVerifierV2.sol 563）。
   攻撃定理partial_zeroing_forces_one_of_three: 供給列とpinned列のbound cellが導出gate点で異なれば、
   root不一致（pinで閉鎖）か抽出接合CellsMatchClaimsの破れかopening関係OpensCommittedTableの破れの
   いずれかが必ず起きる。具体的偽造例（重要行のみ零化）で、旧仮定（activeFilter等）は検知しないが
   新鎖は接合で捕捉することを示す。最強gate定理をpinned列上のfilterで再述した。
   bound cell一致と列同定の差はGatePointZeroCheckで導出gate点上のSchwartz–Zippelとして扱った。
   cell(bindColumn col point)=extension col pointの橋渡し（2^|point|≤|col|で成立。短い列ではbindColumnが
   切り詰めextensionがゼロ埋めするため破れる反例つき）により、2列の一致集合は差分列の多重線形拡張の
   零点集合で、列がcube上で異なれば濃度≤n·|F|^(n-1)、一様積法則上の質量≤tauTerm n。合成定理: 列が
   異なり導出gate点が一致集合外なら、受理下で抽出接合CellsMatchClaimsかopening関係OpensCommittedTableが
   破れる（root分岐はpinで閉鎖）。供給列の幅2^degreeBitsは採用済みConsistent+EqCellBindingから、
   committed列の幅はopening関係のfull条件から導出され、追加の幅仮定はない。gate点列がgate laneの
   round challenge列そのものであることを抽象engineで証明し、JointChallengeSpaceの第4族として
   outerGate座標上の質量≤tauTerm dを得る。
   供給列を点の一部を見てから選ぶ読みはAdaptiveAgreementFamilyで扱った。一致集合を座標ごとの
   Schwartz–Zippel（各座標のbad setはaffine制限の根で濃度≤1、恒等零の場合は数えず先行座標に課金）に
   分解してOuterSequentialConditioningのadaptiveエンジンに載せ、供給列を最初の`cut`座標のみの関数として、
   質量≤tauTerm d、第5族込みの結合bad事象≤combinedBound+tauTerm d（envelope極値で≤2^-171）を得た。
   **ただし二分法の形でのみ閉じる**: 実現prefixを通るaffine slice上で差分列の拡張が恒等的に零になるか、
   点が質量≤tauTermの集合に入るかのいずれかである。前者は偽造者が1座標を見ただけで構成できる
   （cc+(x0 / −(1−x0))型の列で第5族は空になる。形式的残余証人として証明済み）ため、R2/R3に渡される
   残余類は「実現prefixのslice上でcommitted列と拡張が一致する列」であり、全座標を待つ必要はない。
   新たに覆われるのは残差を保つadaptiveな選択（多数の異なる列から選ぶ場合の費用がtauTermで済むこと）
   だけである。cut=dでは事象は空で上界は空虚、cut=0・定数colOfはGPZCの固定列の読みに一致する。
   Lane水準の凍結比較はDrawEncodesRun下でlaneごとに両方向同値として証明した（OSCの未証明項目を閉じる）。
   **なお未解決**: 供給列s0.tables.constantsは結論の2分岐（R2/R3）以外ではrootに束縛されない
   （half (B)は未形式化）。
   round digestがprefixの後に連鎖することは具体engineでのみ文書化（抽象engineでは未導出）。
   engine不透明性R1、opening関係R2、root→列写像R3は可視仮定のまま。
   tauの束縛はGateDerivedRejectionで扱った。棄却定理と合成定理をtranscript導出の
   gate tau/alphaで再述し（DerivedInitial下、eq列は導出tauのeqTableに全行固定、cube indexは
   採用済み列長から導出）、bound cell仮定を全表eq由来と構造的binding fieldから導いて、
   自由なchallenge値を含まない9フィールドの縮約仮定集合を与える。§2のみ例外で、
   暗黙の自由alphaを保持しtauを具体化するに留まる。残るchallenge側の仮定は3つ、
   導出tau/alphaに関する2つのhgoodと、sumcheck roundのchallengeに関する採用済みBadEventFreeである。
   これらは依然として仮定であり確率ではない。
   適応性の決定論的半分はCommitmentOrderで扱った。gate alpha/tauのsqueeze前に吸収される
   prefixは22 frameで採用済みrelationStateと一致し、preprocessed/witness/norm-inverse rootは
   13/15/19番目、最終rootとsqueezeの間は固定domain tag 2つだけである（実装の
   MleVerifierV2.sol 400-455とverifier_v2.rs 233-275で照合）。gateのbad setはeq列に依存せず
   committed wire/constant列にのみ依存し、表を変えつつprefix digestを保つには具体的な
   transcript衝突が要ることを、衝突耐性を仮定せずに示す。確率的半分（squeezeがprefixに対して
   uniformかつ独立であること）は定数hashに対する反例で否定されるため、順序論法では得られず
   hash仮定として残る。gate list・設定・public input hashは固定パラメータであり、
   その config/VK digestからの由来はここでは証明しない。
   union boundはChallengeUnionBoundで扱った。tauのzero-check bad setをn個の独立digest tripleの
   積事象へ持ち上げ（採用済み単一座標のfibre上界を座標ごとに適用、指数3n、n個の独立性は
   明示的な積の法則であってKeccakの性質ではない）、行ごとのalpha bad setを2^n行のunionへ
   持ち上げて濃度≤2^n·(numGateConstraints−1)≤122·2^nを導き、外側sumcheck項
   （norm 5·d、gate (q+2)·d）と合わせて3つの質量の和を上界化する。envelope極値
   （degreeBits 13、q 8、制約123）で等式として展開し、有理数の厳密計算で≤2^-172を証明した。
   **この数値の読み方**: 余裕は約0.07 bitでenvelopeぎりぎりであり（degreeBits 14で破れる。制約数は123〜128まで成立し129で初めて破れる。以前の「125」は誤記）、
   WHIR/Merkle項を含まないため系の健全性誤差ではない（設計点は約100 bit）。3項は別々の
   標本空間上の質量の和であった。filterが零の行は非拘束であり、これは
   selector範囲外の行として正しい挙動である。
   結合事象はJointChallengeSpaceで形式化した。squeeze schedule（gate alpha、gate tau×d、外側log round×d、
   外側gate round×d、計3d+1座標。log/gate roundは同一round digestのcounter 0と3で別のsqueeze）で添字づけた
   `Draw d → DigestTriple`上の一様計数測度を定義し、座標事象とtau積事象の質量を計数で証明、
   真のdisjunction事象の質量≤combinedBound（joint_union_bound、外側項は両laneの2d座標を被覆）を証明した。
   seam `DrawEncodesRun`は「run の challenge がある1点の座標ごとの縮約である」という座標符号化の主張で、
   reduceTripleの全射性により全hash・全engine・全受理実行で可住であることを補題として示す。
   したがって**hash仮定ではない**。Fiat–Shamir半分(B)＝「符号化drawがjointProbability分布に従う」は
   Lean上のどこにも表現されておらず、合成定理は暗号仮定を一切持たない（質量連言は計数事実、
   結論連言は「runのdrawがbad set外なら制約が零」の含意）。外側roundのbad setは実現した
   challengeとround messageに相対的で、prefix定数なのはtau/alpha族だけである。
   逐次条件付けはOuterSequentialConditioningで証明した。有限積空間上の一般エンジン（Nodup座標列、
   round kのbad setは先行座標のみに依存するPrefixDependent族、Fubiniの剥ぎ取りで質量≤Σ c_k/|A|）を、
   round messageを先行challengeの関数とする`Lane`で両laneに具体化する。走査順は実装どおりroundごとに
   log→gate（両challengeは同一round digestのcounter 0/3、両messageは1回のcommitで先に固定される。
   モデルはgate messageが同roundのlog challengeを見ることを許し実物より強い敵対者を扱う）。adaptive
   外側事象の質量≤outerTermでprefix凍結版と同じ数値、adaptive結合bad事象≤combinedBound。凍結版
   laneEventはエンジンの特殊例で採用済みjoint_union_boundを再導出する（Lane水準の凍結比較は
   DrawEncodesRunを要し未証明）。ConditionalSoundness ASSUMPTION 3の逐次条件付け部分はこれで閉じるが、
   法則は依然として手で書いた理想一様分布であり、half (B)は未形式化である。schedulePositionはモジュール自身の写像で、alpha/tauは
   DerivedInitial経由で固定されるが外側round座標のラベルは抽象engineに対して文書化のみである。
   受理実行への束縛はAttachedUnionBoundで扱った。tau arityはdegreeBitsから導出（derived_gate_tau_width）、
   行値はgateValue、alpha側の係数族は受理由来のslotCoefficients、制約数≤123は受理から導出し、
   attached tupleがtranscriptの導出tau列そのものであること（attached_tau_tuple_ofFn）と、
   attached bad setの回避が採用済みGoodDerivedTau/GoodDerivedAlphaと同値であることを示す。
   combinedBoundは4引数すべてで単調（⌈2^256/p⌉·p≥2^256による）で、envelope下で
   ≤combinedBound 13 8 13 123≤2^-172。attached_seamが計数上界と「導出tau/alphaがattached bad set外なら
   全行で選択gateの制約が零」を1定理に結合する。法則は依然として明示的な理想一様分布であり、
   tauの積構造は独立性の仮定そのもの、実transcriptとの橋（Fiat–Shamir半分(B)）は与えない。
   195·(⌈2^256/p⌉/2^256)³≒2^-184は外側sumcheckの一致事象のみで、支配項のWHIR/Merkleを含まない。
   実装の設計点は約100 bitであり、この数値を系の健全性誤差として引用してはならない。
   failureは自由な有理数で上からしか抑えられておらず、実確率との橋渡しはどのフィールドも与えない。
   第1連言と第4連言は合成されておらず、実行に関する確率空間はこのファイルにない。
   Assumptions全体の充足可能性は示していないため、instantiation次第では空虚になりうる。
   抽出とcommitmentの接合はOpeningBindingで部分的に扱った。同root/index/depthの2つの受理
   openingが同じraw row・復号値・dotを返すことを、実行から計算した有限listに対するhashの
   単射性のみへ還元する（自由変数ではなく、空listへの具体化で定理が空虚化しないことも確認済み）。
   これはbindingであって抽出ではない。「あるcommitted tableが存在してその評価である」という
   抽出はextractorを要し、ここでは証明しない。仮定17は双条件で書き換わるが、残余はfold水準
   （点でのbound cell値）であって列の同定より弱い。さらに限界を定理として明示する。
   不透明なengineのWHIR検査は任意のcontextとproofを受理するため、binding結果は具体的な
   WHIR verifierに置き換わるまで外側の受理と接続しない。opening関係は3つのMerkle rootを
   任意に差し替えても成立するため、同root性からこの関係を導くことはできない。
   復号したrowをp.usedのどのfieldにも結び付ける定理もまだない。
   engine不透明性はInstalledWhirTailで扱った。採用済みの手動WHIR tailモデル`WhirConfigured.run`を
   Integrated.modelEngineの`whirTail`に据え付け（parseWhir・configurationHash・deploymentValid・
   initialTranscript・commitRound・sampleIndices・publicInputsHashは観測のまま、transcript/roundは不変）、
   受理から具体tail実行の成功、3 rootが[pinned preprocessed, witness, normInverse]であること、初期評価値が
   5つのbound cellのpacked foldであることを導く。session/instance（instanceは空）、claim mask `[31]`、
   評価点のctx.pointsによる上書き、root byte変換の可逆性は実装と照合済み。配備プロファイル（v2 fixtureは
   numRounds∈{1,2,3,4}）では3 rootが中間round 1で開かれ、各root位置のrowが`(initialOpen wp).merkleDepth`
   でMerkle認証されること、2つの受理実行が同root・同leaf indexで同じrow bytesを返すか具体的衝突を出す
   ことを、OpeningBindingの入口（openGroups）を通して証明した（inDomainSamples>0の下でindex非空も導出）。
   numRounds=0のfinalsplit経路は別掲で、配備系ではない。このengineは空hintの例を実際に棄却する。
   **なお未解決（R1b）**: 「最終検査が通れば期待値が認証済み行の多重線形評価に等しい」は、3 rootと
   round-1 opening のみから列族を抽出する固定関数の存在（TailExtractsCommittedTables）として可視仮定に
   した。WHIR近接性・list decoding・sumcheck健全性（確率的）に当たり未形式化。per-column形はR3を包含する
   ため fold 水準の変種も併記した。`wp`（WHIRパラメータ）は engine の自由パラメータで、ソースでは
   profile digestで固定されるがLeanでは観測にとどまる。R2は変わらない。
   `wp`の固定はPinnedWhirProfileで扱った。`CanonicalWhirProfileV2.validateCanonical`の4制約
   （1≤numVariables≤21、sessionId、`keccak256(abi.encode(config.whir))`=表の行[0:32]、protocolId=行[32:96]。
   MleVerifierV2.sol 150-153）を`deploymentValid`の具体化として据え付け、受理から復号wpの正準性、
   tailが走ったレコードと検査済みレコードの一致、numVariables=degreeBits+indexBitsを導く。ソースは
   `inDomainSamples>0`を構文的にどこでも強制しないため、正値性とnumRounds≥1は表の意味論仮定
   `TableIsCanonical`（行digestの対応、keccak単射性の代役rowSeparates）の下で、転記済み2行
   （n=10、n=21。fixtureと生成表のkeccak再計算で一致を確認）に対してのみ導出する。他の19行はdigestのみで
   未転記（生成器から機械的に追加可能）。`c.whirEncoding=c₀.whirEncoding`は`_requirePinnedConfiguration`
   の理想化でkeccak単射性の残余として明記した。keccak自体・VK immutable store・復号器のRust/Solidity
   refinementは未モデル。
   index点samplerの観測はInstalledIndexSamplerで具体化した。採用済みの検査付きsampler
   （OuterAdapter.sampleResult：used claimsをdomain separator「pcs-constituent-claims-v3」、tag 6の5 frame
   （log preprocessed/witness/normInverse、gate preprocessed/witness）と空vector、separator
   「pcs-constituent-index-v3」で吸収し、1つのdigestからlogはcounter 3i、gateは3·indexBits+3iでsqueeze。
   prover_v2.rs 144-164、verifier_v2.rs 303-311、MleVerifierV2.sol 458-476と照合）をdecode上で全域化し、
   installed engineに据え付けた。index squeeze前のprefixがround状態++claim framesであること、index digest
   が等しければ状態digestとused claimsが等しいか具体的なtranscript衝突が出ること、両laneの長さがindexBits
   であること、ObservationOnlyDerivedのlogIndex/gateIndex項が定理になることを証明した。これにより
   「indexはcellの後に引かれる」というR3の順序面は定理になったが、偽造cell族が新鮮なindex点で失敗する
   確率的段階は未証明でR1b/R3はそのまま。decode仮定は採用済みCommitAgrees下の実行とfixtureで可住。
   index点の座標空間は座標主張のみで法則は付けない。commitRound・parseWhir・configurationHash・
   initialTranscript・publicInputsHashはInstalledInitialTranscriptで据え付けた。sampler engineの上に
   `initialObservation := OuterInitial.derive`（`Verifier.statement p`に対する採用済み導出）と
   `publicInputsHash := PublicInputHashBinding.hashNoPad`を置き、8フィールドが同時に具体化された1つの
   engineを得る。`DerivedInitial`自体は採用済み`withInitial_derived`がrflで与えていたので新規性は合成に
   あり、この engine では下流36箇所の`hderiv`とPublicInputHashBindingの`hsub`が無条件化する
   （GateDerivedRejection・AttachedUnionBound・JointChallengeSpaceの合成定理・ConstantsProvenance・
   CommitmentOrderの主要定理を再述。`hacc`は具体engine下の受理でより強い前提）。導出はengineの他の
   hookを読まず（公開入力は生値をframe 3で吸収）、verifyはhookをinitialTranscript経由でのみ読む。
   受理proofでは公開入力がSolidityの256語capと語ごとの<p検査を満たすことも導いた。残る観測は
   commitRound・parseWhir・configurationHash・deploymentValid。prover側のchallenge一致（prover の
   Prepared recordに関する仮定）はverifier側の据え付けでは消えない。hashは任意の決定的関数のままで、
   単射性・一様性・random oracle性は使わない（順序と配管の同一性でありFiat–Shamir健全性ではない）。
   round commitの観測はInstalledRoundCommitで具体化した。採用済みの検査付きround commit（5 frame：
   domain separator、round index（u64）、log/gate messageのtag 6 frame、separator。round digestの
   counter 0と3からlog/gate challenge。transcript_v2.rs 133-146とTranscriptV2.sol 247-261に一致）を
   decode上で全域化してsampler engineに据え付け、`CommitAgrees`を定理化した。導出されたroundは採用済み
   OuterAdapter.executeと一致し（残る仮定は初期transcript観測とdegreeBits≤13）、round digestが
   CommitmentOrderの22 frame prefixの後に5 frameずつ連鎖してcounter 0/3から引かれること、laneの
   challenge列が実digestの縮約であること、round messageの改変が具体的なtranscript衝突を要することを
   証明した。これによりGatePointZeroCheckのRES-4とJointChallengeSpaceの外側counterラベルはこのengineでは
   定理になった（sourceBlockの番号とindex blockの位置はラベルのまま）。**限界**: envelopeはwidth c=1のとき
   indexBits=0を許し、その設定ではdecode失敗経路（challenge全零・空のindex lane）をindex長guardが通す。
   ただし初期transcript観測とdegreeBits≤13の下では全snapshotがdecodeするため、本モジュールの定理では
   その経路に到達しない（導出でないinitialObservationを持つengineでのみ生きる）。DrawEncodesRunは依然
   座標主張で、laneの値が実digestの縮約であることまでを示す。初期transcriptとpublicInputsHashの据え付け
   （InstalledInitialTranscript）との合成はComposedEngineで行った。modelEngineの4評価器、whirTail
   （PinnedWhirProfileのpinned record）、sampleIndices、initialObservation、publicInputsHash、commitRound、
   deploymentValidの10フィールドが具体化された1つのengineを与え、観測は`parseWhir`と`configurationHash`
   の2つだけになった。各据え付けengineとの同一性を5つのrflで示し、InstalledRoundCommitの9定理が担ぐ
   初期transcript仮定はrflで消え、degreeBits≤13と形状仮定は受理から導かれる。要約定理は受理・
   TableIsCanonical・転記済み行から16連言を導き、各連言は採用済み定理の適用のみで新しい証明内容を含まない。
   抽象parseWhirは良いproofを落とせても誤ったrootを通せない（tailはparsed recordを読まず、WhirInitialが
   transcriptから読むrootをctx.rootsと照合する。deployment-pinnedなのはpreprocessed rootのみ）。
   protocolId/sessionIdの長さはenvelopeにもcanonical検査にも含まれず、検査付き実行の存在にはその2仮定が
   要る。indexBits=0の失敗経路はこのengineでは到達不能。R1b/R2/R3・half (B)・keccak・TableIsCanonicalの
   限定は不変。
   parseWhirの観測はInstalledWhirParseで具体化した。採用済みWhirInitial.phaseInitial→WhirPrefix.run→
   WhirTail.runPrefix（初期phase・初期sumcheck・中間round）の射影として定義し（actualRootsはtranscriptの
   1本目のroot、boundRootsは2本目、claimsはmask 0x1fのreadClaims。whir_pcs.rs 1514-1556/1586-1614、
   SpongefishWhirVerify.sol 374/384-387と照合。新規のモデル化はない）、verifyWhirがprefix成功∧root一致∧
   claim一致∧tail受理と同値であること、root条件はprefix成功に含まれ冗長であること、transcriptバイト列が
   位置k·stride（stride=64+24·outDomainSamples·numVectors）と+32+24·(…)にroot 2本を運ぶこと、先頭32バイトが
   先頭rootの符号化と異なる（または欠ける）transcriptは棄却されること、parseとtailが同じprefix実行を
   読むこと（tailRun=prefixRun.bind runTail、定義的）を証明した。derivedContextの先頭rootはproofの
   preprocessedRootで、受理下ではshapeによりpinに一致する。ComposedEngineと合わせると残る観測は
   configurationHashのみ（本moduleは合成を行わない）。WhirContextのprotocolId/sessionId/parametersと`wp`は
   依然自由（ソースではprofile digestで固定、Leanでは観測）。R1b/R2/R3は不変。
   R3（per-column同定）の確率的段階はIndexPointZeroCheckで二分法として与えた。packed foldと多重線形拡張の
   橋渡し（cells長≤2^indexBits、両者LSB先頭で反転なし）により、2つのcell族のpacked foldが一致するindex点の
   集合は差分の零点集合で密度≤indexBits/|F|、一様積法則上の質量≤tauTerm indexBits。fold水準の関係の下、
   supplied cellsがcommitted列のopeningに一致する（HonestOpenings.openedそのもの）か、導出index点が明示的に
   上界された集合に入るかのいずれかで、bound cell i∈Fin 5で両laneを被覆する。同じ幅なら一致集合が全体⇔列が
   等しい（Boolean点補間による単射性）ので残余類は空。committed幅は仮定（HonestOpenings.capacityは≤のみを
   与える）で、幅が異なればゼロ埋めで差が隠れうるため、capacityのみから末尾零を除いた同定を結論する
   変種も定理化した。cellsは
   index squeeze前に吸収される（InstalledIndexSamplerの順序）がhalf (B)は未形式化。IndexSpace上の
   法則は結合形のみで逐次形はない。R1b（fold水準）とR2は不変。
   最後の観測configurationHashはExplicitEngineで据え付け、抽象base engineを持たないverifierモデルを得た。
   12フィールド全てが(gdec, hash, thash, khash, P, c₀)の関数である。config digestは`khash ∘ encodeConfig`で、
   `encodeConfig`はSolidityの`abi.encode(VerificationConfig)`のフィールド順（8つの回路スカラー、
   publicInputWireMap、kIs、subgroupGenPowers、gates、whir）を鏡写しにするが、offset語の省略・gates/whirの
   不透明化・Nat対uint256の3点でバイト同一ではない（keccakは未モデル）。符号化は13フィールドのcore上で
   単射（有界性は受理とgates/whirのバイト長上界から導出）で、digest一致はcore一致か具体的なkhash衝突を
   強制する。受理下でdigestはpinのdigestに一致し、配備仮定`pin.configDigest = khash (encodeConfig c₀)`の下で
   core c = core c₀（衝突を除く）。PinnedWhirProfileの理想化仮定（whirEncoding一致）は衝突を除き定理となり、
   その仮定を落としたengineでも受理から回復する。`deploymentValid`は残りの配備検証（kIs/subgroup連鎖、
   gate評価器・WHIRパラメータ検証、wire-map範囲）がSolidityではconstructor限定であることを根拠に
   whirEncoding一致とprofileOkのみとした。**これはSolidity経路のモデルであり、Rustのmle_verify_v2は
   kIs・subgroup powers・gates・circuit_config_digest・protocol/session idをcallごとに再検証する**。
   gate評価器の検証は受理の帰結として残る。**残余**: circuitDigestとcircuitConfigDigestは符号化されず
   （Solidityではimmutableで固定、モデルでは攻撃者が選ぶtranscript入力で、半分(B)の自由度に属する）。
   gateRowsは非符号化だが受理でdecodeされたgatesの長さに固定される。hash/thash/khashは任意の決定的関数で、
   衝突型の結論は全て明示的な選言である。
   残るcircuitDigest・circuitConfigDigestはCanonicalProofCheckで固定した。Solidityがcallごとに走らせる
   `_requireCanonicalProof`の10比較のうち未モデルはproofのcircuitDigest 4語とimmutableの比較のみで、
   circuitConfigDigestはimmutableを430でtranscriptに吸収する。両digestが配備値に等しいことを
   `deploymentValid`に据え付け（Integrated.verifyはVerifier.verify経由でdeploymentValidを検査する。
   verifyCall読みでは配備不変条件の一部であり、immutableがcalldataに無いことで正当化される）、受理は
   全19フィールドについて`c = c₀`か具体的khash衝突を強制する（WHIRのid 2つとdigest 2つは選言なし）。
   transcriptのframe 2/7は配備digestを吸収し、Configに自由フィールドは残らない。`_validateConfiguration`が
   digest語の正準性を強制するため、`Fin modulus`モデルはSolidityの受理集合を下から近似する（安全側）。
   proof側で固定されるのはcircuitDigest・protocolVersion・preprocessedRoot・widthで、witness/normInverse
   root・round多項式・used・WHIRバイト列は攻撃者が選びshapeの長さとtailのみが制約する。
   Rust側の呼び出し境界はRustCallBoundaryで扱った。`mle_verify_v2`がcallごとに走らせる検査（byte cap、
   digest長、幅profile、制約数・次数のcap、kIs、正準subgroup powers、gates、circuit_config_digestの再計算、
   WHIR id、proofのcircuit digest等）を行単位でLeanの対応物に対応付け、kIsの正準連鎖（builder由来の値。
   CommonCircuitData未モデルのためソースより厳しい下近似）とcircuit_config_digestの再計算（前像の鏡写し、
   14メンバーで単射）を新たにモデル化して`rustDeployment`を定義した。Rustの境界にはdigestのpinが無く
   VKが配備そのものであるため、Solidity側受理から（衝突を除き）Rust検査が従う一方、Rust検査だけでは
   Solidityのpinは出ない（whirEncodingはRustに入力が無い）。配備config上で両engineは同じ結果を返す。
   rustEngineはVerifier.verifyの骨格経由でconfigurationHash/chainId guardとpinned preprocessed rootも
   読む。残余: vk次元とcommon_dataの比較、wire-map範囲、体の位数とD、lookupの不在は仮定。
   **横断的所見（LocalizedCollisions）**: `TranscriptCollision`・`KhashCollision`・`Khash2Collision`
   （∃ a b, a ≠ b ∧ hash a = hash b）は無限の入力域から有限のdigestへの任意の関数で成り立つ鳩の巣の
   トートロジーであり、`RowCollision`の第2選言も有限の鳩の巣で常に真である。本SCOPEとREPORTで
   「衝突耐性を仮定せず具体的衝突を出す」と記した採用済み定理（37件＋17件）は、文としては仮定なしに
   真であり、監査内容は構成的証明が示す2つの具体的入力にしか無い。これは健全性欠陥ではなく文の形での
   過大主張である。局所化した反証可能な述語（FrameFoldCollision、Index/RoundDigestClash、
   ConfigEncodingCollision、LeafCollision）で主要定理を言い直した。採用木側の要修正:
   `ConditionalSoundness.no_row_collision_binds_opened_dot`は仮定¬RowCollisionが充足不能で空虚
   （NoCollisionAmong型の局所的単射性に置き換えるべき→OpenedDotBindingで置き換え済み。Lean上の利用箇所は0件で
   健全性への帰結はない）。本SCOPEの「具体的なtranscript衝突」の各記述は
   「その実行の2つの具体的入力の衝突（局所述語）」と読むこと。
   Fiat–Shamir半分(B)の最初の形式化はRandomOracleSqueezesで行った。hashを有限集合Q上の一様ランダム表
   （random oracleの有限計数法則）とし、相異なる入力での射影の一様性、block digestを固定した条件付きでの
   スケジュールsqueezeの一様性とbad draw質量≤combinedBound（d≤13で仮定の充足を証明、d=13の閉じた実例）
   を示した。block digest自体がframe問い合わせの出力で逐次依存することを見出し、frame/challenge入力の
   prefix分離（15バイト目）からcongruence補題を証明、frame fibre上のFubiniでrun水準の上界
   P[bad draw] ≤ combinedBound + P[round digestの局所的衝突]を得た。**限定**: 最小の閉包証人では加算項が
   1で空虚、実行のframe入力を含むQで<1（存在のみ証明）、小さい上界は未証明（birthday型計数）、適応的
   prover（pがTに依存）は未対応。初稿の非適応定理は仮定が全digestをzeroDigestに強制し空虚だったため
   棄却して再定式化した（2度目の空虚性検出）。ROMであってkeccakの性質ではない。
   加算項のbirthday型計数はBirthdayClashBoundで進めた。fresh query補題（qでの回答に依存しない事象に
   対する等式）とadaptive版、因果的で新鮮なchainの衝突確率上界、有界長の問い合わせ集合上でround foldの
   5 frameから成るchainモデルの衝突確率≤5d(5d+1)/2/|Block|（d=13で2145/|Block|）を証明した（freshnessは
   frame_injectiveから証明、定数表は衝突事象に属する）。**限定**: 上界はchainモデル上で、実行の
   actualChainへの接続のうち、関係prefixの22 frameを繋いだchainの起点がderiveのdigestと一致すること
   （87段で衝突確率≤3828/|Block|）は証明済み、concreteChainの帰納は未了で、run水準の加算項は仮定のまま（→ConcreteChainThreadingで帰納を完了し加算項を放棄、下記）。
   局所化定理はstageQueriesの同位置frame対を名指す形に強化した。
   chainモデルと実行の接続はConcreteChainThreadingで完了した: chainの22+5r段目は採用済みconcreteFinalの
   先頭rメッセージ後のdigestに等しく（帰納法。absorbは入力stateのdigestのみを読むのでcounterの追跡は不要）、
   `sourceDigest`はchainの22+5r+5段目、RandomOracleSqueezesの`clashEvent`はchainモデルの
   `prefixRoundDigestClashEvent`と同じFinsetであるから、run水準上界の加算項はbirthday型の
   (22+5d)(22+5d+1)/2/|Block|（d=13で3828/|Block| ≤ 2^-244）で放棄され、`run_bad_draw_probability_le_birthday`
   は固定（非適応）プローバのROM下で確率的側条件を残さない。閉じた証人（L=381）でRHS<1。残るのは
   適応的プローバ（strategyに対するfresh-query帰納）、index lane（IndexLanesOracleが固定digest下で扱う）、
   WHIR/Merkle、keccak自体、そしてこれらの質量が系の健全性誤差ではないという事実。
   index laneはIndexLanesOracleで同じROM法則下に置いた: claim frame 8個を足した拡張chainの22+5d+8段目は
   採用済みindexDigestであり、固定index digest下でactualIndexDrawの押し出しは採用済みindexProbabilityに厳密に等しく、
   guard付きindex bad事象は≤2·tauTerm、joint族とindex族の和集合は固定digest下で≤combinedBound+2·tauTerm
   （索引カウンタは外側カウンタと重なるため分離はdigestのみ）、拡張chainのbirthday上界はd=13で4560/|Block|。
   残るのは和集合に対するrun水準Fubini（両draw共に同一frame fibre上でdigestが定数になる素材は揃っている）と、
   `hst`（22+5d段目がpost-rounds snapshot）のLean上の接続（ConcreteChainThreadingの`chain_model_is_the_run_chain`が
   同じ事実を証明しているが、両モジュールは互いにimportしない）。
   run水準の和集合上界はRunLevelUnionBoundで与えた: ILOの`hst`はCCTで放棄され、frame fibre Fubiniを2族同時に
   1回実行して P[jointBad ∪ guardedIndexBad] ≤ combinedBound + 2·tauTerm + P[拡張chainのclash]（d=13で4560/|Block|、
   閉じた実例でRHS<1、good table存在）。explicit engineの組立結論の失敗集合はhash添字付きの和集合事象に含まれる
   （無条件）が、その質量上界は未達: 被覆仮定（∀hashで固定事象が支配）は非退化な実行で充足が知られず、
   本監査の空虚性方針により削除した。残る橋渡しは固定プローバの2段階条件付き計数（alpha条件付き外側対角事象、
   外側draw条件付きの索引一様性）で、適応的プローバとは別の問題。適応的プローバはStrategyChainBound（chainの
   birthday項のみ）で着手。
   適応的プローバはStrategyChainBoundで着手した: 戦略（既出digestとそれらのchallenge回答から次frameを選ぶ関数、
   因果性は型に組込み）に対してもchainのclash確率はn(n+1)/2/|Block|（87段で3828/|Block|、固定プローバと同じ定数）で、
   chain自身のno-clash事象で条件付けたchallenge回答は一様（単一・有限集合版）、戦略的外側プローバのchainは表ごとの
   実現メッセージでconcreteFinalに一致する。戦略は自前の神託問合せを持たない（transcript制限付き適応性）ため、自分でhashを叩いて衝突を探すgrindingプローバは
   対象外で、その衝突質量は問合せ数qに比例する（q·n/|Block|）。**未達**: 適応的プローバのjointBadEvent（combinedBound側）の上界。
   OuterSequentialConditioningが理想モデルで与える逐次条件付けの計数を、13個のround digestにわたる入れ子の
   no-clash事象の下で神託表へ輸送する段が残る。
   grindingプローバはGrindingQueryBoundで扱った: 各段q回の自前probe問合せ（frame形、逐次適応的）を持つプローバに対しても
   chainの衝突質量は N(N+1)/2/|Block|（N=(q+1)n）で、q=0は採用済みの3828/|Block|に戻る。採用済みCausalは再問合せに
   耐えないためfreshness事象で条件付けるFreshCausalへ置き換えた（採用済み結果は弱めない）。challenge入力へのprobeは
   列の位置にはならないが、challenge入力の読み取り自体は任意のdigestで無償。上界はqについて2次で先頭項は≈(q+1)倍緩い。
   適応的/grindingプローバの和集合上界は依然未達。
   固定プローバの2段階条件付き計数はTwoStageConditionalCountで外側段を完了した: explicit engineのouter bad事象はgate alpha座標経由でのみ
   hashに依存し、対角事象の質量は一座標条件付き計数で採用済みcombinedBoundのまま、RLUBのfibre Fubiniで神託表へ輸送される。索引段は
   依存事実（row点は外側drawの関数。初稿の障害主張は反証・撤回）まで証明し、条件付き計数自体は`RowPointFixed`（定数committed列で
   非退化に充足）を明示仮定として`assembly_failure_mass_le`を与えた（定数committed列のみ）。残る細分割（frame半分＋外側challenge
   cellを固定し索引cellを自由にするfibre）は抽象計数`product_diagonal_card_le`と3段契約で規定済み。
   索引段の細分割はIndexStageFinerSplitで完成した: 結合scheduleのclash外単射性から外側cellと索引cellが互いに素、restrict_ratioで
   (外側draw, 索引draw)が同時一様、2群条件付き計数で索引半分がrun自身の外側drawに依存する対角事象を各点≤2·tauTermで評価し、
   frame fibre Fubiniで加算項1つのまま神託表へ。これによりexplicit engineの組立結論の失敗集合の質量上界
   `assembly_failure_mass_le_unconditional ≤ combinedBound + 2·tauTerm + P[拡張clash]`（d=13で4560/|Block|）が、固定プローバのROM下で
   committed列に条件なく成立し、閉実例でRHS<1。残るのは非定数列でのguard生存性（緩みのみ）、適応的プローバ
   （AdaptiveUnionTransportで着手）、R1b、回路の真値、受理の提示。
   適応的プローバの和集合上界はOuterLaneTransportで前進した: 対角fresh step（targetの値で分割）と入れ子no-clash事象により
   OSCの各round条件付けを神託表へ輸送し、任意の戦略駆動chainに対し ≤ outerTerm + chain衝突項。ただし一般形はlaneと戦略を
   独立に量化しており（prefix依存lane輸送。raw blockを読む一般のStrategyにはlaneOfStrategyが構成不能）、SCB (iii)を閉じるのは
   縮約履歴部分クラス（ReducedStrategy、lane messageと実現メッセージの一致を証明）に限る。残るのはraw block読みの戦略、
   tauTerm/alphaTermの輸送、grindingプローバの和集合上界。
   索引guardの生死はIndexGuardLivenessで特徴づけた: 共通幅ではdead ↔ 主張cell = committed cell（正直な場合）で索引事象は∅、
   非定数列（spikeColumn）ではdead ↔ eqAtZero(row) = (x−v)/(w−v) という単一の体方程式。dead な外側drawの質量上界
   （Schwartz–Zippel型）と、提示した行点の外側drawによる実現は未着手。
   grinding上界のq線形化はGrindingLinearBoundで、probeが形成済み段digestでframeするstate-framedプローバに対して (q+1)n(n+1)/2/|Block|
   を得た（q=0で採用済み定数に一致）。probe予算内で候補chainを模擬する攻撃者は除外（問合せグラフ上の計数が未着手。GQBの2次上界は
   彼も覆う）。
   縮約履歴部分クラスの適応的上界はReducedFullTransportでblock-0のgate tau/gate alpha事象（derive digestでの固定target）を加え、
   完全なcombinedBound + chain衝突項に到達した（閉実例でRHS<1）。索引laneは適応的プローバでは使用claimが表の関数になるため未含
   （対角形が必要）。g/coeffsOfが配備表であることの結合は未了。
   縮約履歴適応プローバの索引laneはReducedIndexLanesで取り込んだ: 履歴依存のused-claims選択を8 claim frameとして吸収し、索引digestでの
   対角fresh step（分離はno-clash下のdigest）と密度補題で ≤ combinedBound + 2·tauTerm + chain衝突項（閉実例でRHS<1）。committed cellは
   履歴の関数のパラメータ（実現proofへの転送は未実施）、索引項は1 bound cell分。
   chain模擬grindingプローバはGrindingGraphBoundで扱い、否定的結論を定理化した: 統一charging定理はGQB/GLB/graph-framedの3実例を
   持つが、chainSimulatorでは eligible 集合が全対に一致し、この方式では全対定数を超えて改善しない（衝突質量の下界は主張しない）。
   一般grindingプローバの線形上界はこの方式の外側にある。
   適応系列の組立失敗上界はAdaptiveAssemblyFailureでlane列の同定を閉じ、EODの全所有事象が実現runでの`SoundnessAssembly.outerBadEvent`と
   Finsetとして一致することを示して、組立失敗集合 ⊆ その事象 ∪ 索引事象、質量 ≤ combinedBound + chain衝突項 + P[索引事象] を得た。
   索引半分の質量はIndexHalfTransportで輸送を実施し、鎖の比較（拡張shapeの無衝突事象 ⊆ strategic shapeの22+5d段のそれ）により
   単一定数 combinedBound + 2·tauTerm + 索引段の birthday 項に閉じた。同モジュールのレビューが採用済みツリーに遡る空虚性を発見した:
   組立失敗事象は受理を連言項に持ち、受理はshapeを含意し、shapeはfixtureの`used`（長さ1,1,0）を通じて
   `numRouted = 0 ∧ numConstants = 1 ∧ numWires = 1`を強制するので、それ以外の構成では事象は空で上界は空虚に真だった。
   これを定理として記録し、かつ`used`をパラメータ化して障害を除去した（matching claimsではshapeの5連言が構成自身で成立）。
   受理そのものの提示は依然として未了である。
   2つの局所化衝突のROM質量はLocalizedCollisionMassesで計算した: 固定ペアはちょうど`1/|Block|`、和集合のサロゲートは構成の族ではなく
   クエリ集合で、「何らかの構成が配備済み構成と衝突する」質量が`(Q.card + 1)/|Block|`以下（族を名指ししない）、`Q := boundedQueries L`で
   採用済みモデルに接続する。ただし`joinFailureEvent`は`DeployedFacts`を連言項に持ちそれだけで質量が`1/|Block|`以下になるため、
   その看板の数値は衝突解析が稼いだものではなく、実質は包含の側にある（negativeな事実として定理化）。
   受理の提示はNonDegenerateAcceptanceで実施した。退化の原因は結局**4つ**あり（usedのfixture、自明engineの索引サンプリング、
   fixtureの1要素logTau、そしてintegrated経路でのlogChallengesの空リスト — 最後のものは採用済みテストengineが無条件に
   `.error .configuration`を返すという、既知のどれより強い事実）、いずれも任意のengineで定理化した。そのうえで、動かしたengine欄は
   2つだけのまま、envelopeの上限構成（degreeBits 13・numRouted 80・numWires 160・gateRows 255・quotientDegree 8・indexBits 8、
   degreeBits + indexBits = 21はprofileの上限ちょうど）で`Verifier.verify`が受理することを`rfl`で示し、上限内の全WHIRバイト列に対する
   パラメトリック版も与えた。ただしこれらはモデルengineであり、9ゲート中実計算は3つで導出トランスクリプトは常に空である。
   したがって採用済み適応事象を非空にはせず、明示engineへの局在化も主張しない（その`deploymentValid`は
   `1 ≤ numVariables ≤ 21`という数値制約を含む）。主張はshapeとenvelopeが受理を妨げなくなったことに限る。
   grindingプローバのlane対応付けはGrindLanePairingで実施した: q=0で採用済みraw上界がGUBの見出しから導出され（非循環性は
   推移的定数依存走査で確認）、laneのメッセージがgrinderの吸収ペイロードそのものであることを条件付け事象なしで示した。
   適用範囲は結合段のペイロードが5元以下のgrinderで、log laneとgate laneが同一メッセージを運ぶという制限が残る。
   検索するプローバの除外は`ChallengeRestricted`が担っており、GUBのpre-readの穴はそのままである。
   受理はDerivedAcceptanceで明示engineまで押し上げた: 受理しているengineは`ExplicitEngine.explicitEngine`から`parseWhir`と
   `whirTail`の2欄だけfixtureに戻したもので（`rfl`）、12欄中10欄が採用済みの実コンポーネント、`thash`と`khash`は全称量化される。
   残る障害はWHIR parse/tailのみで、採用済みツリーには`WhirConfigured.run`の具体的成功例が実在するがマスクと主張数が合わず
   再利用できない。欠けている補題は名指しした。ただし誠実なゲート数は9中4であり、(2)と(4)は`rfl`で閉じ、(7)は`numRouted = 0`のため
   どの2つのproofも区別できない。構成は`quotientDegree`まで上限だが`numRouted = 0`で、これは元の退化ピンへの復帰である。
   採用済み`maximalConfig`とは比較不能で、どちらも他方を支配しない。`numRouted = 1`での受理は導出challenge間の偶然の一致と
   同値であることを定理化し、抜け道もゲート8が塞ぐことを示した。WHIR完全な実例は`thash`全称量化を保てないという緊張も記録した。
   TwoLaneMessagesはGLPのhonesty項目(v)を撤去したが、より重要なのは採用済みgrindingモデルについての発見である:
   プロトコルは1段離れた2つの結合セルを持つのに`GrindCausal`はそのどちらにも届かせないため、grindingのlineは厳密に粗い粒度にあり、
   単一ペイロードの分割では直らない。分割自体は予算を5元から15元に上げるが、2 laneが分離するのは120バイト超のときだけで、
   それ以下ではgate側が空になる（空のgateセルは合法なroundメッセージではない）。この長さ不正はGLPからの継承である。
   WhirTailWitnessはinstalled水準のWHIR成功を初めて具体的に示した。見出しは
   `configured_six_claim_execution_example`（6主張・配備マスク・408/72バイト・両EOF）と
   `installed_whir_pair_accepts_a_full_verification`（`parseWhir`/`whirTail` 両方 installed の `Verifier.verify`）。
   6主張文脈は `six_context_is_the_derived_context_of_the_installed_engine` により outer が導出する形そのもの。
   ただし定数 toy ハッシュ（`the_witness_hash_ignores_every_input`）・toy no-round プロファイル・
   `Verifier.testConfig`（1変数）であり、engine は `DerivedAcceptance` の補集合（4欄が抽象観測のまま、
   `accepting_engine_field_ledger`）であって `ExplicitEngine.explicitEngine` ではない。
   21変数の witness は未構成。マスク `[⟨31⟩]` 対 `[⟨7⟩]` はブロッカーではなく主張数が実障害だった
   （`configured_run_mask_congruent`）。RoutedAcceptanceは同じ derived engine のまま `numRouted = 80` で受理する
   （`routed_acceptance`）が、`routedHash` は digest を無視する（`routed_hash_is_a_transcript_collision`）。
   導出 challenge は statement に非依存（`rho_ignores_the_statement`）で、根だけ異なる2つの proof が両方受理される
   （`alt_proof_is_also_accepted`）。これは最後の退化ピンの除去ではなく、proof 依存 challenge との交換である。
   derived / routed / maximal の3実例はすべて比較不能。ゲート7は80回の wire loop を実行するが2つの proof を区別しない。
   そのdigest無視はDigestRoutedAcceptanceで修復した: `fixedHash`はバイト15でフレーム/チャレンジをドメイン分離し、
   受理の消滅論法が必要とするカウンタ3/4/5だけを固定して残りはdigestを実際に読む。採用済みのroutedConfig/routedProof/
   routedPin/matchingClaimsを一切変えず、ハッシュだけ差し替えて`numRouted = 80`の受理が成立し（`fixed_acceptance`）、
   root違いの2つのproofの導出トランスクリプトは旧ハッシュでは一致・新ハッシュでは分離することを対比定理対で示した。
   残余は開示済み: 228回の絞り出し中180回がchainを読み48回は符号固定のまま、そしてchain状態は1バイト幅
   （末尾31バイトは全導出でゼロ、連鎖は高々256 digest）。復元はFiat–Shamir依存の構造であって量的衝突耐性ではない。
   分離はfold特異的（foldが等しいroot対はトランスクリプト全体が一致）で、altProofは依然受理される — 2つのproofの
   分離には非ゼロnorm-inverse列かinstalled WHIR parseが要る。`thash`は代入であり全称ではない。
   `CommittedTables`結合はCommittedTablesClausesで節ごとに判定した: preprocessedPinnedは受理から任意のengineで導出、configDeployedは
   Solidity経路で局所的な構成符号化衝突1つまで導出、rootDeterminedはR1bそのもので、開示を読む抽出器では節を満たす写像が存在しないため
   COSの退化した証人は強制されていた。採用済みbinding補題が届くのは開かれたcellのみ（局所leaf/path衝突まで）で、開かれないcellと全列の
   root決定性はR1bに残る。従って「tablesは固定データ」はR1b + 2つの局所衝突に還元され、`g`は依然固定データではない。
   RILの転送はReducedEngineIndexで実施した: 二戦略・同一表の合同補題、OLT §6の実現proofでのdraw同定、TSCCのrow点定理により
   committed cellが縮約履歴の関数であることを示し、engine自身の索引bad事象との Finset 恒等式を経て縮約適応上界
   ≤ combinedBound + 2·tauTerm + chain衝突項（多cell版は5·2·tauTerm）を得た（閉実例でRHS<1）。残るのは列とg/coeffsOfの配備との
   結合（CommitmentOrder）、raw block読み戦略、grinding、R1b、受理の提示。
   reduced-history制限はRawBlockLanesで解除した: OSCのLaneを経由せず、rawメッセージと縮約challengeでの評価を持つraw laneにより、
   任意のRoundCausal transcript制限付き戦略に対して外側+block-0で ≤ combinedBound + chain衝突項（閉実例はOLTが対応づけられなかった
   challengeTruncatedMessage）。残るのは索引半分のraw版（RILの機械的再導出）、grinding、列/表の配備との結合。
   raw戦略の索引半分とengine転送はRawIndexLanesで完了し、任意のcausal transcript制限付き戦略（RoundCausal S, ClaimsCausal U）に対して
   explicit engine自身の事象上で ≤ combinedBound + 2·tauTerm + chain衝突項（5 cell版は5·2·tauTerm）が成立、閉実例でRHS<1。
   これでROMの適応的上界はtranscript制限付きの範囲で全laneに及んだ。残るのはgrinding（自前問合せ）の和集合上界、列・表の
   配備との結合、R1b、回路の真値、受理の提示。
   SCB HONESTY (iii) 末尾のrun水準輸送はRunLevelTransportAuditで決着した: RBLのraw全事象は実現proofでの`actualDigestDraw`が
   `jointBadEvent`（実現lane）に落ちるrun水準事象とFinsetとして等しく、適応的run水準上界は固定プローバ定理と同じ文の形で成立、
   whole-schedule一様性は不要（一段事象の和）。積法則自体は主張しない（閉性は既知でなく成否は未決）。
   「固定データ」残余の正体はCommitmentOrderSurveyで分類した: gate alphaはderive digestでのsqueeze = challenge座標であり、tau表gは
   それを読むので固定gのtau事象はengine自身のtau事象のalpha固定スライス（対角はEngineTauDiagonalで評価）、coeffsOfは表のみの関数、
   committed列はround-one opening（索引squeezeの後に吸収）に依存しprefixデータではなく、「固定」はR1b型のrootDetermined仮定。
   採用済み6ファイルの過大な文言12箇所を修正した。残るのはCommittedTablesJoin（rootDetermined・preprocessedPinned・
   configDeployed）そのもの、すなわちCommonCircuitData鏡像とVK/Rust境界を含む配備との結合。
   grindingプローバの和集合上界はGrindingUnionBoundで、ChallengeRestricted（challengeは自身の段digestでのみ読む）の下に
   ≤ combinedBound + N(N+1)/2/|Block|（N=(22+5d)(q+1)）を得た。laneはprobe回答履歴も読める（GrindLane）。除外されるのはpre-readプローバ
   （probe回答digestでchallengeを先読み = FS challenge grinding。同一文字列の反復なので相異文字列衝突では評価できず、事象は質量1）で、
   問合せ計数型の別論法が必要。bad集合がgrinder自身のabsorb payloadを運ぶ結合は未了。
   engine自身のtau事象の対角はEngineTauDiagonalで評価した: alpha三つ組で分割しRFTの同時剥離を各ブロックに適用して ≤ tauTerm d
   （任意の戦略・任意のG）、RXL経路を再構築して engine 自身の tau+索引事象上で ≤ combinedBound + 2·tauTerm + chain衝突項。
   最終定理で∀-lane形のまま残るのは外側（`SoundnessAssembly.outerBadEvent`のalpha依存対角は適応系列で未解決。TSCCは固定プローバのみ）
   とalpha（対角不要）。
   適応系列の外側alpha対角はEngineOuterDiagonalで完了し、transcript制限付き因果的プローバに対するROM適応的上界は外側・tau・alpha・索引
   の**4事象すべてをengine自身のもの**として ≤ combinedBound + 2·tauTerm + chain衝突項（閉実例でRHS<1）になった。評価した事象は実現proof
   の`actualDigestDraw`のouterEvent事象と一致（証明済み）。`explicit_good_draw_assembly`の失敗集合への系は、lane列の同定（実現lane列 = gateLaneOf at the realized run）1本が残るため未到達。
   pre-read（FS challenge grinding）プローバはPreReadChargeで、probeをchargeする二段fresh peelにより ≤ (q+1)·outerTerm（一般のgrinding
   プローバ、ChallengeRestricted不要）を得た。好都合な分岐ではroundのchallenge digestがprobeのdigestそのものなので、probeのchargeが攻撃を
   chargeする。残るのは結合（grinder自身のメッセージ）、tau/alpha/索引lane、定数の統合。
   これらの結果はSoundnessAssemblyで1定理に組み立てた。explicit engineの受理、残余仮定の名前付き構造体
   （表の意味論と転記行、配備digestと有界性、fold水準のopening、抽出列の高さとcommitted幅、
   GateDerivedRejectionの9フィールド、slot係数）、実digest drawが4族のbad event外、実index drawが
   ガード付きindex bad event外、から全行の選択gate制約消失・per-column同定・pinned profile行・
   core一致（衝突を除く）を導く。質量はjoint spaceで≤combinedBound+tauTerm d（≤2^-171）、index spaceで
   ≤2·tauTerm bits（≤2^-187）で、別空間なので加算しない。（IndexLanesOracleはROM法則下・固定digest版で両者を同一の表上の和集合として≤combinedBound+2·tauTermを与えた。）初稿はindex bad eventが無ガードで結論が仮定と
   矛盾し（レビューがFalseを導出）、偽造前提が残余に紛れていたため棄却され、修正後の再レビューで
   反駁が型検査を通らないこと、正直な抽出ではbad eventが空になることを確認した。**残る限定**: 受理と
   残余仮定の同時充足可能性はexplicit engineで受理されるproofを構成しない限り提示できない；結論は
   good draw条件付きの制約消失と同定であって回路真理・WHIR近接性・hash安全性ではない；R1b・R2・
   half (B)・circuitDigest/circuitConfigDigest・Solidity限定の配備意味論は残る。
   抽出接合はExtractorConstructionで構成的に消化した。抽出状態を受理proofのused claimsとR1b抽出器の出力から
   定義し（eq列は導出tauのeq table、rounds/pointは空）、TruthChainがmessageに言及しない定義的述語である
   ことから任意の整合状態に対して構成した（message≠truthはroundBadSetが運用claimの非対角で吸収する）。
   SoundnessAssemblyの残余19のうち10（Consistent・TruthChain・cellsMatchClaims・eqProvenance・slotCoefficients・
   eqCellBindingの構造は構成、foldLevelOpening・列高・committed幅・lastCellsはR1bのHonestOpeningsから）が
   定理となり、残る仮定は受理、R1b、TableIsCanonicalと行、配備digestと有界性、gate復号、制約数正、
   active filterのみになった。committed幅はHonestOpenings.openedがmapであることから導け、fold水準述語の
   下でのみ既約である（IndexPointZeroCheckの記述と整合。SoundnessAssemblyのcommittedWidth注記は要更新）。
   **残る限定**: R1bはWHIR近接性とsumcheck健全性を措定する未形式化の確率的主張であり、受理との同時充足
   可能性はexplicit engineで受理されるproofを構成しない限り提示できない；結論は抽出表上のgood draw
   条件付き制約消失で回路真理ではない；hashは未モデル。

現target105の約101.5-bit値はリポジトリのgeneric-work見積もりで、Leanが証明した
128-bit/end-to-end安全性ではありません。実装変更・デプロイ承認もこの更新には含みません。

GoldilocksCertificate単独は数値証明書であり、素数性の根拠はGoldilocksFoundationの
Lucas適用・全prime-divisor列挙・小因子の素数性の証明と組み合わせたものに限る。
Mathlib v4.10.0のcommitと公式lockの6依存を監査専用に固定し、直接importは特定の
モジュール/名称だけ許可する（Foundationの3import、NormのRing、WhirPolynomialのRoots、
WhirChallengeのFintype.Card、WhirQuicksortのList.Perm、CorrectnessのList.Sort、
GatePolynomialのList.Count）。
標準3公理allowlistと全名付き定理の検査は維持する。
依存guardは全tracked sourceの実Git blob・HEAD・origin・固定release tagと追加sourceを検査。
この検査は生成済み.oleanやProofWidgets release archiveの出自を認証しない。
通常Lakeビルドにはそれらの成果物とLean toolchainの信頼境界があり、全source-only再現とは呼ばない。
別途40モデル/1019定理のcheckpointで、固定7依存の非toolchain Lean source全1370モジュールを
空の新規出力先へ再生成し、その出力だけで全定理を検査した。実行前後のsource/hash/依存/JSを
照合し、既存の依存.oleanは使わない。ただし11個のProofWidgets JSは固定した既存データで、
JS source再生成・Lean toolchain/core artifactの再現・全実装/PCS証明を主張しない。
その記録は後続追加モデルのfresh検査済みという意味でもない。詳細はREPORTを参照する。
