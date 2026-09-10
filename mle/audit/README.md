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
| [WhirSampling](Audit/Wire3/WhirSampling.lean) | byteごとの実hash/counter・BE query・maskと挿入sort基準版。実indexed sortとの接続は後段WhirSamplingExecutionを参照 |
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
| [WhirDomainBridge](Audit/Wire3/WhirDomainBridge.lean) | 実domainPointを固定生成式へ接続。明示した生成元・次元条件下で単射と、同長・不同の固定vectorの一致query数≤長さ−1 |
| [WhirChallenge](Audit/Wire3/WhirChallenge.lean) | 実120byte/3×LE40byte還元の全単射と事象数上界。明示的uniform入力なら固定不同WHIR quadraticの一致確率≤2(ceil(2^320/p)/2^320)³。実FS分布は未証明 |
| [WhirConfigured](Audit/Wire3/WhirConfigured.lean) | 単一checked設定から全相へ投影し、実行成功と明示3×1条件から全到達相/終端Contextの形状を導出 |
| [WhirQuicksort/Correctness](Audit/Wire3/WhirQuicksortCorrectness.lean) | 実indexed scan/swap/partition/左右再帰をモデル化。一般終了・範囲外保存・整列・重複数保存から基準sortとの一致を証明 |
| [WhirSamplingExecution](Audit/Wire3/WhirSamplingExecution.lean) | 実sort→indexed compaction→raw queryを全WHIR両sampling箇所へ接続。結果・全状態・失敗の一致と単一checked設定入口の形状を証明 |
| [WhirDomainPower](Audit/Wire3/WhirDomainPower.lean) | 実64bit mask/low-bit/shift/mulmodのscalar loopと既存冪乗の一致。256bit指数で終了し、範囲内queryの実domainPointへ接続。compiler/EVM refinementではない |
| [OuterRound](Audit/Wire3/OuterRound.lean) | 外側の実係数和・inverse-two・Hornerを具体体多項式へ接続。端点和、次数、固定不同claimの一致点数、両laneの同じ更新を証明 |
| [OuterChallenge](Audit/Wire3/OuterChallenge.lean) | 外側の実3×32byte squeezeとcoupled commit後の6counterを接続。明示uniform law下の偏り込み固定多項式上界。実FSや両laneの積増幅は未証明 |
| [GatePolynomial/Basic/Mds](Audit/Wire3/GatePolynomial.lean) | 全14familyのzero-filter分岐除去と、7familyの実制約式・selector・固定alpha Hornerへの多項式評価一致と次数 |
| [GateCheckedPolynomial](Audit/Wire3/GateCheckedPolynomial.lean) | 7familyに限定し、実設定検査と両入力長から寄与次数≤q+1、明示affine重み後≤q+2。未対応familyはNONEを保持 |
| [NormPolynomial](Audit/Wire3/NormPolynomial.lean) | off-cube形式norm/adjugateと実寄与式からhelper≤4、eq重み込み行・有限和≤5、PI≤2。endpoint抽出/PI routing/送信係数は別境界 |
| [GateLoop/Random/TwelvePolynomial](Audit/Wire3/GateTwelvePolynomial.lean) | Exponentiation・BaseSum・Reducing2種・RandomAccessを追加し12familyの実次数と設定済み行寄与を証明。Poseidon/Cosetのsymbolic NONEは残る |
| [WhirRlc](Audit/Wire3/WhirRlc.lean) | 実geometric係数とrow dotを同じ多項式へ接続。固定同長不同vectorの一致点数≤n−1、明示uniform120byte上界、2RLCの実順序/別state・無消費分岐 |
| [GateCoset/Poseidon/AllPolynomial](Audit/Wire3/GateAllPolynomial.lean) | Poseidon4の全30round実状態・S-box・MDSから123制約・次数≤7、Coset13のchunk/reset/中間からD≥2で次数≤D。全14familyの実validateGateから寄与≤q+1、affine重み後≤q+2。gate truth/endpoint由来は別境界 |
| [GateAggregate/SuffixPolynomial](Audit/Wire3/GateSuffixPolynomial.lean) | 実combineRows全行の順序付き集約を1多項式へ接続し次数q+1、実設定包絡q≤8から重み後≤10。2s/2s+1読取り・同一challenge補間・Boolean suffix和も同じ多項式。Rust slot-first順序との可換は未証明 |
| [OuterInterpolation/Total](Audit/Wire3/OuterInterpolationTotal.lean) | coefficients.rsの実Gauss消去（自然node・pivot交換なし・書込み前factor）を添字付きで模し、証明専用ghost RHSで到達pivot=∏(p−j)を同定。n≤pで全段成功・実inverse実行・非空全域、norm5/gate q+2へ特殊化 |
| [DenseMleIndexed](Audit/Wire3/DenseMleIndexed.lean) | ext3.rs bindの2i/2i+1 read-before-write・増順書込み・truncate・未書込suffix不変、Valid長=2^numVars、numVars>0 guard、全bindManyとPacked.layer/foldの一致、affine Norm橋 |
| [OuterInitial](Audit/Wire3/OuterInitial.lean) | 外側初期transcriptの16frame（circuit digest・raw PI・15語metadata・config digest・64/32byte識別子・2roots）とeta〜gate tauの順序/counter、d≤13で全checked squeeze成功。PI hash・VK意味論・Hash安全性は未証明 |
| [OuterAdapter](Audit/Wire3/OuterAdapter.lean) | 40byte内部snapshotの無損失decoder、実coupledRoundの6limb/counter、5claim+空第6cell→index domain→log/gate index列の実順序、checked外側loop=Verifier.roundStep、初期→WHIR contextのOption prefix。既存total Engineとの一致は明示CommitAgrees/SamplesAgree条件付き |
| [GateSlotAlgebra/Commutation/Round](Audit/Wire3/GateSlotRound.lean) | Rustのslot-first累積（accumulated[slot]+=filter·value、範囲外writeはnone）とforward alpha powersが実combineRows/evalCombinedと可換。current_roundのsuffix外側・integer内側のmutable累積がGateSuffixの整数ごとのsuffix和に一致し、Valid eq表でhalf=2^(numVars−1)。補間/DenseMle構成は別 |
| [NormDenseRound](Audit/Wire3/NormDenseRound.lean) | norm_logup.rsのround_sum_at（4 scratch vector・suffix loop・shift/mask PI loop）、evaluate_target_from_valuesの幅assert、current_roundの0..=5 sample→採用済み補間→定数省略、bindのprefix更新順とbindBuffer、prover stateのErr/panic/cache/Consistentを模し、送信5係数を実evaluateRoundが復元することを証明。構成データの由来・不正proverは別 |
| [OpenedClaimFold](Audit/Wire3/OpenedClaimFold.lean) | 採用済みPacked.fold/packedFold/bindManyのrow++index分割、pack_mlesの列優先padded table、Solidity cell/Rust slot対応（0-2はlog点、3-4はgate点、第6はnone）、native点=dense点の反転。明示的honest-prover仮定（claimed cell=各列のrow fold）下でexpectedClaimsの各cellがpadded tableのWHIR点での評価に一致。PCS binding/WHIR受理は別 |
| [GateTerminalBinding](Audit/Wire3/GateTerminalBinding.lean) | gate proverのbind_challenge（degree ensure→eq/全wire/全constantのbindBuffer→rounds/point push）とinto_proof_and_pointを模し、全変数bind後の各列=採用済みpacked fold、最終roundのeq·aggregateがGatesComplete.evalCombinedとVerifier.gateTerminalに一致（eq cell=eqEvaluation(gateTau,gatePoint)は明示仮定）。honest prover限定の受理claim一致も証明。回路truth/PCSは別 |
| [NormTerminalBinding](Audit/Wire3/NormTerminalBinding.lean) | 全変数bind後のnorm prover表（単一cell列）をNormTerminalInput（constants++sigma、routed wire cells++非routed tail、identity/sigma helper、PI値）へ対応させ、prover targetとVerifier側Norm.evaluate/checkedEvaluate/Engine.logTerminalの項ごとの一致を証明。各bound cell=採用済みpacked fold。eq/subgroup cellのtau由来・lambda/eta/wire-map由来は明示仮定、honest prover定理は表示 |
| [OuterClaimChain](Audit/Wire3/OuterClaimChain.lean) | honest proverのlog laneを実Verifier.roundStep/runRoundsで駆動し、各round後のlogClaim=直前表のroundValue(r_i)、次表のf'(0)+f'(1)=roundValue(r)（2≤remaining、読取り境界証明済み）、初期零claim⇔端点和零、intoProofAndPoint=verifierが消費したmessage/challenge、OuterAdapterとの一致。gate laneは明示仮定でparameterise。健全性は主張しない |
| [IntegratedTerminalChain](Audit/Wire3/IntegratedTerminalChain.lean) | OuterClaimChain/NormTerminalBinding/GateTerminalBinding/OpenedClaimFoldを採用済みIntegrated.verify/verify_success_checksへ接続。honest proverではlogTerminal=derivedRoundsの最終logClaim、gateTerminal=gateClaim、WHIR期待claim=padded table評価となり、決定論的検査は全て成立、残りは名前付き観測（config hash/envelope/deployment/shape/長さ/verifyWhir/7 challenge/normShape）のみ。Rust順（WHIR→norm）とSolidity順の受理同値。健全性は主張しない |
| [EqTableProvenance](Audit/Wire3/EqTableProvenance.lean) | 実eq表builder（tau順の外側loop・index内側loop・左側累積）を模し、各entry=Norm.booleanRowEq、低位bitが先にbindされることを採用済みbindBufferから証明。全点bind後のeq cell=Norm.eqEvaluation(tau,point)、subgroup cell=verifierの積形subgroupEvaluation。これによりnorm/gateのterminal定理からeq/subgroup由来の仮定を除去した系を与える。VK generator由来は明示仮定のまま |
| [PublicInputHashBinding](Audit/Wire3/PublicInputHashBinding.lean) | 実hash-no-padスポンジ（rate8/capacity4、overwrite、⌈len/8⌉chunk、4要素digest）を採用済みPoseidon上で具体化し、全30roundで基底体が保たれること・c0読出しが無損失であること、raw canonical preflight（256語上限と各語<P、fallbackなし）を証明。gate terminalのhash観測を具体関数へ置換し、hashLength仮定を除去 |
| [TranscriptProvenance](Audit/Wire3/TranscriptProvenance.lean) | 「engineの初期transcriptが実導出そのもの」という単一前提から、7 challengeがchallengesFromInitialと一致すること、log/gate tau列とgate alphaが導出値であること、各challengeがsourceのdigest/counter位置に載ることを証明。ObservationOnlyは12→9項へ減る。hashの性質は一切使わず、順序と受け渡しのみ |
| [VkSubgroupProvenance](Audit/Wire3/VkSubgroupProvenance.lean) | plonky2のtwo_adic_subgroupとVK生成元導出を模し、固定two-adic生成元の位数2^32を核証明書から確定。verifier_v2.rsの再計算検査は「VKのpowersが表の生成元の反復二乗である」ことと同値であることを証明し、EqTableProvenanceのSubgroupPowersProvenance仮定を解消する |
| [ConditionalSoundness](Audit/Wire3/ConditionalSoundness.lean) | 18個の暗号仮定を可視フィールドとして列挙し、受理かつlog laneのbad eventなしなら抽出表のendpointSum=0（IntegratedTerminalChainが仮定していたzeroSumの導出）。bad set濃度は195·⌈2^256/p⌉³以下。**gate laneは未証明、2^-184は外側sumcheck項のみでWHIRを含まず、系全体の健全性誤差ではない** |
| [GateDenseRound](Audit/Wire3/GateDenseRound.lean) | NormDenseRoundのgate版。current_roundを採用済みgridと補間で端まで模し、送信長=q+2、省略定数=verifierの半和復元、実evaluateRoundの再現、Consistentとround間端点恒等式、Boolean cube和の定義と第1roundでの一致を証明。多round帰納は未実施、cube和=0は主張しない（回路truth） |
| [OpeningBinding](Audit/Wire3/OpeningBinding.lean) | 同root/index/depthの2つの受理openingが一致することを、実行から計算した有限listへのhash単射性へ還元（自由変数ではない）。抽出ではなくbindingであることを明示し、限界も定理として証明する（不透明engineのWHIR検査は任意のcontextを受理、opening関係は3つのrootを差し替えても不変） |
| [ZeroCheckSemantics](Audit/Wire3/ZeroCheckSemantics.lean) | 採用済みeqによる多重線形拡張がcube上でgを補間し、非零値があれば恒等的に零でないこと、零点の密度≤n/\|F\|（Schwartz-Zippel、総次数≤n、帰納法は完遂）を証明。bad set外のtauでGateDenseRoundの各行値が0になる系を与える。badSetsとは合成しない（単一challenge対n組） |
| [GateClaimChain](Audit/Wire3/GateClaimChain.lean) | gate laneを実Verifier.roundStepで多round連鎖し、terminal橋を渡し、受理+gate lane bad eventなしから抽出表のcube和=0を導く。gate lane固有の上界(q+2)·degreeBitsも再具体化。**供給者への棄却力はまだない**（eq表の自由度、selector零化、`numGateConstraints=0`退化は仮定4で除外） |
| [AlphaZeroCheck](Audit/Wire3/AlphaZeroCheck.lean) | 行の集約をalphaの多項式として係数を同定（slot値そのもの）し、根の個数≤numGateConstraints−1≤122をenvelopeから導く。bad set外のalphaで各slot値が0、filterが非零のgateは制約自体が0。tauとalphaの両zero-checkの合成も採用済みchallenge上で証明。filter零の行は非拘束（正しい挙動） |
| [GateRejectionPower](Audit/Wire3/GateRejectionPower.lean) | 攻撃シナリオ4つを定理として提示し、eqの単位分解（行和=1）で行和ゼロ偽造を不可能にする。強化仮定は旧仮定が受理した偽造状態を棄却することを具体例で示す。**selectorの部分的零化は未解決**（constants由来＝抽出接合）。tauはtranscriptに束縛されていない |
| [GateDerivedRejection](Audit/Wire3/GateDerivedRejection.lean) | 棄却定理をtranscript導出のgate tau/alphaで再述し、§3–4と縮約仮定集合から自由なchallengeを消す（10フィールド→9、bound cell仮定は全表eq由来から導出）。残るchallenge側の仮定は導出tau/alphaの2つの`hgood`と、sumcheck roundのBadEventFreeの3つ。§2は例外で自由alphaを保持 |
| [CommitmentOrder](Audit/Wire3/CommitmentOrder.lean) | 適応性の決定論的半分。22 frameのprefixが採用済みrelationStateと一致し、3つのrootが13/15/19番目、最終rootとgate alpha/tau squeezeの間は固定domain tag 2つだけ。表の変更はprefixを変えるか具体的hash衝突を生む。確率的半分（B）は定数hashで反例が存在し、順序論法では届かないと定理で示す |
| [ChallengeUnionBound](Audit/Wire3/ChallengeUnionBound.lean) | tauのzero-check bad setをn個の独立digest tripleの積事象へ、行ごとのalpha bad setを2^n行のunionへ持ち上げ、外側sumcheck項と合わせて3つの質量の和を上界化。envelope極値で≤2^-172を厳密有理数計算で証明（余裕0.07 bit、envelopeぎりぎり）。**WHIR/Merkle項を含まず系の健全性誤差ではない**。3項は別々の標本空間上で結合則は未形式化 |
| [AttachedUnionBound](Audit/Wire3/AttachedUnionBound.lean) | ChallengeUnionBoundの自由パラメータ（n、g、係数族）を受理実行に束縛する。tau arityはdegreeBitsから導出、行値はgateValue、係数族は受理由来のslotCoefficients、制約数≤123は受理から導出。attached tuple＝transcriptのtau列（attached_tau_tuple_ofFn）。combinedBoundの4引数単調性を証明し、envelope下で≤combinedBound 13 8 13 123≤2^-172。attached_seamが計数上界と「全行で選択gateの制約が零」を1定理に結合。**数値はWHIR/Merkle項を含まず系の健全性誤差ではない**（余裕0.07 bit、制約129で破れる） |
| [ConstantsProvenance](Audit/Wire3/ConstantsProvenance.lean) | selector部分零化攻撃の由来鎖L1–L6。selector値←供給constants列←bound cell←gatePreprocessed claim←committed列のbound cell←preprocessed root下のopening←deployment pin（Verifier.shape、verifier_v2.rs 184-187、MleVerifierV2.sol 563）。攻撃定理partial_zeroing_forces_one_of_three：供給列とpinned列のbound cellが導出gate点で異なれば、root不一致（pinで閉鎖）∨抽出接合の破れ∨opening関係の破れ。具体的偽造例で旧仮定は検知せず新鎖が接合で捕捉することを示す。**残余**: bound cell一致は列同定より弱い（反例つき）、engine不透明性R1、opening関係R2、root→列写像R3 |
| [JointChallengeSpace](Audit/Wire3/JointChallengeSpace.lean) | 3つの質量を1つの標本空間に載せる。squeeze schedule（alpha、tau×d、外側log/gate round×d）で添字づけた`Draw d → DigestTriple`上の一様計数測度を定義し、座標事象・tau積事象の質量を計数で証明、真のdisjunction事象`jointBadEvent`の質量≤combinedBound（joint_union_bound）を証明。外側項は両laneの2d座標を被覆。seam `DrawEncodesRun`は座標符号化の主張で**hash仮定ではない**（reduceTriple全射により全hash・全受理実行で可住、補題つき）。Fiat–Shamir半分(B)「符号化drawがjointProbability分布」は未形式化で、合成定理は暗号仮定を一切持たない。外側bad setは実現challenge/messageに相対的で「prefix定数」ではない（tau/alphaのみ定数）。2^-173≤bound 13 8 13 123≤2^-172、**WHIR/Merkle項を含まず系の健全性誤差ではない** |
| [GatePointZeroCheck](Audit/Wire3/GatePointZeroCheck.lean) | ConstantsProvenanceの残余「bound cell一致は列同定より弱い」を導出gate点上のSchwartz–Zippelで閉じる。橋渡しcell(bindColumn col point)=extension col point（2^|point|≤|col|で成立、短い列では切り詰めとゼロ埋めで破れる反例つき）、一致集合=差分列の零点集合で密度≤n/|F|、一様質量≤tauTerm。合成定理: 列が異なり導出gate点が一致集合外なら抽出接合CellsMatchClaimsかopening関係OpensCommittedTableが破れる（受理下、root分岐はpinで閉鎖）。供給列幅は採用済みConsistent+EqCellBindingから、committed列幅はopening関係から導出。gate点列=gate laneのround challenge列を抽象engineで証明し、JointSpaceの第4族として質量≤tauTerm d。**残余**: 供給列は結論の2分岐以外でrootに束縛されない（col固定後の点という読みでのみ密度が意味を持つ）、round digest連鎖は具体engineのみ、R1–R3、half (B)未形式化 |
| [OuterSequentialConditioning](Audit/Wire3/OuterSequentialConditioning.lean) | JointChallengeSpaceの外側座標に対する逐次条件付け（Fubini）版union bound。有限積空間上の一般エンジン（Nodup座標列、round kのbad setは先行座標のみに依存：PrefixDependent）で質量≤Σ c_k/|A|を証明し、round message を先行challengeの関数とする`Lane`（`ownsNext`は交互走査 log 0, gate 0, log 1, … の位相ビット）で両laneに具体化。adaptive外側事象の質量≤outerTerm（prefix凍結版と同じ数値）、adaptive結合bad事象≤combinedBound、凍結版laneEventはエンジンの特殊例で採用済みjoint_union_boundを再導出。モデルの敵対者はgate messageが同roundのlog challengeを見られる分だけ実物より強い（安全側）。**依然として理想一様法則上で、half (B)は未形式化、WHIR/Merkle項を含まず系の健全性誤差ではない** |
| [InstalledWhirTail](Audit/Wire3/InstalledWhirTail.lean) | 残余R1（engine不透明性）。採用済みの手動WHIR tailモデル`WhirConfigured.run`をIntegrated.modelEngineの`whirTail`に据え付け（parseWhir等は観測のまま、transcript/roundは不変）、受理⇒具体tail実行成功・3 root=[pinned preprocessed, witness, normInverse]・評価値=5つのbound cellのpacked fold。配備プロファイル（numRounds≥1）では中間round 1で3 rootが開かれ、各root位置のrowが`(initialOpen wp).merkleDepth`でMerkle認証されること、2つの受理実行で同root・同leafのrowが一致するか衝突することを証明。finalsplit経路（numRounds=0、fixtureには無い）は`_finalsplit`として別掲。この engine は空hintを実際に棄却する（盲目engine反例はこのengineには当たらない）。**残余R1b**: 「認証済み round-1 行ブロックと3 rootのみから抽出する固定関数が存在する」（WHIR近接性+sumcheck健全性、確率的、未形式化；per-column形はR3を包含し、fold水準の変種も併記）。`wp`は自由パラメータ（ソースはprofile digestで固定、Leanでは観測） |
| [AdaptiveAgreementFamily](Audit/Wire3/AdaptiveAgreementFamily.lean) | GatePointZeroCheckの一致集合を座標ごとのSchwartz–Zippel（各座標のbad setは affine 制限の根で濃度≤1、恒等零の場合は数えない）に分解し、OuterSequentialConditioningの adaptive エンジンに載せる。供給列は最初の`cut`座標のみの関数`colOf (xs.take cut)`。質量≤tauTerm d、第5族込みの結合bad事象≤combinedBound+tauTerm d（envelope極値で≤2^-171）。**二分法の形でのみ閉じる**: 実現prefixを通るaffine slice上で差分列の拡張が恒等的に零（偽造者は1座標を見ただけで構成でき、形式的残余証人として証明。R2/R3の領分）か、点が質量≤tauTermの集合に入るか。cut=dでは事象は空、cut=0・定数colOfはGPZCの固定列の読みに一致。Lane水準の凍結比較: DrawEncodesRun下でlaneごとにOSCのadaptiveLaneEvent(frozenLane)⟺JCSのlaneEvent（両方向）。理想一様法則、half (B)未形式化、**WHIR/Merkle項を含まず系の健全性誤差ではない** |
| [PinnedWhirProfile](Audit/Wire3/PinnedWhirProfile.lean) | InstalledWhirTailの自由パラメータ`wp`をconfigに固定する。`CanonicalWhirProfileV2.validateCanonical`の4制約（1≤numVariables≤21、sessionId、パラメータdigest=表の行[0:32]、protocolId=行[32:96]）を`deploymentValid`の具体化として据え付け（他は観測のまま）、受理⇒復号したwpが正準検査を通り、tailが走ったレコードとソースの検査が検証したレコードが一致。**ソースは`inDomainSamples>0`をどこでも構文的に強制しない**（F3の確認）。正値性とnumRounds≥1は表の意味論仮定`TableIsCanonical`（rowDigest／rowSeparates＝keccak単射性の代役）の下、転記済み2行（n=10: samples 29・rounds 1、n=21: 29・4。fixtureと生成表のkeccak再計算で一致）に対してのみ導出し、`pinned_round_one_authentication`でhsamples/hroundsを消す。残り19行はdigestのみ。`c.whirEncoding=c₀.whirEncoding`は`_requirePinnedConfiguration`の理想化（keccak単射性の残余として明記）。keccak・VK immutable store・復号器のrefinementは未モデル |
| [InstalledIndexSampler](Audit/Wire3/InstalledIndexSampler.lean) | 観測だった`sampleIndices`を具体化。採用済みの検査付きsampler（OuterAdapter.sampleResult：used claimsを6 frame＝domain sep「pcs-constituent-claims-v3」・tag 6のlog pre/wit/norm・gate pre/wit・空vec・domain sep「pcs-constituent-index-v3」で吸収後、1つのdigestからcounter 3i（log）と3·indexBits+3i（gate）でsqueeze）をdecode上で全域化し、`installedSamplerEngine = installedEngine (resampled e thash)`（rfl）。index squeeze前のprefixがround状態++claim framesであること、index digestが等しければ状態digestとused claimsが等しいか具体的transcript衝突が出ること（tag 6 payload単射性＋採用済みabsorb_messages_bind_or_collide）、両laneの長さ=indexBits、ObservationOnlyDerivedのlogIndex/gateIndex項が定理化されることを証明。「indexはcellの後に引かれる」（R3の順序面）を`per_column_identification_hook`として定理化（確率的段階は未証明）。decode仮定は採用済みCommitAgrees下の実行とfixtureで可住。index点の座標空間はcoordinate statementのみで法則は主張しない。schedule上のblock番号はラベル（未導出）。commitRound・parseWhir等は観測のまま |

現行rootは105モデル・3575件の名付き定理です。
**ConditionalSoundnessの数値2^-184を系の健全性誤差として引用しないでください。**
これは外側sumcheckの一致事象のみを数えた値で、支配項であるWHIR/Merkleを含みません。
gate laneは証明されておらず、抽出とcommitmentの接合も仮定のままです。直近の検査結果はREPORTとmanifestで管理します。
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
fresh source再生成検査は `mle/audit/fresh-source-audit.py --run` で実行します（旧一時runnerの
再実装、self-check29件は `test-fresh-source-audit.py`）。全非toolchainモジュールを空の出力先へ
sourceから再compileし、既存`.lake/build`を検索pathに含めず、`lean --deps`で各moduleのimport解決を
確認し、全定理を再probeしてreceiptを `~/.local/share/wire3-fresh-source/` へ書きます。
`sorry`、`admit`、独自公理、`native_decide` による穴埋めは認めません。
許容するglobalな論理公理は `propext`、`Classical.choice`、`Quot.sound` のみです。
Poseidon/Cosetの全18表・1147語をSolidityと逐語比較し、PoseidonはRustとも比較します。
これは定数抽出の継続検査であり、コンパイラやソース全体の形式的同値性ではありません。

**公理リストが短くても、定理の引数やEngine観測は仮定として残ります。**
hash照合は変更検知であり、コードとLeanモデルの形式的同値性を証明しません。
未証明のWHIR健全性を `Engine.whirTail = true` で証明済みにすることもありません。
