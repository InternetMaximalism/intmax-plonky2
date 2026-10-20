# MLE WHIR HEAD 健全性調査

対象コミット: `3a20a05fb99d2653c4d37debb4f1ead2f422dfb2`。調査日: 2026年10月16日。

現在の wire v3／V2 API に対し、偽の公開入力または制約を破る witness を受理する新たな実装上の欠陥は確認できなかった。確認できた指摘は、compact fraud 判定の既知のガス境界での誤分類と、現行仕様を名乗る安全性資料の古い数値である。この結果は、WHIR／Fiat–Shamir の完全な健全性証明や本番利用の承認を意味しない。

## 対象と検証条件

`mle/src` の Rust 35ファイルと `mle/contracts/src` の Solidity 33ファイル、計68ファイルの非テスト実装をファイルごとに読んだ。以下の台帳に各ファイルの着眼点と結果を記す。テストコードは関係する箇所を確認・実行しており、すべてのテストファイルを逐行精読したという範囲ではない。

現行経路の攻撃者は証明と公開入力を制御する。VK、回路設定、PI wire map、WHIR profile、配備先 chain ID は正しい設定に固定する。設定の任意変更による失敗と、固定した設定での無効証明の受理を区別した。旧 V1 は別に到達性と封じ込めを確認した。

親リポジトリの settlement／recursion／返却公開入力の利用は今回の実装レビューの対象外。外部依存は pinned `leohio/whir@3db5dec4f45d7e9dd5527ea3c30778889f53a405` の検証アルゴリズム、最終 claim、IRS opening、query sampler、PoW、MLE／NTT の境界を重点的に照合した。依存クレート全体の再監査ではない。

作業開始時から存在した未追跡テスト `AuditFraudVerdictBoundary20261016.t.sol` と `AuditWhirMaxDimension20261016.t.sol` は既存の検証資料として実行した。今回作成したものとして扱わず、変更していない。実装・既存テストへの修正は行っていない。

## 確認した指摘

### P2 compact fraud 判定が完了済みの拒否を STARVED にする

箇所: [PinnedMleVerifierV2.sol](../contracts/src/PinnedMleVerifierV2.sol#L158)。既知事項の再現確認。

`fraudVerdictCompact` の catch は、戻ったエラーが正確な `InvalidMleProof()` かを見る前に `gasleft() < reserve + budget / 8` を評価する。そのため、本体が検証を完了して確定的に無効と判定しても、消費ガスがしきい値を越えると `INVALID = 0` ではなく `STARVED = 3` を返す。

既存の `AuditFraudVerdictBoundary20261016Test.test_completedRejectionCanBecomeStarved` を再実行し、最大21変数の fixture の hint 末尾改変で以下を確認した。

| classifier に与えたガス | より少ないガスを与えた本体の結果 | classifier の結果 |
| --- | --- | --- |
| 10,500,000 | 正確な `InvalidMleProof()`、計測消費 9,974,874 | STARVED |
| 11,000,000 | 同上 | STARVED |
| 11,500,000 | 同上 | STARVED |
| 12,000,000 | 同上 | INVALID |
| 12,500,000 | 同上 | INVALID |

これは core が無効証明を受理する問題ではない。fraud 判定の活性・必要ガスマージンに影響する。親側で十分な最低ガスを保証している場合の実際の影響は、その呼び出し条件に依存する。

修正候補は、信頼された decoder／core が返す正確な `InvalidMleProof()` を先に分類し、リソース不足の推定はその後に行うこと。`fraudVerdictEncoded` の core 検証後の分岐は既にこの順序になっている。今回は調査のみとし変更していない。

### P2 現行と明記された安全性資料が旧128 bit profile のまま

箇所: [mle_whir_v1_security.md](../paper/mle_whir_v1_security.md#L5)、同89–105行・143–155行。

冒頭 addendum は自分を current protocol/security statement と定義しているが、target 133、inverse-rate exponent 4、queries `[58,33,23,18,14]`、集約128.356 bit、local 128 bit target を記載している。

実際の [protocol schema](../protocol/mle_whir_v2.json#L32) は target 105、PoW 22、inverse-rate exponent 6、fold 4。[outer_soundness_budget.rs](../tests/outer_soundness_budget.rs#L482) と再計算の結果は、最大21変数で queries `[29,19,14,12,10]`、35イベント中9イベントが target に達し、集約値は **101.534561723 bit**。全許容 packed dimension 1–21 のうち最小値は21変数だった。

[README](../README.md#L332) は現行値と旧 profile の退役を正しく記載しているが、同時にこの addendum を current derivation として案内している。約26.82 bit の差があるため、安全性判断の根拠を誤らせる。古い addendum を歴史資料に限定するか、現行値・ROM の数値までまとめて更新する必要がある。

この指摘は文書と実装の不一致であり、証明偽造の実証ではない。現行の約100 bit 設計自体は README と schema に明記されている。

## 実装の確認結果

主要な束縛関係に次の欠落は見つからなかった。

- preprocessed／witness root を関係チャレンジより前に固定し、challenge-dependent norm-inverse root を残りの関係チャレンジより前に固定している。
- 公開入力は Poseidon digest の照合に加え、VK の canonical PI wire map を使う直接関係 `D_PI` で committed witness cell に束縛している。
- log／gate の round polynomial をそれぞれ厳密な係数数で読み、初期 claim 0 から定数係数を復元する。現行 log は formal coordinate norm により次数5、gate は設定から導く次数上限を検査する。
- 全 constituent claim を outer index challenge より前に吸収する。WHIR 内でも6セルすべてを vector RLC より前に吸収し、終端で使用する5セルを照合する。未使用の gate/norm セルも WHIR 自体では検証する。
- packed table の low row bits／high constituent bits と、WHIR の MSB-first 評価境界の反転が対応している。最終多項式と最後の opened rows の等式、全 linear forms の final claim、両ストリームの EOF が検査される。
- Rust／Solidity の canonical field limbs、hint の Vec prefix、配列長、compact EOF、resource caps、root 二重出現の一致を検査する。Solidity の profile は canonical table と完全な設定 digest で固定される。

実テーブルでコピー制約を破った witness、raw PI の変更、PI-mapped cell の変更は、gate 条件だけでは排除できない場合も norm/logUp terminal で拒否された。ゲート差分テストは本体 Plonky2 の evaluator と一致した。

## Rust のファイル別台帳

「確認」は実装の読解・相互照合を表す。各行を独立した健全性証明とは扱わない。

| ファイル | 確認内容と結果 |
| --- | --- |
| `src/lib.rs` | 公開 API と feature gate。旧 prover/verifier と optional-evaluation verifier の既定無効化を確認。 |
| `src/config.rs` | MLE 設定と構成。現行 VK／profile 側の検査との関係を確認。 |
| `src/dense_mle.rs` | LSB-first 評価・fold・表サイズ。WHIR 境界での反転と照合。 |
| `src/eq_poly.rs` | eq 評価と Boolean table の順序。direct PI と terminal の利用に整合。 |
| `src/constraint_eval.rs` | Plonky2 制約評価と列の取り扱い。current gate evaluator と照合。 |
| `src/gate_ext3.rs` | 14 gate families、selector filter、Ext2 の座標式、メタデータ・次数検査を全確認。 |
| `src/proof_v2.rs` | wire version、3 group／2 point／6 cell、packing と padding、VK 型を確認。 |
| `src/vk_v2.rs` | canonical PI copy-class map、gate metadata、回路設定 digest の導出・encoding。trusted setup 境界を確認。 |
| `src/prover_v2.rs` | setup の preprocessed commitment、root と challenge の順序、両 sumcheck、constituent opening の構成を確認。 |
| `src/verifier_v2.rs` | VK・shape・challenge・係数・PCS・両 terminal の連結を確認。偽受理を確認できず。 |
| `src/compact_v2.rs` | 厳密な version／shape／limbs／stream 長／EOF。旧 wire・末尾を拒否。 |
| `src/transcript_v2.rs` | tag と length を含む frame、domain、counter、256-bit reduction、独立 Ext3 limbs を確認。 |
| `src/fixture_v2.rs` | 非テスト部分を全確認。profile 再導出、ABI offset、canonical parsing、cross-view 一致、検証を伴う export。 |
| `src/fixture.rs` | 非テスト部分を全確認。current は型による gate downcast／narrowing と共有型を利用。旧 exporter/parser は protocol 1。 |
| `src/generated/mle_whir_v2.rs` | schema 由来の constants／domain／shape。生成回帰で drift なし。 |
| `src/generated/mle_whir_v1.rs` | 歴史 profile と domain の分離を確認。 |
| `src/commitment/mod.rs` | PCS module の公開範囲を確認。 |
| `src/commitment/traits.rs` | commit/open/verify の型境界と legacy transcript 利用を確認。 |
| `src/commitment/merkle_pcs.rs` | full reveal の root 再構築と MLE 評価。current grouped WHIR 経路からの利用なし。 |
| `src/commitment/whir_pcs.rs` | 全非テスト実装を確認。grouped root／pre-RLC claims、canonical preflight、zero divisor、native final claim／EOF。旧 split/aux API と現行利用を区別。 |
| `src/permutation/mod.rs` | norm／旧 logUp／lookup の公開関係を確認。 |
| `src/permutation/norm_logup.rs` | formal coordinate norm、inverse helper、degree-5 relation、PI 項、終端を全確認。 |
| `src/permutation/logup.rs` | 旧関係を確認。wire v3 の production relation ではない。 |
| `src/permutation/lookup.rs` | lookup 構成を確認。current circuit admission は lookup を拒否。 |
| `src/sumcheck/mod.rs` | current coefficient lanes と旧 sumcheck の区別を確認。 |
| `src/sumcheck/coefficients.rs` | 厳密な次数・係数数、定数係数復元と round 評価を確認。 |
| `src/sumcheck/ext3.rs` | Ext3 評価／補間と base-to-extension 境界を確認。 |
| `src/sumcheck/gate_ext3_v2.rs` | gate round nodes と terminal に同じ evaluator、次数上限の対応を確認。 |
| `src/sumcheck/prover.rs` | 旧 sumcheck の fold と challenge を確認。 |
| `src/sumcheck/types.rs` | round message と proof 型を確認。 |
| `src/sumcheck/verifier.rs` | generic verifier 自体に次数上限なし。旧 MLE caller が exact lengths を検査し、current は係数版を使うことを確認。 |
| `src/proof.rs` | 旧 proof／packing 型と protocol 境界を確認。 |
| `src/prover.rs` | 旧 prover を全読解。feature-gated、現行 v3 からの遷移なし。 |
| `src/verifier.rs` | 旧 verifier を全読解。弱い base-field 関係を現行保証に混入させない。 |
| `src/transcript.rs` | 歴史 transcript の serialization／counter／reduction。current 外側は TranscriptV2。 |

## Solidity のファイル別台帳

| ファイル | 確認内容と結果 |
| --- | --- |
| `contracts/src/MleVerifierV2.sol` | 配備・設定 pin、shape／canonical limbs、PCS expected values／points／roots、gate／norm terminal を確認。 |
| `contracts/src/PinnedMleVerifierV2.sol` | immutable config store、chain guard、authenticated PI return、fraud 分類。上記 P2 を再現。 |
| `contracts/src/CircuitConfigV2.sol` | exact metadata／gate／PI map を digest に含め、設定との一致を検査。 |
| `contracts/src/CanonicalWhirProfileV2.sol` | dimension ごとの digest／protocol ID／session の完全な allowlist 比較。 |
| `contracts/src/CompactMleProofV2.sol` | shape 由来の全長、canonical limbs、prefix／bounds／EOF。core 向け軽量 decode 後も core が再検査。 |
| `contracts/src/MleProofErrors.sol` | proof-dependent failure と設定・利用不可の分類を確認。 |
| `contracts/src/OuterLogupExt3Verifier.sol` | formal norm degree5、direct PI、係数復元、coupled rounds と terminal。 |
| `contracts/src/PackedClaimExt3.sol` | constituent projection、padding、index bits と claim 順序。 |
| `contracts/src/PackedClaimLib.sol` | 旧 packed helpers と current 利用範囲を確認。 |
| `contracts/src/EqPolyLib.sol` | eq と row/index convention、canonical 値への前提を確認。 |
| `contracts/src/GoldilocksField.sol` | base field 演算、reduction、逆元境界を確認。 |
| `contracts/src/TranscriptV2.sol` | frame／domain／counter、Ext3 challenge、Rust と byte-level 対応。 |
| `contracts/src/Plonky2GateEvaluatorExt3.sol` | 全14 dispatch、selector filter、constraint slot、metadata／degree、Ext2 座標演算。 |
| `contracts/src/CosetInterpolationGateExt3.sol` | interpolation、barycentric weight、shift、Ext2 arithmetic と次数の対応。 |
| `contracts/src/CosetInterpolationConstants.sol` | 対応 subgroup の定数表と index 範囲を確認。 |
| `contracts/src/PoseidonGateExt3.sol` | 全round、swap、MDS、partial round、constants と Rust／native 対応を確認。 |
| `contracts/src/PoseidonPublicInputsHash.sol` | public input hash、canonical input、shared hash helper の利用を確認。direct PI も別途拘束。 |
| `contracts/src/PoseidonGate.sol` | legacy gate と current 共用 hashNoPad を全読解。native の最適化式と照合。 |
| `contracts/src/PoseidonConstants.sol` | 定数 byte table と読取 index の caller 側範囲を確認。 |
| `contracts/src/MleVerifier.sol` | abstract の旧 verifier。current V2 から呼ばれず、test harness のみ具象化。 |
| `contracts/src/ConstraintEvaluator.sol` | 未使用の oracle-only helper。任意 C oracle の PCS binding だけで gate 健全性が得られるという説明は不十分。current は exact gate terminal を持つ。 |
| `contracts/src/SumcheckVerifier.sol` | 歴史 round verifier。V2 からの import なし。 |
| `contracts/src/TranscriptLib.sol` | 歴史 transcript。V2 からの import なし。 |
| `contracts/src/Plonky2GateEvaluator.sol` | 歴史 base evaluator の全gate／selector を確認。V2 は Ext3 版。 |
| `contracts/src/generated/MleWhirV1.sol` | 旧 schema／domain／proof layout の分離。 |
| `contracts/src/generated/MleWhirV2.sol` | 現行 schema constants、bound mask、resource cap。 |
| `contracts/src/generated/WhirProfilesV2.sol` | 21 profile の table、ID／digest。Rust 再生成テストに一致。 |
| `contracts/src/spongefish/GoldilocksExt3.sol` | cubic arithmetic、norm inverse、zero／canonical の扱いを確認。 |
| `contracts/src/spongefish/Keccak256Chain.sol` | absorb／squeeze／ratchet、BE counter、partial-block 出力、overflow を確認。 |
| `contracts/src/spongefish/SpongefishMerkle.sol` | sorted unique indices、paired／lone rows、hint bounds、配列の交互 scratch、root／depth の最終検査。 |
| `contracts/src/spongefish/SpongefishWhir.sol` | canonical NARG、120-byte Ext3 challenge、query entropy、geometric RLC。古い base sumcheck の PoW TODO は production verifier から未使用。 |
| `contracts/src/spongefish/SpongefishWhirVerify.sol` | root／OOD／claim／RLC 順序、PoW、全round opening、final vector／final claim／EOF を全確認。潜在的 eqW 境界不足は下記。 |
| `contracts/src/spongefish/WhirLinearAlgebra.sol` | eq weights／tensor／dot、MSB-first MLE、univariate powers、in-place folding と native 対応。 |

## 到達性で区別した既知の注意点

`SpongefishWhirVerify._dotEqWithRow` は hint 範囲を検査するが、`numCols <= eqW.length` を独立には検査しない。`numCommitments == 1 && numVectors > 1 && numRounds >= 1` という汎用設定では配列外の memory pointer を読む。既存 `PocWhirDotEqBounds` もこれを示す。

現行 core は3 commitments／1 vector に固定し、初期 opening は `_dotGroupedRow` に入る。この設定を証明から変えることはできないため、現行経路の健全性欠陥としては計上しなかった。汎用ライブラリを再利用するなら、等長検査と単一 commitment の vector RLC の扱いを直す必要がある。

旧 protocol 1 の base-field challenges／Poseidon のみの PI binding、optional-evaluation verifier は current wire v3 の安全性を支えない。Rust の非既定 `legacy-conformance` と Solidity の abstract legacy verifier による封じ込めを確認した。

## 安全性の数値と形式検証の限界

現行 WHIR の **101.534561723 bit は PoW を含む generic work の集約指標**である。中間段階で試行を放棄する prover に対する無条件の失敗確率ではない。README の粗い ROM 式へ `H = 2^32` を代入すると約69.535 bit の上界になるが、これは `2^69` 計算量の攻撃を発見したという意味ではない。計算仕事量の指標と oracle-query-dependent advantage を混ぜない。

Lean は次の採用済み定義・定理インターフェース・仮定と checker を重点確認した。157ファイルすべての逐行レビューではない。

- `SoundnessAssembly.lean:367` は5つの bound cells の fold-level opening 結論を仮定している。
- `R1bBridge.lean:182` は `WhirDecodeUniqueness` がこのツリーで証明されていないと明記する。これは構造体の仮定なので `#print axioms` だけでは未解決の暗号仮定を把握できない。
- `CircuitTruth.lean:62` は acceptance と `AssemblyResidue` などの同時充足をまだ実証していないと明記する。copy/routing と公開入力・truth columns の由来も同ファイルの ledger に残る。
- `PinnedWhirProfile` の具体的 record の転写は dimensions 10 と21のみ。残りの profile は digest による表現。実行可能な Rust／Solidity 生成テストは全21 profile を検査する。

manifest／定数照合を追跡ファイルに限定した診断では、304 Rust／Solidityファイルのうち40が部分的なモデル化、264が未モデル化、current Lean 157 modules、520 hashes、18定数表／1147 words が整合した。これは whole-implementation refinement の証明ではない。

`mle/audit/.lake` がないため、実際の proof dependency check は依存不足で失敗した。Lean 定理の再コンパイルは実施していない。checker 自身の self-tests の成功と、Lean build の成功を区別する。原論文 [WHIR](https://eprint.iacr.org/2024/1586.pdf) の保証を、この fork・外側プロトコル・Solidity への完全な refinement に置き換えることもできない。

## 実行した検証

Rust は pinned nightly `2025-03-23`、ネットワーク取得なしで実行した。重複実行したテストを二重に加算していない。

| コマンドまたは対象 | 結果 |
| --- | --- |
| `cargo test --offline -p plonky2_mle --lib` | 81 passed |
| `--test outer_soundness_budget` | 16 passed |
| `--test poc_perm_copy_constraint` | 6 passed |
| `--test poc_gates_differential` | 2 passed |
| `--test v2_cross_language_fixture` | 2 passed、生成専用1件 ignored |
| `--test fixture_v2` | 4 passed |
| `--test whir_profile_v2_codegen` | 2 passed |
| `cargo test --offline -p plonky2_mle --doc` | 4 compile-fail doctests passed。旧 API の既定公開なしを確認 |
| `forge test --offline --no-match-path 'test/Audit*.t.sol'` | 33 suites、385 passed、0 failed／skipped |
| 既存 `AuditFraudVerdictBoundary20261016.t.sol` | 1 passed、上記誤分類を再現 |
| 既存 `AuditWhirMaxDimension20261016.t.sol --fuzz-runs 64` | 9 passed、NARG全238ワード改変とhint 64 fuzz runs を拒否 |
| `WhirAssemblyDifferential.t.sol` | 正常終了。上記385件にも含まれる |
| audit checker／dependency guard／fresh-source self-tests | 33／34／29 passed |

重複を除く Rust の上記テストは117 passed、生成専用1件 ignored。Solidity は既存診断2ファイルを含め395 passed。

本番入口での新しい偽受理は再現できなかった。残る暗号学的な保証と親システムとの合成は、上記の未証明部分と明示した scope に従って判断する必要がある。
