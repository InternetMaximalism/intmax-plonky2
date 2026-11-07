# MLE verifier ガス半減 戦略（2026-11-07）

対象: `mle/contracts`（wire v3、HEAD `48705559` = main）。親（`~/repos/intmax3-zkp`）の 6 配備プロファイルはすべて degree_bits 13・幅 160・WHIR 21 変数で、これはチェックイン済みの最大次元 fixture（`v2_max_resource.json`）と同じ形である。したがって本戦略の基準値は最大次元 fixture の実測値とする。

## 1. 基準値と目標

実測（本セッション、Forge、生の `staticcall`、uninstrumented）:

| 項目 | 値 |
| --- | ---: |
| `PinnedMleVerifierV2.verifyCompact` 実行ガス（最大 fixture） | 12,654,251 |
| 同 calldata 固有ガス（129,380 B、非零 123,037 B、21k + 4/16 per byte） | 2,014,964 |
| **合計（現状）** | **14,669,215** |
| **目標（半分）** | **≈ 7,335,000** |
| 小 fixture（degree_bits 2、10 変数）実行ガス | 7,850,402 |
| compact proof の内訳 | WHIR hints 108,184 B、narg 1,904 B、固定部 19,196 B（claim ベクトル 5 本 ≈ 14.4 KB が大半） |
| EIP-7623 floor（同じ calldata を送った場合の下限） | ≈ 5,005,910 |

含意:
- 小 fixture でも最大の 62% のガスを使う。固定コスト（norm 終端、Poseidon ゲート、transcript、ABI 境界）が大きく、回路サイズに比例しない。
- calldata をそのままにすると floor 5.0M があるため、実行ガスを 5.3M 以下にしても合計は 7.3M までしか下がらない。半減には **実行 −7.3M 相当か、実行 −6M + calldata −1.3M** のどちらかが必要。
- 親の close プロファイルは PI が 103 個で、公開入力 Poseidon ハッシュが 13 permutation（fixture は 1）、直接 PI 項も大きい（README: +508,524）。配備形状では基準値がさらに約 2M 高い（README: 親 cold close 16.9M 実行）。戦略の測定は **配備形状の fixture** でも行う必要がある。

### 配備プロファイルの形（`~/repos/intmax3-zkp/contracts/test/data/*_mle_config.json`、15 本、本体確認）

全プロファイルが degree_bits 13・幅 160・WHIR 21 変数・ゲート 13 行。公開入力数は 8（validity 系 5 本）、17（withdrawal 系 4 本）、29（cancel_close）、35（close_asset_backing）、50（withdrawal_claim）、58（post_close_claim）、103（close_intent）。ゲート族の和集合は id 0〜13 の全 14 族（Exponentiation は withdrawal_claim／post_close_claim のみ、num_power_bits 66）。最大 fixture（PI 1、ゲート 5 族）との差は主に公開入力 Poseidon（PI 103 で 13 permutation）、直接 PI 項、ゲート終端の族数である。Phase 0 の配備形状 fixture はこの和集合（全 14 族、PI 103）で作る。

### 配備形状 fixture の実測（Phase 0 で追加、`v2_production_shape.json`: 全 14 ゲート族・PI 103・degree_bits 13）

| 項目 | 配備形状 | 最大 fixture | 差 |
| --- | ---: | ---: | ---: |
| `verifyCompact` 実行ガス | **17,009,363** | 12,666,921 | +4,342,442 |
| `verifyCompactPublicInputs` 実行ガス | 17,018,738 | 12,667,290 | |
| core `verify` 実行ガス | 15,773,397 | 11,689,441 | |
| compact calldata（bytes／固有ガス） | 131,236 B／2,042,512 | 129,364 B／2,014,964 | |
| **合計上限（verifyCompact）** | **19,051,875** | 14,681,885 | |
| 公開入力 Poseidon（13 permutation） | 1,751,305 | 144,076（1 permutation） | +1.61M |
| ゲート終端 `evalCombined`（14 族） | 3,337,374 | 1,240,293（5 族） | +2.10M |

したがって **半減の目標は配備形状で ≈ 9.5M（実行 ≈ 7.5M + calldata ≈ 2.0M）** とする。最大 fixture の 7.3M はサブ目標。増分 4.3M のうち 3.7M は公開入力 Poseidon とゲート終端で、どちらも実装最適化（assembly 化）と、公開入力 Poseidon については設計上の削減余地（下記 B5）がある。

## 2. ガスの行き先（最大 fixture、計測器補正後 12,688,189 = 実測 +0.27%）

| フェーズ | ガス | 比率 |
| --- | ---: | ---: |
| WHIR 全体（`verifyWhirProofBound` 内） | 5,638,527 | 44.4% |
| ├ Merkle 認証（2,506 ノード、583 gas/ノード、keccak 自体は 42） | 1,460,598 | 11.5% |
| ├ in-domain 行評価（round0: 87 行 × 16 base 列 @615 gas、round1-3: 720 Ext3 列 @≈1,010、final openings） | 1,779,927 | 14.0% |
| ├ final claim の round-constraint 減算（`mleEvaluateUnivariateFrom` 1,033 回 @≈905） | 934,324 | 7.4% |
| ├ eval point の `glPow`（84 回 @≈3.5k）、challenge index の keccak（252 回 @≈1.0k）、sumcheck 21 round | 730,103 | 5.8% |
| 外側 sumcheck 13 round（transcript commit 467,706 + 多項式評価 422,671） | 903,651 | 7.1% |
| norm/logUp 終端（routed 80 本 × 15.3k、回路サイズ非依存） | 1,315,805 | 10.4% |
| ゲート終端（Poseidon ゲート 861,547 + 境界 94,392 + その他 14 族 123,341 + PI hash 139,682） | 1,219,000 | 9.6% |
| ABI/DELEGATECALL 境界（Pinned→core 437k、core→Outer 545k、core→WHIR 191k、gate 99k ほか） | 1,391,598 | 11.0% |
| TranscriptV2（squeeze ≈5.8k/Ext3、absorb 548/record、323 keccak で 41 KB） | 1,114,532 | 8.8% |
| データ実体化（compact decode 693,979 + canonical copy 270,623） | 964,602 | 7.6% |
| packed-claim fold（613 butterflies @903） | 553,533 | 4.4% |

横断的事実: 同じ 793 個の Ext3 レコードが約 6 回コピー／直列化される（decode → ABI 再エンコード → canonical copy → ライブラリ ABI → transcript frame → fold scratch → wire 2 回コピー）で ≈2.4M（19%）。Ext3 演算は 6,584 mul 相当だが、メモリ確保型ライブラリ呼出（`GoldilocksExt3.mul` 等）は 1.0〜1.7k/op、inline Yul は 260〜640/op。

計測器と再現: `scratchpad/gasprof/`（`patch.py`、`GasProbe.sol`、`profile_full.txt`、`summary_tables.txt`）。マーク 1 回 207 gas で補正済み。

## 3. レバー（期待削減、確度、変更範囲）

### A. 実装のみ（wire・ABI・証明バイト列を変えない）— 目標 −5.0〜−6.0M

| # | レバー | 期待削減 | 確度 | 根拠 |
| --- | --- | ---: | --- | --- |
| A1 | ABI/DELEGATECALL 境界の除去: core／Outer／WHIR／gate を **calldata オフセット渡し**にして memory 配列の ABI 再エンコードをやめる。EIP-170 により 1 コントラクト化は不可（core 20.0 KB、WHIR 23.7 KB）なので、ライブラリは残しつつ引数を calldata ポインタ＋小さな struct にする | −1.0〜−1.2M | 高 | 境界 1.39M のうち ABI コピーが大半（Pinned→core 197 KB、Outer 行き ≈800 Ext3） |
| A2 | 証明データの一回実体化: compact decode を「読みながら検査」に変え、canonical copy・transcript frame 直列化・fold scratch を同じバッファで共有。decode 790 gas/record → core の `_copyCanonicalExt3` 283/record 相当へ | −0.7〜−0.9M | 高 | decode 694k + copy 271k + absorb 328k |
| A3 | ホットループの Ext3 を stack 常駐 Yul に: 外側 round 評価（422k）、norm 終端 wire ループ（1.22M、15.3k/wire → 目標 7〜8k）、eq 評価、fold butterfly（903 → ≈400）、`mleEvaluateUnivariateFrom`（905 → ≈300） | −1.5〜−2.0M | 中〜高 | library op 1.0〜1.7k vs inline 260〜640 の実測差 |
| A4 | Merkle ノード処理の最適化: 583/ノード → 目標 ≈200（layer 配列の swap をやめ in-place、hint の calldataload をまとめ、pairing 判定を単純化） | −0.9M | 中 | keccak 42 に対し 14 倍のオーバーヘッド |
| A5 | in-domain 行評価: 列ごとの calldataload＋byte swap＋canonical 検査＋3 mulmod（615/列）を、行単位の一括ロードと weight 事前計算で ≈300/列へ | −0.7M | 中 | 1.78M の約半分 |
| A6 | TranscriptV2 の squeeze/absorb を固定 scratch バッファの assembly に（5.8k/Ext3 → ≈1.5k、frame 直列化 548/record → ≈150） | −0.6M | 高 | 228 squeeze + 34 vec frame |
| A7 | Poseidon ゲート（Ext3）と PI Poseidon（base）の専用 assembly（S-box x^7 = 2 square + 2 mul、MDS を定数畳み込み）: full round 60k → ≈25k、partial 11k → ≈5k；PI hash 140k/permutation → ≈60k | −0.5M（PI 103 個の配備形状では −1.5M） | 中 | 既存実装は memory 配列ベース |
| A8 | `glPow`（3.5k × 84）をビット分解＋テーブルで ≈1k、challenge index の keccak 1,020 → ≈300 | −0.35M | 高 | 単純な assembly 化 |

合計（重複を除いた保守的見積）: **−5.0〜−6.5M** → 実行 12.65M → 6.2〜7.6M。

### B. プロトコルのうち「束縛を変えない」軽微な wire 変更 — 目標 −0.8〜−1.2M

| # | レバー | 期待削減 | 影響 |
| --- | --- | ---: | --- |
| B1 | transcript の squeeze を 1 keccak = 4 limb に（現状 1 Ext3 = 3 keccak）。Rust `transcript_v2.rs` と Solidity を同時変更、ドメイン文字列を v4 に | −0.4M | 健全性: 同じ ROM 仮定、limb あたりの bias 不変 |
| B2 | hint の葉エンコードを 32 B 境界の big-endian（または Solidity が直接読める形）に | −0.2〜−0.3M 実行、calldata ±0 | フォークの hint 書き出しのみ |
| B3 | preprocessed 表（VK 固定）の Merkle **cap** を設定ストアに置く（cap 高さ 8〜10: 8〜32 KB の code-resident データ、`EXTCODECOPY` 1 回）: round0 の preprocessed 経路が 23 → 13〜15 段 | 実行 −0.17M、calldata −9 KB（−0.15M） | 証明形式変更（preprocessed の経路長）、VK 形式変更 |
| B4 | final claim の round-constraint 減算をアルゴリズム的に削減: 同一 r に対する 81 点の eq 評価を、点の構造（univariate x^{2^i}）を使って共有計算 | −0.4M | WHIR の検算式は不変（実装のみだが要数学的確認） |

| B5 | **verifier 側の公開入力 Poseidon 再計算の廃止**（PI 103 で 1.75M）: 回路内の Poseidon ゲートが PI target から hash wire を計算し、D_PI が raw PI を witness cell に束縛しているため、verifier の再計算は二重の束縛。PublicInputGate の hash wire を verifier 計算値と照合する代わりに「回路内ハッシュに任せる」設計（wire v4）にすれば 1.75M をほぼ全額削れる | −1.6M（PI 103）、−0.14M（PI 8） | 健全性の再審査が必要: D_PI＋回路内 Poseidon で raw PI の束縛が閉じていることを Lean／監査文書で明示する。PublicInputGate 制約の扱いを Rust/Solidity 両方で変更 |

### C. パラメータ再調整（≈100 bit 設計点を維持）— 目標 実行 −0.6M、calldata −0.5M

| # | レバー | 効果 | 代償 |
| --- | --- | --- | --- |
| C1 | 初期 log inv rate 6 → 8: クエリ 29/19/14/12/10 → ≈22/16/12/10/9（per-query bits 2.93 → 3.93）。Merkle・in-domain・final subtraction がクエリ数比例で −18%、hints −20 KB | 実行 −0.6M、calldata −0.33M | prover の初期 codeword が 4 倍（グループあたり 2^29 要素 ≈ 4 GB）。親は server-side 証明なので許容範囲か要確認。`outer_soundness_budget` の再計算と全 21 profile の再生成が必要 |
| C2 | PoW 22 → 26〜28 bit | クエリ −3〜6（−5〜8%）、hints −5 KB | prover の grinding 16〜64 倍 |
| C3 | 外側 index point・tau など squeeze 本数の削減は不可（束縛に必要）。final poly を大きくして round を減らす案は評価コストが増えるため不採用 | — | — |

C を全部入れると実行 −0.8M、calldata −0.5M 程度。

## 4. 到達見込み

| シナリオ | 実行 | calldata | 合計 | 目標比 |
| --- | ---: | ---: | ---: | --- |
| 現状（最大 fixture） | 12.65M | 2.01M | 14.67M | 100% |
| 現状（配備形状） | 17.01M | 2.04M | 19.05M | 100% |
| A のみ（保守） | 7.6M | 2.01M | 9.6M | 65% |
| A（楽観）+ B | 5.5M | 1.85M | 7.4M | 50% |
| A + B + C | 4.8M | 1.35M | 6.2M | 42% |

半減は A+B でぎりぎり、A+B+C で余裕がある。A は ABI と証明形式を変えないため親との互換性を保ったまま先行投入でき、B・C は wire v4 として親・fixture・Lean manifest・監査文書の更新を伴う。

## 5. 制約（守るもの）

1. **健全性**: 10 月の監査で確認した検査（終端式、root ピン、claim 吸収順序、cap 検査、canonical limb）は一つも省かない。負のテスト空白（終端式を消しても既存テストが通る）が既知なので、最適化前に **終端式・root・claim の負のテスト**を追加してから書き換える。
2. **Rust/Solidity 同一性**: 変異差分ハーネス（`audit_probe_cross_impl_mutations`: 201 変異で受理集合一致）を回帰テストとして各ステップで実行。
3. **EIP-170**: core 20,053 B（余裕 4,523）、WHIR 23,656 B（余裕 920）。assembly 化はコードが膨らむため、分割（calldata 渡し）とセットで進める。
4. **親の ABI**: Phase A は `verifyCompactPublicInputs`／`fraudVerdictCompact` の ABI・compact 形式を変えない。fraud 分類の `reserve + budget/8` しきい値は実行ガスの変化に合わせて再評価（拒否コスト ≈ 正直コストの 95% という前提が変わる）。
5. **監査ガード**: `mle/audit/wire3-manifest.json` のハッシュ更新と Lean モデルとの対応確認、`whir_profile_v2_codegen`／`protocol_schema_v2_codegen` の再生成。

## 6. 実行計画

Phase 0（計測基盤、1〜2 日）
- `gasprof` 計測器を `mle/contracts/test/GasProfile.t.sol` として正式化し、最大 fixture と **配備形状 fixture（PI 103、gate 13 行、CosetInterpolation 含む）** の両方で CI に数値を出す。
- 終端式・root・claim の負のテスト（cheating-prover fixture）を追加。

Phase 1（A1〜A8、ABI 不変、2〜3 週間）
- 順序: A1（境界）→ A2（一回実体化）→ A3（norm 終端・fold・round 評価）→ A4/A5（Merkle・in-domain）→ A6（transcript）→ A7（Poseidon）→ A8。各段で fixture 全件・変異差分・gas 表を更新。
- 判定ゲート: 実行 ≤ 7.6M。

Phase 2（B1〜B4、wire v4、1〜2 週間）
- Rust 側（`transcript_v2.rs`、フォークの hint 書き出し、VK の preprocessed cap）と Solidity を同時変更、全 fixture 再生成、schema/codegen 更新、manifest 更新。
- 判定ゲート: 合計 ≤ 7.4M。

Phase 3（C1/C2、任意）
- prover 側の実測（2^29 codeword のメモリ・時間）が許容なら rate 8 を採用。`outer_soundness_budget` を再計算し 100 bit 設計点を文書化。

## 7. 最初の一手（提案）

A1+A2 は 1 つの改修で扱える（「core は compact calldata を直接読む」設計）。ここだけで ≈1.8〜2.0M（14%）が見込め、他のレバーの前提（データが 1 箇所にある）にもなる。次に A3 の norm 終端 wire ループ（1.22M の固定費）。この 2 つで −3M 前後を先に確定させ、その実測で残りの見積を更新する。

## 8. 未確認事項

- 各レバーの削減値は実測プロファイルからの見積で、実装後の再計測で確定する。
- 配備形状（PI 103）での基準値は本セッションで未計測（README の親 cold close 16.9M は親のロジック込み）。
- C1 の prover コスト（2^29 要素）は未計測。
- B1 の transcript 変更は Lean モデル（Transcript フレーム定理）の更新が必要。

## 9. Phase 1 の結果（2026-11-07、ブランチ `claude/mle-gas-phase1`）

実装のみ（wire・ABI・証明バイト列・検査項目は不変）で以下に到達した。実測はすべて `GasBaselineV2.t.sol`（生の `staticcall`、uninstrumented）。

| fixture / 入口 | Phase 0 | Phase 1 | 削減 |
| --- | ---: | ---: | ---: |
| 配備形状 `verifyCompact` 実行 | 17,009,357 | **7,224,965** | −57.5% |
| 配備形状 `verifyCompactPublicInputs` 実行 | 17,018,732 | 7,254,059 | −57.4% |
| 配備形状 `fraudVerdictCompact`（正直、PI_MISMATCH） | 17,068,394 | 7,305,952 | −57.2% |
| 配備形状 合計上限（`verifyCompact` + calldata 2,042,512） | 19,051,869 | **9,267,477** | −51.4% |
| 最大 fixture `verifyCompact` 実行 | 12,654,254 | 5,827,238 | −54.0% |
| 小 fixture `verifyCompact` 実行 | 7,850,405 | 3,538,696 | −54.9% |

ユーザー目標（配備形状で合計 10M 以下）は達成。calldata（2.04M、EIP-7623 floor 5.07M）は不変。

### 効いた手段（実測ベース）

| 手段 | 効果（配備形状、実行ガス） |
| --- | ---: |
| core が compact calldata を直読みし、各 Ext3 ベクトルを 1 回だけ flat limb バッファに実体化（Pinned の decode・ABI 再エンコード・core の canonical copy を廃止、claim 吸収は calldatacopy）| −1.45M |
| TranscriptV2 を Yul 化（フレームは free pointer 先の一時メモリ、challenge は scratch 空間） | −0.37M |
| WHIR（Merkle の in-place 層縮約、hint 行の 4 limb 同時デコード、final claim の base-field 高速路、nibble 表 `glPow`、挿入ソート）: フレーム 5.64M → 2.90M | −2.7M |
| ゲート終端（flat limb バッファ上の Yul ゲート本体、Poseidon を limb 平面ごとの整数 FFT MDS、Karatsuba Ext2、lazy reduction）: フレーム 3.14M → 1.02M | −2.1M |
| 公開入力 Poseidon（定数を全てリテラル化、lazy reduction、13 permutation）: 1.75M → 0.56M | −1.2M |
| Outer（stack 常駐 Yul、lazy reduction、PI 束縛の行ごとの Horner）: 境界を除くフレーム ≈2.27M → ≈0.96M | −1.3M |
| ライブラリ境界の引数を `uint256[]` から 1 本の `bytes` に（2,000 語で 337k → 36k を実測）: Outer 境界 375k → ≈60k、gate 境界 80k → ≈30k | −0.4M |
| fold の lazy reduction、squeeze 展開、デコーダのレーン一括 byte 反転、ゲート終端式の core 内インライン | −0.3M |

### 検証

- `forge test --offline`: 455 tests pass（Phase 0 の 418 ＋ 新規の Flat/Blob 等価テスト 37）。未追跡の監査プローブ 27 件（Rust/Solidity 変異差分 201 変異、fraud 分類タクソノミ、transcript 合成、selector 設定）は全 pass、DIVERGENCE なし（`test_shiftNargHintBoundary` のみデフォルト gas 上限で OOG、監査記録どおりの既知事項）。
- 各サブエージェントは旧ライブラリ（5c3f72e2）との差分ハーネス（乱数・境界値入力）で新旧の同値を確認した上でコミット（ハーネスは scratch、未コミット）。
- 公開入力 Poseidon のインラインリテラル 734 個は `PoseidonConstants.sol` の blob と一致（本体で照合: 未知のリテラル 0、不足 0）。
- 実測された EVM の実コスト: Yul でも Ext3 積 1 回 ≈350〜400 gas（mulmod/addmod 連鎖）、lazy reduction（2^64 未満の canonical limb の積和を整数で累積し limb ごとに 1 回 `mod`）で ≈25% 減。机上見積（§3）は実コストを 3〜4 倍過小評価していた。

### フェーズ別の内訳（配備形状、計測器補正後、`gas_profile_2026-11-07/summary_tables_phase1.txt`）

| フェーズ | Phase 0 | Phase 1 |
| --- | ---: | ---: |
| Compact decode／parse（Pinned の decode → core の flat limb 化） | 733,188 | 471,161 |
| Pinned→core 境界 | 470,851 | 71,929 |
| core: 初期 transcript | 261,431 | 138,394 |
| core: canonical copy／views | 274,971 | 9,893 |
| core→Outer 境界 | 568,666 | 98,929 |
| Outer 結合 sumcheck 13 round | 905,348 | 418,231 |
| norm/logUp 終端（PI 束縛含む） | 1,834,153 | 848,269 |
| claim 吸収 + index squeeze | 420,829 | 54,017 |
| packed-claim fold | 557,093 | 424,830 |
| core→WHIR 境界 | 195,648 | 145,480 |
| WHIR フレーム計 | 5,638,527 | 2,901,251 |
| 公開入力 Poseidon（13 permutation） | 1,736,738 | 560,261 |
| core→gate 境界 | 107,952 | 24,685 |
| ゲート終端（非 Poseidon 13 行 + Poseidon） | 3,337,374 | 1,020,805 |
| ゲート終端式（外部 → core 内） | 70,540 | 13,586 |
| 計（補正後 callee total） | 17,050,048 | 7,258,321 |

### 残り（実装レベルで各 ≲10k）とプロトコル側の選択肢

実装のみでの残余は各項目 10k 未満（エージェント報告）。さらに削るなら B5（verifier 側の公開入力 Poseidon 廃止、−0.56M）、B1（squeeze の 4 limb/keccak 化）、C（rate 再調整で calldata −0.3M）が候補で、いずれも wire v4（Rust・Lean manifest・監査文書の更新）を伴う。
