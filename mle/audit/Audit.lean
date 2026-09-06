/-
Current wire-v3 audit root at becfe98e.
Executable partial models and deterministic proofs, NOT full implementation
refinement or cryptographic soundness. See README.md, SCOPE.md and REPORT.md.
Historical models remain in HistoricalAudit.lean and are deliberately not
imported by this current root.
-/
import Audit.Wire3.Arithmetic
import Audit.Wire3.Packed
import Audit.Wire3.Transcript
import Audit.Wire3.Compact
import Audit.Wire3.Sumcheck
import Audit.Wire3.Verifier
import Audit.Wire3.Connections
import Audit.Wire3.WhirTerminal
import Audit.Wire3.WhirFinal
import Audit.Wire3.Merkle
import Audit.Wire3.Norm
import Audit.Wire3.Gates
import Audit.Wire3.Algebra
import Audit.Wire3.Integrated
import Audit.Wire3.GatesAdditionalCoset
import Audit.Wire3.GatesAdditional
import Audit.Wire3.PoseidonConstants
import Audit.Wire3.Poseidon
import Audit.Wire3.GatesComplete
import Audit.Wire3.NormIdentity
import Audit.Wire3.ModularPower
import Audit.Wire3.Spongefish
import Audit.Wire3.WhirInitial
import Audit.Wire3.WhirFinalSpongefish
import Audit.Wire3.WhirPrefix
import Audit.Wire3.PiSharedBits
import Audit.Wire3.PiCache
import Audit.Wire3.GoldilocksCertificate
import Audit.Wire3.MerkleExtraction
import Audit.Wire3.WhirSampling
import Audit.Wire3.WhirRows
import Audit.Wire3.WhirRowBinding
import Audit.Wire3.FermatBridge
import Audit.Wire3.WhirSchedule
import Audit.Wire3.GoldilocksFoundation
import Audit.Wire3.GoldilocksNorm
import Audit.Wire3.GoldilocksExt3Field
import Audit.Wire3.WhirPolynomial
import Audit.Wire3.GoldilocksLagrange
import Audit.Wire3.WhirIntermediate
import Audit.Wire3.WhirDedup
import Audit.Wire3.WhirTail
import Audit.Wire3.GoldilocksDomain
import Audit.Wire3.WhirQuadratic
import Audit.Wire3.WhirParameters
import Audit.Wire3.WhirDomainBridge
import Audit.Wire3.WhirChallenge
