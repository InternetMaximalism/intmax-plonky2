import Audit.Wire3.Verifier
import Audit.Wire3.Transcript

/-!
Explicit connections among the current wire-v3 audit modules at becfe98e.
The canonical arithmetic subtype used by Verifier and the three Fin limbs used
by Transcript carry exactly the same data. The conversions below are lossless
and preserve the actual c0/c1/c2 little-endian transcript encoding. Packed.fold
also supplies a concrete implementation of Verifier.Engine.foldClaim.

These are connections BETWEEN EXECUTABLE LEAN MODELS, not a Rust/EVM refinement
proof. They do not instantiate initial transcript derivation, Keccak, norm or
gate evaluation, parsing, or the WHIR tail. Width/point/input-shape checks remain
the verifier's responsibility. The sparse fold ignores width because changing
the count of trailing zeros cannot change its result for a fixed index point.
-/
namespace Audit.Wire3.Connections

def toTranscript (a : Verifier.Ext3) : Transcript.Ext3 :=
  ⟨⟨a.val.c0, a.property.1⟩,
   ⟨a.val.c1, a.property.2.1⟩,
   ⟨a.val.c2, a.property.2.2⟩⟩

def fromTranscript (a : Transcript.Ext3) : Verifier.Ext3 :=
  ⟨⟨a.c0.val, a.c1.val, a.c2.val⟩, a.c0.isLt, a.c1.isLt, a.c2.isLt⟩

theorem verifier_transcript_roundtrip (a : Verifier.Ext3) :
    fromTranscript (toTranscript a) = a := by
  apply Subtype.eq
  rfl

theorem transcript_verifier_roundtrip (a : Transcript.Ext3) :
    toTranscript (fromTranscript a) = a := rfl

theorem toTranscript_injective {a b : Verifier.Ext3}
    (h : toTranscript a = toTranscript b) : a = b := by
  have h := congrArg fromTranscript h
  simpa only [verifier_transcript_roundtrip] using h

theorem fromTranscript_injective {a b : Transcript.Ext3}
    (h : fromTranscript a = fromTranscript b) : a = b := by
  have h := congrArg toTranscript h
  simpa only [transcript_verifier_roundtrip] using h

theorem converted_arithmetic_is_canonical (a : Transcript.Ext3) :
    Arithmetic.Canonical (fromTranscript a).val := (fromTranscript a).property

def encode (a : Verifier.Ext3) : Transcript.Bytes := Transcript.ext3Bytes (toTranscript a)

theorem encoding_exact_limb_order (a : Verifier.Ext3) :
    encode a = Transcript.le 8 a.val.c0 ++ Transcript.le 8 a.val.c1 ++
      Transcript.le 8 a.val.c2 := rfl

theorem encoding_length (a : Verifier.Ext3) : (encode a).length = 24 :=
  Transcript.ext3_bytes_length _

theorem encoding_agrees_after_conversion (a : Transcript.Ext3) :
    encode (fromTranscript a) = Transcript.ext3Bytes a := rfl

theorem each_encoded_limb_roundtrips (a : Verifier.Ext3) :
    Transcript.fromLe (Transcript.fieldBytes (toTranscript a).c0) = a.val.c0 ∧
    Transcript.fromLe (Transcript.fieldBytes (toTranscript a).c1) = a.val.c1 ∧
    Transcript.fromLe (Transcript.fieldBytes (toTranscript a).c2) = a.val.c2 := by
  exact ⟨Transcript.field_encoding_roundtrip _, Transcript.field_encoding_roundtrip _,
    Transcript.field_encoding_roundtrip _⟩

theorem mapped_values_canonical (values : List Verifier.Ext3) :
    ∀ v ∈ values.map Subtype.val, Arithmetic.Canonical v := by
  intro v hv
  rcases List.mem_map.mp hv with ⟨a, _, h⟩
  subst h
  exact a.property

/-- A concrete implementation of the verifier's previously observed fold. -/
def packedFold : Verifier.FoldClaim := fun values _width point =>
  ⟨Packed.fold (values.map Subtype.val) (point.map Subtype.val),
    Packed.fold_canonical _ _ (mapped_values_canonical values)⟩

theorem packedFold_exact (values point : List Verifier.Ext3) (width : Nat) :
    (packedFold values width point).val =
      Packed.fold (values.map Subtype.val) (point.map Subtype.val) := rfl

theorem packedFold_width_only_controls_padding (values point : List Verifier.Ext3)
    (width otherWidth : Nat) : packedFold values width point = packedFold values otherWidth point := rfl

theorem packedFold_padding_invariant (values point : List Verifier.Ext3) (width padding : Nat) :
    packedFold (values ++ List.replicate padding Verifier.zero) width point =
      packedFold values width point := by
  apply Subtype.eq
  change Packed.fold ((values ++ List.replicate padding Verifier.zero).map Subtype.val)
    (point.map Subtype.val) = Packed.fold (values.map Subtype.val) (point.map Subtype.val)
  simpa only [List.map_append, List.map_replicate, Verifier.zero] using
    Packed.sparse_fold_equals_zero_padded_fold (values.map Subtype.val) (point.map Subtype.val) padding

def withPackedFold (e : Verifier.Engine) : Verifier.Engine := { e with foldClaim := packedFold }

theorem engine_uses_concrete_packed_fold (e : Verifier.Engine) (values point : List Verifier.Ext3)
    (width : Nat) :
    ((withPackedFold e).foldClaim values width point).val =
      Packed.fold (values.map Subtype.val) (point.map Subtype.val) := rfl

theorem concrete_engine_retains_exact_claim_mask (e : Verifier.Engine) (c : Verifier.Config)
    (p : Verifier.Proof) (idx : Verifier.IndexPoints) :
    (Verifier.expectedClaims (withPackedFold e).foldClaim c p idx).map Option.isSome =
      [true, true, true, true, true, false] :=
  Verifier.context_bound_mask_exact _ _ _ _

end Audit.Wire3.Connections
