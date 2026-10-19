Require Import ecdsa.simulate.lib.
Require Import ecdsa.simulate.verifying.
Require Import simulate.RocqOfRust.

(** REVM's secp256r1 provider delegates to the P256 ECDSA implementation. This
    executable specialization is not a proof of the RustCrypto limb arithmetic,
    constant-time behavior, or native-provider correspondence. *)
Module P256Ecdsa.
  Definition verify_signature (message signature public_key : list u8) : option unit :=
    match Signature.from_slice signature, VerifyingKey.from_encoded_point public_key with
    | Some signature, Some public_key =>
      VerifyingKey.verify_prehash public_key message signature
    | _, _ => None
    end.
End P256Ecdsa.
