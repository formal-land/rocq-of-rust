module Big = Z
module N = Native_transactions
module Host = N.StatefulHost
module Accounting = N.TransactionAccounting
module Handler = N.LegacyCall
module Authentication = N.TransactionAuth
module Raw_validation = N.TransactionValidation
module Commitments = N.EthereumCommitment

exception Bridge_error of string

let fail message = raise (Bridge_error message)
let max_wire_bytes = 16 * 1024 * 1024

let fields expected = function
| `Assoc entries ->
    let keys = List.map fst entries in
    if List.sort String.compare keys <> List.sort String.compare expected then
        fail "object has missing, duplicate, or unknown fields";
    entries
| _ -> fail "expected JSON object"

let field entries key =
    match List.assoc_opt key entries with Some value -> value | None -> fail ("missing field " ^ key)
let text = function `String value -> value | _ -> fail "expected JSON string"
let array = function `List values -> values | _ -> fail "expected JSON array"
let boolean = function `Bool value -> value | _ -> fail "expected JSON boolean"

let big = function
| `Int value when value >= 0 -> Big.of_int value
| `Intlit value ->
    if String.length value = 0 || String.length value > 1024 then fail "integer size limit";
    String.iter (fun char -> if char < '0' || char > '9' then fail "expected unsigned integer") value;
    Big.of_string value
| _ -> fail "expected unsigned JSON integer"

let rocq_z value = Native_numeric.of_big (big value)

let optional_z = function `Null -> None | value -> Some (rocq_z value)
let z_field entries name = rocq_z (field entries name)
let option_field entries name = optional_z (field entries name)
let z_list value = List.map rocq_z (array value)
let pairs value = List.map (function
    | `List [left; right] -> (rocq_z left, rocq_z right)
    | _ -> fail "expected pair") (array value)

let json_z = Native_numeric.json_z

let json_z_list values = `List (List.map json_z values)
let json_pairs values = `List (List.map (fun (left, right) -> `List [json_z left; json_z right]) values)

let account value =
    let value = fields ["address"; "balance"; "nonce"; "code"; "code_hash"; "storage"; "transient_storage"] value in
    { Host.Account.address = z_field value "address";
      balance = z_field value "balance"; nonce = z_field value "nonce";
      code = z_list (field value "code"); code_hash = z_field value "code_hash";
      storage = pairs (field value "storage"); transient_storage = pairs (field value "transient_storage") }

let json_account (value : Host.Account.t) = `Assoc
    ["address", json_z value.address; "balance", json_z value.balance;
     "nonce", json_z value.nonce; "code", json_z_list value.code;
     "code_hash", json_z value.code_hash; "storage", json_pairs value.storage;
     "transient_storage", json_pairs value.transient_storage]

let block value =
    let value = fields ["coinbase"; "gas_limit"; "number"; "timestamp"; "difficulty"; "base_fee";
                        "blob_base_fee"; "previous_randao"; "hashes"; "use_state_test_hashes"] value in
    { Host.Environment.Block.coinbase = z_field value "coinbase";
      gas_limit = z_field value "gas_limit"; number = z_field value "number";
      timestamp = z_field value "timestamp"; difficulty = z_field value "difficulty";
      base_fee = z_field value "base_fee"; blob_base_fee = z_field value "blob_base_fee";
      previous_randao = option_field value "previous_randao"; hashes = pairs (field value "hashes");
      use_state_test_hashes = boolean (field value "use_state_test_hashes") }

let transaction value =
    let value = fields ["tx_type"; "caller"; "target"; "nonce"; "chain_id"; "gas_limit"; "gas_price";
                        "max_priority_fee"; "access_list"; "max_fee_per_blob_gas"; "blob_hashes";
                        "value"; "data"; "authorization_list"] value in
    if field value "authorization_list" <> `Null then fail "authorization transactions are unsupported";
    { Accounting.Transaction.tx_type = z_field value "tx_type";
      caller = z_field value "caller"; target = option_field value "target"; nonce = z_field value "nonce";
      chain_id = option_field value "chain_id"; gas_limit = z_field value "gas_limit";
      gas_price = z_field value "gas_price"; max_priority_fee = option_field value "max_priority_fee";
      access_list = List.map (function
          | `List [address; keys] -> (rocq_z address, z_list keys)
          | _ -> fail "invalid access-list entry") (array (field value "access_list"));
      max_fee_per_blob_gas = z_field value "max_fee_per_blob_gas";
      blob_hashes = z_list (field value "blob_hashes"); value = z_field value "value";
      data = z_list (field value "data") }

let json_option_z = function None -> `Null | Some value -> json_z value

let json_transaction (value : Accounting.Transaction.t) = `Assoc
    ["tx_type", json_z value.tx_type; "caller", json_z value.caller;
     "target", json_option_z value.target; "nonce", json_z value.nonce;
     "chain_id", json_option_z value.chain_id; "gas_limit", json_z value.gas_limit;
     "gas_price", json_z value.gas_price; "max_priority_fee", json_option_z value.max_priority_fee;
     "access_list", `List (List.map (fun (address, keys) -> `List [json_z address; json_z_list keys]) value.access_list);
     "max_fee_per_blob_gas", json_z value.max_fee_per_blob_gas;
     "blob_hashes", json_z_list value.blob_hashes; "value", json_z value.value;
     "data", json_z_list value.data; "authorization_list", `Null]

let input value =
    let value = fields ["chain_id"; "block"; "excess_blob_gas"; "max_blobs_per_tx"; "accounts"] value in
    { Handler.Input.chain_id = z_field value "chain_id"; block = block (field value "block");
      excess_blob_gas = option_field value "excess_blob_gas";
      max_blobs_per_tx = option_field value "max_blobs_per_tx";
      accounts = List.map account (array (field value "accounts")) }

let json_gas (value : Accounting.Settlement.t) = `Assoc
    ["gas_remaining", json_z value.gas_remaining; "gas_refunded", json_z value.gas_refunded;
     "gas_used", json_z value.gas_used; "caller_reimbursement", json_z value.caller_reimbursement;
     "beneficiary_reward", json_z value.beneficiary_reward; "base_fee_burn", json_z value.base_fee_burn;
     "blob_fee_burn", json_z value.blob_fee_burn]

let json_log (value : Host.EvmLog.t) = `Assoc
    ["address", json_z value.address; "topics", json_z_list value.topics; "data", json_z_list value.data]

let status_name = function
| N.InstructionResult.Continue -> "Continue"
| N.InstructionResult.Stop -> "Stop"
| N.InstructionResult.Return -> "Return"
| N.InstructionResult.SelfDestruct -> "SelfDestruct"
| N.InstructionResult.ReturnContract -> "ReturnContract"
| N.InstructionResult.Revert -> "Revert"
| N.InstructionResult.CallTooDeep -> "CallTooDeep"
| N.InstructionResult.OutOfFunds -> "OutOfFunds"
| N.InstructionResult.CreateInitCodeStartingEF00 -> "CreateInitCodeStartingEF00"
| N.InstructionResult.InvalidEOFInitCode -> "InvalidEOFInitCode"
| N.InstructionResult.InvalidExtDelegateCallTarget -> "InvalidExtDelegateCallTarget"
| N.InstructionResult.CallOrCreate -> "CallOrCreate"
| N.InstructionResult.OutOfGas -> "OutOfGas"
| N.InstructionResult.MemoryOOG -> "MemoryOOG"
| N.InstructionResult.MemoryLimitOOG -> "MemoryLimitOOG"
| N.InstructionResult.PrecompileOOG -> "PrecompileOOG"
| N.InstructionResult.InvalidOperandOOG -> "InvalidOperandOOG"
| N.InstructionResult.ReentrancySentryOOG -> "ReentrancySentryOOG"
| N.InstructionResult.OpcodeNotFound -> "OpcodeNotFound"
| N.InstructionResult.CallNotAllowedInsideStatic -> "CallNotAllowedInsideStatic"
| N.InstructionResult.StateChangeDuringStaticCall -> "StateChangeDuringStaticCall"
| N.InstructionResult.InvalidFEOpcode -> "InvalidFEOpcode"
| N.InstructionResult.InvalidJump -> "InvalidJump"
| N.InstructionResult.NotActivated -> "NotActivated"
| N.InstructionResult.StackUnderflow -> "StackUnderflow"
| N.InstructionResult.StackOverflow -> "StackOverflow"
| N.InstructionResult.OutOfOffset -> "OutOfOffset"
| N.InstructionResult.CreateCollision -> "CreateCollision"
| N.InstructionResult.OverflowPayment -> "OverflowPayment"
| N.InstructionResult.PrecompileError -> "PrecompileError"
| N.InstructionResult.NonceOverflow -> "NonceOverflow"
| N.InstructionResult.CreateContractSizeLimit -> "CreateContractSizeLimit"
| N.InstructionResult.CreateContractStartingWithEF -> "CreateContractStartingWithEF"
| N.InstructionResult.CreateInitCodeSizeLimit -> "CreateInitCodeSizeLimit"
| N.InstructionResult.FatalExternalError -> "FatalExternalError"
| N.InstructionResult.ReturnContractInNotInitEOF -> "ReturnContractInNotInitEOF"
| N.InstructionResult.EOFOpcodeDisabledInLegacy -> "EOFOpcodeDisabledInLegacy"
| N.InstructionResult.SubRoutineStackOverflow -> "SubRoutineStackOverflow"
| N.InstructionResult.EofAuxDataOverflow -> "EofAuxDataOverflow"
| N.InstructionResult.EofAuxDataTooSmall -> "EofAuxDataTooSmall"
| N.InstructionResult.InvalidEXTCALLTarget -> "InvalidEXTCALLTarget"

let gas_error = function
| Accounting.GasError.GasPriceBelowBaseFee -> ("GasPriceBelowBaseFee", [])
| Accounting.GasError.Eip2930NotSupported -> ("Eip2930NotSupported", [])
| Accounting.GasError.Eip1559NotSupported -> ("Eip1559NotSupported", [])
| Accounting.GasError.Eip4844NotSupported -> ("Eip4844NotSupported", [])
| Accounting.GasError.PriorityFeeGreaterThanMaxFee -> ("PriorityFeeGreaterThanMaxFee", [])
| Accounting.GasError.CreateInitCodeSizeLimit -> ("CreateInitCodeSizeLimit", [])
| Accounting.GasError.BlobGasPriceGreaterThanMax (left, right) -> ("BlobGasPriceGreaterThanMax", [left; right])
| Accounting.GasError.EmptyBlobs -> ("EmptyBlobs", [])
| Accounting.GasError.BlobVersionNotSupported -> ("BlobVersionNotSupported", [])
| Accounting.GasError.TooManyBlobs (left, right) -> ("TooManyBlobs", [left; right])
| Accounting.GasError.GasLimitAboveBlock -> ("GasLimitAboveBlock", [])
| Accounting.GasError.GasLimitAboveCap (left, right) -> ("GasLimitAboveCap", [left; right])
| Accounting.GasError.IntrinsicGasTooHigh (left, right) -> ("IntrinsicGasTooHigh", [left; right])
| Accounting.GasError.FloorGasTooHigh (left, right) -> ("FloorGasTooHigh", [left; right])
| Accounting.GasError.PaymentOverflow -> ("PaymentOverflow", [])

let rejection = function
| Handler.Rejection.Gas reason -> gas_error reason
| Handler.Rejection.PrevrandaoNotSet -> ("PrevrandaoNotSet", [])
| Handler.Rejection.ExcessBlobGasNotSet -> ("ExcessBlobGasNotSet", [])
| Handler.Rejection.InvalidChainId -> ("InvalidChainId", [])
| Handler.Rejection.MissingChainId -> ("MissingChainId", [])
| Handler.Rejection.RejectCallerWithCode -> ("RejectCallerWithCode", [])
| Handler.Rejection.NonceTooLow -> ("NonceTooLow", [])
| Handler.Rejection.NonceTooHigh -> ("NonceTooHigh", [])
| Handler.Rejection.NonceOverflow -> ("NonceOverflow", [])
| Handler.Rejection.LackOfFunds -> ("LackOfFunds", [])

let gap = function
| Handler.Gap.TopLevelPrecompile -> ("TopLevelPrecompile", [])
| Handler.Gap.Delegation -> ("Delegation", [])
| Handler.Gap.Accounting reason ->
    match reason with
    | Accounting.UnsupportedReason.Fork spec -> ("Fork", [N.SpecId.get_discriminant spec])
    | Accounting.UnsupportedReason.TransactionType tx_type -> ("TransactionType", [tx_type])
    | Accounting.UnsupportedReason.Creation -> ("Creation", [])
    | Accounting.UnsupportedReason.GasArithmeticOverflow -> ("GasArithmeticOverflow", [])

let response authentication kind fields = `Assoc
    (["protocol", `Int 1; "engine", `String "rocq_revm"; "kind", `String kind;
      "authentication", authentication] @ fields)

let authentication_record = function
| None -> `Assoc ["verified", `Bool false; "transaction", `Null]
| Some transaction -> `Assoc ["verified", `Bool true; "transaction", json_transaction transaction]

let json_commitments accounts logs =
    match Commitments.state_root accounts, Commitments.logs_hash logs with
    | Some state_root, Some logs_hash -> `Assoc
        ["source", `String "rocq"; "state_root", json_z_list state_root; "logs_hash", json_z_list logs_hash]
    | _ -> fail "completed state or log commitment is malformed"

let json_result authentication initial_accounts = function
| Handler.Result.Completed value -> response authentication "Completed"
    ["status", `String (status_name value.status); "gas", json_gas value.gas;
     "data", json_z_list value.data; "accounts", `List (List.map json_account value.accounts);
     "logs", `List (List.map json_log value.logs);
     "commitments", json_commitments value.accounts value.logs]
| Handler.Result.Rejected reason ->
    let reason, details = rejection reason in
    response authentication "Rejected"
        ["reason", `String reason; "details", json_z_list details;
         "accounts", `List (List.map json_account initial_accounts); "logs", `List [];
         "commitments", json_commitments initial_accounts []]
| Handler.Result.Unsupported reason ->
    let reason, details = gap reason in
    response authentication "Unsupported" ["reason", `String reason; "details", json_z_list details]
| Handler.Result.Malformed -> response authentication "Malformed" []
| Handler.Result.Incomplete -> response authentication "Incomplete" []

let authentication_error = function
| Authentication.Error.MalformedRlp -> ("MalformedRlp", [])
| Authentication.Error.MalformedFields -> ("MalformedFields", [])
| Authentication.Error.InvalidSignature -> ("InvalidSignature", [])
| Authentication.Error.TransactionTypeNotSupported tx_type -> ("TransactionTypeNotSupported", [tx_type])
| Authentication.Error.RecoveryFailed -> ("RecoveryFailed", [])
| Authentication.Error.ChainIdMismatch (have, expected) -> ("ChainIdMismatch", [have; expected])
| Authentication.Error.SenderMismatch (have, expected) -> ("SenderMismatch", [have; expected])

let authentication_gap = function
| Authentication.Unsupported.TransactionType tx_type -> ("TransactionType", [tx_type])
| Authentication.Unsupported.BlobSidecar -> ("BlobSidecar", [])

let spec = function
| "Frontier" -> N.SpecId.FRONTIER
| "Homestead" -> N.SpecId.HOMESTEAD
| "TangerineWhistle" -> N.SpecId.TANGERINE
| "SpuriousDragon" -> N.SpecId.SPURIOUS_DRAGON
| "Byzantium" -> N.SpecId.BYZANTIUM
| "ConstantinopleFix" -> N.SpecId.PETERSBURG
| "Istanbul" -> N.SpecId.ISTANBUL
| "Berlin" -> N.SpecId.BERLIN
| "London" -> N.SpecId.LONDON
| "Paris" -> N.SpecId.MERGE
| "Shanghai" -> N.SpecId.SHANGHAI
| "Cancun" -> N.SpecId.CANCUN
| "Prague" -> N.SpecId.PRAGUE
| "Osaka" -> N.SpecId.OSAKA
| _ -> fail "unsupported fork"

let nat_of_int value =
    let rec loop remaining result =
        if remaining = 0 then result else loop (remaining - 1) (N.S result)
    in
    loop value N.O

let raw_response kind extra = `Assoc
    (["protocol", `Int 1; "engine", `String "rocq_revm";
      "scope", `String "raw_transaction"; "kind", `String kind] @ extra)

let raw_rejection = function
| Raw_validation.Rejection.MalformedEnvelope -> "MalformedEnvelope"
| Raw_validation.Rejection.InvalidSignature -> "InvalidSignature"
| Raw_validation.Rejection.EmptyAuthorizationList -> "EmptyAuthorizationList"
| Raw_validation.Rejection.IntrinsicGasTooHigh -> "IntrinsicGasTooHigh"
| Raw_validation.Rejection.FloorGasTooHigh -> "FloorGasTooHigh"
| Raw_validation.Rejection.GasArithmeticOverflow -> "GasArithmeticOverflow"

let raw_result = function
| Raw_validation.Result.Valid (sender, hash, intrinsic_gas) ->
    raw_response "Valid" ["sender", json_z sender; "hash", json_z_list hash;
                          "intrinsic_gas", json_z intrinsic_gas]
| Raw_validation.Result.Rejected reason ->
    raw_response "Rejected" ["reason", `String (raw_rejection reason); "details", `List []]
| Raw_validation.Result.Unsupported reason ->
    let label, details = match reason with
    | Raw_validation.Unsupported.TransactionType tx_type -> "TransactionType", [tx_type]
    | Raw_validation.Unsupported.BlobSidecar -> "BlobSidecar", []
    | Raw_validation.Unsupported.AuthorizationExecution -> "AuthorizationExecution", []
    in
    raw_response "Unsupported" ["reason", `String label; "details", json_z_list details]

let execute request =
    let request_kind = match request with
        | `Assoc entries -> text (field entries "request")
        | _ -> fail "expected JSON object"
    in
    if request_kind = "validate_signed_transaction" then
        let request = fields ["protocol"; "request"; "fork"; "chain_id"; "signed_transaction"] request in
        if field request "protocol" <> `Int 1 then fail "unsupported protocol";
        let fork = spec (text (field request "fork")) in
        let chain_id = z_field request "chain_id" in
        let raw = z_list (field request "signed_transaction") in
        raw_result (Raw_validation.validate fork chain_id raw)
    else
    let common = ["protocol"; "request"; "fuel"; "fork"; "input"] in
    let expected = match request_kind with
        | "execute_transaction" -> common @ ["transaction"]
        | "execute_signed_transaction" -> common @ ["signed_transaction"; "declared_sender"]
        | _ -> fail "unsupported request"
    in
    let request = fields expected request in
    if field request "protocol" <> `Int 1 then fail "unsupported protocol";
    let fuel = big (field request "fuel") in
    if Big.gt fuel (Big.of_int 10000000) then fail "fuel exceeds limit";
    let fuel = nat_of_int (Big.to_int fuel) in
    let spec = spec (text (field request "fork")) in
    let input = input (field request "input") in
    if request_kind = "execute_transaction" then
        let tx = transaction (field request "transaction") in
        json_result (authentication_record None) input.accounts (N.native_transaction_run fuel spec tx input)
    else
        let raw = z_list (field request "signed_transaction") in
        let declared_sender = option_field request "declared_sender" in
        match Authentication.authenticate_for_spec spec input.chain_id declared_sender raw with
        | Authentication.Result.Authenticated transaction ->
            json_result (authentication_record (Some transaction)) input.accounts
                (N.native_eest_transaction_run fuel spec transaction input)
        | Authentication.Result.Rejected error ->
            let reason, details = authentication_error error in
            response (authentication_record None) "AuthenticationRejected"
                ["reason", `String reason; "details", json_z_list details;
                 "accounts", `List (List.map json_account input.accounts); "logs", `List [];
                 "commitments", json_commitments input.accounts []]
        | Authentication.Result.Unsupported gap ->
            let reason, details = authentication_gap gap in
            response (authentication_record None) "Unsupported"
                ["reason", `String reason; "details", json_z_list details]

let bounded_line channel =
    let buffer = Buffer.create 4096 in
    let rec loop count =
        match input_char channel with
        | '\n' -> Some (Buffer.contents buffer)
        | char ->
            if count >= max_wire_bytes then fail "request exceeds input size limit";
            Buffer.add_char buffer char;
            loop (count + 1)
        | exception End_of_file ->
            if count = 0 then None else Some (Buffer.contents buffer)
    in
    loop 0

let () =
    try
        let rec loop () =
            match bounded_line stdin with
            | None -> ()
            | Some line ->
                let request = Yojson.Safe.from_string line in
                let output = execute request in
                print_endline (Yojson.Safe.to_string output);
                flush stdout;
                loop ()
        in
        loop ()
    with
    | Bridge_error message -> prerr_endline ("bridge input error: " ^ message); exit 2
    | Yojson.Json_error message -> prerr_endline ("bridge JSON error: " ^ message); exit 2
