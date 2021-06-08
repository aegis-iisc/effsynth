module VC = TransTypeChecker.VerificationC

val z3_log : string -> unit

type result = Success | Undef | Failure

val discharge : VC.standardt -> result
