import NativeByteWordsLiterals
import NativeUartFenceCertificate
import NativeUartByteCertificates
import NativeUartFenceRestoration
import Lean

open Lean Elab Command in
run_elab do
  let env ← getEnv
  let modules := #[`NativeByteWordsLiterals, `NativeUartFenceCertificate,
    `NativeUartByteCertificates, `NativeUartFenceRestoration]
  let mut total : Nat := 0
  for moduleName in modules do
    let some moduleIdx := env.getModuleIdx? moduleName | throwError "Missing fixture {moduleName}"
    let mut count : Nat := 0
    for (name, info) in env.constants.toList do
      if env.getModuleIdxFor? name == some moduleIdx then
        match info with
        | .axiomInfo _ => throwError "Source axiom {name}"
        | _ => pure ()
        if info.isUnsafe then throwError "Unsafe fixture declaration {name}"
        let axioms ← collectAxioms name
        for axiomName in axioms do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "Prohibited axiom {axiomName} in {name}"
        logInfo m!"FIXTURE_DECL {moduleName} {name}: {axioms}"
        count := count + 1
    unless count > 0 do throwError "Empty fixture audit for {moduleName}"
    total := total + count
    logInfo m!"FIXTURE_OWNER {moduleName} declarations={count}"
  logInfo m!"FIXTURE_SUMMARY declarations={total} inspectedGeneratedWrappers=0"
