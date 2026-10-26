import NativeDialetheicOrganism

open Lean Lean.DialetheicOrganism

def main (args : List String) : IO Unit := do
  let [sourceFile, neuralLibrary, factorLibrary, seconds] := args
    | throw <| IO.userError "organism-factor N-only-file VGI-adapter.so factor-bridge.so seconds"
  let some limit := seconds.toNat? | throw <| IO.userError "invalid execution boundary"
  let source ← IO.FS.readFile sourceFile
  let body ← create (Sixteen3.ofMask 8)
  attachVGI body neuralLibrary
  attachFactor body source.trimAscii.toString factorLibrary
  let started ← IO.monoMsNow
  repeat
    if (← taskClosed body) then break
    if (← IO.monoMsNow) - started >= limit*1000 then break
    step body
  let returning ← IO.monoMsNow
  IO.eprintln s!"ORGANISM_RETURN_BEGIN {returning - started} {limit*1000}"
  IO.println (← snapshot body)
  IO.eprintln s!"ORGANISM_RETURN_END {(← IO.monoMsNow) - returning}"
