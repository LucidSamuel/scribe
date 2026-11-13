import ZkGadgets.Poseidon.Orchard

/-! Executable differential checks, not kernel-certified collision evidence. -/
open Scribe.Poseidon.Orchard

def parseBytes (text : String) : IO (List UInt8) :=
  (text.splitOn ",").mapM fun part => do
    let some n := part.toNat? | throw (IO.userError "bad byte")
    unless n < 256 do throw (IO.userError "non-byte value")
    pure (UInt8.ofNat n)

def main (args : List String) : IO Unit := do
  let [file] := args | throw (IO.userError "expected vector-file path")
  let lines ← IO.FS.lines file
  for line in lines do
    let [rs, ns, ps, expectedText, messageText, outputText] := line.splitOn " "
      | throw (IO.userError "bad vector row")
    let some r := rs.toNat? | throw (IO.userError "bad round")
    let some nk := ns.toNat? | throw (IO.userError "bad nk")
    let some rho := ps.toNat? | throw (IO.userError "bad rho")
    let expected := expectedText.toNat?
    let actual := digest? r nk rho
    unless actual == expected do
      throw (IO.userError s!"integer digest mismatch at r={r}, nk={nk}, rho={rho}")
    let bytes ← parseBytes messageText
    let expectedBytes : Option (List UInt8) ← if outputText == "none" then pure none
      else do pure (some (← parseBytes outputText))
    unless encodeLE nk ++ encodeLE rho == bytes do
      throw (IO.userError "little-endian encoder mismatch")
    let actualBytes := digestBytes? r bytes
    unless actualBytes == expectedBytes do
      throw (IO.userError s!"byte digest mismatch at r={r}, nk={nk}, rho={rho}")
  for n in [0, 1, 31, 32, 63, 65] do
    unless digestBytes? 3 (List.replicate n 0) == none do
      throw (IO.userError s!"accepted malformed input length {n}")
  IO.println s!"PASS {lines.size} reference vectors and malformed-length rejection"
