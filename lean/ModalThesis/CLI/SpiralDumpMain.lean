import ModalThesis.IteratedVirtual.Spiral

/-!
# CLI.SpiralDumpMain

Emit a JSON array of helix points (a concrete visualization artifact for the “spiral”).

Options (all optional):
- `--n <Nat>` number of steps (default: 32)
- `--step <Float>` angular step (default: 0.35)
- `--pitch <Float>` z pitch per radian (default: 0.15)
- `--help`

This executable is intended to succeed on the happy path with no args.
-/

namespace ModalThesis.CLI.SpiralDumpMain

open ModalThesis.IteratedVirtual
open Lean

private def parseNatArg (argv : List String) (flag : String) : Option Nat :=
  match argv.dropWhile (fun s => s != flag) with
  | _ :: v :: _ => String.toNat? v
  | _ => none

private def parseFloat? (s : String) : Option Float :=
  match Json.parse s with
  | .ok (.num n) => some n.toFloat
  | .ok _ => none
  | .error _ => none

private def parseFloatArg (argv : List String) (flag : String) : Option Float :=
  match argv.dropWhile (fun s => s != flag) with
  | _ :: v :: _ => parseFloat? v
  | _ => none

private def usage : String :=
  String.intercalate "\n"
    [ "modal_thesis_spiral_dump"
    , ""
    , "Emits a JSON array of helix points."
    , ""
    , "Options:"
    , "  --n <Nat>       number of steps (default: 32)"
    , "  --step <Float>  angular step (default: 0.35)"
    , "  --pitch <Float> z pitch per radian (default: 0.15)"
    , "  --help"
    ]

def main (argv : List String) : IO UInt32 := do
  if argv.contains "--help" then
    IO.println usage
    return 0

  let n := (parseNatArg argv "--n").getD 32
  let step := (parseFloatArg argv "--step").getD 0.35
  let pitch := (parseFloatArg argv "--pitch").getD 0.15

  let pts := embedSteps n step pitch
  let out := Json.arr <| (pts.map Point3.toJson |>.toArray)
  IO.println (Json.pretty out)
  return 0

end ModalThesis.CLI.SpiralDumpMain

def main (argv : List String) : IO UInt32 :=
  ModalThesis.CLI.SpiralDumpMain.main argv
