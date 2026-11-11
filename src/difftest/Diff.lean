import ExactFDiv.Checker
open ExactFDiv

/-- read one integer per line -/
def readYs (path : System.FilePath) : IO (List ℤ) := do
  let s ← IO.FS.readFile path
  return (s.splitOn "\n").filterMap (fun l => l.trim.toInt?)

/-- prints the verdicts of the verified check `accept` as a 0/1 string (1 = accepted) -/
#eval show IO Unit from do
  let y64 ← readYs "../src/difftest/ys64.txt"
  IO.println (String.mk (y64.map (fun y => if accept 53 y then '1' else '0')))
  let y32 ← readYs "../src/difftest/ys32.txt"
  IO.println (String.mk (y32.map (fun y => if accept 24 y then '1' else '0')))
