import ExactFDiv.RNE
open ExactFDiv

/-- the IEEE quotient of two binary64 values in the model, printed like `pairs_expected.txt` -/
def show1 (r : IEEE) : String :=
  match r with
  | .num v => s!"{v.num} {v.den}"
  | .zero s => if s then "zero -" else "zero +"
  | .inf s => if s then "inf -" else "inf +"
  | .nan => "nan"

#eval show IO Unit from do
  let s ← IO.FS.readFile "../src/difftest/pairs.txt"
  let mut out : Array String := #[]
  for l in s.splitOn "\n" do
    match (l.splitOn " ").filterMap (fun w => w.toInt?) with
    | [a, b, c, d] =>
      let x : ℚ := (a : ℚ) / (b : ℚ)
      let y : ℚ := (c : ℚ) / (d : ℚ)
      out := out.push (show1 (div (rneR 53 (-1074) 971) (IEEE.num x) (IEEE.num y)))
    | _ => pure ()
  IO.FS.writeFile "../src/difftest/pairs_lean.txt" (String.intercalate "\n" out.toList ++ "\n")
