
import Regex.Data

def Regex.denotes : Regex → List Int → Prop
  | .Emp, ns => ns = []
  | .Atom a, ns => ns = [a]
  | .Seq r1 r2, ns =>
    ∃ ns1 ns2, ns = ns1 ++ ns2 ∧ r1.denotes ns1 ∧ r2.denotes ns2
  | .Disj r1 r2, ns => r1.denotes ns ∨ r2.denotes ns
