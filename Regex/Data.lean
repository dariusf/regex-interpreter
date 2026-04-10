
inductive Regex where
  | Emp
  | Atom (a:Int)
  | Seq (a b:Regex)
  | Disj (a b:Regex)

prefix:max "~" => Regex.Atom
infixl:65 " ;; " => Regex.Seq
infixl:60 " ∣ " => Regex.Disj
