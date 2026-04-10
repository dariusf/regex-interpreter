
import Regex.Data

def matches_prefix (r:Regex) (ns:List Int) : Option (List Int) :=
  match r with
  | .Emp => some ns
  | ~ a =>
    match ns with
    | b :: ns1 => if a = b then some ns1 else none
    | _ => none
  | r1 ;; r2 =>
    match matches_prefix r1 ns with
    | none => none
    | some rest => matches_prefix r2 rest
  | .Disj r1 r2 =>
    -- This commits (unsoundly) to the first intermediate match, so
    -- if there a failure later, we cannot retry the second branch from this point.
    -- The problem is that we don't have a way to either
    -- 1. return all possible remainders (List), or
    -- 2. have the computation after this point somehow feature in the none result (CPSOption)
    match matches_prefix r1 ns with
    | none => matches_prefix r2 ns
    | some r => some r

def regex_matches (r:Regex) (ns:List Int) : Bool :=
  match matches_prefix r ns with
  | some [] => true
  | _ => false

-- Disjunction appears to work...
example : regex_matches ((~1 ;; ~2) ∣ ~1) [1, 2] = true := by
  simp [regex_matches, matches_prefix]

-- ... but isn't commutative
example : regex_matches (~1 ∣ (~1 ;; ~2)) [1, 2] = false := rfl
