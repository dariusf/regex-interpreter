
inductive Regex where
  | Emp
  | Atom (a:Int)
  | Seq (a b:Regex)
  | Disj (a b:Regex)

namespace simple

-- #check DecidableEq Int
-- #check DecidableEq (List Int)
-- #print DecidableEq (List Int)

def matches_prefix (r:Regex) (ns:List Int) : Option (List Int) :=
  match r with
  | .Emp => some ns
  | .Atom a =>
    match ns with
    | b :: ns1 => if a = b then some ns1 else none
    | _ => none
  | .Seq r1 r2 =>
    match matches_prefix r1 ns with
    | none => none
    | some rest => matches_prefix r2 rest
  | .Disj _ _ => none

-- decidable eq is used
-- set_option pp.all true
-- #print matches_prefix

def regex_matches (r:Regex) (ns:List Int) : Bool :=
  match matches_prefix r ns with
  | some [] => true
  | _ => false

theorem emp_empty:
  regex_matches .Emp [] = true
:= by
  -- dsimp [regex_matches, matches_prefix]
  rfl

theorem emp_nonempty (ns:List Int):
  ns ≠ [] →
  regex_matches .Emp ns = false
:= by
  intro H
  simp [regex_matches, matches_prefix]
  cases ns with
  | nil =>
    -- have: False := Ne.irrefl H
    contradiction
  | cons h t => dsimp

theorem matches_prefix_assoc (r1 r2 r3:Regex) (ns:List Int) :
  matches_prefix (.Seq r1 (.Seq r2 r3)) ns =
  matches_prefix (.Seq (.Seq r1 r2) r3) ns
:= by
  simp [matches_prefix]
  cases _ : matches_prefix r1 ns
  case some => simp
  case none => simp

open Regex

theorem seq_assoc (r1 r2 r3:Regex) (ns:List Int):
  regex_matches (Seq r1 (Seq r2 r3)) ns =
  regex_matches (Seq (Seq r1 r2) r3) ns
:= by
  simp [regex_matches, matches_prefix_assoc]

theorem seq_emp_l (r:Regex) (ns:List Int):
  regex_matches (Seq Emp r) ns =
  regex_matches r ns
:= by
  simp [regex_matches, matches_prefix]

theorem seq_emp_r (r:Regex) (ns:List Int):
  regex_matches (Seq r Emp) ns =
  regex_matches r ns
:= by
  simp [regex_matches, matches_prefix]
  cases matches_prefix r ns
  case none => dsimp
  case some ns1 => dsimp

-- the result of matches_prefix will always be a suffix of the input
theorem matches_prefix_correct (r:Regex) (ns rest:List Int) :
  matches_prefix r ns = some rest →
  ∃ ns1, ns = ns1 ++ rest
:= by
  revert ns rest
  induction r <;> intros ns rest
  case Emp =>
    intros H
    injection H with H
    -- the prefix will be empty
    exists []
  case Atom a =>
    cases ns
    -- the list cannot be empty
    case nil => dsimp [matches_prefix]; intros; contradiction
    case cons hd tl =>
      dsimp [matches_prefix]
      by_cases a = hd
      case neg Hneq =>
        -- the head has to match
        simp [Hneq]
      case pos Heq =>
        simp [Heq]
        intros H
        exists [hd]
        simp [H]
  case Seq r1 r2 IH1 IH2 =>
    dsimp [matches_prefix]
    cases Hr1 : matches_prefix r1 ns
    { dsimp; intros; contradiction }
    case some ns2 =>
      -- ns2 is what remains after matching r1
      dsimp
      intros H1
      specialize (IH2 _ _ H1)
      -- ns3 is what got matched by r2
      let ⟨ns3, IH2⟩ := IH2
      -- specialize (IH1 _ _ Hr1);
      let ⟨ns1, IH1⟩ := IH1 _ _ Hr1
      exists ns1 ++ ns3
      simp [IH2, IH1]

  case Disj r1 r2 IH1 IH2 =>
    dsimp [matches_prefix]
    intros
    contradiction

theorem matches_prefix_atom_spec (a:Int) (ns rest:List Int) :
  matches_prefix (Atom a) ns = some rest →
  ns = a :: rest
:= by
  dsimp [matches_prefix]
  cases ns
  case nil => dsimp; intros; contradiction
  case cons h t =>
    dsimp
    by_cases a = h
    case pos Heq => simp [Heq]
    case neg Hneq => simp [Hneq]

theorem regex_matches_correct (r:Regex) (ns:List Int) :
  regex_matches r ns = true →
  matches_prefix r ns = some []
:= by
  simp [regex_matches]
  cases matches_prefix r ns
  case none => simp
  case some ns1 =>
    cases ns1
    case nil => simp
    case cons => simp

end simple

namespace cps

open Regex

def matches_prefix (r:Regex) (ns:List Int) (k: Option (List Int) → Option (List Int)) : Option (List Int) :=
  match r with
  | Emp => k (some ns)
  | Atom a =>
    match ns with
    | b :: ns1 => if a = b then k (some ns1) else k none
    | _ => k none
  | .Seq r1 r2 =>
    matches_prefix r1 ns (fun
      | none => k none
      | some rest => matches_prefix r2 rest k)
  | .Disj r1 r2 =>
    match matches_prefix r1 ns k with
    | none => matches_prefix r2 ns k
    | some r => r

def regex_matches (r:Regex) (ns:List Int) : Bool :=
  match matches_prefix r ns (fun x => x) with
  | some [] => true
  | _ => false

def Disj_free : Regex → Bool
  | .Emp => true
  | .Atom _ => true
  | .Seq r1 r2 => Disj_free r1 && Disj_free r2
  | .Disj _ _ => false

theorem Disj_free_Seq_inv (r1 r2:Regex):
  Disj_free (.Seq r1 r2) →
  Disj_free r1 ∧ Disj_free r2
:= by
  intro h
  -- split
  -- exact?
  exact Bool.and_eq_true_iff.mp h

theorem matches_prefix_cps_eqiuv (r:Regex) (ns:List Int)
    (k:Option (List Int) → Option (List Int)) :
  Disj_free r →
  k (simple.matches_prefix r ns) = matches_prefix r ns k
:= by
  intro Hnd
  revert ns k
  induction r <;> intros ns k
  case Emp =>
    -- unfold simple.matches_prefix
    -- unfold matches_prefix
    -- dsimp [simple.matches_prefix, matches_prefix]
    rfl
  case Atom a =>
    dsimp [simple.matches_prefix, matches_prefix]
    cases ns
    case nil => rfl
    case cons h t =>
      by_cases a = h
      case pos Heq =>
        rw [Heq]
        dsimp
        -- apply?
        apply apply_ite
      case neg Hneq =>
        dsimp
        -- apply?
        apply apply_ite
  case Seq r1 r2 IH1 IH2 =>
    dsimp [simple.matches_prefix, matches_prefix]
    have h1: Disj_free r1 := by
      simp [Disj_free] at Hnd
      let ⟨ _, _ ⟩ := Hnd
      assumption

    have h2: Disj_free r2 := by
      simp [Disj_free] at Hnd
      let ⟨ _, _ ⟩ := Hnd
      assumption

    rw [← IH1 h1]

    cases simple.matches_prefix r1 ns
    case none => dsimp
    case some ns1 =>
      dsimp
      rw [← IH2 h2]

  case Disj r1 r2 IH1 IH2 =>
    simp [Disj_free] at Hnd


theorem disj_idem (r:Regex) (ns:List Int) (k:Option (List Int) → Option (List Int)):
  matches_prefix (Disj r r) ns k = matches_prefix r ns k
:= by
  simp [matches_prefix]
  cases (matches_prefix r ns k) <;> rfl

-- disj is not comm, as we commit to returning the first result
theorem disj_comm (r1 r2:Regex) (ns:List Int) (k:Option (List Int) → Option (List Int)):
  matches_prefix (Disj r1 r2) ns k = matches_prefix (Disj r2 r1) ns k
:= by
  simp [matches_prefix]
  cases (matches_prefix r1 ns k)
  case none =>
    cases (matches_prefix r2 ns k) <;> simp
  case some a =>
    cases (matches_prefix r2 ns k)
    case none => simp
    case some b =>
      simp
      -- counterexample: Disj 1 11, input 11
      sorry

theorem disj_emp_l (r:Regex) (ns:List Int):
  regex_matches (Disj Emp r) ns = regex_matches Emp ns
:= by
  simp [regex_matches, matches_prefix]

theorem disj_seq_distr (r r1 r2:Regex) (ns:List Int):
  regex_matches (Seq (Disj r1 r2) r) ns = regex_matches (Disj (Seq r1 r) (Seq r2 r)) ns
:= by
  simp [regex_matches, matches_prefix]

-- theorem matches_prefix_det (r:Regex) (ns:List Int)
--     (k:Option (List Int) → Option (List Int)) :
--   k (simple.matches_prefix r ns) = matches_prefix r ns k

-- det
-- matches_prefix r ns = some x
-- matches_prefix r ns = some y
-- → x = y

-- prefix closure of failure. if shorter string fails to match, longer string fails

end cps

namespace list

open Regex

def matches_prefix (r:Regex) (ns:List Int) : List (List Int) :=
  match r with
  | Emp => [ns]
  | Atom a =>
    match ns with
    | b :: ns1 => if a = b then [ns1] else []
    | _ => []
  | .Seq r1 r2 =>
    List.flatMap
      (fun
        | [] => []
        | rest => matches_prefix r2 rest)
      (matches_prefix r1 ns)
  | .Disj r1 r2 =>
    List.append
      (matches_prefix r1 ns)
      (matches_prefix r2 ns)

def regex_matches (r:Regex) (ns:List Int) : Bool :=
  match matches_prefix r ns with
  | [] :: _ => true
  | _ => false

theorem matches_prefix_cps_eqiuv (r:Regex) (ns:List Int)
    (k:Option (List Int) → Option (List Int)) :
  List.head? (matches_prefix r ns) =
  cps.matches_prefix r ns (fun x => x)
:= by
  revert ns k
  induction r <;> intros ns k
  case Emp => rfl
  case Atom a =>
    dsimp [simple.matches_prefix, matches_prefix]
    cases ns
    case nil => rfl
    case cons h t =>
      by_cases a = h
      case pos Heq =>
        rw [Heq]
        dsimp
        apply apply_ite
      case neg Hneq =>
        dsimp
        apply apply_ite
  case Seq r1 r2 IH1 IH2 =>
    dsimp [simple.matches_prefix, matches_prefix]
    -- need a more general statement which gives the relation between k and the list
    sorry

  case Disj r1 r2 IH1 IH2 =>
    sorry

end list
