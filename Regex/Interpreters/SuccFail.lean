
import Regex.Matcher

-- Explicit success + failure continuations
namespace SuccFail

open Regex

def matches_prefix (r:Regex) (ns:List Int)
    (succ : List Int → (Unit → Option (List Int)) → Option (List Int))
    (fail : Unit → Option (List Int)) : Option (List Int) :=
  match r with
  | Emp => succ ns fail
  | Atom a =>
    match ns with
    | b :: ns1 => if a = b then succ ns1 fail else fail ()
    | _ => fail ()
  | .Seq r1 r2 =>
    matches_prefix r1 ns (fun rest f => matches_prefix r2 rest succ f) fail
  | .Disj r1 r2 =>
    matches_prefix r1 ns succ (fun _ => matches_prefix r2 ns succ fail)

def regex_matches (r:Regex) (ns:List Int) : Bool :=
  match matches_prefix r ns
      (fun rest f => match rest with | [] => some [] | _ => f ())
      (fun _ => none) with
  | some _ => true
  | _ => false

namespace succ_fail

open Regex

theorem matches_prefix_ne_none
    (r : Regex) (ns : List Int)
    (succ : List Int → (Unit → Option (List Int)) → Option (List Int))
    (fail : Unit → Option (List Int))
    (P : List Int → Prop)
    (hsucc : ∀ ns2 f, succ ns2 f ≠ none ↔ P ns2 ∨ f () ≠ none) :
    matches_prefix r ns succ fail ≠ none ↔
      (∃ ns1 ns2, ns = ns1 ++ ns2 ∧ r.denotes ns1 ∧ P ns2) ∨ fail () ≠ none := by
  revert ns succ fail P
  induction r with
  | Emp =>
    intro ns succ fail P hsucc
    show succ ns fail ≠ none ↔ _
    rw [hsucc]
    constructor
    · rintro (hP | hf)
      · exact Or.inl ⟨[], ns, by simp, by simp [Regex.denotes], hP⟩
      · exact Or.inr hf
    · rintro (⟨ns1, ns2, hns, hd, hP⟩ | hf)
      · simp [Regex.denotes] at hd
        subst hd
        simp at hns
        subst hns
        exact Or.inl hP
      · exact Or.inr hf
  | Atom a =>
    intro ns succ fail P hsucc
    cases ns with
    | nil =>
      show fail () ≠ none ↔ _
      constructor
      · intro hf; exact Or.inr hf
      · rintro (⟨ns1, ns2, hns, hd, _⟩ | hf)
        · simp [Regex.denotes] at hd; subst hd; simp at hns
        · exact hf
    | cons b ns1 =>
      by_cases hab : a = b
      · subst hab
        show (if a = a then succ ns1 fail else fail ()) ≠ none ↔ _
        rw [if_pos rfl, hsucc]
        constructor
        · rintro (hP | hf)
          · exact Or.inl ⟨[a], ns1, rfl, by simp [Regex.denotes], hP⟩
          · exact Or.inr hf
        · rintro (⟨ns1', ns2, hns, hd, hP⟩ | hf)
          · simp [Regex.denotes] at hd
            subst hd
            simp at hns
            obtain ⟨_, rfl⟩ := hns
            exact Or.inl hP
          · exact Or.inr hf
      · show (if a = b then succ ns1 fail else fail ()) ≠ none ↔ _
        rw [if_neg hab]
        constructor
        · intro hf; exact Or.inr hf
        · rintro (⟨ns1', ns2, hns, hd, _⟩ | hf)
          · simp [Regex.denotes] at hd
            subst hd
            simp at hns
            obtain ⟨rfl, _⟩ := hns
            exact absurd rfl hab
          · exact hf
  | Seq r1 r2 ih1 ih2 =>
    intro ns succ fail P hsucc
    simp only [matches_prefix]
    let succ' : List Int → (Unit → Option (List Int)) → Option (List Int) :=
      fun rest f => matches_prefix r2 rest succ f
    let P' : List Int → Prop :=
      fun rest => ∃ ns1 ns2, rest = ns1 ++ ns2 ∧ r2.denotes ns1 ∧ P ns2
    have hsucc' : ∀ rest f, succ' rest f ≠ none ↔ P' rest ∨ f () ≠ none := by
      intro rest f
      show matches_prefix r2 rest succ f ≠ none ↔ _
      exact ih2 rest succ f P hsucc
    have h1 := ih1 ns succ' fail P' hsucc'
    show matches_prefix r1 ns succ' fail ≠ none ↔ _
    rw [h1]
    constructor
    · rintro (⟨ns1, rest, hns, hd1, ns2, ns3, hrest, hd2, hP⟩ | hf)
      · subst hns; subst hrest
        refine Or.inl ⟨ns1 ++ ns2, ns3, by simp [List.append_assoc], ?_, hP⟩
        exact ⟨ns1, ns2, rfl, hd1, hd2⟩
      · exact Or.inr hf
    · rintro (⟨ns12, ns3, hns, ⟨ns1, ns2, hns12, hd1, hd2⟩, hP⟩ | hf)
      · subst hns; subst hns12
        refine Or.inl ⟨ns1, ns2 ++ ns3, by simp [List.append_assoc], hd1, ?_⟩
        exact ⟨ns2, ns3, rfl, hd2, hP⟩
      · exact Or.inr hf
  | Disj r1 r2 ih1 ih2 =>
    intro ns succ fail P hsucc
    simp only [matches_prefix]
    let fail' : Unit → Option (List Int) := fun _ => matches_prefix r2 ns succ fail
    have h1 := ih1 ns succ fail' P hsucc
    show matches_prefix r1 ns succ fail' ≠ none ↔ _
    rw [h1]
    have h2 := ih2 ns succ fail P hsucc
    have hfail' : fail' () ≠ none ↔
        (∃ ns1 ns2, ns = ns1 ++ ns2 ∧ r2.denotes ns1 ∧ P ns2) ∨ fail () ≠ none := by
      show matches_prefix r2 ns succ fail ≠ none ↔ _
      exact h2
    rw [hfail']
    constructor
    · rintro (⟨ns1, ns2, hns, hd, hP⟩ | ⟨ns1, ns2, hns, hd, hP⟩ | hf)
      · exact Or.inl ⟨ns1, ns2, hns, Or.inl hd, hP⟩
      · exact Or.inl ⟨ns1, ns2, hns, Or.inr hd, hP⟩
      · exact Or.inr hf
    · rintro (⟨ns1, ns2, hns, (hd | hd), hP⟩ | hf)
      · exact Or.inl ⟨ns1, ns2, hns, hd, hP⟩
      · exact Or.inr (Or.inl ⟨ns1, ns2, hns, hd, hP⟩)
      · exact Or.inr (Or.inr hf)

instance : Matcher regex_matches where
  correct := by
    intro r ns
    let succ_top : List Int → (Unit → Option (List Int)) → Option (List Int) :=
      fun rest f => match rest with | [] => some [] | _ => f ()
    let fail_top : Unit → Option (List Int) := fun _ => none
    let P_top : List Int → Prop := fun ns2 => ns2 = []
    have hsucc : ∀ ns2 f, succ_top ns2 f ≠ none ↔ P_top ns2 ∨ f () ≠ none := by
      intro ns2 f
      cases ns2 with
      | nil => simp [succ_top, P_top]
      | cons h t => simp [succ_top, P_top]
    have hmain :=
      succ_fail.matches_prefix_ne_none r ns succ_top fail_top P_top hsucc
    show (match matches_prefix r ns succ_top fail_top with
            | some _ => true | _ => false) = true ↔ r.denotes ns
    have hbool : (match matches_prefix r ns succ_top fail_top with
                    | some _ => true | _ => false) = true ↔
                 matches_prefix r ns succ_top fail_top ≠ none := by
      cases h : matches_prefix r ns succ_top fail_top with
      | none => simp
      | some _ => simp
    rw [hbool, hmain]
    constructor
    · rintro (⟨ns1, ns2, hns, hd, hP⟩ | hf)
      · have : ns2 = [] := hP
        subst this
        simp at hns
        subst hns
        exact hd
      · exact absurd rfl hf
    · intro hd
      exact Or.inl ⟨ns, [], by simp, hd, rfl⟩
