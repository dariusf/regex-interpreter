
import Regex.Matcher

/- Defunctionalized form of CPSOption. The closure
  fun | none => k none | some rest => matches_prefix r2 rest k
becomes the data constructor `SeqK r2 k`. Since every continuation
here propagates `none` unchanged, we drop the `none` case entirely
and have apply/denoteCont only handle the success path; failure is just `none`
returned directly by the matcher. -/

namespace Defunc

open Regex

inductive Cont where
  | Id
  | SeqK : Regex → Cont → Cont

def Regex.cCount : Regex → Nat
  | .Emp => 1
  | .Atom _ => 1
  | .Seq a b => 1 + cCount a + cCount b
  | .Disj a b => 1 + cCount a + cCount b

def Cont.cCount : Cont → Nat
  | .Id => 0
  | .SeqK r k => Regex.cCount r + Cont.cCount k

def matches_prefix : Regex → List Int → Cont → Option (List Int)
  | .Emp, [], .Id => some []
  | .Emp, _ :: _, .Id => none
  | .Emp, ns, .SeqK r2 k => matches_prefix r2 ns k
  | .Atom _, [], _ => none
  | .Atom a, b :: [], .Id => if a = b then some [] else none
  | .Atom _, _ :: _ :: _, .Id => none
  | .Atom a, b :: ns1, .SeqK r2 k => if a = b then matches_prefix r2 ns1 k else none
  | .Seq r1 r2, ns, k => matches_prefix r1 ns (.SeqK r2 k)
  | .Disj r1 r2, ns, k =>
    match matches_prefix r1 ns k with
    | none => matches_prefix r2 ns k
    | some r => some r
termination_by r _ k => Regex.cCount r + Cont.cCount k
decreasing_by all_goals simp_wf <;> simp [Regex.cCount, Cont.cCount] <;> omega

def regex_matches (r:Regex) (ns:List Int) : Bool :=
  match matches_prefix r ns .Id with
  | some [] => true
  | _ => false

def denoteCont : Cont → List Int → Prop
  | .Id, ns => ns = []
  | .SeqK r2 k, ns => ∃ ns1 ns2, ns = ns1 ++ ns2 ∧ r2.denotes ns1 ∧ denoteCont k ns2

-- The defunctionalized matcher only ever returns `some []` or `none`.
theorem matches_prefix_result_aux :
    ∀ (n : Nat) (r : Regex) (ns : List Int) (k : Cont) (rs : List Int),
      Regex.cCount r + Cont.cCount k = n →
      matches_prefix r ns k = some rs → rs = [] := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro r ns k rs hn h
    match r, ns, k with
    | .Emp, [], .Id =>
      rw [matches_prefix] at h
      exact (Option.some.inj h).symm
    | .Emp, _ :: _, .Id => rw [matches_prefix] at h; cases h
    | .Emp, ns, .SeqK r2 k' =>
      have hlt : Regex.cCount r2 + Cont.cCount k' < n := by
        subst hn; simp only [Regex.cCount, Cont.cCount]; omega
      rw [matches_prefix] at h
      exact ih _ hlt r2 ns k' rs rfl h
    | .Atom _, [], _ => rw [matches_prefix] at h; cases h
    | .Atom a, [b], .Id =>
      rw [matches_prefix] at h
      by_cases hab : a = b
      · simp [hab] at h; exact h
      · simp [hab] at h
    | .Atom _, _ :: _ :: _, .Id => rw [matches_prefix] at h; cases h
    | .Atom a, b :: ns1, .SeqK r2 k' =>
      have hlt : Regex.cCount r2 + Cont.cCount k' < n := by
        subst hn; simp only [Regex.cCount, Cont.cCount]; omega
      rw [matches_prefix] at h
      by_cases hab : a = b
      · simp [hab] at h; exact ih _ hlt r2 ns1 k' rs rfl h
      · simp [hab] at h
    | .Seq r1 r2, ns, k =>
      have hlt : Regex.cCount r1 + Cont.cCount (.SeqK r2 k) < n := by
        subst hn; simp only [Regex.cCount, Cont.cCount]; omega
      rw [matches_prefix] at h
      exact ih _ hlt r1 ns (.SeqK r2 k) rs rfl h
    | .Disj r1 r2, ns, k =>
      have hlt1 : Regex.cCount r1 + Cont.cCount k < n := by
        subst hn; simp only [Regex.cCount]; omega
      have hlt2 : Regex.cCount r2 + Cont.cCount k < n := by
        subst hn; simp only [Regex.cCount]; omega
      rw [matches_prefix] at h
      split at h
      · exact ih _ hlt2 r2 ns k rs rfl h
      · rename_i rs' h1
        obtain rfl := Option.some.inj h
        exact ih _ hlt1 r1 ns k rs' rfl h1

theorem matches_prefix_result (r : Regex) (ns : List Int) (k : Cont) (rs : List Int)
    (h : matches_prefix r ns k = some rs) : rs = [] :=
  matches_prefix_result_aux _ r ns k rs rfl h

theorem matches_prefix_iff_aux :
    ∀ (n : Nat) (r : Regex) (ns : List Int) (k : Cont),
      Regex.cCount r + Cont.cCount k = n →
      (matches_prefix r ns k = some [] ↔
        ∃ ns1 ns2, ns = ns1 ++ ns2 ∧ r.denotes ns1 ∧ denoteCont k ns2) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro r ns k hn
    match r, k with
    | .Emp, .Id =>
      constructor
      · intro h
        cases ns with
        | nil => exact ⟨[], [], rfl, by simp [denotes], by simp [denoteCont]⟩
        | cons _ _ => rw [matches_prefix] at h; cases h
      · rintro ⟨ns1, ns2, hns, hd, hk⟩
        have hd' : ns1 = [] := hd
        subst hd'
        have hk' : ns2 = [] := hk
        subst hk'
        simp at hns; subst hns
        rw [matches_prefix]
    | .Emp, .SeqK r2 k' =>
      have hlt : Regex.cCount r2 + Cont.cCount k' < n := by
        subst hn; simp only [Regex.cCount, Cont.cCount]; omega
      have ih2 := ih _ hlt r2 ns k' rfl
      simp only [matches_prefix]
      rw [ih2]
      constructor
      · rintro ⟨ns1, ns2, rfl, hd, hk⟩
        refine ⟨[], ns1 ++ ns2, by simp, rfl, ?_⟩
        simp [denoteCont]
        exact ⟨ns1, ns2, rfl, hd, hk⟩
      · rintro ⟨ns1, ns2, hns, hd, hk⟩
        simp [denotes] at hd; subst hd
        simp at hns; subst hns
        simp [denoteCont] at hk
        exact hk
    | .Atom a, .Id =>
      match ns with
      | [] =>
        simp only [matches_prefix]
        constructor
        · intro h; simp at h
        · rintro ⟨ns1, ns2, hns, hd, hk⟩
          simp [denotes] at hd; subst hd
          simp at hns
      | [b] =>
        simp only [matches_prefix]
        by_cases hab : a = b
        · subst hab; simp
          refine ⟨[a], [], by simp, by simp [denotes], by simp [denoteCont]⟩
        · constructor
          · intro h; simp [hab] at h
          · rintro ⟨ns1, ns2, hns, hd, hk⟩
            have hd' : ns1 = [a] := hd
            subst hd'
            have hk' : ns2 = [] := hk
            subst hk'
            simp at hns
            exact absurd hns.symm hab
      | b :: c :: rest =>
        simp only [matches_prefix]
        constructor
        · intro h; simp at h
        · rintro ⟨ns1, ns2, hns, hd, hk⟩
          simp [denotes] at hd; subst hd
          simp [denoteCont] at hk; subst hk
          simp at hns
    | .Atom a, .SeqK r2 k' =>
      have hlt : Regex.cCount r2 + Cont.cCount k' < n := by
        subst hn; simp only [Regex.cCount, Cont.cCount]; omega
      match ns with
      | [] =>
        simp only [matches_prefix]
        constructor
        · intro h; simp at h
        · rintro ⟨ns1, ns2, hns, hd, _⟩
          simp [denotes] at hd; subst hd
          simp at hns
      | b :: ns1 =>
        simp only [matches_prefix]
        by_cases hab : a = b
        · subst hab
          simp
          have ih2 := ih _ hlt r2 ns1 k' rfl
          rw [ih2]
          constructor
          · rintro ⟨ms1, ms2, rfl, hd, hk⟩
            refine ⟨[a], ms1 ++ ms2, by simp, by simp [denotes], ?_⟩
            simp [denoteCont]
            exact ⟨ms1, ms2, rfl, hd, hk⟩
          · rintro ⟨ms1, ms2, hns, hd, hk⟩
            simp [denotes] at hd; subst hd
            simp at hns
            obtain ⟨_, rfl⟩ := hns
            simp [denoteCont] at hk
            exact hk
        · constructor
          · intro h; simp [hab] at h
          · rintro ⟨ms1, ms2, hns, hd, _⟩
            have hd' : ms1 = [a] := hd
            subst hd'
            simp at hns
            exact absurd hns.1.symm hab
    | .Seq r1 r2, k =>
      have hlt : Regex.cCount r1 + Cont.cCount (.SeqK r2 k) < n := by
        subst hn; simp only [Regex.cCount, Cont.cCount]; omega
      have ih1 := ih _ hlt r1 ns (.SeqK r2 k) rfl
      simp only [matches_prefix]
      rw [ih1]
      constructor
      · rintro ⟨ns1, ns2, rfl, hd1, hk⟩
        simp [denoteCont] at hk
        obtain ⟨ms1, ms2, rfl, hd2, hk⟩ := hk
        refine ⟨ns1 ++ ms1, ms2, by simp [List.append_assoc], ?_, hk⟩
        exact ⟨ns1, ms1, rfl, hd1, hd2⟩
      · rintro ⟨ns12, ns3, hns, ⟨ns1, ns2, hns12, hd1, hd2⟩, hk⟩
        subst hns12; subst hns
        refine ⟨ns1, ns2 ++ ns3, by simp, hd1, ?_⟩
        simp [denoteCont]
        exact ⟨ns2, ns3, rfl, hd2, hk⟩
    | .Disj r1 r2, k =>
      have hlt1 : Regex.cCount r1 + Cont.cCount k < n := by
        subst hn; simp only [Regex.cCount]; omega
      have hlt2 : Regex.cCount r2 + Cont.cCount k < n := by
        subst hn; simp only [Regex.cCount]; omega
      have ih1 := ih _ hlt1 r1 ns k rfl
      have ih2 := ih _ hlt2 r2 ns k rfl
      simp only [matches_prefix]
      constructor
      · intro h
        split at h
        · rw [ih2] at h
          obtain ⟨ns1, ns2, rfl, hd, hk⟩ := h
          exact ⟨ns1, ns2, rfl, Or.inr hd, hk⟩
        · rename_i rs h1
          obtain rfl := Option.some.inj h
          rw [ih1] at h1
          obtain ⟨ns1, ns2, rfl, hd, hk⟩ := h1
          exact ⟨ns1, ns2, rfl, Or.inl hd, hk⟩
      · rintro ⟨ns1, ns2, rfl, hd, hk⟩
        cases hd with
        | inl hl =>
          have := ih1.mpr ⟨ns1, ns2, rfl, hl, hk⟩
          rw [this]
        | inr hr =>
          have := ih2.mpr ⟨ns1, ns2, rfl, hr, hk⟩
          cases h1 : matches_prefix r1 (ns1 ++ ns2) k with
          | none => exact this
          | some rs =>
            have hrs : rs = [] := matches_prefix_result r1 (ns1 ++ ns2) k rs h1
            subst hrs; rfl

theorem matches_prefix_iff (r : Regex) (ns : List Int) (k : Cont) :
    matches_prefix r ns k = some [] ↔
      ∃ ns1 ns2, ns = ns1 ++ ns2 ∧ r.denotes ns1 ∧ denoteCont k ns2 :=
  matches_prefix_iff_aux _ r ns k rfl

instance : Matcher regex_matches where
  correct := by
    intro r ns
    show (match matches_prefix r ns .Id with | some [] => true | _ => false) = true ↔ r.denotes ns
    constructor
    · intro h
      have hmp : matches_prefix r ns .Id = some [] := by
        cases hmp : matches_prefix r ns .Id with
        | none => rw [hmp] at h; simp at h
        | some v =>
          have : v = [] := matches_prefix_result r ns .Id v hmp
          subst this; rfl
      obtain ⟨ns1, ns2, rfl, hd, hk⟩ := (matches_prefix_iff r ns .Id).mp hmp
      simp [denoteCont] at hk
      subst hk
      simpa using hd
    · intro hd
      have hmp : matches_prefix r ns .Id = some [] := by
        apply (matches_prefix_iff r ns .Id).mpr
        exact ⟨ns, [], by simp, hd, rfl⟩
      rw [hmp]
