
import Regex.Matcher

namespace CPSOption

open Regex

/- This solves the problems of the naive interpreter with a representation of the continuation.

1. it is continuation-composing, as in the Disj case, we inspect the eventual result
2. k takes an option because in the Seq case, we need to handle the intermediate failure
3. k returns option because Disj has to tell if the computation failed
4. the return type is then forced to be option
5. Disj tries r1 with the full continuation. Only if entire computation after fails does it "retry" with r2. -/
def matches_prefix (r:Regex) (ns:List Int)
    (k: Option (List Int) → Option (List Int)) : Option (List Int) :=
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
    -- aka <|>
    match matches_prefix r1 ns k with
    | none => matches_prefix r2 ns k
    | some r => some r

def regex_matches (r:Regex) (ns:List Int) : Bool :=
  match matches_prefix r ns (fun | some [] => some [] | _ => none) with
  | some [] => true
  | _ => false

-- Disjunction is now commutative
example : regex_matches (~1 ∣ (~1 ;; ~2)) [1, 2] = true := rfl
example : regex_matches ((~1 ;; ~2) ∣ ~1) [1, 2] = true := rfl

theorem matches_prefix_some : ∀ (r : Regex) (ns : List Int)
    (k : Option (List Int) → Option (List Int))
    (_hk_none : k none = none)
    (rs : List Int),
    matches_prefix r ns k = some rs →
      ∃ ns1 ns2, ns = ns1 ++ ns2 ∧ r.denotes ns1 ∧ k (some ns2) = some rs := by
  intro r
  induction r with
  | Emp =>
    intro ns k _ rs h
    exact ⟨[], ns, rfl, rfl, h⟩
  | Atom a =>
    intro ns k hk_none rs h
    cases ns with
    | nil => simp [matches_prefix, hk_none] at h
    | cons b ns1 =>
      simp [matches_prefix] at h
      by_cases hab : a = b
      · subst hab
        simp at h
        exact ⟨[a], ns1, rfl, by simp [denotes], h⟩
      · simp [hab, hk_none] at h
  | Seq r1 r2 ih1 ih2 =>
    intro ns k hk_none rs h
    simp [matches_prefix] at h
    let k' : Option (List Int) → Option (List Int) :=
      fun | none => k none | some rest => matches_prefix r2 rest k
    have hk_none' : k' none = none := by simp [k', hk_none]
    obtain ⟨ns1, ns2, rfl, hd1, hk⟩ := ih1 ns k' hk_none' rs h
    simp [k'] at hk
    obtain ⟨ns3, ns4, rfl, hd2, hk⟩ := ih2 _ _ hk_none _ hk
    refine ⟨ns1 ++ ns3, ns4, by simp [List.append_assoc], ?_, hk⟩
    exact ⟨ns1, ns3, rfl, hd1, hd2⟩
  | Disj r1 r2 ih1 ih2 =>
    intro ns k hk_none rs h
    simp [matches_prefix] at h
    split at h
    · rename_i h1
      obtain ⟨ns1, ns2, rfl, hd, hk⟩ := ih2 _ _ hk_none _ h
      exact ⟨ns1, ns2, rfl, Or.inr hd, hk⟩
    · rename_i rs' h1
      obtain ⟨ns1, ns2, rfl, hd, hk⟩ := ih1 _ _ hk_none _ h1
      rw [h] at hk
      exact ⟨ns1, ns2, rfl, Or.inl hd, hk⟩

theorem matches_prefix_iff (r : Regex) : ∀ (ns : List Int)
    (k : Option (List Int) → Option (List Int))
    (_hk_none : k none = none)
    (_hk_clean : ∀ x rs, k x = some rs → rs = []),
    matches_prefix r ns k = some [] ↔
      ∃ ns1 ns2, ns = ns1 ++ ns2 ∧ r.denotes ns1 ∧ k (some ns2) = some [] := by
  intro ns k hk_none hk_clean
  constructor
  · intro h
    exact matches_prefix_some r ns k hk_none [] h
  · revert ns k hk_none hk_clean
    induction r with
    | Emp =>
      intro ns k hk_none hk_clean ⟨ns1, ns2, hns, hd, hk⟩
      simp [denotes] at hd; subst hd
      simp at hns; subst hns
      exact hk
    | Atom a =>
      intro ns k hk_none hk_clean ⟨ns1, ns2, hns, hd, hk⟩
      simp [denotes] at hd; subst hd
      simp at hns
      obtain ⟨rfl, rfl⟩ := hns
      simp [matches_prefix, hk]
    | Seq r1 r2 ih1 ih2 =>
      intro ns k hk_none hk_clean ⟨ns12, ns3, hns, ⟨ns1, ns2, hns12, hd1, hd2⟩, hk⟩
      subst hns12; subst hns
      simp [matches_prefix]
      let k' : Option (List Int) → Option (List Int) :=
        fun | none => k none | some rest => matches_prefix r2 rest k
      have hk_none' : k' none = none := by simp [k', hk_none]
      have hk_clean' : ∀ (x : Option (List Int)) (rs : List Int),
          k' x = some rs → rs = [] := by
        intro x rs h
        cases x with
        | none => simp [k', hk_none] at h
        | some rest =>
          simp [k'] at h
          obtain ⟨_, _, _, _, hk'⟩ := matches_prefix_some r2 rest k hk_none rs h
          exact hk_clean _ _ hk'
      refine ih1 _ k' hk_none' hk_clean' ?_
      refine ⟨ns1, ns2 ++ ns3, by simp, hd1, ?_⟩
      simp [k']
      refine ih2 _ _ hk_none hk_clean ?_
      exact ⟨ns2, ns3, rfl, hd2, hk⟩
    | Disj r1 r2 ih1 ih2 =>
      intro ns k hk_none hk_clean ⟨ns1, ns2, hns, hd, hk⟩
      subst hns
      simp [matches_prefix]
      cases hd with
      | inl hl =>
        have h1 := ih1 _ _ hk_none hk_clean ⟨ns1, ns2, rfl, hl, hk⟩
        rw [h1]
      | inr hr =>
        cases h1 : matches_prefix r1 (ns1 ++ ns2) k with
        | none =>
          refine ih2 _ _ hk_none hk_clean ?_
          exact ⟨ns1, ns2, rfl, hr, hk⟩
        | some rs =>
          obtain ⟨_, _, _, _, hk'⟩ :=
            matches_prefix_some r1 (ns1 ++ ns2) k hk_none rs h1
          have : rs = [] := hk_clean _ _ hk'
          rw [this]


instance : Matcher regex_matches where
  correct := by
    intro r ns
    let k : Option (List Int) → Option (List Int) := fun | some [] => some [] | _ => none
    have hk_def : k = fun | some [] => some [] | _ => none := rfl
    have hk_none : k none = none := rfl
    have hk_clean : ∀ x rs, k x = some rs → rs = [] := by
      intro x rs h
      match x, h with
      | some [], h => exact (Option.some.inj h).symm
    show (match matches_prefix r ns k with | some [] => true | _ => false) = true ↔ r.denotes ns
    constructor
    · intro h
      have hmp : matches_prefix r ns k = some [] := by
        cases hmp : matches_prefix r ns k with
        | none => rw [hmp] at h; simp at h
        | some v =>
          cases v with
          | nil => rfl
          | cons _ _ => rw [hmp] at h; simp at h
      obtain ⟨ns1, ns2, rfl, hd, hk⟩ :=
        (matches_prefix_iff r ns k hk_none hk_clean).mp hmp
      have hns2 : ns2 = [] := by
        match ns2, hk with
        | [], _ => rfl
        | _ :: _, hk => simp [hk_def] at hk
      subst hns2
      simpa using hd
    · intro hd
      have hmp : matches_prefix r ns k = some [] := by
        apply (matches_prefix_iff r ns k hk_none hk_clean).mpr
        exact ⟨ns, [], by simp, hd, rfl⟩
      rw [hmp]
