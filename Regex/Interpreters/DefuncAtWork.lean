
import Regex.Matcher

-- Higher-order, continuation-based matcher from
-- Danvy & Nielsen, "Defunctionalization at Work", Figure 1.
namespace DefuncAtWork

open Regex

def matches_prefix (r:Regex) (s:List Int) (k:List Int → Bool) : Bool :=
  match r with
  | Emp => k s
  | Atom c =>
    match s with
    | c' :: s' => (c = c') && k s'
    | [] => false
  | .Seq r1 r2 => matches_prefix r1 s (fun s' => matches_prefix r2 s' k)
  | .Disj r1 r2 => matches_prefix r1 s k || matches_prefix r2 s k

def regex_matches (r:Regex) (s:List Int) : Bool :=
  matches_prefix r s (fun s1 => s1.isEmpty)

theorem matches_prefix_iff (r : Regex) :
    ∀ (s : List Int) (k : List Int → Bool),
    matches_prefix r s k = true ↔
      ∃ s1 s2, s = s1 ++ s2 ∧ r.denotes s1 ∧ k s2 = true := by
  induction r with
  | Emp =>
    intro s k
    constructor
    · intro h
      refine ⟨[], s, rfl, ?_, h⟩
      simp [denotes]
    · rintro ⟨s1, s2, hs, hd, hk⟩
      simp [denotes] at hd; subst hd
      simp at hs; subst hs
      exact hk
  | Atom a =>
    intro s k
    constructor
    · intro h
      cases s with
      | nil => simp [matches_prefix] at h
      | cons b s' =>
        simp [matches_prefix] at h
        obtain ⟨hab, hk⟩ := h
        subst hab
        refine ⟨[a], s', rfl, ?_, hk⟩
        simp [denotes]
    · rintro ⟨s1, s2, hs, hd, hk⟩
      simp [denotes] at hd
      subst hd
      simp at hs
      obtain ⟨rfl, rfl⟩ := hs
      simp [matches_prefix, hk]
  | Seq r1 r2 ih1 ih2 =>
    intro s k
    simp only [matches_prefix]
    rw [ih1]
    constructor
    · rintro ⟨s1, s2, rfl, hd1, h2⟩
      rw [ih2] at h2
      obtain ⟨s3, s4, rfl, hd2, hk⟩ := h2
      refine ⟨s1 ++ s3, s4, by simp, ?_, hk⟩
      exact ⟨s1, s3, rfl, hd1, hd2⟩
    · rintro ⟨s12, s3, hs, ⟨s1, s2, rfl, hd1, hd2⟩, hk⟩
      refine ⟨s1, s2 ++ s3, by simp [hs, List.append_assoc], hd1, ?_⟩
      rw [ih2]
      exact ⟨s2, s3, rfl, hd2, hk⟩
  | Disj r1 r2 ih1 ih2 =>
    intro s k
    simp only [matches_prefix, Bool.or_eq_true]
    rw [ih1, ih2]
    constructor
    · rintro (⟨s1, s2, rfl, hd, hk⟩ | ⟨s1, s2, rfl, hd, hk⟩)
      · exact ⟨s1, s2, rfl, Or.inl hd, hk⟩
      · exact ⟨s1, s2, rfl, Or.inr hd, hk⟩
    · rintro ⟨s1, s2, rfl, hd | hd, hk⟩
      · exact Or.inl ⟨s1, s2, rfl, hd, hk⟩
      · exact Or.inr ⟨s1, s2, rfl, hd, hk⟩

instance : Matcher regex_matches where
  correct := by
    intro r ns
    simp [regex_matches]
    rw [matches_prefix_iff]
    constructor
    · rintro ⟨s1, s2, rfl, hd, hk⟩
      rw [List.isEmpty_iff] at hk
      subst hk
      simp
      assumption
    · intro hd
      exact ⟨ns, [], by simp, hd, rfl⟩
