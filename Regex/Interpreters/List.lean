
import Regex.Matcher

namespace List

open Regex

-- List monad
def matches_prefix (r:Regex) (ns:List Int) : List (List Int) :=
  match r with
  | Emp => [ns]
  | Atom a =>
    match ns with
    | b :: ns1 => if a = b then [ns1] else []
    | _ => []
  | .Seq r1 r2 => List.flatMap (matches_prefix r2) (matches_prefix r1 ns)
  | .Disj r1 r2 => matches_prefix r1 ns ++ matches_prefix r2 ns

def regex_matches (r:Regex) (ns:List Int) : Bool :=
  (matches_prefix r ns).any (·.isEmpty)

example : regex_matches ((~1) ∣ (~1 ;; ~2)) [1, 2] = true := rfl

theorem mem_matches_prefix (r : Regex) :
    ∀ (ns rest : List Int),
    rest ∈ matches_prefix r ns ↔ ∃ ns1, ns = ns1 ++ rest ∧ r.denotes ns1 := by
  induction r with
  | Emp =>
    intro ns rest
    simp only [matches_prefix, List.mem_singleton, denotes]
    constructor
    · rintro rfl; exact ⟨[], rfl, rfl⟩
    · rintro ⟨ns1, rfl, rfl⟩; rfl
  | Atom a =>
    intro ns rest
    cases ns with
    | nil =>
      simp only [matches_prefix, List.not_mem_nil, false_iff, denotes]
      rintro ⟨ns1, h, rfl⟩; simp at h
    | cons b ns1 =>
      simp only [matches_prefix]
      by_cases hab : a = b
      · subst hab
        simp only [if_true, List.mem_singleton, denotes]
        constructor
        · rintro rfl; exact ⟨[a], by simp, rfl⟩
        · rintro ⟨ns2, h, rfl⟩; simpa using h.symm
      · simp only [if_neg hab, List.not_mem_nil, false_iff, denotes]
        rintro ⟨ns2, h, rfl⟩
        simp at h
        exact hab h.1.symm
  | Seq r1 r2 ih1 ih2 =>
    intro ns rest
    simp only [matches_prefix, List.mem_flatMap]
    constructor
    · rintro ⟨mid, hmid, hrest⟩
      obtain ⟨a, hns, ha⟩ := (ih1 ns mid).mp hmid
      obtain ⟨b, hmid2, hb⟩ := (ih2 mid rest).mp hrest
      refine ⟨a ++ b, ?_, a, b, rfl, ha, hb⟩
      rw [hns, hmid2, List.append_assoc]
    · rintro ⟨ns1, hns, a, b, hab, ha, hb⟩
      refine ⟨b ++ rest, (ih1 ns (b ++ rest)).mpr ⟨a, ?_, ha⟩,
        (ih2 (b ++ rest) rest).mpr ⟨b, rfl, hb⟩⟩
      rw [hns, hab, List.append_assoc]
  | Disj r1 r2 ih1 ih2 =>
    intro ns rest
    simp only [matches_prefix, List.mem_append, denotes]
    rw [ih1 ns rest, ih2 ns rest]
    constructor
    · rintro (⟨ns1, h, hd⟩ | ⟨ns1, h, hd⟩)
      · exact ⟨ns1, h, Or.inl hd⟩
      · exact ⟨ns1, h, Or.inr hd⟩
    · rintro ⟨ns1, h, (hd | hd)⟩
      · exact Or.inl ⟨ns1, h, hd⟩
      · exact Or.inr ⟨ns1, h, hd⟩

instance : Matcher regex_matches where
  correct := by
    intro r ns
    simp only [regex_matches, List.any_eq_true]
    constructor
    · rintro ⟨x, hx, hempty⟩
      rw [List.isEmpty_iff] at hempty
      subst hempty
      obtain ⟨ns1, hns, hd⟩ := (mem_matches_prefix r ns []).mp hx
      simp at hns; subst hns; exact hd
    · intro hd
      exact ⟨[], (mem_matches_prefix r ns []).mpr ⟨ns, by simp, hd⟩, by simp⟩
