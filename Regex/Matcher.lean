
import Regex.Denotation
open Regex

class Matcher (M : Regex → List Int → Bool) where
  correct : ∀ r ns, M r ns = true ↔ r.denotes ns

namespace ExhaustiveMatcher

variable {M : Regex → List Int → Bool} [E : Matcher M]

theorem emp_iff (ns) : M .Emp ns = true ↔ ns = [] := by
  rw [E.correct]; simp [denotes]

theorem atom_iff (a ns) : M (~a) ns = true ↔ ns = [a] := by
  rw [E.correct]; simp [denotes]

theorem seq_assoc (r1 r2 r3 ns) :
    M (r1 ;; (r2 ;; r3)) ns = M ((r1 ;; r2) ;; r3) ns := by
  rw [Bool.eq_iff_iff, E.correct, E.correct]
  simp [denotes]
  constructor
  · rintro ⟨a, _, rfl, ha, b, c, rfl, hb, hc⟩
    exact ⟨_, c, by simp [List.append_assoc], ⟨a, b, rfl, ha, hb⟩, hc⟩
  · rintro ⟨_, c, rfl, ⟨a, b, rfl, ha, hb⟩, hc⟩
    exact ⟨a, _, by simp [List.append_assoc], ha, b, c, rfl, hb, hc⟩

theorem seq_emp_l (r ns) : M (.Emp ;; r) ns = M r ns := by
  rw [Bool.eq_iff_iff, E.correct, E.correct]
  simp [denotes]
  constructor
  · rintro ⟨_, ns2, rfl, rfl, h⟩; simpa using h
  · intro h; exact ⟨[], ns, rfl, rfl, h⟩

theorem seq_emp_r (r ns) : M (r ;; .Emp) ns = M r ns := by
  rw [Bool.eq_iff_iff, E.correct, E.correct]
  simp [denotes]

theorem disj_idem (r ns) : M (r ∣ r) ns = M r ns := by
  rw [Bool.eq_iff_iff, E.correct, E.correct]
  simp [denotes]

theorem disj_seq_distr (r r1 r2 ns) :
    M ((r1 ∣ r2) ;; r) ns = M ((r1 ;; r) ∣ (r2 ;; r)) ns := by
  rw [Bool.eq_iff_iff, E.correct, E.correct]
  simp [denotes]
  constructor
  · rintro ⟨a, b, hns, (h1 | h2), hr⟩
    · exact Or.inl ⟨a, b, hns, h1, hr⟩
    · exact Or.inr ⟨a, b, hns, h2, hr⟩
  · rintro (⟨a, b, hns, h1, hr⟩ | ⟨a, b, hns, h2, hr⟩)
    · exact ⟨a, b, hns, Or.inl h1, hr⟩
    · exact ⟨a, b, hns, Or.inr h2, hr⟩
