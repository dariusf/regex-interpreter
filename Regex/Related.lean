
import Regex.Interpreters.CPSOption
import Regex.Interpreters.DefuncAtWork

theorem cps_option_eq_cps (r: Regex) : ∀ (ns : List Int)
    (k1 : Option (List Int) → Option (List Int))
    (k2 : List Int → Bool)
    -- these need to be generalised
    (_hks : ∀ n, Option.isSome (k1 (some n)) = k2 n)
    -- k1 none doesn't relate to k2, but we just need to say it doesn't succeed "spuriously"
    (_hkn : k1 none = none),
    Option.isSome (CPSOption.matches_prefix r ns k1) =
      DefuncAtWork.matches_prefix r ns k2
    := by
  induction r with
  | Emp =>
    intro ns k1 k2 hks hkn
    simp [CPSOption.matches_prefix, DefuncAtWork.matches_prefix]
    -- the use of hks or hkn says how the continuations relate
    apply hks
  | Atom a =>
    intro ns k1 k2 hks hkn
    simp [CPSOption.matches_prefix, DefuncAtWork.matches_prefix]
    cases ns with
    | nil =>
      simp
      -- if the list is empty, neither match.
      -- k1 has no result, while k2 is not used.
      apply hkn
    | cons =>
      simp
      split -- if the list is nonempty, we still may not match
      next he =>
        simp [he]; apply hks -- match
      next hne =>
        simp [hne]; apply hkn -- no match
  | Seq r1 r2 ih1 ih2 =>
    intro ns k1 k2 hks hkn
    simp [CPSOption.matches_prefix, DefuncAtWork.matches_prefix]
    -- both push the remaining computation into the continuation,
    -- but on the left, we check the intermediate option result,
    -- while on the right, we unconditionally match using r2 in a continuation that may not be called.

    -- apply the IH to go inside the continuation.
    -- we need to generalise over the continuation for this.
    -- we now have to show that hks and hkn are preserved.
    apply ih1
    case _hks =>
      intro ns
      simp
      apply ih2 ns k1 k2 hks hkn -- both recursive calls occur
    case _hkn =>
      simp
      apply hkn -- continuation is not called
  | Disj r1 r2 ih1 ih2 =>
    intro ns k1 k2 hks hkn
    simp [CPSOption.matches_prefix, DefuncAtWork.matches_prefix]
    -- both cases short-circuit, one with <|>, the other with ||.
    cases he : CPSOption.matches_prefix r1 ns k1 <;> simp
    case some a =>
      -- if r1 matches, both take the left branch (ih1)
      left
      rw [← ih1 ns k1 k2 hks hkn, he]
      rfl
    case none =>
      -- otherwise, both take the right branch (ih2).
      -- ih1 tells us that the left branch isn't taken.
      rw [ih2 ns k1 k2 hks hkn]
      have h1 : DefuncAtWork.matches_prefix r1 ns k2 = false := by
        rw [← ih1 ns k1 k2 hks hkn, he]; rfl
      rw [h1, Bool.false_or]
