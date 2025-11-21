import Mathlib.Tactic
import Test.Libary.Bijections

open Bool

-- THis is mostly a learning excersise for myself and should not
-- be considered an example of good code that should be replicated.
-- Indeed I strongly suspect that I've made errors in style and
-- there are better ways to solve these problems.

-- A really simple test case.  Everything is bijective with itself.
theorem BijectionsReflexive {A} : hasBijection (A) (A) := by {
    rw [hasBijection]
    exists id
    exists id
}

-- My proof of cantor's theorm.  That |A| ≠ |2^A|
theorem cantor {A} : ¬ hasBijection (A) (A → Bool) := by {
    intro h1
    rw [hasBijection] at h1

    -- Use the ∃ to introduce the universal function
    -- its inverse and a witness to the left inverse
    obtain ⟨ f, ⟨ fi, ⟨left_inverse, _ ⟩⟩⟩ := h1

    -- Set up the anty diagonal a number stream that
    -- differs from every possible number stream.
    let AntiDiagonal : A → Bool := fun a ↦ !f a a

    -- Find the index of the diagonal
    let d : A := fi AntiDiagonal

    -- Ask what happens when the index of the anti-diagonal
    -- is fed into the diagonal function
    have := funext_iff.mp left_inverse AntiDiagonal
    have := funext_iff.mp this d

    exact (eq_not_self ((f ∘ fi) AntiDiagonal d)).mp this
}
