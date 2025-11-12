import Mathlib.Tactic
import Test.Libary.Bijections

open Nat
open Bool

-- THis is mostly a learning excersise for myself and should not
-- be considered an example of good code that should be replicated.
-- Indeed I strongly suspect that I've made errors in style and
-- there are better ways to solve these problems.

-- A really simple test case.  Natural numbers are bijective with itself.
theorem natBijectsNat : hasBijection (Nat) (Nat) := by {
    rw [hasBijection]
    exists id
    exists id
}

-- My proof of cantor's theorm.  That |ℵ_0| ≠ |2^ℵ_0|
theorem cantor : ¬ hasBijection (Nat) (Nat → Bool) := by {
    intro h1
    rw [hasBijection] at h1

    -- Use the ∃ to introduce the universal function
    -- its inverse and a witness to the left inverse
    obtain ⟨ f, ⟨ fi, ⟨left_inverse, _ ⟩⟩⟩ := h1

    -- Set up the anty diagonal a number stream that
    -- differs from every possible number stream.
    let AntiDiagonal : Nat → Bool := fun a ↦ !f a a

    -- Find the index of the diagonal
    let d: Nat := fi AntiDiagonal

    -- Ask what happens when the index of the anti-diagonal
    -- is fed into the diagonal function
    have h2 := funext_iff.mp left_inverse AntiDiagonal
    have h5 := funext_iff.mp h2 d

    exact (eq_not_self ((f ∘ fi) AntiDiagonal d)).mp h5
}
