import Mathlib.Tactic

open Nat
open Bool

-- THis is mostly a learning excersise for myself and should not
-- be considered an example of good code that should be replicated.
-- Indeed I strongly suspect that I've made errors in style and
-- there are better ways to solve these problems.

-- Lean has a built in Bijective.  However in part this is so I grow
-- more familure with how to state that a bijunction exists between to
-- types.
def isBijective (A : Type) (B : Type) :=
    ∃ (f : A → B), ∃ (fi : B → A), (f ∘ fi = id) ∧ (fi ∘ f = id)

-- A really simple test case.  Natural numbers are bijective with itself.
theorem natBijectsNat : isBijective (Nat) (Nat) := by {
    rw [isBijective]
    exists id
    exists id
}

-- My proof of cantor's theorm.  That |ℵ_0| ≠ |2^ℵ_0|
theorem cantor : ¬ isBijective (Nat) (Nat → Bool) := by {
    intro h1
    rw [isBijective] at h1

    -- Use the ∃ to introduce the functions and its inverse
    rcases h1 with ⟨ f , ⟨fi, h2 ⟩  ⟩

    -- we only need the left hand side of the bijection
    -- since we are proving the lack of an injection from
    -- |2^ℵ_0| to |ℵ_0|
    have h3 := h2.left

    -- Set up the anty diagonal a number stream that
    -- differs from every possible number stream.
    let Diagonal : Nat → Bool := fun a ↦ !f a a
    have h4 := funext_iff.mp h3 Diagonal

    -- Find the index of the diagonal
    let d: Nat := fi Diagonal

    -- Ask what happens when the index of the anti-diagonal
    -- is fed into the diagonal function
    have h5 := funext_iff.mp h4 d

    exact (eq_not_self ((f ∘ fi) Diagonal d)).mp h5
}
