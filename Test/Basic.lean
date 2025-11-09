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

-- I am sure that there is a way to do this natively in lean.  However I wasn't able
-- to find this.
theorem comp_rewrite (X : Type) (Y : Type) (Z : Type) (f : Y → Z) (g : X → Y) (x : X) :
    (f ∘ g) x = f  (g x) := by rfl

-- My proof of cantor's theorm.  That |ℵ_0| ≠ |2^ℵ_0|
theorem cantor : ¬ isBijective (Nat) (Nat → Bool) := by {
    intro h1
    rw [isBijective] at h1

    -- I'm not sure if there is a better way to use a ∃ in a
    -- hypothiusis
    cases h1 with
    | intro f h2 =>
        cases h2 with
        | intro fi h3 =>

            -- we only need the left hand side of the bijection
            -- since we are proving the lack of an injection from
            -- |2^ℵ_0| to |ℵ_0|
            have h4 := h3.left

            -- Is there a cleaner way to add ᗡ to both sides
            rw [funext_iff] at h4
            let D : Nat → Bool := fun a ↦ !f a a
            specialize h4 D

            rw [funext_iff] at h4
            let d: Nat := fi D
            specialize h4 d

            rw [comp_rewrite] at h4

            -- Another case where I would think there is a more natural way
            -- to do this.
            have hdD : fi D = d := rfl
            rw [hdD] at h4

            rw [id] at h4
            have hDd : D d = !f d d := rfl
            rw [hDd] at h4

            -- exact? told me to do this
            exact (eq_not_self (f d d)).mp h4
}
