import Mathlib.Tactic

open Nat
open Bool

/- Proving things about bijections.-/

-- My definition of a bijection.  Yes I know there is one in the libary but this is in part
-- an excersize to allow me to teach myself lean.
def hasBijection (A) (B) :=
    ∃ (f : A → B), ∃ (fi : B → A), (f ∘ fi = id) ∧ (fi ∘ f = id)


-- bijections are transatrive
theorem bijectionTrans : ∀ (A B C), hasBijection (A) (B) ∧ hasBijection (B) (C) →
  hasBijection (A) (C) := by {

  rintro A B C h1
  rw[hasBijection, hasBijection] at h1

  obtain ⟨ fab, ⟨ fba, h2 ⟩⟩ := h1.left
  obtain ⟨ fbc, ⟨ fcb, h3 ⟩⟩ := h1.right

  let fac := fbc ∘ fab
  let fca := fba ∘ fcb

  have left_inverse : fac ∘ fca = id := by {
    rw[Function.comp_assoc]
    rw[← Function.comp_assoc fab fba]
    rw[h2.left]

    rw[← Function.comp_assoc fbc]
    rw[Function.comp_id]
    rw[h3.left]
  }

  have right_inverse : fca ∘ fac = id := by {
    rw[Function.comp_assoc]
    rw[← Function.comp_assoc fcb fbc]
    rw[h3.right]

    rw[← Function.comp_assoc fba]
    rw[Function.comp_id]
    rw[h2.right]
  }

  rw [hasBijection]
  exists fac
  exists fca
}

-- Bijection is communicative
theorem bijectionComm :  ∀ (A B), hasBijection (A) (B) ↔ hasBijection (B) (A) := by {
  rintro A B

  rw[hasBijection, hasBijection]

  apply Iff.intro

  case mp =>
    intro h1
    obtain ⟨f, ⟨fi, inverse_witness⟩⟩ := h1
    use fi
    use f
    rw [And.comm]
    exact inverse_witness

  case mpr =>
    intro h1
    obtain ⟨f, ⟨fi, inverse_witness⟩⟩ := h1
    use fi
    use f
    rw [And.comm]
    exact inverse_witness
}

def hasInjection (A) (B) := ∃ (f : A → B), ∃ (fi : B → A), fi ∘ f = id
