import Mathlib.Tactic
import Mathlib.Data.Set.Basic

open Nat
open Bool
open Set

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

theorem injectionTrans : ∀ (A B C), hasInjection (A) (B) ∧ hasInjection (B) (C) →
  hasInjection (A) (C) := by {
    rintro A B C
    rw[hasInjection, hasInjection, hasInjection]

    rintro ⟨ inj_ab, inj_bc ⟩
    obtain ⟨ f_ab, ⟨ f_ba, left_inverse_ab ⟩⟩ := inj_ab
    obtain ⟨ f_bc, ⟨ f_cb, left_inverse_bc ⟩⟩ := inj_bc

    use f_bc ∘ f_ab
    use f_ba ∘ f_cb

    rw[Function.comp_assoc]
    rw[← Function.comp_assoc f_cb]
    rw[left_inverse_bc]
    rw[Function.id_comp]
    exact left_inverse_ab
  }

theorem biImpInj : ∀ (A B), hasBijection (A) (B) →
   hasInjection (A) (B) ∧ hasInjection (B) (A) := by {
  intro A B

  rw[hasBijection, hasInjection, hasInjection]
  intro bi
  obtain ⟨ f_ab, ⟨ f_ba , ⟨ left_inverse, right_inverse ⟩ ⟩⟩ := bi

  apply And.intro
  case left =>
    use f_ab
    use f_ba

  case right =>
    use f_ba
    use f_ab
}

-- cancelInverse allows me to fi (f x) = x
theorem cancelInverse (A) (B) (f : A → B) (fi : B → A)
  (isInverse : fi ∘ f = id) (x : A) : (fi (f x)) = x := by {
  have cgy : (fi ∘ f) x = id x := by {exact congrFun isInverse x}
  rw [Function.comp_apply] at cgy
  rw [id] at cgy
  exact cgy
}

theorem inverseIsUnique (A) (B) (f : A → B) (fi : B → A)
  (isInverse : fi ∘ f = id) (y z a) (forwardEQ : a = f y) (backwardEQ : fi a = z) :
  (y = z ) := by {
    have ci := cancelInverse A B f fi isInverse z
    rw[← ci] at backwardEQ
    rw [forwardEQ] at backwardEQ
    rw [cancelInverse A B f fi isInverse, cancelInverse A B f fi isInverse] at backwardEQ
    exact backwardEQ
  }

def hasSurjection (A) (B) := ∃ (f : A → B), ∃ (fi : B → A), f ∘ fi = id
