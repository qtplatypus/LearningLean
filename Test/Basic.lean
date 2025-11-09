import Mathlib.Tactic

open Nat
open Bool

def hello := "world"

def idNat (n : Nat) : Nat := n

theorem idNatClosed : idNat ∘ idNat = id := by
    ext x
    exact rfl

def isBijective (A : Type) (B : Type) (f : A → B) (fi : B → A) :=
    (f ∘ fi = id) ∧ (fi ∘ f = id)

theorem natBijectsNat : isBijective (Nat) (Nat) (idNat) (idNat) := by {
    apply And.intro
    apply idNatClosed
    apply idNatClosed
}

theorem comp_rewrite (X : Type) (Y : Type) (Z : Type) (f : Y → Z) (g : X → Y) (x : X) : (f ∘ g) x = f  (g x) := by rfl

theorem cantor : ¬ ∃ f:Nat→(Nat → Bool), ∃ fi:(Nat → Bool)→Nat,  isBijective (Nat) (Nat → Bool) (f) (fi):= by {
    intro h1
    cases h1 with
    | intro f h2 =>
        have hD : ∃ D: Nat → Bool, ∀n:Nat, D n = !(f n n) := by {
             exact Exists.intro (fun a ↦ !f a a) (congrFun rfl)
        }
        cases h2 with
        | intro fi h3 =>
            cases hD with
                | intro D h4 =>
                    have hb: ∃ b: Nat, fi D = b := by {
                        exact exists_eq'
                    }
                    cases hb with
                    | intro b h5 =>
                        rw [isBijective] at h3
                        have h6 := h4 b
                        nth_rw 2 [← h5] at h6
                        have h7 := h3.left
                        rw [funext_iff] at h7
                        have h8 := h7 D
                        rw [comp_rewrite] at h8
                        rw [h8] at h6
                        exact (eq_not_self (D b)).mp h6
}
--
